open Stdlib
open Fun
module Json = Yojson.Safe
open Json
open JmlAst

let (@), (@@) = (@@), (@)

let return = Result.ok
let (let*) = Result.bind

type error =
  | Normal_error of string
  | Unknown_variant of {class_name: string; types: string list}

type component = Field of string | Index of int
type path = component list

type 'a json_result = ('a, error * path) result

let error msg : 'a json_result =
  Error (Normal_error msg, [])

let unknown_variant class_name typ : 'a json_result =
  Error (Unknown_variant {class_name; types=[typ]}, [])

let rec all_ok ?(ix=0) = function
  | [] -> return []
  | Ok x :: t ->
    let* t' = all_ok ~ix:(ix+1) t in
    return (x :: t')
  | Error (error, path) :: _ ->
    Error (error, Index ix::path)

let string = function
  | `String str -> return str
  | json -> error ("Not a string: "^show json)

let bool = function
  | `Bool b -> return b
  | `Int 0 -> return false
  | `Int 1 -> return true
  | _ -> error "Not an bool"

let raw_int = function
  | `Int n -> return n
  | _ -> error "Not an int or too large"

let int = function
  | `Int n -> return (Why3.BigInt.of_int n)
  | `Intlit s -> return (Why3.BigInt.of_string s)
  | _ -> error "Not an int"

let empty_array = function
  | `List [] -> return ()
  | _ -> error "Not empty array"

let null = function
  | `Null -> return ()
  | _ -> error "Not null"

let list ?null k = function
  | `List jsons -> all_ok @ List.map k jsons
  | `Null when Option.is_some null -> return (Option.get null)
  | _ -> error "Not a json list"

let option (k : Json.t -> 'a json_result) : Json.t -> 'a option json_result = function
  | `Null -> return None
  | json ->
    let* res = k json in
    return @ Some res

type in_field = {
  in_field: 'a . string -> (Json.t -> 'a json_result) -> 'a json_result;
  has_field: string -> bool;
}

let in_fields fields =
  let in_field field k =
    Result.map_error (fun (error, path) -> error, Field field :: path) @
    let* json =
      List.assoc_opt field fields |>
      Option.to_result ~none:(Normal_error ("Field not found: "^field), []) in
    k json in
  let has_field field =
    List.assoc_opt field fields <> None in
  {in_field; has_field}

module Make (Arg: sig val resolve : string -> Json.t end) = struct

  let obj
      (type a)
      (objs : (string, a obj) Hashtbl.t)
      ?(subparsers:(string -> in_field -> a json_result) list=[])
      ?(class_names:string list option)
      (k:string -> in_field -> a json_result)
      (json: Json.t) =
    let obj_fields fields =
      let f = in_fields fields in
      let* class_name = f.in_field "@class" string in
      if Option.map (List.mem class_name) class_names = Some false then
        let open Format in
        let pp_list =
          let pp_sep fmt () = pp_print_string fmt ", " in
          pp_print_list ~pp_sep pp_print_string in
        unknown_variant class_name (asprintf "obj' %a" pp_list @ Option.get class_names)
      else
        let* id = f.in_field "@id" string in
        let* pos =
          if f.has_field "pos" then
            f.in_field "pos" raw_int |>
            Result.map Option.some
          else
            return None in
        let opt_value = ref None in
        let obj = lazy (Option.get !opt_value), (id, pos) in
        Hashtbl.add objs id obj;
        let* obj' =
          match k class_name f with
          | Ok _ | Error (Normal_error _, _) | Error (Unknown_variant _, _::_) as res ->
            res
          | Error (Unknown_variant info, []) ->
            assert (String.equal info.class_name class_name);
            let rec try_subparsers types = function
              | [] -> Error (Unknown_variant {class_name; types}, [])
              | subparser :: subparsers ->
                match subparser class_name f with
                | Error (Unknown_variant info, []) ->
                  assert (String.equal class_name info.class_name);
                  try_subparsers (types @@ info.types) subparsers
                | res -> res in
            try_subparsers info.types subparsers in
        opt_value := Some obj';
        return obj in
    match json with
    | `Assoc ["@ref", `String id] -> (* {"@ref": id}*)
      (try return (Hashtbl.find objs id)
       with Not_found ->
       match Arg.resolve id with
       | `Assoc fields -> obj_fields fields
       | json -> error ("Neither object nor reference: "^show json))
    | `Assoc fields -> obj_fields fields
    | json -> error ("Neither object nor reference: "^show json)

  let rec typ' class_name f =
    match class_name with
    | "Type$BottomType" ->
      return @ BotType
    | "JCTree$JCIdent" ->
      let* name = f.in_field "name" string in
      let* typ = f.in_field "type" typ in
      let* sym = f.in_field "sym" symbol in
      return @ TypIdent {name; typ; sym}
    | "Type$1" ->
      let* tsym = f.in_field "tsym" null in
      return @ Typ1 {tsym}
    | "Type$JCVoidType" ->
      return @ VoidType
    | "Type$ArrayType" ->
      let* tsym = f.in_field "tsym" type_symbol in
      let* elemtype = f.in_field "elemtype" typ in
      return @ ArrayType {tsym; elemtype}
    | "Type$MethodType" ->
      let* tsym = f.in_field "tsym" type_symbol in
      let* argtypes = f.in_field "argtypes" (list typ) in
      let* restype = f.in_field "restype" typ in
      return @ MethodType {tsym; argtypes; restype}
    | "Type$ErasedClassType" ->
      let* tsym = f.in_field "tsym" type_symbol in
      let* typarams = f.in_field "typarams_field" (list ~null:[] typ) in
      let* supertype = f.in_field "supertype_field" (option typ) in
      let* interfaces = f.in_field "interfaces_field" (list ~null:[] typ) in
      return @ ErasedClassType {tsym; typarams; supertype; interfaces}
    | "Type$ClassType" ->
      let* tsym = f.in_field "tsym" type_symbol in
      let* typarams = f.in_field "typarams_field" (list ~null:[] typ) in
      let* supertype = f.in_field "supertype_field" (option typ) in
      let* interfaces = f.in_field "interfaces_field" (list ~null:[] typ) in
      return @ ClassType {tsym; typarams; supertype; interfaces}
    | "Type$ForAll" ->
      let* tsym = f.in_field "tsym" type_symbol in
      let* tvars = f.in_field "tvars" (list typ) in
      let* qtype = f.in_field "qtype" typ in
      let* tag = f.in_field "tag" type_tag in
      return @ ForAllType {tsym; tvars; qtype; tag}
    | "Type$TypeVar" ->
      let* tsym = f.in_field "tsym" type_symbol in
      return @ TypeVarType {tsym}
    | "Type$JCPrimitiveType$1" (* FIXME what is `Type.constValue()`? *)
    | "Type$JCPrimitiveType" ->
      let* type_tag = f.in_field "tag" type_tag in
      return @ PrimitiveType {type_tag}
    | "Type$AnnotatedType" ->
      let* type_annotations = f.in_field "typeAnnotations" (list type_compound) in
      let* underlying_type = f.in_field "underlyingType" typ in
      let* tsym = f.in_field "tsym" type_symbol in
      return @ AnnotatedType {type_annotations; underlying_type; tsym}
    | "Type$PackageType" ->
      let* tsym = f.in_field "tsym" type_symbol in
      return @ PackageType {tsym}
    | "ClassReader$2" ->
      return @ ClassReader
    | _ -> unknown_variant class_name "typ"

  and typ_objs = Hashtbl.create 13
  and typ json : typ json_result =
    obj typ_objs typ' json

  and type_compound _json = return ()

  and type_symbol' class_name f =
    match class_name with
    | "Symbol$TypeVariableSymbol" ->
      let* name = f.in_field "name" string in
      let* typ = f.in_field "type" typ in
      let* owner = f.in_field "owner" (option symbol) in
      return @ TypeVariableSymbol {name; typ; owner}
    | "Symbol$ClassSymbol" ->
      let* name = f.in_field "name" string in
      let* fullname = f.in_field "fullname" string in
      let* typ = f.in_field "type" typ in
      let* owner = f.in_field "owner" (option symbol) in
      return @ ClassSymbol {name; fullname; typ; owner}
    | "Symbol$PackageSymbol" ->
      let* name = f.in_field "name" string in
      let* owner = f.in_field "owner" (option symbol) in
      return @ PackageSymbol {name; owner}
    | "Symtab$3" | "Symtab$UnnamedPackageSymbol" ->
      return @ UnnamedPackage (* ??? *)
    | "Symtab$NoTypeSymbol" ->
      return @ NoTypeSymbol (* ??? *)
    | _ -> unknown_variant class_name "type_symbol"

  and type_symbol_objs = Hashtbl.create 13
  and type_symbol json : type_symbol json_result =
    obj type_symbol_objs type_symbol' json

  and var_symbol' _ f =
    let* name = f.in_field "name" string in
    let* typ = f.in_field "type" typ in
    let* owner = f.in_field "owner" (option symbol) in
    return @ VarSymbol {name; typ; owner}

  and var_symbol_objs = Hashtbl.create 13
  and var_symbol json =
    obj var_symbol_objs var_symbol' json

  and method_symbol' class_name f =
    match class_name with
    | "Symbol$MethodSymbol" ->
      let* name = f.in_field "name" string in
      let* typ = f.in_field "type" (option typ) in
      let* owner = f.in_field "owner" (option symbol) in
      return @ MethodSymbol {name; typ; owner}
    | _ -> unknown_variant class_name "method_symbol"

  and method_symbol_objs = Hashtbl.create 13
  and method_symbol json =
    obj method_symbol_objs method_symbol' json

  and symbol' class_name f =
    match class_name with
    | "Symbol$OperatorSymbol" ->
      let* name = f.in_field "name" string in
      let* typ = f.in_field "type" typ in
      let* owner = f.in_field "owner" (option symbol) in
      return @ OperatorSymbol {name; typ; owner}
    | "Symbol$VarSymbol" ->
      let* var_symbol = var_symbol' class_name f in
      return @ VarSymbol' var_symbol
    | _ -> Error (Unknown_variant {class_name; types=["symbol"]}, [])

  and symbol_objs = Hashtbl.create 13
  and symbol json : symbol json_result =
    let subparsers = [
      (fun n f -> let* ms = method_symbol' n f in return @ MethodSymbol' ms);
      (fun n f -> let* ts = type_symbol' n f in return @ TypeSymbol' ts);
    ] in
    obj symbol_objs ~subparsers symbol' json

  and type_tag json : type_tag json_result =
    let* str = string json in
    match str with
    | "INT" -> return TagInt
    | "VOID" -> return TagVoid
    | "BOOLEAN" -> return TagBool
    | "FORALL" -> return TagForall
    | "CLASS" -> return TagClass
    | "BOT" -> return TagBot
    | _ -> error ("Unknow type tag: "^str)

  and type_specs' class_name f =
    match class_name with
    | "JmlSpecs$TypeSpecs" ->
      let* clauses = f.in_field "clauses" (list type_clause) in
      return @ TypeSpecs {clauses}
    | _ -> unknown_variant class_name "type_specs"

  and type_specs_objs = Hashtbl.create 13
  and type_specs json : type_specs json_result =
    obj type_specs_objs type_specs' json

  and type_clause' class_name f =
    match class_name with
    | "JmlTree$JmlTypeClauseExpr" ->
      let* keyword = f.in_field "keyword" (option string) in
      let* clause_type = f.in_field "clauseType" jml_clause_kind in
      let* expr = f.in_field "expression" expr in
      return @ TypeClauseExpr {keyword; clause_type; expr}
    | "JmlTree$JmlTypeClauseRepresents" ->
      let* keyword = f.in_field "keyword" (option string) in
      let* clause_type = f.in_field "clauseType" jml_clause_kind in
      let* ident = f.in_field "ident" expr in
      let* such_that = f.in_field "suchThat" bool in
      let* expr = f.in_field "expression" expr in
      return @ TypeClauseRepresents {keyword; clause_type; ident; such_that; expr}
    | _ -> unknown_variant class_name "type_clause"

  and type_clause_objs = Hashtbl.create 13
  and type_clause json : jml_type_clause json_result =
    obj type_clause_objs type_clause' json

  and variable_decl' f : variable_decl' json_result =
    let* name = f.in_field "name" string in
    let* vartype = f.in_field "vartype" expr in
    let* typ = f.in_field "type" typ in
    let* nameexpr = f.in_field "nameexpr" (option expr) in
    let* init = f.in_field "init" (option expr) in
    let* sym = f.in_field "sym" var_symbol in
    let* mods = f.in_field "mods" modifiers in
    return {typ; name; nameexpr; vartype; init; sym; mods}

  and annotation_objs = Hashtbl.create 13
  and annotation json =
    flip (obj annotation_objs) json @ fun class_name f ->
      match class_name with
      | "JmlTree$JmlAnnotation" ->
        let* annotation_type = f.in_field "annotationType" tree in
        let* args = f.in_field "args" (list expr) in
        return @ {annotation_type; args}
      | _ -> unknown_variant class_name "annotation"

  and modifiers_objs = Hashtbl.create 13
  and modifiers json =
    let flag : Json.t -> modifier json_result = function
      | `List [`String "Modifier"; `String "final"] ->
        return Final
      | `List [`String "Modifier"; `String "private"] ->
        return Private
      | `List [`String "Modifier"; `String "public"] ->
        return Public
      | `List [`String "Modifier"; `String "static"] ->
        return Static
      | _ ->
        error "Unknown modifier" in
    flip (obj modifiers_objs) json @ fun class_name f ->
      match class_name with
      | "JCTree$JCModifiers" ->
        let* flags = f.in_field "flags" (list flag) in
        let* annotations = f.in_field "annotations" (list annotation) in
        return @ {flags; annotations}
      | _ ->
        unknown_variant class_name "modifiers"

  and variable_decl_objs = Hashtbl.create 13
  and variable_decl json : variable_decl json_result =
    obj variable_decl_objs ~class_names:["JmlTree$JmlVariableDecl"]
      (fun _ -> variable_decl') json

  and jml_expr' class_name f =
    match class_name with
    | "JmlTree$JmlBinary" ->
      let* typ = f.in_field "type" typ in
      let* lhs = f.in_field "lhs" expr in
      let* rhs = f.in_field "rhs" expr in
      let* op = f.in_field "op" jml_clause_kind in
      return @ JmlBinary {typ; lhs; rhs; op}
    | _ -> unknown_variant class_name "jml_expr'"

  and expr_objs = Hashtbl.create 13
  and expr json : expr json_result =
    let subparsers = [
      (fun class_name f -> let* jml_expr = jml_expr' class_name f in return @ JmlExpr' jml_expr);
    ] in
    obj expr_objs ~subparsers expr' json

  and expr' class_name f =
    match class_name with
    | "JCTree$JCArrayTypeTree" ->
      let* typ = f.in_field "type" typ in
      let* elemtype = f.in_field "elemtype" expr in
      return @ ArrayTypeTree {typ; elemtype}
    | "JCTree$JCPrimitiveTypeTree" ->
      let* typ = f.in_field "type" typ in
      let* type_tag = f.in_field "typetag" type_tag in
      return @ PrimitiveTypeTree {typ; type_tag}
    | "JCTree$JCIdent" ->
      let* name = f.in_field "name" string in
      let* typ = f.in_field "type" (option typ) in
      let* sym = f.in_field "sym" (option symbol) in
      (match typ, sym with
       | Some typ, Some sym ->
         return @ Ident {name; typ; sym}
       | None, None ->
         return @ PlainIdent {name}
       | _ ->
         error "Neither ident nor plain ident")
    | "JCTree$JCAssign" ->
      let* typ = f.in_field "type" typ in
      let* lhs = f.in_field "lhs" expr in
      let* rhs = f.in_field "rhs" expr in
      return @ Assign {typ; lhs; rhs}
    | "JCTree$JCFieldAccess" ->
      let* typ = f.in_field "type" typ in
      let* selected = f.in_field "selected" expr in
      let* name = f.in_field "name" string in
      let* sym = f.in_field "sym" symbol in
      return @ FieldAccess {typ; selected; name; sym}
    | "JCTree$JCArrayAccess" ->
      let* typ = f.in_field "type" typ in
      let* indexed = f.in_field "indexed" expr in
      let* index = f.in_field "index" expr in
      return @ ArrayAccess {typ; indexed; index}
    | "JCTree$JCNewArray" ->
      let* typ = f.in_field "type" typ in
      let* elemtype = f.in_field "elemtype" expr in
      let* dims = f.in_field "dims" (list expr) in
      let* elems = f.in_field "elems" (list ~null:[] expr) in
      return @ NewArray {typ; elemtype; dims; elems}
    | "JCTree$JCBinary" ->
      let* typ = f.in_field "type" typ in
      let* lhs = f.in_field "lhs" expr in
      let* rhs = f.in_field "rhs" expr in
      let* operator = f.in_field "operator" symbol in
      return @ Binary {typ; lhs; rhs; operator}
    | "JCTree$JCUnary" ->
      let* typ = f.in_field "type" typ in
      let* arg = f.in_field "arg" expr in
      let* operator = f.in_field "operator" symbol in
      return @ Unary {typ; arg; operator}
    | "JCTree$JCTypeApply" ->
      let* typ = f.in_field "type" typ in
      let* clazz = f.in_field "clazz" expr in
      let* arguments = f.in_field "arguments" (list expr) in
      return @ TypeApply {typ; clazz; arguments}
    | "JCTree$JCLiteral" ->
      let* typ = f.in_field "type" typ in
      let* type_tag = f.in_field "typetag" type_tag in
      Result.map (fun l -> Literal' l) @
      (match type_tag with
       | TagInt ->
         let* value = f.in_field "value" int in
         return @ (IntLiteral {typ; value})
       | TagBool ->
         let* value = f.in_field "value" bool in
         return @ (BoolLiteral {typ; value})
       | TagBot ->
         return @ BotLiteral {typ}
       | _ ->
         error "literal not implemented")
         (* (\* TODO value *\)
          * return @ (OtherLiteral {typ; type_tag})) *)
    | "JCTree$JCParens" ->
      let* typ = f.in_field "type" typ in
      let* expr = f.in_field "expr" expr in
      return @ Parens {typ; expr}
    | "JmlTree$JmlQuantifiedExpr" ->
      let* typ = f.in_field "type" typ in
      let* kind = f.in_field "kind" jml_clause_kind in
      let* decls = f.in_field "decls" @ list @ function
          | `Assoc fields -> variable_decl' (in_fields fields)
          | _ -> error "decls not an object" in
      let* range = f.in_field "range" expr in
      let* value = f.in_field "value" expr in
      return @ QuantifiedExpr {typ; kind; decls; range; value}
    | "JCTree$JCNewClass" ->
      let* typ = f.in_field "type" typ in
      let* constructor = f.in_field "constructor" method_symbol in
      let* clazz = f.in_field "clazz" expr in
      let* args = f.in_field "args" (list expr) in
      return @ NewClass {typ; constructor; clazz; args}
    | "JCTree$JCAssignOp" ->
      let* typ = f.in_field "type" typ in
      let* lhs = f.in_field "lhs" expr in
      let* rhs = f.in_field "rhs" expr in
      let* operator = f.in_field "operator" symbol in
      return @ AssignOp {typ; lhs; rhs; operator}
    | "JmlTree$JmlStoreRefKeyword" ->
      let* kind = f.in_field "kind" jml_clause_kind in
      return @ JmlStoreRefKeyword {kind}
    | "JCTree$JCMethodInvocation" ->
      let* typ = f.in_field "type" typ in
      let* typeargs = f.in_field "typeargs" (list expr) in
      let* meth = f.in_field "meth" (option expr) in
      let* args = f.in_field "args" (list expr) in
      return @ MethodInvocation {typ; typeargs; meth; args; kind=None}
    | "JmlTree$JmlMethodInvocation" ->
      let* kind = f.in_field "kind" (option jml_clause_kind) in
      let* typ = f.in_field "type" typ in
      let* typeargs = f.in_field "typeargs" (list expr) in
      let* meth = f.in_field "meth" (option expr) in
      let* args = f.in_field "args" (list expr) in
      return @ MethodInvocation {typ; typeargs; meth; args; kind}
    | "JmlTree$JmlSingleton" ->
      let* typ = f.in_field "type" typ in
      let* kind = f.in_field "kind" jml_clause_kind in
      return @ JmlSingleton {typ; kind}
    | _ -> unknown_variant class_name "expr"

  and statement' class_name f : statement' json_result =
    match class_name with
    | "JCTree$JCIf" ->
      let* cond = f.in_field "cond" expr in
      let* thenpart = f.in_field "thenpart" statement in
      let* elsepart = f.in_field "elsepart" (option statement) in
      return @ If {cond; thenpart; elsepart}
    | "JCTree$JCReturn" ->
      let* expr = f.in_field "expr" expr in
      return @ Return {expr}
    | "JmlTree$JmlVariableDecl" ->
      let* var_decl = variable_decl' f in
      return @ VariableDecl var_decl
    | "JCTree$JCLabeledStatement" ->
      let* label = f.in_field "label" string in
      let* body = f.in_field "body" statement in
      return @ Label {label; body}
    | "JmlTree$JmlStatementExpr" ->
      let* typ = f.in_field "type" (option typ) in
      let* keyword = f.in_field "keyword" string in
      let* clause_type = f.in_field "clauseType" jml_clause_kind in
      let* expr = f.in_field "expression" expr in
      return @ JmlStatementExpr {typ; keyword; clause_type; expr}
    | "JCTree$JCExpressionStatement" ->
      let* expr = f.in_field "expr" expr in
      return @ ExprStatement {expr}
    | "JmlTree$JmlStatement" ->
      let* typ = f.in_field "type" typ in
      let* statement = f.in_field "statement" statement in
      let* keyword = f.in_field "keyword" string in
      let* clause_type = f.in_field "clauseType" jml_clause_kind in
      return @ JmlStatement {typ; statement; keyword; clause_type}
    | "JmlTree$JmlBlock" ->
      let* block = block' f in
      return @ Block' block
    | "JmlTree$JmlForLoop" ->
      let* typ = f.in_field "type" (option typ) in
      let* loop_specs = f.in_field "loopSpecs" (list ~null:[] statement_loop) in
      let* init = f.in_field "init" (list statement) in
      let* cond = f.in_field "cond" expr in
      let* step = f.in_field "step" (list expr_statement) in
      let* body = f.in_field "body" statement in
      return @ ForLoop {typ; loop_specs; init; cond; step; body}
    | "JmlTree$JmlEnhancedForLoop" ->
      let* typ = f.in_field "type" (option typ) in
      let* var = f.in_field "var" variable_decl in
      let* expr = f.in_field "expr" expr in
      let* body = f.in_field "body" statement in
      let* loop_specs = f.in_field "loopSpecs" (list statement_loop) in
      return @ EnhancedForLoop {typ; var; expr; body; loop_specs}
    | "JCTree$JCThrow" ->
      let* expr = f.in_field "expr" expr in
      return @ Throw {expr}
    | "JCTree$JCTry" ->
      let* body = f.in_field "body" block in
      let* catchers = f.in_field "catchers" (list catch) in
      let* finalizer = f.in_field "finalizer" (option block) in
      let* resources = f.in_field "resources" (list tree) in
      return @ Try {body; catchers; finalizer; resources}
    | "JmlTree$JmlImport" ->
      let* qualid = f.in_field "qualid" tree in
      return @ Import {qualid}
    | _ -> unknown_variant class_name "statement"

  and statement_objs = Hashtbl.create 13
  and statement json : statement json_result =
    obj statement_objs statement' json

  and expr_statement_objs = Hashtbl.create 13
  and expr_statement json : expr_statement json_result =
    obj expr_statement_objs expr_statement' json

  and expr_statement' (class_name:string) (f:in_field) : expr_statement' json_result =
    match class_name with
    | "JCTree$JCExpressionStatement" ->
      let* expr = f.in_field "expr" expr in
      return @ {expr}
    | _ -> unknown_variant class_name "expr_statement"

  and catch_objs = Hashtbl.create 13
  and catch json : catch json_result =
    flip (obj catch_objs) json @ fun class_name f ->
      match class_name with
      | "JCTree$JCCatch" ->
        let* param = f.in_field "param" variable_decl in
        let* body = f.in_field "body" block in
        return @ Catch {param; body}
      | _ -> unknown_variant class_name "catcher"

  and block' f =
    let* stats = f.in_field "stats" (list statement) in
    let* cases = f.in_field "cases" (option jml_method_specs) in
    return {stats; cases}

  and block_objs = Hashtbl.create 13
  and block json : block json_result =
    obj block_objs ~class_names:["JmlTree$JmlBlock"] (fun _ -> block') json

  and statement_loop_objs = Hashtbl.create 13
  and statement_loop json : jml_statement_loop json_result =
    flip (obj statement_loop_objs) json @ fun class_name f ->
      match class_name with
      | "JmlTree$JmlStatementLoopExpr" ->
        let* expr = f.in_field "expression" expr in
        return @ StatementLoopExpr {expr}
      | "JmlTree$JmlStatementLoopModifies" ->
        return @ StatementLoopModifies
      | _ -> unknown_variant class_name "statement_loop"

  and method_specs_objs = Hashtbl.create 13
  and method_specs json =
    flip (obj method_specs_objs) json @ fun class_name f ->
      match class_name with
      | "JmlSpecs$MethodSpecs" ->
        let* cases = f.in_field "cases" jml_method_specs in
        let* () = f.in_field "queryDatagroup" null in
        let* () = f.in_field "secretDatagroup" null in
        return @ MethodSpecs {cases}
      | _ -> unknown_variant class_name "method_specs"

  and jml_method_clause_objs = Hashtbl.create 13
  and jml_method_clause json =
    flip (obj jml_method_clause_objs) json @ fun class_name f ->
      match class_name with
      | "JmlTree$JmlMethodClauseSignalsOnly" ->
        let* list = f.in_field "list" (list expr) in
        return @ JmlMethodClauseSignalsOnly {list}
      | "JmlTree$JmlMethodClauseStoreRef" ->
        let* list = f.in_field "list" (list expr) in
        return @ JmlMethodClauseStoreRef {list}
      | "JmlTree$JmlMethodClauseSignals" ->
        let* vardef = f.in_field "vardef" (option variable_decl) in
        let* expr = f.in_field "expression" expr in
        return @ JmlMethodClauseSignals {vardef; expr}
      | "RequiresClause$Node" ->
        let* keyword = f.in_field "keyword" string in
        let* clause_kind = f.in_field "clauseKind" jml_clause_kind in
        let* exc_typ = f.in_field "exceptionType" (option expr) in
        let* expr = f.in_field "expression" expr in
        return @ JmlMethodClauseExprExc {keyword; clause_kind; expr; exc_typ}
      | "JmlTree$JmlMethodClauseExpr" ->
        let* keyword = f.in_field "keyword" string in
        let* clause_kind = f.in_field "clauseKind" jml_clause_kind in
        let* expr = f.in_field "expression" expr in
        return @ JmlMethodClauseExpr {keyword; clause_kind; expr}
      | _ -> unknown_variant class_name "jml_method_clause"

  and jml_clause_kind_objs = Hashtbl.create 13
  and jml_clause_kind json : jml_clause_kind json_result =
    flip (obj jml_clause_kind_objs) json @ fun class_name f ->
      match class_name with
      | "MethodExprClauseExtensions$1"
      | "RequiresClause$1" ->
        let* keyword = f.in_field "keyword" string in
        return @ MethodClauseExprType {keyword}
      | "MiscExtensions$NoTypeMisc" ->
        let* keyword = f.in_field "keyword" string in
        return @ NoTypeMisc {keyword}
      | "TypeExprClauseExtension$TypeClause" ->
        let* keyword = f.in_field "keyword" string in
        return @ TypeClause {keyword}
      | "StateExpressions$StateExpression" ->
        let* keyword = f.in_field "keyword" string in
        return @ StateExpression {keyword}
      | "QuantifiedExpressions$QuantifiedExpression" ->
        let* keyword = f.in_field "keyword" string in
        return @ QuantifiedExpression {keyword}
      | "Operators$Operator"
      | "SetStatement$JmlStatementType"
      | "SingletonExpressions$1"
      | "StatementExprType"
      | "FunctionLikeExpressions$8"
      | "FunctionLikeExpressions$9"
      | "TypeRepresentsClauseExtension$1" ->
        let* keyword = f.in_field "keyword" string in
        return @ OtherClauseKind {keyword; class_name}
      | _ -> unknown_variant class_name "jml_clause_kind"

  and jml_specification_case_objs = Hashtbl.create 13
  and jml_specification_case json =
    flip (obj jml_specification_case_objs) json @ fun class_name f ->
      match class_name with
      | "JmlTree$JmlSpecificationCase" ->
        let* token = f.in_field "token" (option (list string)) in
        let* token =
          match token with
            | Some ["JmlTokenKind"; token] -> return (Some token)
            | None -> return None
            | _ -> error "Strange token" in
        let* clauses = f.in_field "clauses" (list jml_method_clause) in
        return @ JmlSpecificationCase {clauses; token}
      | _ -> unknown_variant class_name "jml_specification_case"

  and jml_method_specs_objs = Hashtbl.create 13
  and jml_method_specs json =
    flip (obj jml_method_specs_objs) json @ fun class_name f ->
      match class_name with
      | "JmlTree$JmlMethodSpecs" ->
        let* cases = f.in_field "cases" (list jml_specification_case) in
        let* () = f.in_field "impliesThatCases" empty_array in
        let* () = f.in_field "forExampleCases" empty_array in
        return @ JmlMethodSpecs {cases}
      | _ -> unknown_variant class_name "jml_method_specs"

  and type_param_objs = Hashtbl.create 13
  and type_param json =
    flip (obj type_param_objs) json @ fun class_name f ->
      match class_name with
      | "JCTree$JCTypeParameter" ->
        let* name = f.in_field "name" string in
        let* bounds = f.in_field "bounds" (list expr) in
        return @ TypeParameter {name; bounds}
      | _ -> unknown_variant class_name "type_param"

  and tree_objs = Hashtbl.create 13
  and tree json : tree json_result =
    let subparsers = [
      (fun class_name f -> let* stat = statement' class_name f in return @ Statement' stat);
      (fun class_name f -> let* expr = expr' class_name f in return @ Expr' expr);
    ] in
    flip (obj tree_objs ~subparsers) json @ fun class_name f ->
      match class_name with
      | "JmlTree$JmlClassDecl" ->
        let* typ = f.in_field "type" typ in
        let* sym = f.in_field "sym" type_symbol in
        let* name = f.in_field "name" string in
        let* defs = f.in_field "defs" (list tree) in
        let* typarams = f.in_field "typarams" (list type_param) in
        let* type_specs = f.in_field "typeSpecs" type_specs in
        let* extending = f.in_field "extending" (option expr) in
        return @ ClassDecl {typ; sym; name; defs; type_specs; extending; typarams}
      | "JmlTree$JmlMethodDecl" ->
        let* name = f.in_field "name" string in
        let* sym = f.in_field "sym" method_symbol in
        let* restype = f.in_field "restype" (option expr) in
        let* typ = f.in_field "type" typ in
        let* params = f.in_field "params" (list tree) in
        let* body = f.in_field "body" (option tree) in
        let* throws = f.in_field "thrown" (list expr) in
        let* this = f.in_field "_this" (option var_symbol) in
        let* specs = f.in_field "methodSpecsCombined" method_specs in
        let* mods = f.in_field "mods" modifiers in
        return @ MethodDecl {name; sym; typ; restype; params; body; throws; specs; this; mods}
      | _ -> unknown_variant class_name "tree"

  and compilation_unit' class_name f =
    match class_name with
    | "JmlTree$JmlCompilationUnit" ->
      let* defs = f.in_field "defs" (list tree) in
      return @ CompilationUnit {defs}
    | _ -> unknown_variant class_name "compilation_unit"

  and compilation_unit_objs = Hashtbl.create 13
  and compilation_unit json : compilation_unit json_result =
    obj compilation_unit_objs compilation_unit' json
end

module ObjIdMap = Map.Make (ObjId)

let rec collect_objs m = function
  | `Null | `Bool _ | `Int _ | `Intlit _ | `Float _ | `String _ -> m
  | `Assoc fields as json ->
    let m =
      match List.assoc_opt "@id" fields with
      | Some (`String id) ->
        ObjIdMap.add id json m
      | _ -> m in
    List.fold_right (fun (_, json) m -> collect_objs m json) fields m
  | `List l ->
    List.fold_right (fun json m -> collect_objs m json) l m
  | `Tuple _ | `Variant _ ->
    failwith "collect_ids"

let compilation_unit json =
  let objs = collect_objs ObjIdMap.empty json in
  let resolve id = ObjIdMap.find id objs in
  let module M = Make (struct let resolve = resolve end) in
  M.compilation_unit json

let pp_error fmt =
  let open Format in
  let pp_path fmt =
    let pp_comp fmt = function
      | Index ix -> fprintf fmt "[%d]" ix
      | Field f -> fprintf fmt ".%s" f in
    List.iter (pp_comp fmt) in
  function
  | Normal_error error, path ->
    fprintf fmt "Error: %s at path %a@." error pp_path path;
  | Unknown_variant {class_name; types}, path ->
    let pp_types =
      let pp_sep fmt () = pp_print_string fmt ", " in
      pp_print_list ~pp_sep pp_print_string in
    fprintf fmt "Unknown variant %s (tried %a) at path %a@."
      class_name pp_types types pp_path path

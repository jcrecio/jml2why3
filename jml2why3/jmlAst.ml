(* To break cyclic references in the AST, (shared) objects are only specified in one
   occurrences but identified by an id, and referenced in further occurrences. *)

module ObjId = struct
  type t = string
  let compare = String.compare
end

(** An object combines a lazy value, an object ID, and a (integer) position. *)
type 'a obj = 'a Lazy.t * (ObjId.t * int option)

let id : 'a obj -> ObjId.t = function
  | _, (id, _) -> id

let pos : 'a obj -> int option = function
  | _, (_, pos) -> pos

let force : 'a obj -> 'a = function
  | lazy x, _ -> x

module ObjIdSet = Set.Make (ObjId)

let pp_ids = ref ObjIdSet.empty

let reset_pp_obj () =
  pp_ids := ObjIdSet.empty

(* (\** Print objects only on first encounter **\)
 * let pp_obj pp fmt = function
 *   | lazy value, id ->
 *     if ObjIdSet.mem id !pp_ids then
 *       Format.fprintf fmt "!%s" id
 *     else
 *       (pp_ids := ObjIdSet.add id !pp_ids;
 *        Format.fprintf fmt "%s:%a" id pp value) *)

(** Don't reprint nested objects twice *)
let pp_obj pp fmt = function
  | lazy value, (id, pos) ->
    if ObjIdSet.mem id !pp_ids then
      Format.fprintf fmt "!%s" id
    else
      (pp_ids := ObjIdSet.add id !pp_ids;
       let pp_pos fmt = match pos with None -> () | Some pos -> Format.fprintf fmt "/%d" pos in
       Format.fprintf fmt "%s%t:%a" id pp_pos pp value;
       pp_ids := ObjIdSet.remove id !pp_ids)

(* com.sun.tools.javac.code.TypeTag *)
type type_tag =
  | TagInt
  | TagVoid
  | TagForall
  | TagClass
  | TagBool
  | TagBot
[@@deriving show { with_path = false }]

(* org.jmlspecs.openjml.IJmlClauseKind *)
type jml_clause_kind' =
  | MethodClauseExprType of {keyword: string}
  | OtherClauseKind of {keyword: string; class_name: string}
  | TypeClause of {keyword: string}
  | NoTypeMisc of {keyword: string}
  | StateExpression of {keyword: string}
  | QuantifiedExpression of {keyword: string}
and jml_clause_kind = jml_clause_kind' obj

(* com.sun.tools.javac.code.Attribute.TypeCompound *)
and type_compound = unit

(* com.sun.tools.javac.code.Type *)
and typ' =
  | TypIdent of {name: string; typ: typ; sym: symbol}
  | AnnotatedType of {type_annotations: type_compound list; underlying_type: typ; tsym: type_symbol}
  | ArrayType of {elemtype: typ; tsym: type_symbol}
  | ClassType of {typarams: typ list; supertype: typ option [@opaque]; interfaces: typ list [@opaque]; tsym: type_symbol}
  | ErasedClassType of {typarams: typ list; supertype: typ option [@opaque]; interfaces: typ list [@opaque]; tsym: type_symbol}
  | ForAllType of {tvars: typ list; qtype: typ; tag: type_tag; tsym: type_symbol}
  | MethodType of {argtypes: typ list; restype: typ; tsym: type_symbol}
  | TypeVarType of {tsym: type_symbol}
  | PrimitiveType of {type_tag: type_tag}
  | PackageType of {tsym: type_symbol}
  | ClassReader
  | VoidType
  | BotType
  | Typ1 of {tsym: unit}
and typ = typ' obj

(* com.sun.tools.javac.code.Symbol.TypeSymbol *)
and type_symbol' =
  | TypeVariableSymbol of {name: string; typ: typ; owner: symbol option}
  | ClassSymbol of {name: string; fullname: string; typ: typ; owner: symbol option}
  | PackageSymbol of {name: string; owner: symbol option}
  | UnnamedPackage (* Anonymous, https://github.com/OpenJML/OpenJML/blob/8fcde85b3670e833b16d94c0f22793ac58a76e0c/OpenJDK/trunk/langtools/src/share/classes/com/sun/tools/javac/code/Symtab.java#L395 *)
  | NoTypeSymbol (* Anonymous, https://github.com/OpenJML/OpenJML/blob/8fcde85b3670e833b16d94c0f22793ac58a76e0c/OpenJDK/trunk/langtools/src/share/classes/com/sun/tools/javac/code/Symtab.java#L400 *)
and type_symbol = type_symbol' obj

(* com.sun.tools.javac.code.Symbol.VarSymbol *)
and var_symbol' = VarSymbol of {name: string; typ: typ; owner: symbol option}
and var_symbol = var_symbol' obj

and method_symbol' = MethodSymbol of {name: string; typ: typ option; owner: symbol option}
and method_symbol = method_symbol' obj

(* com.sun.tools.javac.code.Symbol *)
and symbol' =
  | TypeSymbol' of type_symbol'
  | VarSymbol' of var_symbol'
  | MethodSymbol' of method_symbol'
  | OperatorSymbol of {name: string; typ: typ; owner: symbol option}
and symbol = symbol' obj
[@@deriving show { with_path = false }]

type literal' =
  | IntLiteral of {typ: typ; value: Why3.BigInt.t [@printer fun fmt n -> Format.pp_print_string fmt (Why3.BigInt.to_string n)]}
  | BoolLiteral of {typ: typ; value: bool}
  | BotLiteral of {typ: typ}
  (* | OtherLiteral of {typ: typ; type_tag: type_tag} *)
[@@deriving show { with_path = false }]

(* javax.lang.model.element.Modifier *)
type modifier = Public | Protected | Private | Abstract | Default | Static | Final | Transient | Volatile | Synchronized | Native | Strictfp
[@@deriving show { with_path = false }]

(* com.sun.tools.javac.tree.JCTree.JCAnnotation *)
(* org.jmlspecs.openjml.JmlTree.JmlAnnotation *)
type annotation' = {annotation_type: tree; args: expr list}
and annotation = annotation' obj
[@@deriving show { with_path = false }]

(* com.sun.tools.javac.tree.JCTree.JCModifiers *)
and modifiers' = {flags: modifier list; annotations: annotation list}
and modifiers = modifiers' obj
[@@deriving show { with_path = false }]

(* org.jmlspecs.openjml.JmlTree.JmlStatementLoop *)
and jml_statement_loop' =
  | StatementLoopExpr of {expr: expr}
  | StatementLoopModifies
and jml_statement_loop = jml_statement_loop' obj
[@@deriving show { with_path = false }]

(* com.sun.tools.javac.tree.JCTree *)
and tree' =
  | Statement' of statement' (* A real subtype *)
  | Expr' of expr' (* A real subtype *)
  | ClassDecl of {name: string; sym: type_symbol; typ: typ; typarams: type_parameter list; type_specs: type_specs; extending: expr option; defs: tree list}
  | MethodDecl of {name: string; sym: method_symbol; typ: typ; this: var_symbol option; restype: expr option; params: tree list; body: tree option; throws: expr list; specs: method_specs; mods: modifiers }
and tree = tree' obj

(* com.sun.tools.javac.tree.JCTree.JCExpression *)
and expr' =
  | JmlSingleton of {typ: typ; kind: jml_clause_kind}
  | JmlExpr' of jml_expr'
  | JmlStoreRefKeyword of {kind: jml_clause_kind}
  | ArrayTypeTree of {elemtype: expr; typ: typ}
  | PrimitiveTypeTree of {type_tag: type_tag; typ: typ}
  | ArrayAccess of {indexed: expr; index: expr; typ: typ}
  | Assign of {lhs: expr; rhs: expr; typ: typ}
  | AssignOp of {lhs: expr; rhs: expr; operator: symbol; typ: typ}
  | Binary of {lhs: expr; rhs: expr; operator: symbol; typ: typ}
  | FieldAccess of {selected: expr; name: string; sym: symbol; typ: typ}
  | Ident of {name: string; typ: typ; sym: symbol}
  | PlainIdent of {name: string}
  | Literal' of literal'
  | MethodInvocation of {typeargs: expr list; meth: expr option; args: expr list; typ: typ; kind: jml_clause_kind option}
  | NewArray of {elemtype: expr; dims: expr list; elems: expr list; typ: typ}
  | NewClass of {clazz: expr; constructor: method_symbol; args: expr list; typ: typ}
  | Parens of {expr: expr; typ: typ}
  | QuantifiedExpr of {kind: jml_clause_kind; decls: variable_decl' list; range: expr; value: expr; typ: typ}
  | TypeApply of {clazz: expr; arguments: expr list; typ: typ}
  | Unary of {arg: expr; operator: symbol; typ: typ}
and expr = expr' obj

(* org.jmlspecs.openjml.JmlTree.JmlExpression *)
and jml_expr' =
  | JmlBinary of {lhs: expr; rhs: expr; op: jml_clause_kind; typ: typ}
and jml_expr = jml_expr' obj

(* org.jmlspecs.openjml.JmlTree.JmlVariableDecl *)
and variable_decl' = {
  name: string;
  nameexpr: expr option;
  vartype: expr;
  init: expr option;
  sym: var_symbol;
  typ: typ;
  mods: modifiers;
}
and variable_decl = variable_decl' obj

and catch' = Catch of {param: variable_decl; body: block}
and catch = catch' obj

(* com.sun.tools.javac.tree.JCTree.JCExpressionStatement *)
and expr_statement' = {expr: expr}
and expr_statement = expr_statement' obj

(* com.sun.tools.javac.tree.JCTree.JCBlock *)
(* org.jmlspecs.openjml.JmlTree.JmlBlock *)
and block' = {stats: statement list; cases: jml_method_specs option}
and block = block' obj

(* com.sun.tools.javac.tree.JCTree.JCStatement *)
and statement' =
  | ExprStatement of {expr: expr}
  | Block' of block'
  | JmlStatementExpr of {keyword: string; clause_type: jml_clause_kind; expr: expr; typ: typ option}
  | ForLoop of {loop_specs: jml_statement_loop list; init: statement list; cond: expr; step: expr_statement list; body: statement; typ: typ option}
  | EnhancedForLoop of {var: variable_decl; expr: expr; body: statement; loop_specs: jml_statement_loop list; typ: typ option}
  | Return of {expr: expr}
  | JmlStatement of {statement: statement; keyword: string; clause_type: jml_clause_kind; typ: typ}
  | If of {cond: expr; thenpart: statement; elsepart: statement option}
  | VariableDecl of variable_decl'
  | Throw of {expr: expr}
  | Try of {body: block; catchers: catch list; finalizer: block option; resources: tree list}
  | Import of {qualid: tree}
  | Label of {label: string; body: statement}
and statement = statement' obj

(* org.jmlspecs.openjml.JmlTree.JmlTypeClause *)
and jml_type_clause' =
  (* org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr *)
  | TypeClauseExpr of {keyword: string option; clause_type: jml_clause_kind; expr: expr}
  (* org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents *)
  | TypeClauseRepresents of {keyword: string option; clause_type: jml_clause_kind; ident: expr; such_that: bool; expr: expr}
and jml_type_clause = jml_type_clause' obj

(* org.jmlspecs.openjml.JmlSpecs.TypeSpecs *)
and type_specs' = TypeSpecs of {clauses: jml_type_clause list}
and type_specs = type_specs' obj

(* com.sun.tools.javac.tree.JCTree.JCTypeParameter *)
and type_parameter' = TypeParameter of {name: string; bounds: expr list}
and type_parameter = type_parameter' obj

(* org.jmlspecs.openjml.JmlTree.JmlMethodClause *)
and jml_method_clause' =
  | JmlMethodClauseExpr of {keyword: string; clause_kind: jml_clause_kind; expr: expr}
  | JmlMethodClauseExprExc of {keyword: string; clause_kind: jml_clause_kind; expr: expr; exc_typ: expr option} (* RequiresClause$Node *)
  | JmlMethodClauseSignals of {vardef: variable_decl option; expr: expr}
  | JmlMethodClauseSignalsOnly of {list: expr list}
  | JmlMethodClauseStoreRef of {list: expr list}
and jml_method_clause = jml_method_clause' obj

(* org.jmlspecs.openjml.JmlTree.JmlSpecificationCase *)
and jml_specification_case' = JmlSpecificationCase of {clauses: jml_method_clause list; token: string option}
and jml_specification_case = jml_specification_case' obj

(* org.jmlspecs.openjml.JmlTree.JmlMethodSpecs *)
and jml_method_specs' = JmlMethodSpecs of {cases: jml_specification_case list (* impliesThatCases; forExampleCases *)}
and jml_method_specs = jml_method_specs' obj

(* org.jmlspecs.openjml.JmlSpecs.MethodSpecs *)
and method_specs' = MethodSpecs of {cases: jml_method_specs (* queryDatagroup; secretDatagroup *)}
and method_specs = method_specs' obj

[@@deriving show { with_path = false }]

(* org.jmlspecs.openjml.JmlTree.JmlCompilationUnit *)
(* com.sun.tools.javac.tree.JCTree.JCCompilationUnit *)
type compilation_unit' = CompilationUnit of {defs: tree list}
and compilation_unit = compilation_unit' obj
[@@deriving show { with_path = false }]


let type_of_expr o =
  match force o with
  | JmlSingleton {typ}
  | JmlExpr' (JmlBinary {typ})
  | ArrayTypeTree {typ}
  | PrimitiveTypeTree {typ}
  | ArrayAccess {typ: typ}
  | Assign {typ: typ}
  | AssignOp {typ}
  | Binary {typ}
  | FieldAccess {typ}
  | Ident {typ}
  | Literal' (IntLiteral {typ} | BoolLiteral {typ} | BotLiteral {typ})
  | MethodInvocation {typ}
  | NewArray {typ}
  | NewClass {typ}
  | Parens {typ}
  | QuantifiedExpr {typ}
  | TypeApply {typ}
  | Unary {typ} ->
    typ
  | PlainIdent _
  | JmlStoreRefKeyword _ ->
    Format.kasprintf failwith "type_of_expr: %a" pp_expr o

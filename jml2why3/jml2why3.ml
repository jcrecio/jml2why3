open Fun
open Why3
open Ptree
open JmlAst
open Why3aux.Ast

(* Sorry, but this code is using way more function applications than list concatenations... *)
let (@), (@@) = (@@), (@)

let map_pair f (x, y) =
  f x, f y

let apply_when b f =
  fun x ->
  if b then f x else x

let eprintf fmt =
  reset_pp_obj ();
  Format.eprintf fmt

let failwith fmt =
  reset_pp_obj ();
  let aux s =
    eprintf "%s@." s;
    failwith "Conversion error" in
  Format.kasprintf aux fmt

let forced f o =
  f @ force o

(** {3 Why3 AST helpers} *)

(** {4 Idents} *)

let this_ident = mk_ident "this"
let result_ident = mk_ident "result"
let null_ident = mk_ident ""

let ident_printer =
  let open Ident in
  let sanitizer =
    let keep_quote f = function '\'' -> "'" | '_' -> "_" | c -> f c in
    sanitizer (keep_quote char_to_lalpha) (keep_quote char_to_alnumus) in
  create_ident_printer ~sanitizer []

let mk_ident' ?suffix str =
  let str =
    let suffix =
      match suffix with
      | None -> ""
      | Some s -> "__"^s in
    str^suffix in
  mk_ident (Ident.string_unique ident_printer str)

let uident_printer =
  let open Ident in
  let sanitizer =
    let keep_quote f = function '\'' -> "'" | '_' -> "_" | c -> f c in
    sanitizer (keep_quote char_to_ualpha) (keep_quote char_to_alnumus) in
  create_ident_printer ~sanitizer []

let mk_uident' ?suffix str =
  let str =
    let suffix =
      match suffix with
      | None -> ""
      | Some s -> "__"^s in
    str^suffix in
  mk_ident (Ident.string_unique uident_printer str)

(** {4 Types} *)

(** nullable t *)
let mk_nullable_type elem_type : pty =
  PTtyapp (mk_qualid ["Nullable"; "nullable"], [elem_type])

(** address *)
let mk_address_pty () : pty =
  PTtyapp (mk_qualid ["Address"; "address"], [])

(** unit *)
let mk_unit_type () : pty =
  PTtyapp (mk_qualid ["unit"], [])

(** ref <t> *)
let mk_ref_type t =
  PTtyapp (mk_qualid ["Ref"; "ref"], [t])

(** {3 Java AST tests} *)

let is_class_type : typ -> bool = forced @ function
    | ClassType _ -> true
    | _ -> false

let is_array_type = forced @ function
    | ArrayType _ -> true
    | _ -> false

let get_array_elem_type t =
  match force t with
  | ArrayType {elemtype} -> elemtype
  | _ -> failwith "get_array_elem_type: %a" pp_typ t

let has_exception_supertype = forced @ function
    | ClassType {
        supertype=Some (lazy (ClassType {
            tsym=lazy (ClassSymbol {
                name="Exception"}), _}), _); _} ->
      true
    | _ -> false

(* The following functions could rely on [com.sun.tools.javac.code.Symbol.kind]? *)

let is_var_symbol : symbol -> bool = forced @ function
    | VarSymbol' _ -> true
    | _ -> false

let is_method_symbol : symbol -> bool = forced @ function
    | MethodSymbol' _ -> true
    | _ -> false

let is_primitive_type : typ -> bool = forced @ function
    | PrimitiveType _ -> true
    | _ -> false

let is_primitive_array_type : typ -> bool = forced @ function
    | ArrayType {elemtype} ->
      is_primitive_type elemtype
    | _ -> false

let is_primitive_type_tag tag = forced @ function
    | PrimitiveType {type_tag} -> tag = type_tag
    | _ -> false

let is_var_symbol_with_name o name = match force o with
  | VarSymbol' (VarSymbol {name=name'}) -> String.equal name' name
  | _ -> false

let is_class_type_with_fullname o fullname = match force o with
  | ClassType {tsym=lazy (ClassSymbol {fullname=fullname'}), _} ->
    String.equal fullname' fullname
  | _ -> false

let is_type_apply_with_fullname o fullname = match force o with
  | TypeApply {clazz=lazy (Ident {sym=lazy (TypeSymbol' (ClassSymbol {fullname=fullname'})), _}), _} ->
    String.equal fullname' fullname
  | _ -> false

let is_class_symbol_with_fullname o fullname = match force o with
  | ClassSymbol {fullname=fullname'} ->
    String.equal fullname' fullname
  | _ -> false

let is_type_symbol_with_fullname o fullname = match force o with
  | TypeSymbol' (ClassSymbol {fullname=fullname'}) ->
    String.equal fullname' fullname
  | _ -> false

let is_jml_singleton keyword = forced @ function
    | JmlSingleton {kind=lazy (OtherClauseKind k), _} ->
      String.equal k.keyword keyword
    | _ -> false

(** {3 Java AST casts} *)

let get_var_symbol : symbol -> var_symbol = function
  | lazy (VarSymbol' sym), id ->
    lazy sym, id
  | o -> failwith "get_var_symbol: %a" pp_symbol o

let get_method_symbol : symbol -> method_symbol = function
  | lazy (MethodSymbol' sym), id ->
    lazy sym, id
  | o ->
    failwith "get_method_symbol: %a" pp_symbol o

let get_type_symbol : symbol -> type_symbol = function
  | lazy (TypeSymbol' sym), id ->
    lazy sym, id
  | o -> failwith "get_type_symbol: %a" pp_symbol o

(** {3 Java AST names} *)

let type_symbol_name = forced @ function
  | TypeVariableSymbol {name}
  | ClassSymbol {name}
  | PackageSymbol {name} ->
    name
  | UnnamedPackage -> "unnamed-package"
  | NoTypeSymbol -> "no-type-symbol"

let var_symbol_name : var_symbol -> string = forced @ function
    | VarSymbol {name} -> name

let method_symbol_name : method_symbol -> string = forced @ function
    | MethodSymbol {name} -> name

let symbol_name o = match force o with
  | TypeSymbol' _ ->
    type_symbol_name (get_type_symbol o)
  | VarSymbol' _ ->
    var_symbol_name (get_var_symbol o)
  | MethodSymbol' _ ->
    method_symbol_name (get_method_symbol o)
  | OperatorSymbol {name} ->
    name

(** {2 Global memory} *)

module M : sig
  type ('a, 'b) memory
  val create : ?test:('a obj -> bool) -> string -> ('a obj, 'b) memory
  val set : ('a obj, 'b) memory -> 'a obj -> 'b -> unit
  val is : ('a obj, 'b) memory -> 'a obj -> bool
  val get : ('a obj, 'b) memory -> 'a obj -> 'b
  val get_opt : ('a obj, 'b) memory -> 'a obj -> 'b option
end = struct
  type ('a, 'b) memory = {name: string; test: 'a -> bool; mem: (string, 'b) Hashtbl.t}
  let test {name; test} o =
    if not (test o) then
      invalid_arg (name^": "^id o)
  let create ?(test=Fun.const true) name =
    let mem = Hashtbl.create 13 in
    {name; test; mem}
  let set m o x =
    test m o;
    (* eprintf "Set %s: %s@." m.name (id o); *)
    Hashtbl.replace m.mem (id o) x
  let get m o =
    test m o;
    try Hashtbl.find m.mem (id o)
    with Not_found -> invalid_arg (m.name^": "^id o)
  let get_opt m o =
    try
      test m o;
      Some (Hashtbl.find m.mem (id o))
    with Invalid_argument _ | Not_found -> None
  let is m o =
    Hashtbl.mem m.mem (id o)
end

(** {3 Global information on Java constructs} *)

type field_info = FieldInfo of {
    sym: var_symbol;
    init: expr option;
    pty: pty;
    ident: ident;
    mods: modifiers'
  }
type method_info = MethodInfo of {
    sym: method_symbol;
    mods: modifiers';
    ident: ident;
    is_pure_model: bool;
    arg_mods: modifiers' list
  }
type var_info = VarInfo of {
    sym: var_symbol;
    ident: ident;
    is_field: bool;
    mods: modifiers'
  }
type exception_info = ExceptionInfo of {
    sym: type_symbol;
    ident: ident
  }
type class_info = ClassInfo of {
    fullname: string;
    sym: type_symbol;
    type_ident: ident;
    new_ident: ident;
    fields: field_info list;
    address_field: ident;
    methods: method_info list;
    invariant_idents: ident list;
  }

let classes : (typ, class_info) M.memory =
  M.create ~test:is_class_type "class"
let exceptions : (typ, exception_info) M.memory =
  M.create ~test:is_class_type "exception"
let fields : (var_symbol, field_info) M.memory =
  M.create "field"
let vars : (var_symbol, var_info) M.memory = (* fields and variables *)
  M.create "var"
let methods : (method_symbol, method_info) M.memory =
  M.create "method"
let labels : (string, ident) Hashtbl.t =
  Hashtbl.create 13

(** {4 Expressions and terms} *)

module MoreHelpers (Helpers: PtreeHelpers) = struct
  include Helpers

  (** NonNull arg *)
  let mk_non_null arg =
    mk_idapp (mk_qualid ["Nullable"; "NonNull"]) [arg]

  (** get_non_null arg *)
  let mk_get_non_null arg =
    mk_idapp (mk_qualid ["Nullable"; "get_non_null"]) [arg]

  let mk_default_value (t: typ) =
    match force t with
    | PrimitiveType {type_tag=TagInt} ->
      mk_const (Constant.int_const_of_int 0)
    | ClassType _ ->
      mk_idapp (mk_qualid ["Nullable"; "Null"]) []
    | _ -> failwith "mk_default_value: %a" pp_typ t

  (** a[i] *)
  let mk_array_get a i =
    mk_idapp (mk_qualid ["Array32"; Ident.op_get ""]) [a; i]

  (** Nullable.map for unpure functions *)
  let mk_map_non_null f e =
    (* match e with Null -> Null | NonNull x -> NonNull (f x)*)
    let null_branch =
      mk_pat @ Papp (mk_qualid ["Nullable"; "Null"], []),
      mk_idapp (mk_qualid ["Nullable"; "Null"]) [] in
    let non_null_branch =
      let var = mk_ident "x" in
      mk_pat @ Papp (mk_qualid ["Nullable"; "NonNull"], [mk_pat @ Pvar var]),
      mk_idapp (mk_qualid ["Nullable"; "NonNull"])
        [mk_idapp f [mk_var (Qident var)]] in
    mk_case e [null_branch; non_null_branch]

  (** () *)
  let mk_unit () =
    mk_tuple []

  (** ignore arg *)
  let mk_ignore arg =
    mk_idapp (mk_qualid ["Utils"; "ignore"]) [arg]

  let fix_nullability = function
    | true, true
    | false, false -> Fun.id
    | true, false -> mk_non_null
    | false, true -> mk_get_non_null

  let fix_nullability2 nullabilities (e1, e2) =
    match nullabilities with
    | true, true
    | false, false ->
      e1, e2
    | true, false ->
      e1, mk_idapp (mk_qualid ["Nullable"; "NonNull"]) [e2]
    | false, true ->
      mk_idapp (mk_qualid ["Nullable"; "NonNull"]) [e1], e2

  let fix_contents final e =
    if final
    then e
    else mk_idapp (mk_qualid ["Ref"; "contents"]) [e]
end

module E = MoreHelpers(E)
module T = MoreHelpers(T)

let mk_true ?loc () = mk_term ?loc Ttrue
let mk_false ?loc () = mk_term ?loc Tfalse

let mk_seq ?loc e1 e2 = mk_expr ?loc (Esequence (e1, e2))
let mk_assign ?loc assgms = mk_expr ?loc (Eassign assgms)

(** ref <e> *)
let mk_ref e : Ptree.expr =
  mk_expr @ Eapply (mk_expr Eref, e)

let mk_while test invariants variant body =
  mk_expr (Ewhile (test, invariants, variant, body))

let fix_mutability : bool -> Ptree.expr -> Ptree.expr = function
  | true -> Fun.id
  | false -> mk_ref

(** {3 Tests for Java AST considering global information on Java constructs} *)

let is_var_ident_symbol : symbol -> bool = fun o ->
  match force o with
  | VarSymbol' (VarSymbol {owner=Some (lazy (TypeSymbol' (ClassSymbol _)), _)}) ->
    false
  | VarSymbol' _ ->
    M.is vars (get_var_symbol o)
  | _ -> false

let is_field_ident_symbol : symbol -> bool = fun o ->
  is_var_symbol o &&
  let vs = get_var_symbol o in
  M.is vars vs &&
  let VarInfo {is_field} = M.get vars vs in
  is_field

let is_method_ident_symbol o =
  is_method_symbol o &&
  M.is methods (get_method_symbol o)

let is_pure_model_symbol o =
  let msym = get_method_symbol o in
  M.is methods msym &&
  let MethodInfo mi = M.get methods msym in
  mi.is_pure_model

(** {3 Dealing with modifiers: nullable and final} *)

let is_final mods =
  List.mem Final mods.flags

let is_annotation fullname o =
  match force (force o).annotation_type with
  | Expr' (FieldAccess {typ}) ->
    is_class_type_with_fullname typ fullname
  | _ -> false

let is_nullable mods =
  List.exists (is_annotation "org.jmlspecs.annotation.Nullable") mods.annotations

let is_model mods =
  List.exists (is_annotation "org.jmlspecs.annotation.Model") mods.annotations

let is_pure mods =
  List.exists (is_annotation "org.jmlspecs.annotation.Pure") mods.annotations

type context = {
  this_ident: ident;
  result_nullable: bool option;
}

(** Test if an JML expression is nullable *)
let rec is_nullable_expr ctx o = match force o with
  | Parens {expr} ->
    is_nullable_expr ctx expr
  | ArrayAccess {typ} ->
    not (is_primitive_type typ)
  | Literal' (BotLiteral _) ->
    (* null *)
    true
  | Unary _ | Binary _ | Literal' _ | NewArray _ | NewClass _ ->
    false
  | Assign {lhs} | AssignOp {lhs} ->
    is_nullable_expr ctx lhs
  | JmlSingleton {kind=lazy (OtherClauseKind {keyword="\\result"}), _} when ctx.result_nullable <> None ->
    Option.get ctx.result_nullable
  | JmlSingleton {typ}
  | FieldAccess {sym=lazy (VarSymbol' (VarSymbol {typ})), _} when
      is_primitive_type typ ->
    false
  | Ident {name="this"} ->
    false
  | FieldAccess {sym}
  | Ident {sym} when is_var_symbol sym && M.is vars (get_var_symbol sym)  -> (*TODO*)
    let VarInfo {mods} = M.get vars (get_var_symbol sym) in
    is_nullable mods
  | MethodInvocation {typ} when is_primitive_type typ ->
    false
  | MethodInvocation {meth=None; args=[arg]; kind=Some (lazy (StateExpression {keyword="\\old"}), _)}
  | MethodInvocation {meth=None; args=[arg; _]; kind=Some (lazy (StateExpression {keyword="\\old"}), _)} ->
    is_nullable_expr ctx arg
  | MethodInvocation {meth=Some (lazy (FieldAccess {selected; name="clone"}), _); args=[]} when
      is_array_type (type_of_expr selected) ->
    false
  | MethodInvocation {meth=Some (lazy (FieldAccess {selected; name="get"}), _); args=[_]} when
      is_class_type_with_fullname (type_of_expr selected) "java.util.LinkedList" ->
    true
  | MethodInvocation {meth=Some (lazy (FieldAccess {selected; name="_get"}), _); args=[_]} when
      is_class_type_with_fullname (type_of_expr selected) "java.util.Queue" ->
    false
  | MethodInvocation {meth=Some (lazy (FieldAccess {selected; name=("peek"|"poll")}), _); args=[]} when
      is_class_type_with_fullname (type_of_expr selected) "java.util.Queue" ->
    true
  | MethodInvocation {meth=Some (lazy (Ident {sym}), _)}
  | MethodInvocation {meth=Some (lazy (FieldAccess {sym}), _)} when
      is_method_symbol sym ->
    let MethodInfo {mods} = M.get methods (get_method_symbol sym) in
    is_nullable mods
  | _ -> failwith "is_nullable_expr: %a" pp_expr o

(** {2 Conversion of Java to Why3} *)

(** {3 Conversion of types} *)

(** Conversion of a JML type to a Why3 type *)
(* Section: Types *)
let rec typ_as_pty ~target (typ:typ) : pty =
  let term_or_expr target t1 t2 =
    match target with
    | `Term -> t1
    | `Expr -> t2 in
  flip forced typ @ function
    | AnnotatedType {underlying_type} ->
      typ_as_pty ~target underlying_type
    | VoidType ->
      mk_atomic_type' ["unit"]
    | PrimitiveType {type_tag=TagInt} ->
      (* Java: int *)
      (* Why3: int.Int32 *)
      mk_atomic_type'
        (term_or_expr target ["int"] ["Int32"; "int32"])
    | ClassType {typarams=[]; tsym} when
        is_class_symbol_with_fullname tsym "java.lang.Integer" ->
      (* Java: java.lang.Integer *)
      (* Why3: int.Int32 *)
      mk_atomic_type'
        (term_or_expr target ["int"] ["Int32"; "int32"])
    | PrimitiveType {type_tag=TagBool} ->
      (* Java: bool *)
      (* Why3: bool.Bool *)
      mk_atomic_type' ["Bool"; "bool"]
    | MethodType {argtypes=[]; restype=lazy VoidType, _} ->
      mk_arrow
        (mk_atomic_type' ["unit"]) (* TODO FIXME should be type of `this` *)
        (mk_atomic_type' ["unit"])
    | ClassType {typarams=[param]; tsym} when
        is_class_symbol_with_fullname tsym "java.util.Queue" ->
      (* Java: java.util.Queue *)
      (* Why3: Queue.t *)
      let param = typ_as_pty ~target param in
      mk_tyapp (mk_qualid ["Queue"; "t"]) [param]
    | ClassType {typarams=[param]; tsym} when
        is_class_symbol_with_fullname tsym "java.util.LinkedList" ->
      (* Java: java.util.LinkedList *)
      (* Why3: LinkedList.linked_list *)
      let param = typ_as_pty ~target param in
      mk_tyapp (mk_qualid ["LinkedList"; "linked_list"]) [param]
    | ClassType {typarams=[]} when
        M.is classes typ ->
      (* Java: C // user-defined class *)
      (* Why3: ‹C› *)
      let ClassInfo ci = M.get classes typ in
      mk_tyapp (Qident ci.type_ident) []
    | TypIdent {typ} when
        M.is classes typ ->
      let ClassInfo {type_ident} = M.get classes typ in
      mk_tyapp (Qident type_ident) []
    | ArrayType {elemtype} ->
      (* Java: t[] // primitive array *)
      (* Why3: Array32.array ‹t› // `t` is primitive type *)
      (* Java: C[] // object array *)
      (* Why3: Array32.array (nullable ‹C›) // `C` is object type *)
      mk_tyapp (mk_qualid ["Array32"; "array"])
        [typ_as_pty ~target elemtype |>
         apply_when (not @ is_primitive_type elemtype)
           mk_nullable_type]
    | _ ->
      failwith "typ_as_pty: %a" pp_typ typ

(** {3 Conversion of expressions and terms} *)

let variable_declaration_as_param ?(force_final=false) ~target {sym; mods=lazy mods, _; typ} =
  let ident = mk_ident' (var_symbol_name sym) in
  let mods = if force_final && not (is_final mods) then {mods with flags=Final :: mods.flags} else mods in
  M.set vars sym (VarInfo {sym; ident; mods; is_field=false});
  let pty =
    let pty = typ_as_pty ~target typ in
    if is_final mods then pty else mk_ref_type pty in
  loc(), Some ident, false, pty

(* let all_params ~this_ident ~type_ident ~target params = *)

let this_binder ~type_ident =
  loc(), Some this_ident, false, mk_atomic_type (Qident type_ident)

let param_binders ~target params =
  let aux = forced @ function
      | Statement' (VariableDecl decl) ->
        variable_declaration_as_param ~target decl
      | t ->
        failwith "tree_as_binder: %a" pp_tree' t in
  List.map aux params

let param_to_binder ?(with_type=true) (l, id, g, t) =
  l, id, g, if with_type then Some t else None

exception Not_general

(** Shared code for conversion to expressions and term. *)
(* Section: Expressions and terms *)
let expr_as (type t) (module Helpers: PtreeHelpers with type t = t) expr_as ctx o =
  let open MoreHelpers(Helpers) in
  match force o with
  | Parens {expr} ->
    expr_as ctx expr
  | Literal' (BotLiteral _) ->
    (* Java: null // Null value *)
    (* Why3: Nullable.Null *)
    mk_idapp (mk_qualid ["Nullable"; "Null"]) []
  | Literal' (IntLiteral {value}) ->
    (* Java: l // Literal of type `int` *)
    (* Why3: (‹l›:int32) *)
    mk_cast
      (mk_const (Constant.int_const value))
      (mk_atomic_type' ["Int32"; "int32"])
  | Literal' (BoolLiteral {value}) ->
    (* Java: l // Literal of type `boolean` *)
    (* Why3: True // if `l` is `true` *)
    (* Why3: False // if `l` is `false` *)
    let ident = mk_ident @ if value then "True" else "False" in
    mk_idapp (Qident ident) []
  | Ident {name="this"} ->
    (* Java: this // This *)
    (* Why3: this *)
    mk_var (Qident ctx.this_ident)
  | Ident {sym} when
      is_var_ident_symbol sym ->
    (* Java: x // Variable or parameter *)
    (* Why3: ‹x› // Identifier `‹x›` from variable info *)
    let VarInfo vi = M.get vars (get_var_symbol sym) in
    mk_var (Qident vi.ident) |>
    fix_contents (is_final vi.mods)
  | Ident {sym} when
      is_field_ident_symbol sym ->
    (* Java: f // Field *)
    (* Why3: this.‹f› // identifier `‹f›` from field info *)
    let VarInfo vi = M.get vars (get_var_symbol sym) in
    mk_idapp (Qident vi.ident)
      [mk_var (Qident ctx.this_ident)]
  | FieldAccess {selected; sym} when
      is_field_ident_symbol sym ->
    (* Java: e.f // Field access *)
    (* Why3: ‹e›|nonnull.‹f› // identifier `‹f›` from field info *)
    let FieldInfo fi = M.get fields (get_var_symbol sym) in
    let selected =
      expr_as ctx selected |>
      fix_nullability (false, is_nullable_expr ctx selected) in
    mk_idapp (Qident fi.ident) [selected]
  | Binary {lhs; rhs; operator=lazy (OperatorSymbol {name="&&"|"||" as op}), _} ->
    (* Java: e1 op e2 // Binary operation for operators `"&&"` and `"||"` *)
    (* Why3: ‹e1› ‹op› ‹e2›  *)
    let t1, t2 = map_pair (expr_as ctx) (lhs, rhs) in
    let op =
      match op with
      | "&&" -> `And
      | "||" -> `Or
      | _ -> assert false in
    mk_binop t1 op t2
  | Binary {lhs=lhs0; rhs=rhs0; operator=lazy (OperatorSymbol {name=op}), _} ->
    let mk_null_non_null_test = function
      | "==" -> mk_qualid ["Nullable"; "is_null"]
      | "!=" -> mk_qualid ["Nullable"; "is_non_null"]
      | _ -> assert false in
    let lhs_type, rhs_type = map_pair type_of_expr (lhs0, rhs0) in
    let lhs_nullable, rhs_nullable = map_pair (is_nullable_expr ctx) (lhs0, rhs0) in
    let lhs, rhs = map_pair (expr_as ctx) (lhs0, rhs0) in
    if (is_primitive_type_tag TagInt lhs_type ||
        is_class_type_with_fullname lhs_type "java.lang.Integer") &&
       (is_primitive_type_tag TagInt rhs_type ||
        is_class_type_with_fullname rhs_type "java.lang.Integer")
    then
      (* int ==/!= int, Integer ==/!= Integer *)
      (* Java: e1 op e2 // Binary operation between integer operants (`int`/`Integer`) *)
      (* Why3: ‹e1› == ‹e2› // op is == *)
      (* Why3: not (‹e1› = ‹e2›) // op is != *)
      (* Why3: ‹e1›|nonnull ‹op› ‹e2›|nonnull // Otherwise *)
      let op, negate, op_allows_null =
        match op with
        | "==" -> "=", false, true
        | "!=" -> "=", true, true
        | _ -> op, false, false in
      let op =
        match target with
        | `Expr -> mk_qualid ["Int32"; Ident.op_infix op]
        | `Term -> mk_qualid [Ident.op_infix op] in
      let lhs, rhs =
        if op_allows_null then
          (* binop between nullable Integers *)
          fix_nullability2 (lhs_nullable, rhs_nullable) (lhs, rhs)
        else
          fix_nullability (false, lhs_nullable) lhs,
          fix_nullability (false, rhs_nullable) rhs in
      mk_idapp op [lhs; rhs] |>
      apply_when negate mk_not
    else
    if (String.equal op "==" || String.equal op "!=") &&
            is_primitive_type_tag TagBool lhs_type &&
            is_primitive_type_tag TagBool rhs_type
    then
      (* Java: e1 == e2 // Equality/inequality between boolean operants*)
      (* Why3: Utils.biff ‹e1›|nonnull ‹e2›|nonnull // if op is "==" *)
      (* Why3: Bool.bxor ‹e1›|nonnull ‹e2›|nonnull // if op is "!=" *)
      let negate =
        match op with
        | "==" -> false
        | "!=" -> true
        | _ -> assert false in
      let op =
        match target with
        | `Expr -> mk_qualid ["Utils"; "biff"]
        | `Term -> mk_qualid [Ident.op_infix "="] in
      let lhs = fix_nullability (false, lhs_nullable) lhs in
      let rhs = fix_nullability (false, rhs_nullable) rhs in
      mk_idapp op [lhs; rhs] |>
      apply_when negate mk_not
    else
      (match force lhs0, op, force rhs0 with
       | Literal' (BotLiteral _), ("=="|"!="), _ when
           M.is classes rhs_type || is_class_type_with_fullname rhs_type "java.lang.Integer" ->
         (* Java: null op x // Test null/nonnull; `op` is `"=="` or `"!="` *)
         (* Why3: Nullable.is_null ‹x› // negate if op is != *)
         mk_idapp (mk_null_non_null_test op) [rhs]
       | _, ("=="|"!="), Literal' (BotLiteral _) when
           M.is classes lhs_type || is_class_type_with_fullname lhs_type "java.lang.Integer" ->
         (* Java: x op null // Test null/nonnull; `op` is `"=="` or `"!="`  *)
         (* Why3: Nullable.is_null ‹x› // negate if `op` is `!=` *)
         mk_idapp (mk_null_non_null_test op) [lhs]
       | _, ("=="|"!="), _ when
           id lhs_type = id rhs_type && M.is classes lhs_type ->
         (* Java: e1 op e2 // Physical equality between obects of user-defined classes; `op` is `==` or `!=` *)
         (* Why3: Address.same ‹e1› ‹e2› // if `e1` and `e2` are non-nullable; negate if `op` is `!=` *)
         (* Why3: Address.nullable_same_address ‹e1›|nullable ‹e2›|nullable // if `e1` or `e2` nullable; negate if `op` is `!=` *)
         let ClassInfo ci = M.get classes lhs_type in
         let negate =
           match op with
           | "==" -> false
           | "!=" -> true
           | _ -> assert false in
         (match lhs_nullable, rhs_nullable with
          | false, false ->
            mk_idapp (mk_qualid ["Address"; "same"]) [lhs; rhs]
          | nullabilities ->
            let lhs, rhs = fix_nullability2 nullabilities (lhs, rhs) in
            mk_idapp
              (mk_qualid ["Address"; "nullable_same_address"])
              [mk_var (Qident ci.address_field); lhs; rhs]) |>
         apply_when negate mk_not
       | _ ->
         raise Not_general)
  | Unary {arg; operator=lazy (OperatorSymbol {name="!"}), _} ->
    (* Java: !x // Negation unary operator *)
    (* Why3: not ‹x› *)
    let arg = expr_as ctx arg in
    mk_not arg
  | FieldAccess {selected; sym} when
      is_array_type (type_of_expr selected) &&
      is_var_symbol_with_name sym "length" ->
    (* Java: x.length // Array length; `x` has type array *)
    (* Why3: Array32.length ‹x› *)
    mk_idapp (mk_qualid ["Array32"; "length"])
      [expr_as ctx selected]
  | FieldAccess {selected; sym} when
      is_class_type_with_fullname (type_of_expr selected) "java.lang.Integer" &&
      is_var_symbol_with_name sym "MAX_VALUE" ->
    (* Java: Integer.MAX_VALUE // Maximum integer constant *)
    (* Why3: Int32.max_int32 *)
    mk_var (mk_qualid ["Int32"; "max_int32"])
  | MethodInvocation { args=[]; meth=Some (lazy (FieldAccess {selected; name="peek"}), _) } when
      is_class_type_with_fullname (type_of_expr selected) "java.util.Queue" ->
    (* Java: x.peek() // Peek from queue ; `x` has type `java.util.Queue` *)
    (* Why3: Queue.nullable_peek ‹e›|nonnull *)
    mk_idapp (mk_qualid ["Queue"; "nullable_peek"])
      [expr_as ctx selected |>
       fix_nullability (false, is_nullable_expr ctx selected)]
  | MethodInvocation { args=[e2]; meth=Some (lazy (FieldAccess {selected; name="add"}), _) } when
      is_class_type_with_fullname (type_of_expr selected) "java.util.Queue" ->
    (* Java: e1.add(e2) // Add to queue ; `e1` has type `java.util.Queue` *)
    (* Why3: Queue.nullable_push ‹e1›|nonnull ‹e2›|nullable *)
    mk_idapp (mk_qualid ["Queue"; "nullable_push"]) [
      expr_as ctx e2 |>
      fix_nullability (true, is_nullable_expr ctx e2);
      expr_as ctx selected
    ]
  | MethodInvocation {args=[]; meth=Some (lazy (FieldAccess {selected; name="size"}), _)} when
      is_class_type_with_fullname (type_of_expr selected) "java.util.LinkedList" ->
    (* Java: e.size() // `e` has type `java.util.LinkedList` *)
    (* Why3: LinkedList.size ‹e›|nonnull *)
    mk_idapp (mk_qualid ["LinkedList"; "size"])
      [expr_as ctx selected |>
       fix_nullability (false, is_nullable_expr ctx selected)]
  | MethodInvocation {args=[arg]; meth=Some (lazy (FieldAccess {selected; name="get"}), _)} when
      is_class_type_with_fullname (type_of_expr selected) "java.util.LinkedList" ->
    (* Java: e.get(i) // `e` has type `java.util.LinkedList` *)
    (* Why3: LinkedList.get ‹e›|nonnull ‹i› *)
    mk_idapp (mk_qualid ["LinkedList"; "get"])
      [expr_as ctx selected |>
       fix_nullability (false, is_nullable_expr ctx selected);
       expr_as ctx arg |>
       fix_nullability (false, is_nullable_expr ctx arg)]
  | MethodInvocation {args=[arg]; meth=Some (lazy (FieldAccess {selected; name="add"}), _)} when
      is_class_type_with_fullname (type_of_expr selected) "java.util.LinkedList" ->
    (* Java: e1.add(e2) // `e1` has type `java.util.LinkedList` *)
    (* Why3: LinkedList.add ‹e1›|nonnull ‹e2›|nullable *)
    mk_idapp (mk_qualid ["LinkedList"; "add"])
      [expr_as ctx selected |>
       fix_nullability (false, is_nullable_expr ctx selected);
       expr_as ctx arg |>
       fix_nullability (true, is_nullable_expr ctx arg)]
  | _ ->
    raise Not_general

(* Section: Expressions *)
let rec expr_as_expr ctx o : Ptree.expr =
  try expr_as (module E) expr_as_expr ctx o
  with Not_general ->
    let open MoreHelpers(E) in
    match force o with
    | NewArray {elems=[]; dims=[dim_expr]; elemtype} ->
      (* Java: new t[N] // New array *)
      (* Why3: Array.(make ‹default› ‹N› : array ‹t›) // ‹default› is for example `0` for integers or `null` for object types *)
      let elemtype = type_of_expr elemtype in
      mk_cast
        (mk_idapp
           (mk_qualid ["Array32"; "make"])
           [expr_as_expr ctx dim_expr;
            mk_default_value elemtype])
        (mk_tyapp
           (mk_qualid ["Array32"; "array"])
           [typ_as_pty ~target:`Expr elemtype])
    | NewClass {constructor; args; typ} when
        M.is methods constructor &&
        M.is classes typ ->
      (* Java: new C() // Constructor call *)
      (* Why3: {‹field› = ‹e›; …} // Values `‹e›` from constructor `C(...) { this.x = e ... }` *)
      let MethodInfo mi = M.get methods constructor in
      mk_idapp (Qident mi.ident)
        (List.map (expr_as_expr ctx) args)
    | MethodInvocation {meth=Some (lazy (FieldAccess {selected; sym}), _); args} when
        is_method_ident_symbol sym ->
      (* Java: e.m(args) // Method call *)
      (* Why3: ‹m› ‹e›|nonnull ‹args›|adapt_nullable // Adapt nullability in `args` to method arguments *)
      let MethodInfo {ident} = M.get methods (get_method_symbol sym) in
      mk_idapp (Qident ident)
        ((expr_as_expr ctx selected |>
          fix_nullability (false, is_nullable_expr ctx selected)) ::
         List.map (expr_as_expr ctx) args)
    | MethodInvocation {meth=Some (lazy (Ident {sym}), _); args} when
        is_method_ident_symbol sym ->
      (* Java: m(args) // Method call *)
      (* Why3: ‹m› this ‹args›|adapt_nullable *)
      let MethodInfo {ident} = M.get methods (get_method_symbol sym) in
      let selected_this = mk_expr @ Eident (Qident ctx.this_ident) in
      let args = List.map (expr_as_expr ctx) args in
      mk_idapp (Qident ident) (selected_this :: args)
    | MethodInvocation {meth=Some (lazy (FieldAccess {selected; name="clone"}), _); args=[]} when
        is_array_type (type_of_expr selected) ->
      mk_idapp (mk_qualid ["Array32"; "copy"])
        [expr_as_expr ctx selected]
    | MethodInvocation {meth=Some (lazy (FieldAccess {selected; name="isEmpty"}), _); args=[]} when
        is_class_type_with_fullname (type_of_expr selected) "java.util.Queue" ->
      (* Java: e.isEmpty() // Test for empty queue ; `e` has type `java.util.Queue` *)
      (* Why3: Queue.is_empty ‹e›|nonnull *)
      let selected = expr_as_expr ctx selected in
      let qident = mk_qualid ["Queue"; "is_empty"] in
      mk_idapp qident [selected]
    | MethodInvocation { args=[]; meth=Some (lazy (FieldAccess {selected; name="size"}), _) } when
        is_class_type_with_fullname (type_of_expr selected) "java.util.Queue" ->
      (* Java: e.size() // Size of queue ; `x` has type `java.util.Queue` *)
      (* Why3: Queue.length ‹e›|nonnull // if target is expr  *)
      mk_idapp (mk_qualid ["Queue"; "length32"])
        [expr_as_expr ctx selected]
    | MethodInvocation {meth=Some (lazy (FieldAccess {selected; name="poll"}), _); args=[]} when
        is_class_type_with_fullname (type_of_expr selected) "java.util.Queue" ->
      (* Java: e.poll() // Poll from queue ; e has type `java.util.Queue` *)
      (* Queue.nullable_pop ‹e› *)
      let selected = expr_as_expr ctx selected in
      mk_idapp (mk_qualid ["Queue"; "nullable_pop"]) [selected]
    | ArrayAccess {indexed; index} ->
      (* Java: e1[e2] // Array access *)
      (* Why3: Array32.(‹e1›|nonnull[‹e2›|nonnull]) *)
      mk_idapp
        (mk_qualid ["Array32"; Ident.op_get ""])
        [expr_as_expr ctx indexed |>
         fix_nullability (false, is_nullable_expr ctx indexed);
         expr_as_expr ctx index |>
         fix_nullability (false, is_nullable_expr ctx index)]
    | Assign {lhs; rhs} ->
      (match force lhs with
       | Ident {sym} when is_var_ident_symbol sym ->
         (* Java: v = e // Assignment to variable ; ‹v› is non-final *)
         (* Why3: ‹v›.contents <- ‹e›|adapt_nullable  *)
         let VarInfo {ident; mods} = M.get vars (get_var_symbol sym) in
         mk_expr @ Eassign [
           mk_var (Qident ident),
           Some (mk_qualid ["Ref"; "contents"]),
           expr_as_expr ctx rhs |>
           fix_nullability (is_nullable mods, is_nullable_expr ctx rhs)
         ]
       | Ident {sym} when is_field_ident_symbol sym ->
         (* Java: f = e // Assignment to field ; ‹f› is non-final *)
         (* Why3: this.‹f› <- ‹e›|adapt_nullable *)
         let VarInfo {ident; mods} = M.get vars (get_var_symbol sym) in
         mk_expr @ Eassign [
           mk_var (Qident ctx.this_ident),
           Some (Qident ident),
           expr_as_expr ctx rhs |>
           fix_nullability (is_nullable mods, is_nullable_expr ctx rhs)
         ]
       | ArrayAccess {indexed=lazy (Ident {sym}), _ as indexed; index; typ} when
           is_var_symbol sym && M.is vars (get_var_symbol sym) ->
         (* Java: f[i] = rhs // Assignment to array element in field `x` *)
         (* Why3: this.‹f›|nonnull[‹i›|nonnull] <- ‹rhs›|adapt_nullable *)
         (* Java: v[i] = rhs // Assignment to array element in variable `x` *)
         (* Why3: ‹v›|nonnull[‹i›|nonnull] <- ‹rhs›|adapt_nullable *)
         let VarInfo {ident; is_field} = M.get vars (get_var_symbol sym) in
         mk_idapp
           (mk_qualid ["Array32"; Ident.op_set ""])
           [(if is_field
             then mk_idapp (Qident ident) [mk_var (Qident ctx.this_ident)]
             else mk_var (Qident ident))
            |> fix_nullability (false, is_nullable_expr ctx indexed) ;
            expr_as_expr ctx index |>
            fix_nullability (false, is_nullable_expr ctx index) ;
            let rhs_nullable = is_nullable_expr ctx rhs in
            expr_as_expr ctx rhs |>
            fix_nullability (not (is_primitive_type typ), rhs_nullable)]
       | _ -> failwith "expr_to_expr, assign: %a" pp_expr o)
    | _ ->
      failwith "expr_as_expr: %a" pp_expr o

(* Section: Terms *)
and expr_as_term ctx o : Ptree.term =
  try expr_as (module T) expr_as_term ctx o
  with Not_general ->
    let open MoreHelpers(T) in
    let failure () = failwith "expr_as_term: %a" pp_expr o in
    if is_jml_singleton "\\result" o then
      (* Java: \result // Method result *)
      (* Why3: result *)
      mk_term @ Tident (Qident result_ident)
    else
    match force o with
    | JmlExpr' (JmlBinary {lhs; rhs; op=lazy (OtherClauseKind {keyword=("||"|"&&"|"==>"|"<==>" as op)}), _}) ->
      (* Java: e1 op e2 // Binary operators; op is ||, &&, ==>, <==> *)
      (* Why3: ‹e1› ‹op› ‹e2› *)
      let lhs = expr_as_term ctx lhs in
      let rhs = expr_as_term ctx rhs in
      let op =
        match op with
        | "||" -> Dterm.DTor_asym  | "&&" -> Dterm.DTand_asym
        | "==>" -> Dterm.DTimplies | "<==>" -> Dterm.DTiff
        | _ -> failwith "expr_as_term, binary: %a@." pp_expr o in
      mk_term @ Tbinop (lhs, op, rhs)
    | FieldAccess {selected=lazy (FieldAccess {selected; name="content"}), _; name="theSize"} ->
      (* Java: e.content.theSize // Size of container *)
      (* Why3: Seq.length ‹e›|nonnull *)
      mk_idapp (mk_qualid ["Seq"; "length"])
        [expr_as_term ctx selected]
    | FieldAccess {selected; name="content"} ->
      (* FIXME remove *)
      expr_as_term ctx selected
    | ArrayAccess {indexed; index} ->
      (* Java: a[i] // Array access *)
      (* Why3: Map.(‹a›|nonnull.elts[‹i›|nonnull]) *)
      mk_idapp (mk_qualid ["Map"; Ident.op_get ""])
        [mk_idapp
          (mk_qualid ["Array32"; "elts"])
          [expr_as_term ctx indexed |>
           fix_nullability (false, is_nullable_expr ctx indexed)];
         expr_as_term ctx index |>
         fix_nullability (false, is_nullable_expr ctx index)]
    | MethodInvocation {args=[]; meth=Some (lazy (FieldAccess {selected; name="isEmpty"}), _)} when
        is_class_type_with_fullname (type_of_expr selected) "java.util.Queue" ->
      (* Java: e.isEmpty() // e has type `java.util.Queue` *)
      (* Why3: ‹e› = Seq.empty *)
      mk_idapp (mk_qualid [Ident.op_equ])
        [expr_as_term ctx selected;
         mk_var (mk_qualid ["Seq"; "empty"])]
    | MethodInvocation { args=[]; meth=Some (lazy (FieldAccess {selected; name="size"}), _) } when
        is_class_type_with_fullname (type_of_expr selected) "java.util.Queue" ->
      (* Java: t.size() // Size of queue ; `t` has type `java.util.Queue` *)
      (* Why3: Seq.length ‹t› // if target is expr  *)
      mk_idapp (mk_qualid ["Seq"; "length"])
        [expr_as_term ctx selected]
    | MethodInvocation {meth=Some (lazy (FieldAccess {selected; name="_get"}), _); args=[arg]} when
        is_class_type_with_fullname (type_of_expr selected) "java.util.Queue" ->
      (* Java: e._get(i) // e has type `java.util.Queue` *)
      (* Why3: Seq.get ‹e› ‹i› *)
      let selected = expr_as_term ctx selected in
      let arg = expr_as_term ctx arg in
      mk_idapp (mk_qualid ["Seq"; "get"])
        [selected; arg]
    | MethodInvocation {args; meth=Some (lazy (Ident {sym}), _)} when
        is_pure_model_symbol sym ->
      (* Java: m(args) // `m` refers to a pure model method *)
      (* Why3: ‹m› this ‹arg› … *)
      let MethodInfo mi = M.get methods (get_method_symbol sym) in
      let aux arg mods =
        expr_as_term ctx arg |>
        fix_nullability (is_nullable mods, is_nullable_expr ctx arg) in
      mk_idapp (Qident mi.ident)
        (mk_var (Qident ctx.this_ident) ::
         List.map2 aux args mi.arg_mods)
    | MethodInvocation {args; meth=Some (lazy (FieldAccess {selected; sym}), _)} when
        is_pure_model_symbol sym ->
      (* Java: e.m(arg, …) // `m` refers to a pure model method *)
      (* Why3: ‹m› ‹e› ‹arg› … *)
      let MethodInfo mi = M.get methods (get_method_symbol sym) in
      let aux arg mods =
        expr_as_term ctx arg |>
        fix_nullability (is_nullable mods, is_nullable_expr ctx arg) in
      let arg0 =
        expr_as_term ctx selected |>
        fix_nullability (false, is_nullable_expr ctx selected) in
      mk_idapp (Qident mi.ident)
        (arg0 :: List.map2 aux args mi.arg_mods)
    | MethodInvocation {meth=Some (lazy (FieldAccess _), _)} ->
      failwith "Can only call pure model methods in terms, not@.%a" pp_expr o
    | MethodInvocation {meth=None; kind=Some (lazy (StateExpression {keyword="\\old"}), _); args=[e]} ->
      (* Java: \old(e) // Value of expression before method *)
      (* Why3: old ‹e› *)
      let t = expr_as_term ctx e in
      mk_term @ Tat (t, mk_ident Dexpr.old_label)
    | MethodInvocation {meth=None; kind=Some (lazy (StateExpression {keyword="\\old"}), _); args=[e; lazy (PlainIdent {name}), _]} when
        Hashtbl.mem labels name ->
      (* Java: \old(t, l) // Value of expression at label `l` *)
      (* Why3: (‹t› at ‹l›) *)
      let t = expr_as_term ctx e in
      let ident = Hashtbl.find labels name in
      mk_term @ Tat (t, ident)
    | MethodInvocation {meth=None; kind=Some (lazy (OtherClauseKind {keyword="\\nonnullelements"}), _); args=[e]} when
        not @ is_primitive_array_type (type_of_expr e) ->
      (* Java: \nonnullelements(e) // e is an array of objects *)
      (* Why3: Utils.non_null_elements ‹e› *)
      mk_idapp (mk_qualid ["Utils"; "non_null_elements"])
        [expr_as_term ctx e]
    | MethodInvocation {meth=None; kind=Some (lazy (OtherClauseKind {keyword="\\invariant_for"}), _); args=[e]} ->
      (* Java: \invariant_for(t) // Class invariants for value `t` *)
      (* Why3: exists ‹t› // Custom, trivially-true predicate to enforce type invariants on ‹t› *)
      mk_idapp (mk_qualid ["Utils"; "exists_"])
        [expr_as_term ctx e]
    | QuantifiedExpr {kind=lazy (QuantifiedExpression {keyword="\\forall"}), _; decls; range; value} ->
      (* Java: (\forall decls; range; value) *)
      (* Why3: forall ‹decls›.‹range› -> ‹value› *)
      let binders =
        let aux d =
          variable_declaration_as_param ~force_final:true ~target:`Expr d |>
          param_to_binder ~with_type:true in
        List.map aux decls in
      let term =
        let t1 = expr_as_term ctx range in
        let t2 = expr_as_term ctx value in
        mk_term @ Tbinop (t1, Dterm.DTimplies, t2) in
      mk_term @ Tquant (Dterm.DTforall, binders, [], term)
    | QuantifiedExpr {
        kind=lazy (QuantifiedExpression {keyword="\\num_of"}), _;
        decls=[{sym; init=None}];
        range=lazy (Binary {
            operator=lazy (OperatorSymbol {name="&&"}), _;
            lhs=lazy (Binary {
                operator=lazy (OperatorSymbol {name="<="}), _;
                lhs=l;
                rhs=lazy (Ident {sym=sym1}), _;
              }), _;
            rhs=lazy (Binary {
                operator=lazy (OperatorSymbol {name="<"}), _;
                lhs=lazy (Ident {sym=sym2}), _;
                rhs=u;
              }), _}), _;
        value=lazy (Binary {
            operator=lazy (OperatorSymbol {name="=="}), _;
            lhs;
            rhs=x;
          }), _;
      } when
        id sym = id sym1 && id sym = id sym2 ->
      (match lhs with
       | lazy (ArrayAccess {
           indexed=a;
           index=lazy (Ident {sym=sym3}), _;
           typ
         }), _ when id sym = id sym3 ->
         (* Java: (\num_of int i; l <= i && i < u; a[i] == x) // Special case of `\num_of` for occurrences in array ranges *)
         (* Why3: Utils.occ_array ‹x› ‹a› ‹l› ‹u› *)
         mk_idapp (mk_qualid ["Utils"; "occ_array"]) [
           expr_as_term ctx x |>
           fix_nullability (not @ is_primitive_type typ, is_nullable_expr ctx x);
           expr_as_term ctx a |>
           fix_nullability (false, is_nullable_expr ctx a) ;
           expr_as_term ctx l;
           expr_as_term ctx u;
         ]
       | lazy (MethodInvocation {
            meth=Some (lazy (FieldAccess {
                selected=q;
                name="_get";
              }), _);
            args=[lazy (Ident {sym=sym3}), _]
          }), _ when
            is_class_type_with_fullname (type_of_expr q) "java.util.Queue" &&
            id sym = id sym3 ->
         (* Java: (\num_of int i; l <= i && i < u; e._get[i] == x) // Special case of `\num_of` for occurrences in queues *)
         (* Why3: Occ.occ ‹x› ‹e› ‹l› ‹u› *)
         mk_idapp (mk_qualid ["Occ"; "occ"]) [
           expr_as_term ctx x |>
           fix_nullability (false, is_nullable_expr ctx x);
           expr_as_term ctx q |>
           fix_nullability (false, is_nullable_expr ctx q);
           expr_as_term ctx l;
           expr_as_term ctx u;
         ]
       | _ -> failure ())
    | _ -> failure ()

and mk_new_object ctx (ClassInfo ci) =
  let open E in
  let address =
    Qident ci.address_field,
    mk_idapp (mk_qualid ["Address"; "fresh"]) [mk_tuple []] in
  let aux (FieldInfo fi) =
    let e =
      match fi.init with
      | Some init ->
        expr_as_expr ctx init
      | None ->
        mk_var (Qident fi.ident) in
    Qident fi.ident, e in
  let record =
    mk_record (address :: List.map aux ci.fields) in
  let aux (FieldInfo fi) e =
    match fi.init with
    | Some _ -> e
    | None ->
      let any = mk_expr @ Eany ([], Expr.RKnone, Some fi.pty, mk_pat Pwild, Ity.MaskVisible, empty_spec) in
      mk_let fi.ident any e in
  List.fold_right aux ci.fields record

(* Section: Statements *)
and statements_as_expr ctx return_exc = function
  | [] ->
    mk_expr @ Etuple []
  | s :: ss ->
    let open MoreHelpers(E) in
    match force s with
    | VariableDecl {sym; vartype; mods=lazy mods, _; init=Some (lazy (NewClass {clazz}), _)} when
        is_type_apply_with_fullname vartype "java.util.LinkedList" &&
        is_type_apply_with_fullname clazz "java.util.LinkedList" ->
      (* Java: LinkedList x = new LinkedList<>(); ... // Linked lists *)
      (* Why3: let x = LinkedList.create() in ... *)
      let ident = mk_ident' (var_symbol_name sym) in
      if not (is_final mods) then
        failwith "Queues must be declared in final variables";
      M.set vars sym (VarInfo {sym; ident; is_field=false; mods});
      let e1 =
        let e1 = mk_idapp (mk_qualid ["LinkedList"; "empty"]) [mk_unit ()] in
        if is_final mods then e1 else mk_ref e1 in
      let e2 = statements_as_expr ctx return_exc ss in
      mk_expr @ Elet (ident, false, Expr.RKnone, e1, e2)
    | VariableDecl {sym; vartype; mods=lazy mods, _; init=Some (lazy (NewClass {clazz}), _)} when
        is_type_apply_with_fullname vartype "java.util.Queue" &&
        is_type_apply_with_fullname clazz "java.util.LinkedList" ->
      (* Java: Queue x = new LinkedList<>(); ... // Special case for instantiation of a linked list as a queue *)
      (* Why3: let x = Queue.create() in ... *)
      let ident = mk_ident' (var_symbol_name sym) in
      if not (is_final mods) then
        failwith "Queues must be declared in final variables";
      M.set vars sym (VarInfo {sym; ident; is_field=false; mods});
      let e1 =
        let e1 = mk_idapp (mk_qualid ["Queue"; "create"]) [mk_unit ()] in
        if is_final mods then e1 else mk_ref e1 in
      let e2 = statements_as_expr ctx return_exc ss in
      mk_expr @ Elet (ident, false, Expr.RKnone, e1, e2)
    | VariableDecl {sym; mods=lazy mods, _; init=Some init} ->
      (* Java: t x = e; ... // Variable declaration *)
      (* Why3: let x = e in ... *)
      let ident = mk_ident' (var_symbol_name sym) in
      M.set vars sym (VarInfo {sym; ident; is_field=false; mods});
      let e1 =
        expr_as_expr ctx init |>
        fix_nullability (is_nullable mods, is_nullable_expr ctx init) |>
        fix_mutability (is_final mods) in
      let e2 = statements_as_expr ctx return_exc ss in
      mk_expr @ Elet (ident, false, Expr.RKnone, e1, e2)
    | ExprStatement {expr=lazy (MethodInvocation {meth=Some (lazy (Ident {name="super"}), _)}), _} ->
      (* -Java: super(); ... // Call to super inserted by OpenJDK, ignored in conversion *)
      (* -Why3: ... *)
      statements_as_expr ctx return_exc ss
    | _ ->
      let e1 = statement_as_expr ctx return_exc s in
      if ss = [] then
        e1
      else
        let e2 = statements_as_expr ctx return_exc ss in
        mk_expr @ Esequence (e1, e2)

(* Section: Statement *)
and statement_as_expr ctx return_exc o =
  match force o with
  | Label {label; body} ->
    (* Java: l: { body } // Label on scope *)
    (* Why3: label ‹l› in ‹body› *)
    let ident = mk_uident' label in
    Hashtbl.replace labels label ident;
    mk_expr @ Elabel (ident, statement_as_expr ctx return_exc body)
  | ExprStatement {expr} ->
    (* Java: expr; // Expression *)
    (* Why3: ‹expr› *)
    E.mk_ignore @ expr_as_expr ctx expr
  | Block' {stats} ->
    (* Java: { stats } // Block *)
    (* Why3: ‹stats› *)
    statements_as_expr ctx return_exc stats
  | If {cond; thenpart; elsepart} ->
    (* Java: if (cond) {thenpart} {elsepart?} // Conditional *)
    (* Why3: if ‹cond› ‹thenpart› ‹elsepart› // When `elsepart` defined *)
    (* Why3: if ‹cond› ‹thenpart› () // When no `elsepart` *)
    mk_expr @ Eif (
      expr_as_expr ctx cond,
      statement_as_expr ctx return_exc thenpart,
      match elsepart with
      | Some e -> statement_as_expr ctx return_exc e
      | None -> mk_expr @ Etuple []
    )
  | ForLoop {
      loop_specs;
      init=[lazy (VariableDecl {
          sym;
          vartype=lazy (PrimitiveTypeTree {type_tag=TagInt}), _;
          init=Some e1;
        }), _];
      cond=lazy (Binary {
          lhs=lazy (Ident {sym=sym1}), _;
          operator=lazy (OperatorSymbol {name="<"}), _;
          rhs=e2;
        }), _;
      step=[lazy {expr=lazy (Unary {
          operator=lazy (OperatorSymbol {name="++"}), _;
          arg=lazy (Ident {sym=sym2}), _;
        }), _}, _];
      body=e3;
    } when id sym = id sym1 && id sym1 = id sym2 ->
    (* Java: invariant I_i; for (int i=e1; i < e2; i++) { ‹stats› } // Simple for-loop *)
    (* Why3: let ref i = ‹e1› in while !i < ‹e2› do variant { ‹e2› - !i } invariant { ‹e1› <= i <= ‹e2› } invariant { ‹I_i› } ‹stats›; i <- i+1 done *)
    let ctr = mk_ident' (var_symbol_name sym) in
    let info =
      let mods = {flags=[]; annotations=[]} in
      VarInfo {sym; ident=ctr; is_field=false; mods} in
    M.set vars sym info;
    let invariant = (* e1 <= !ctr <= e2 *)
      let open T in
      mk_binop
        (mk_infix
            (expr_as_term ctx e1)
            (mk_ident @ Ident.op_infix "<=")
            (mk_idapp (mk_qualid ["Ref"; "contents"])
              [mk_var (Qident ctr)]))
        `And
        (mk_infix
            (mk_idapp (mk_qualid ["Ref"; "contents"])
              [mk_var (Qident ctr)])
            (mk_ident @ Ident.op_infix "<=")
            (expr_as_term ctx e2)) in
    let invariants =
      let aux o = match force o with
        | StatementLoopExpr {expr} ->
          Some (expr_as_term ctx expr)
        | StatementLoopModifies ->
          (* TODO Can we do something with Jml’s keyword "loop_modifies"? Or just rely on inference by Why3. *)
          None in
      List.filter_map aux loop_specs in
    let variant = (* variant { e2 - !ctr } *)
      T.mk_idapp
        (mk_qualid ["Int"; Ident.op_infix "-"])
        [expr_as_term ctx e2;
          T.mk_idapp (mk_qualid ["Ref"; "contents"]) [T.mk_var (Qident ctr)]] in
    let open E in
    mk_let ctr
      (mk_idapp (mk_qualid ["Ref"; "ref"])
         [mk_cast
            (expr_as_expr ctx e1)
            (PTtyapp (mk_qualid ["Int32"; "int32"], []))])
      (mk_while
         (mk_apply
            (mk_apply
               (mk_var (mk_qualid ["Int32"; Ident.op_infix "<"]))
               (mk_idapp (mk_qualid ["Ref"; "contents"]) [E.mk_var (Qident ctr)]))
            (expr_as_expr ctx e2))
         (invariant :: invariants)
         [variant, None]
         (mk_seq
            (statement_as_expr ctx return_exc e3)
            (mk_expr @ Eassign [
                mk_var (Qident ctr),
                Some (mk_qualid ["Ref"; "contents"]),
                mk_apply
                  (mk_apply
                     (mk_var @ mk_qualid ["Int32"; Ident.op_infix "+"])
                     (mk_idapp
                        (mk_qualid ["Ref"; "contents"])
                        [mk_var (Qident ctr)]))
                  (mk_const (Constant.int_const_of_int 1))])))

  | Try {body=lazy {stats}, _; catchers; finalizer=None; resources=[]} ->
    (* Java: try { body } except (E e) {stats} ...; // Try-except *)
    (* Why3: match ‹body› with exception ‹E› as ‹e› -> ‹stats› ... *)
    let body = statements_as_expr ctx return_exc stats in
    let branches =
      let aux = forced @ function
          | Catch {param; body=lazy {stats}, _} ->
            (* Java: except (E e) { stats } // Except case *)
            (* Why3: exception ‹E› as ‹e› -> ‹stats› *)
            let ExceptionInfo {ident} = M.get exceptions (force param).typ in
            let pat = mk_pat @ Ptuple [] in
            let stats = statements_as_expr ctx return_exc stats in
            Qident ident, Some pat, stats in
      List.map aux catchers in
    mk_expr @ Ematch (body, [], branches)
  | Return {expr} ->
    (* Java: return e; // Return statement *)
    (* Why3: raise (Return' ‹e›) *)
    (match return_exc with
      | Some exc_ident ->
        let e =
          match force expr with
          | Literal' (BotLiteral _) ->
            None
          | _ ->
            Some (expr_as_expr ctx expr)
        in
        mk_expr @ Eraise (Qident exc_ident, e)
      | None -> failwith "Cannot return")
  | Throw {expr=lazy (Parens {expr=lazy (NewClass {clazz=lazy (Ident {typ}), _; args=[]}), _}), _;}
  | Throw {expr=lazy (NewClass {clazz=lazy (Ident {typ}), _; args=[]}), _} when
      M.is exceptions typ ->
    (* Java: raise (new E()); // E is user-defined exception *)
    (* Why3: raise (‹E› ())  *)
    let ExceptionInfo {ident} = M.get exceptions typ in
    mk_expr @ Eraise (Qident ident, Some (mk_expr @ Etuple []))
  | JmlStatementExpr {keyword="assert"; expr} ->
    (* Java: assert e; // Assertion *)
    (* Why3: assert ‹e› *)
    let e = mk_expr @ Eassert (
        Expr.Assert,
        expr_as_term ctx expr
      ) in
    (match pos expr with
     | None -> e
     | Some pos ->
       mk_expr @ Eattr (ATstr (Ident.create_attribute ("hyp_name:"^string_of_int pos)), e))
  | s ->
    failwith "statement_as_expr not implemented: %a" pp_statement' s

(** {3 Conversion of declarations} *)

let type_clause_as_term ctx o = flip forced o @ function
    | TypeClauseExpr {keyword=None; expr} ->
      expr_as_term ctx expr
    | c ->
      failwith "type_clause_as_term %a" pp_jml_type_clause' c

let exception_decl sym typ =
  let class_name = type_symbol_name sym in
  (* eprintf "Make exception %s:%s@." (id sym) class_name; *)
  let ident = mk_ident' class_name in
  let info = ExceptionInfo {sym; ident} in
  let decls = [Dexn (ident, PTtuple [], Ity.MaskVisible)] in
  M.set exceptions typ info;
  decls, []

let separate_defs defs =
  let fields, constructors, methods, pure_model_methods = ref [], ref [], ref [], ref [] in
  let aux def = match force def with
    | Statement' (VariableDecl {sym; init; typ; nameexpr=None; mods=lazy mods, _}) ->
      fields := (sym, init, typ, mods) :: !fields
    | MethodDecl {name = "<init>"; restype = None; sym; params; specs; throws;
                  body = Some (lazy (Statement' (Block' {
                      stats =  (lazy (ExprStatement {
                          expr = lazy (MethodInvocation {
                              meth = Some (lazy (Ident {
                                  name = "super"}), _)
                            }), _
                        }), _) :: stats
                    })), _)
                 } ->
      (* -Java: C(args) { this.field = expr; … } *)
      let assignments =
        let aux = forced @ function
            | ExprStatement {
                expr = lazy (Assign {
                    lhs = lazy (FieldAccess {
                        selected = lazy (Ident {name="this"}), _;
                        sym = field_sym
                      }), _;
                    rhs = expr;
                  }), _} ->
              field_sym, expr
            | x -> failwith "Not an assignment: %a" pp_statement' x in
        List.map aux stats in
      constructors := (sym, params, specs, assignments, throws) :: !constructors
    | MethodDecl {name; sym; params; specs; throws=[];
                  mods=lazy mods, _;
                  typ=lazy (MethodType {restype}), _;
                  body=None} when
        not @ String.equal name "<init>" &&
        is_model mods && is_pure mods ->
      pure_model_methods := (sym, params, specs, restype, mods) :: !pure_model_methods
    | MethodDecl {
        name; sym; params; specs; throws; mods=lazy mods, _;
        typ=lazy (MethodType {restype}), _;
        body=Some (lazy (Statement' (Block' {stats})), _)
      } when
        not @ String.equal name "<init>" ->
      methods := (sym, params, restype, specs, stats, throws, mods) :: !methods
    | _ ->
      failwith "Unexpected tree as decl: %a" pp_tree def in
  List.iter aux defs;
  List.(rev !fields, rev !constructors, rev !methods, rev !pure_model_methods)

let separate_behavior_clauses ctx clauses =
  let requires, assigns, ensures, signals = ref [], ref [], ref [], ref [] in
  let aux clause =
    (* eprintf "Clause %a@." pp_jml_method_clause clause; *)
    match force clause with
    | JmlMethodClauseExprExc {keyword="requires"; expr} ->
      let t = expr_as_term ctx expr in
      requires := t :: !requires
    | JmlMethodClauseStoreRef {list} ->
      let aux expr =
        match force expr with
        | Ident {sym=lazy (VarSymbol' _), _ as sym} when is_field_ident_symbol sym ->
          let VarInfo {ident} = M.get vars (get_var_symbol sym) in
          let info = mk_term @ Tidapp (Qident ident, [mk_term @ Tident (Qident ctx.this_ident)]) in
          assigns := info :: !assigns
        | JmlStoreRefKeyword {kind=lazy (NoTypeMisc {keyword="\\nothing"}), _} ->
          () (* JML assignable \nothing: only locations of newly allocated objects *)
        | FieldAccess {selected; sym} ->
          let selected_this = expr_as_term ctx selected in
          let VarInfo {ident} = M.get vars (get_var_symbol sym) in
          let info = mk_term @ Tidapp (Qident ident, [selected_this]) in
          assigns := info :: !assigns
        (* eprintf "Ignore writes annotation - how to encode in Why3? %a@." pp_expr expr *)
        | _ ->
          failwith "JmlStoreRefKeyword list element: %a" pp_expr expr in
      List.iter aux list
    | JmlMethodClauseExpr {keyword="ensures"; expr} ->
      let t = expr_as_term ctx expr in
      let t =
        match pos expr with
        | None -> t
        | Some pos ->
          mk_term @ Tattr (ATstr (Ident.create_attribute (string_of_int pos)), t) in
      ensures := t :: !ensures
    | JmlMethodClauseSignalsOnly {list} ->
      let aux o =
        match force o with
        | FieldAccess {name="RuntimeException"} ->
          None
        | FieldAccess {
            selected=lazy (Ident {sym=lazy (TypeSymbol' UnnamedPackage), _}), _;
            sym=lazy (TypeSymbol' (ClassSymbol {typ})), _
          } ->
          let info =
            let ExceptionInfo {ident} = M.get exceptions typ in
            loc(), [Qident ident, None] in
          Some info
        | _ ->
          failwith "clause: %a" pp_expr o in
      signals := List.filter_map aux list @@ !signals
    | JmlMethodClauseSignals {expr; vardef=Some (lazy {sym; typ}, _)} ->
      let info =
        let exn_ident =
          let ExceptionInfo {ident} = M.get exceptions typ in
          Qident ident in
        let p =
          let ident = mk_ident' (var_symbol_name sym) in
          let mods = {flags=[]; annotations=[]} in
          M.set vars sym (VarInfo {sym; ident; is_field=false; mods});
          mk_pat @ Pvar ident in
        let t = expr_as_term ctx expr in
        loc(), [exn_ident, Some (p, t)] in
      signals := info :: !signals
    | JmlMethodClauseSignals {vardef=None; expr=lazy (Literal' (BoolLiteral {value=false})), _} ->
      (* TODO What does this indicate? That the method does not throw any exception? *)
      eprintf "Ignoring: %a@." pp_jml_method_clause clause
    | c ->
      failwith "clause: %a" pp_jml_method_clause' c
  in
  List.iter aux clauses;
  List.(rev !requires, rev !assigns, rev !ensures, rev !signals)

let mk_apply_invariants invariant_idents id =
  let aux id' = T.(mk_idapp (Qident id') [mk_var (Qident id)]) in
  List.map aux invariant_idents

let mk_conjunction = function
  | [] -> mk_term @ Ttrue
  | t :: ts ->
    let aux sofar t = mk_term @ Tbinop (sofar, Dterm.DTand, t) in
    List.fold_left aux t ts

let class_decl (sym: type_symbol) (typ:typ) (defs:tree list) (clauses: jml_type_clause list) =

  let class_name = type_symbol_name sym in
  let fullname = class_name in (* TODO *)
  (* eprintf "Make class %s:%s@." (id typ) class_name; *)

  let type_ident = mk_ident' class_name in

  let new_ident = mk_ident' ~suffix:"new" class_name in

  let address_field = mk_ident' ~suffix:"address" class_name in

  let fields_memory, methods_memory = fields, methods in
  eprintf "Separate...@.";
  let fields, constructors, methods, pure_model_methods = separate_defs defs in
  eprintf "Separated: %d/%d@." (List.length methods) (List.length pure_model_methods);

  let field_infos =
    let aux (sym, init, typ, mods) =
      let pty = typ_as_pty ~target:`Expr typ in
      let ident = mk_ident' (var_symbol_name sym) in
      M.set vars sym (VarInfo {sym; ident; is_field=true; mods=mods});
      let info = FieldInfo {sym; init; pty; ident; mods} in
      M.set fields_memory sym info;
      info in
    List.map aux fields in

  let tree_decl_mods = forced @ function
      | Statement' (VariableDecl {mods=lazy mods, _}) -> mods
      | t -> failwith "tree_as_binder': %a" pp_tree' t in

  let constructor_infos =
    let aux (sym, params, _, _, _) =
      let ident = mk_ident' ~suffix:"init" class_name in
      let arg_mods = List.map tree_decl_mods params in
      let info = MethodInfo {sym; ident; arg_mods; mods={flags=[]; annotations=[]}; is_pure_model=false} in
      M.set methods_memory sym info;
      info in
    List.map aux constructors in

  let method_infos =
    let aux (sym, params, _restype, _specs, _stats, _throws, mods) =
      let ident = mk_ident' ~suffix:(method_symbol_name sym) class_name in
      let arg_mods = List.map tree_decl_mods params in
      let info = MethodInfo {sym; ident; mods; arg_mods; is_pure_model=false} in
      M.set methods_memory sym info;
      info in
    List.map aux methods in

  let invariant_idents =
    let aux _ =
      mk_ident' ~suffix:"invariant" class_name in
    List.map aux clauses in

  M.set classes typ
    (ClassInfo {fullname; sym; type_ident; new_ident; fields=field_infos; address_field;
                methods=constructor_infos@@method_infos; invariant_idents});

  let type_decl =
    (* completely immutable to concretize type paramaters, e.g. `array c'im` *)
    let td_def =
      let f_mutable = false in
      let address_field =
        {f_ident=address_field; f_pty=mk_address_pty (); f_mutable; f_ghost=false; f_loc=loc()} in
      let aux (FieldInfo fi) =
        {f_ident=fi.ident; f_pty=fi.pty; f_mutable; f_ghost=false; f_loc=loc()} in
      TDrecord (List.map aux field_infos @@ [address_field]) in
    Dtype [{td_def; td_ident=type_ident; td_vis=Public; td_mut=false;
            td_inv=[]; td_params=[]; td_wit=None; td_loc=loc()}] in

  let predicates_functions =
    let aux (sym, params, (specs: method_specs), restype, mods) =
      eprintf "Predicate function: %s/%s@." (method_symbol_name sym) (id sym);
      let ident = mk_ident' ~suffix:(method_symbol_name sym) class_name in
      let arg_mods = List.map tree_decl_mods params in
      M.set methods_memory sym
        (MethodInfo {sym; ident; mods; arg_mods; is_pure_model=true});
      let params =
        this_binder ~type_ident ::
        param_binders ~target:`Expr params in
      let def =
        match specs with
        | lazy (MethodSpecs {
            cases=lazy (JmlMethodSpecs {
                cases=[lazy (JmlSpecificationCase {clauses}), _]
              }), _}), _ ->
          let rec aux requires = function
            | [] -> failwith "Missing trailing \"ensures \\result == ...;\" in pure method"
            | [lazy (JmlMethodClauseExpr {
                keyword="ensures";
                expr=lazy (Binary {
                    lhs=result; rhs=def;
                    operator=lazy (OperatorSymbol {name="=="}), _
                  }), _}), _] when is_jml_singleton "\\result" result ->
              let t =
                let ctx = {this_ident; result_nullable=None (* bool *)} in
                expr_as_term ctx def in
              List.rev requires, t
            | (lazy (JmlMethodClauseExprExc {keyword="requires"; expr}), _) :: clauses ->
              let ctx = {this_ident; result_nullable=Some false (* bool *)} in
              let t = expr_as_term ctx expr in
              aux (t :: requires) clauses
            | _ -> failwith "Only requires and trailing ensures allowed in pure methods" in
          let requires, ensures = aux [] clauses in
          let aux requires t = mk_binop Dterm.DTimplies requires t in
          List.fold_right aux requires ensures
        | _ -> failwith "Only simple behaviour specification for pure methods" in
      let typ =
        if is_primitive_type_tag TagBool restype then
          None (* predicate *)
        else
          Some (typ_as_pty ~target:`Term restype) in
      Dlogic [{ld_loc=loc(); ld_ident=ident; ld_params=params; ld_type=typ; ld_def=Some def}] in
    List.map aux pure_model_methods in

  let invariant_decls =
    let ctx = {this_ident; result_nullable=None} in
    let aux ident clause =
      let term = type_clause_as_term ctx clause in
      let ld_params =
        [loc(), Some this_ident, false, mk_atomic_type (Qident type_ident)] in
      Dlogic [{ld_ident=ident; ld_params; ld_def=Some term; ld_loc=loc(); ld_type=None}] in
    List.map2 aux invariant_idents clauses in

  let for_throws = forced @ function
      | Ident {typ} ->
        let ExceptionInfo {ident} = M.get exceptions typ in
        loc(), [Qident ident, None]
      | e ->
        failwith "for_throws: %a" pp_expr' e in

  let separate_specs ctx o =
    let MethodSpecs {cases=lazy (JmlMethodSpecs {cases}), _} = force o in
    match List.map force cases with
    | [] ->
      [], [], [], []
    | [JmlSpecificationCase {clauses; token=(None|Some "BEHAVIOR")}] ->
      separate_behavior_clauses ctx clauses
    | [JmlSpecificationCase {clauses=cs1; token=Some "BEHAVIOR"};
       JmlSpecificationCase {clauses=cs2; token=Some "EXCEPTIONAL_BEHAVIOR"}] ->
      let r1,a1,e1,s1 = separate_behavior_clauses ctx cs1 in
      let r2,a2,e2,s2 = separate_behavior_clauses ctx cs2 in
      r1@@r2, a1@@a2, e1@@e2, s1@@s2
    | _ ->
      failwith "Method specs not implemented: %a" pp_method_specs o in

  (* Precompute things that are shared between declarations and implementations *)

  let constructors =
    let aux (sym, params, specs, stats, throws) =
      let all_binders = param_binders ~target:`Expr params in
      let specs =
        (* TODO Add invariants for all object params? Not yet, see Tafat’s thesis *)
        let sp_pre, sp_writes, ensures, signals =
          let ctx = {this_ident=result_ident (* SIC! for functional constructors *); result_nullable=None} in
          separate_specs ctx specs in
        (* TODO add: all fields to sp_writes for mutable constructors *)
        let sp_post =
          let aux t = loc(), [mk_pat @ Pvar result_ident, t] in
          let invariants = mk_apply_invariants invariant_idents result_ident in
          List.map aux (ensures @@ invariants) in
        let sp_xpost =
          List.map for_throws throws @@ signals in
        {empty_spec with sp_pre; sp_post; sp_xpost; sp_writes} in
      (sym, params, all_binders, specs, stats) in
    List.map aux constructors in

  let methods =
    let aux (sym, params, restype, specs, stats, throws, mods) =
      eprintf "Method: %s/%s@." (method_symbol_name sym) (id sym);
      let res_pty =
        let res_pty = typ_as_pty ~target:`Expr restype in
        if is_nullable mods then
          mk_nullable_type res_pty
        else
          res_pty in
      let all_binders =
        this_binder ~type_ident ::
        param_binders ~target:`Expr params in
      let specs =
        (* Add invariants for all object params? Not yet, see Tafat’s thesis *)
        let ctx = {this_ident; result_nullable=Some (is_nullable mods)} in
        (* TODO Add invariant for this! *)
        let sp_pre, sp_writes, ensures, signals = separate_specs ctx specs in
        let sp_pre =
          let this_invariants =
            mk_apply_invariants invariant_idents this_ident in
          this_invariants @@ sp_pre in
        let sp_post =
          let this_invariants =
            mk_apply_invariants invariant_idents this_ident in
          let result_invariants =
            match M.get_opt classes restype with
            | Some (ClassInfo {invariant_idents}) ->
              mk_apply_invariants invariant_idents result_ident
            | None -> [] in
          let aux t = loc(), [mk_pat @ Pvar result_ident, t] in
          List.map aux (ensures @@ this_invariants @@ result_invariants) in
        let sp_xpost = List.map for_throws throws @@ signals in
        {empty_spec with sp_pre; sp_post; sp_xpost; sp_writes} in
      (sym, res_pty, params, all_binders, specs, stats) in
    List.map aux methods in

  let constructor_decls =
    let aux (_sym, _, all_binders, specs, _) (MethodInfo {ident}) =
      let expr =
        let res_pty = mk_tyapp (Qident type_ident) [] in
        mk_expr @ Eany (all_binders, Expr.RKnone, Some res_pty, mk_pat @ Pwild, Ity.MaskVisible, specs) in
      Dlet (ident, false, Expr.RKnone, expr) in
    List.map2 aux constructors constructor_infos in

  let method_decls =
    let aux (_sym, res_pty, _, all_binders, specs, _) (MethodInfo {ident}) =
      let expr = mk_expr @ Eany (all_binders, Expr.RKnone, Some res_pty, mk_pat @ Pwild, Ity.MaskVisible, specs) in
      Dlet (ident, false, Expr.RKnone, expr) in
    List.map2 aux methods method_infos in

  let let_params_as_refs params expr =
    let aux expr tree =
      match force tree with
      | Statement' (VariableDecl {sym}) ->
        let VarInfo {ident; mods} = M.get vars sym in
        if is_final mods then
          expr
        else
          let e =
            let qualid = mk_qualid ["Ref"; "ref"] in
            E.mk_idapp qualid [E.mk_var (Qident ident)] in
          mk_expr @ Elet (ident, false, Expr.RKnone, e, expr)
      | _ -> assert false in
    List.fold_left aux expr params in

  let constructor_impls =
    let aux (_sym, params, all_params, specs, stats) =
      let ident = mk_ident' ~suffix:"init'impl" class_name in
      let expr = (* Constructor body *)
        let fields =
          let aux (field_sym, expr) =
            let FieldInfo fi = M.get fields_memory (get_var_symbol field_sym) in
            let ctx = {this_ident = this_ident; result_nullable = None} in
            Qident fi.ident, expr_as_expr ctx expr in
          List.map aux stats in
        let address =
          Qident address_field,
          E.mk_idapp (mk_qualid ["Address"; "fresh"])
            [E.mk_tuple []] in
        E.mk_record (fields @@ [address]) in
      let expr = (* Bind non-final parameters as references *)
        let_params_as_refs params expr in
      let expr = (* Instruct Why3 to split the VC efficiently *)
        let attr = ATstr (Ident.create_attribute "vc:sp") in
        mk_expr @ Eattr (attr, expr) in
      let expr = (* Define function, bind parameters *)
        let res_pty = mk_tyapp (Qident type_ident) [] in
        mk_expr @ Efun (List.map param_to_binder all_params, Some res_pty, mk_pat @ Pwild, Ity.MaskVisible, specs, expr) in
      Dlet (ident, false, Expr.RKnone, expr) in
    List.map aux constructors in

  let method_impls =
    let aux (sym, res_pty, params, all_binders, specs, stats) =
      let ident = mk_ident' ~suffix:(method_symbol_name sym^"_impl") class_name in
      let return_exc = mk_ident "Return" in
      let expr = (* Method body *)
        let ctx = {this_ident; result_nullable=None} in
        statements_as_expr ctx (Some return_exc) stats in
      let expr = (* Treat return exceptions *)
        let v = mk_ident' "v" in
        let branch = Qident return_exc, (Some (mk_pat @ Pvar v)), mk_expr @ Eident (Qident v) in
        mk_expr @ Ematch (expr, [], [branch]) in
      let expr = (* Define return exception *)
        mk_expr @ Eexn (return_exc, res_pty, Ity.MaskVisible, expr) in
      let expr = (* Bind non-final parameters as references *)
        let_params_as_refs params expr in
      let expr = (* Instruct Why3 to split the VC efficiently *)
        let attr = ATstr (Ident.create_attribute "vc:sp") in
        mk_expr @ Eattr (attr, expr) in
      let expr = (* Define function, bind parameters *)
        let binders =
          let aux (l,n,b,t) = (l,n,b,Some t) in
          List.map aux all_binders in
        let specs =
          let sp_pre =
            mk_apply_invariants invariant_idents this_ident
            @@ specs.sp_pre in
          let sp_post =
            let invariants =
              let aux t = loc(), [mk_pat @ Pvar result_ident, t] in
              List.map aux (mk_apply_invariants invariant_idents this_ident) in
            specs.sp_post @@ invariants in
          {specs with sp_pre; sp_post} in
        mk_expr @ Efun (binders, Some res_pty, mk_pat @ Pwild, Ity.MaskVisible, specs, expr) in
      (* Define method *)
      Dlet (ident, false, Expr.RKnone, expr) in
    List.map aux methods in

  let decls =
    type_decl :: predicates_functions @@ invariant_decls @@ constructor_decls @@ method_decls in
  let impls =
    constructor_impls @@ method_impls in
  decls, impls

let tree_as_decl o = flip forced o @ function

    | Statement' (Import {qualid=lazy (Expr' qualid), _}) ->
      (* -Java: import expr *)
      (* -Why3: ignore for now *)
      let rec pp_qualid fmt = function
        | FieldAccess {selected=lazy selected, _; name} ->
          Format.fprintf fmt "%a.%s" pp_qualid selected name
        | Ident {name} ->
          Format.pp_print_string fmt name
        | t' -> failwith "pp_qualid: %a" pp_expr' t' in
      eprintf "Ignoring import %a@." pp_qualid qualid;
      [], []

    | ClassDecl {sym; typ} when
        has_exception_supertype typ ->
      (* Section: Exception declaration *)
      (* Java: class E extends Exception {} *)
      (* Why3: exception ‹E› () *)
      (* A plain exception subclass, TODO test only <init> method with just a call super() *)
      exception_decl sym typ

    | ClassDecl {
        sym; typ; defs;
        type_specs=lazy (TypeSpecs {clauses}), _;
        extending=None;
        typarams=[];
      } ->
      (* -Java: class C { fields + constructors + methods } *)
      class_decl sym typ defs clauses

    | t ->
      failwith "tree_as_decl: %a" pp_tree' t

let compilation_unit = forced @ function
    | CompilationUnit {defs} ->
      let imports = [
        use_import [ "bool"; "Bool" ];
        use_import [ "ref"; "Ref" ];
        use_import [ "int"; "Int" ];
        use_import [ "mach"; "int"; "Int32" ];
        use_import [ "mach"; "array"; "Array32" ];
        use_import [ "seq"; "Seq" ];
        use_import [ "seq"; "Occ" ];
        use_import [ "seq"; "FreeMonoid" ];
        use_import [ "jml2why3"; "Queue" ];
        use_import [ "jml2why3"; "Nullable"];
        use_import [ "jml2why3"; "LinkedList"];
        use_import [ "jml2why3"; "Address"];
        use_import [ "jml2why3"; "Utils"];
      ] in
      let decls, impls = List.split @ List.map tree_as_decl defs in
      imports @@ List.flatten decls @@ List.flatten impls

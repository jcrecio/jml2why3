open Format
open Why3
open Ptree

let (@) = (@@)

module Ast = struct

  (* let loc () = Loc.dummy_position *)
  let loc =
    let counter = ref 0 in
    fun () ->
      incr counter;
      Loc.user_position "" !counter 0 !counter 0

  let reloc l expr =
    let s,_,b,_,e = Loc.get expr.expr_loc in
    let expr_loc = Loc.user_position s l b l e in
    {expr with expr_loc}

  let mk_ident s =
    { id_str = s; id_ats = []; id_loc = loc() }

  let mk_qualid l =
    let rec aux l =
      match l with
      | [] -> assert false
      | [x] -> Qident(mk_ident x)
      | x::r -> Qdot(aux r,mk_ident x)
    in
    aux (List.rev l)
  let use_import l =
    let qid_id_opt = (mk_qualid l, None) in
    Duseimport(loc(),false,[qid_id_opt])
  let mk_loc = function
    | None -> loc()
    | Some l -> Loc.user_position "" l 0 l 0

  let mk_expr ?loc e = { expr_desc = e; expr_loc = mk_loc loc }
  let mk_term ?loc t = { term_desc = t; term_loc = mk_loc loc }
  let mk_pat ?loc p = { pat_desc = p; pat_loc = mk_loc loc }

  let param0 = [loc(), None, false, Some (PTtuple [])]
  let param1 id ty = [loc(), Some id, false, Some ty]

  let mk_arrow t1 t2 = PTarrow (t1, t2)
  let mk_tyapp qid l = PTtyapp (qid, l)
  let mk_atomic_type l = mk_tyapp l []
  let mk_atomic_type' l = mk_atomic_type (mk_qualid l)
  let mk_binop ?loc op e1 e2 = mk_term ?loc (Tbinop (e1, op, e2))

  module type PtreeHelpers = sig
    type t
    val name : string
    val target : [`Expr|`Term]
    val mk_const : ?loc:int -> Constant.constant -> t
    val mk_idapp : ?loc:int -> qualid -> t list -> t
    val mk_apply : ?loc:int -> t -> t -> t
    val mk_var : ?loc:int -> qualid -> t
    val mk_cast : ?loc:int -> t -> pty -> t
    val mk_case : ?loc:int -> t -> (pattern * t) list -> t
    val mk_tuple : ?loc:int -> t list -> t
    val mk_record : ?loc:int -> (qualid * t) list -> t
    val mk_update : ?loc:int -> t -> (qualid * t) list -> t
    val mk_binop : ?loc:int -> t -> [`And|`Or] -> t -> t
    val mk_not : ?loc:int -> t -> t
    val mk_infix : ?loc:int -> t -> ident -> t -> t
    val mk_innfix : ?loc:int -> t -> ident -> t -> t
    val mk_let : ?loc:int -> ident -> t -> t -> t
    val mk_scope : ?loc:int -> qualid -> t -> t
  end

  module E : PtreeHelpers with type t = expr = struct
    type t = expr
    let name = "expr"
    let target = `Expr
    let mk = mk_expr
    let mk_const ?loc i = mk ?loc (Econst i)
    let mk_idapp ?loc f li = mk ?loc (Eidapp (f, li))
    let mk_apply ?loc e1 e2 = mk ?loc (Eapply (e1, e2))
    let mk_var ?loc x = mk ?loc (Eident x)
    let mk_cast ?loc e pty = mk ?loc (Ecast (e, pty))
    let mk_tuple ?loc es = mk ?loc (Etuple es)
    let mk_case ?loc e cases = mk ?loc (Ematch (e, cases, []))
    let mk_record ?loc fields = mk ?loc (Erecord fields)
    let mk_update ?loc e fields = mk ?loc (Eupdate (e, fields))
    let mk_not ?loc e = mk ?loc (Enot e)
    let mk_binop ?loc e1 op e2 =
      mk ?loc
        (match op with
         | `And -> Eand (e1, e2)
         | `Or -> Eor (e1, e2))
    let mk_infix ?loc e1 op e2 =
      mk ?loc (Einfix (e1, op, e2))
    let mk_innfix ?loc e1 op e2 =
      mk ?loc (Einfix (e1, op, e2))
    let mk_let ?loc id e1 e2 =
      mk ?loc (Elet (id, false, Expr.RKnone, e1, e2))
    let mk_scope ?loc qid e =
      mk ?loc (Escope (qid, e))
  end

  module T : PtreeHelpers with type t = term = struct
    type t = term
    let name = "term"
    let target = `Term
    let mk = mk_term
    let mk_const ?loc i = mk ?loc (Tconst i)
    let mk_idapp ?loc f li = mk ?loc (Tidapp (f, li))
    let mk_apply ?loc t1 t2 = mk ?loc (Tapply (t1, t2))
    let mk_var ?loc x = mk ?loc (Tident x)
    let mk_cast ?loc t pty = mk ?loc (Tcast (t, pty))
    let mk_tuple ?loc ts = mk ?loc (Ttuple ts)
    let mk_case ?loc t cases = mk ?loc (Tcase (t, cases))
    let mk_record ?loc fields = mk ?loc (Trecord fields)
    let mk_update ?loc t fields = mk ?loc (Tupdate (t, fields))
    let mk_not ?loc t = mk ?loc (Tnot t)
    let mk_binop ?loc t1 op t2 =
      let op = match op with `And -> Dterm.DTand_asym | `Or -> Dterm.DTor_asym in
      mk ?loc (Tbinop (t1, op, t2))
    let mk_infix ?loc t1 op t2 =
      mk ?loc (Tinfix (t1, op, t2))
    let mk_innfix ?loc t1 op t2 =
      mk ?loc (Tinnfix (t1, op, t2))
    let mk_let ?loc id t1 t2 =
      mk ?loc (Tlet (id, t1, t2))
    let mk_scope ?loc qid e =
      mk ?loc (Tscope (qid, e))
  end

  let empty_spec = {
    sp_pre = [];
    sp_post = [];
    sp_xpost = [];
    sp_reads = [];
    sp_writes = [];
    sp_alias = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
    sp_partial = false;
  }
end

let config = Whyconf.read_config None
let main = Whyconf.get_main config
let env = Env.create_env ("." :: Whyconf.loadpath main)

let why3_type_file =
  Typing.type_mlw_file env [] "<generated>"

let provers =
  let driver prover : Driver.driver =
    try
      Driver.load_driver_for_prover main env prover
    with e ->
      eprintf "Failed to load driver: %a@."
        Exn_printer.exn_printer e;
      exit 1 in
  let alt_ergo =
    let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
    let provers = Whyconf.filter_provers config fp in
    if Whyconf.Mprover.is_empty provers then begin
      eprintf "Prover Alt-Ergo not installed or not configured@.";
      exit 1
    end else
      snd (Whyconf.Mprover.max_binding provers) in
  let alt_ergo_driver = driver alt_ergo in
  let z3 =
    let fp = Whyconf.parse_filter_prover "Z3" in
    let provers = Whyconf.filter_provers config fp in
    if Whyconf.Mprover.is_empty provers then begin
      eprintf "Prover Z3 not installed or not configured@.";
      exit 1
    end else
      snd (Whyconf.Mprover.max_binding provers) in
  let z3_driver = driver z3 in
  let cvc4 =
    let fp = Whyconf.parse_filter_prover "CVC4" in
    let provers = Whyconf.filter_provers config fp in
    if Whyconf.Mprover.is_empty provers then begin
      eprintf "Prover CVC4 not installed or not configured@.";
      exit 1
    end else
      snd (Whyconf.Mprover.max_binding provers) in
  let cvc4_driver = driver cvc4 in
  let eprover =
    let fp = Whyconf.parse_filter_prover "Eprover" in
    let provers = Whyconf.filter_provers config fp in
    if Whyconf.Mprover.is_empty provers then begin
      eprintf "Prover Eprover not installed or not configured@.";
      exit 1
    end else
      snd (Whyconf.Mprover.max_binding provers) in
  let eprover_driver = driver eprover in
  ["CVC4",     cvc4,     cvc4_driver;
   "Alt-ergo", alt_ergo, alt_ergo_driver;
   "Z3",       z3,       z3_driver;
   "Eprover",  eprover,  eprover_driver]

type answer = Valid | Invalid | Dontknow

let run_provers limit_time t =
  let rec aux = function
    | [] ->
      failwith "run_provers"
    | (name, prover, driver) :: provers ->
      printf " %s…@?" name;
      let r =
        let limit = Call_provers.{empty_limit with limit_time} in
        let command = prover.Whyconf.command in
        Driver.prove_task ~config:main ~limit ~command driver t |>
        Call_provers.wait_on_call in
      match r.pr_answer with
      | Valid -> Valid
      | Invalid -> Invalid
      | _ ->
        if provers = []
        then Dontknow
        else aux provers in
  aux provers

let indent n =
  String.make (2*n) ' '

let res_to_string = function
  | Valid -> "Valid"
  | Invalid -> "Invalid"
  | Dontknow -> "Dontknow"

let shorten_res rs =
  if List.for_all ((=) Valid) rs then
    Valid
  else if List.exists ((=) Invalid) rs then
    Invalid
  else
    Dontknow

let rec solve_task name ~limit_depth ~limit_time1 ~limit_time2 ~context ~depth ~total i t =
  let id = sprintf "%s%d" (if context = "" then "" else context^"-") i in
  let goal, _ = Task.task_separate_goal t in
  let _, expl, _ = Termcode.goal_expl_task ~root:(depth=0) t in
  printf "%s%s/%d: %s - %a.@?"
    (indent depth) id total
    expl
    (if 0 < depth then Pretty.print_tdecl else fun fmt _ -> pp_print_string fmt "…") goal;
  let res = run_provers limit_time1 t in
  printf " %s.@?" (res_to_string res);
  let res =
    if res <> Dontknow then
      (printf "@.";
       res)
    else if depth < limit_depth then
      (printf " Splitting…@?";
       let ts = Trans.apply_transform "split_vc" env t in
       if 1 < List.length ts then
         (printf "@.";
          List.mapi (solve_task name ~limit_depth ~limit_time1 ~limit_time2 ~context:id ~depth:(succ depth) ~total:(List.length ts)) ts
          |> shorten_res)
       else
         (printf " didn't work, trying harder@.";
          let res = run_provers limit_time2 t in
          printf "%s.@." (res_to_string res);
          res))
    else
      (printf " Trying harder@.";
       let res = run_provers limit_time2 t in
       printf "%s.@." (res_to_string res);
       res) in
  if res <> Valid && depth < 2 then
    (let goal, _ = Task.task_separate_goal t in
     printf "    %a @."Pretty.print_tdecl goal;
     let filename = Format.sprintf "/tmp/%s-%s.mlw" name id in
     let f = open_out filename in
     let fmt = formatter_of_out_channel f in
     Pretty.print_task fmt t;
     close_out f;
     printf "    --> printed task to file %s@." filename);
  res

let why3_prove ~name ~limit_depth ~limit_time1 ~limit_time2 mods =
  let ts =
    let mods =
      let aux _ m =
        List.rev_append @
        Task.split_theory m.Pmodule.mod_theory None None in
      Wstdlib.Mstr.fold aux mods [] in
    List.rev mods in
  shorten_res @ List.mapi (solve_task name ~limit_depth ~limit_time1 ~limit_time2 ~context:"" ~depth:0 ~total:(List.length ts)) ts

module PtreeDebug = struct

  let opaque fmt _ =
    Format.pp_print_string fmt "<opaque>"

  type position = Loc.position

  let pp_position fmt p =
    let _,l,_,_,_ = Loc.get p in
    Format.pp_print_int fmt l

  type attribute = Ident.attribute = private {
    attr_string : string;
    attr_tag    : int;
  }
  [@@deriving show {with_path=false}]

  type attr = Ptree.attr =
    | ATstr of attribute
    | ATpos of position
  [@@deriving show {with_path=false}]

  type ident = Ptree.ident
  let pp_ident fmt id =
    Format.pp_print_string fmt id.id_str

  let pp_qualid fmt q =
    let rec aux fmt = function
      | Qident id ->
        Format.pp_print_string fmt id.id_str
      | Qdot (q, id) ->
        aux fmt q;
        Format.pp_print_string fmt ".";
        Format.pp_print_string fmt id.id_str in
    Format.fprintf fmt "Qualid %a" aux q

  type pty = Ptree.pty =
    | PTtyvar of ident
    | PTtyapp of qualid * pty list
    | PTtuple of pty list
    | PTref   of pty list
    | PTarrow of pty * pty
    | PTscope of qualid * pty
    | PTparen of pty
    | PTpure  of pty
  [@@deriving show {with_path=false}]

  type ghost = bool
  [@@deriving show {with_path=false}]

  type pattern = Ptree.pattern = {
    pat_desc : pat_desc;
    pat_loc  : position;
  }

  and pat_desc = Ptree.pat_desc =
    | Pwild
    | Pvar of ident
    | Papp of qualid * pattern list
    | Prec of (qualid * pattern) list
    | Ptuple of pattern list
    | Pas of pattern * ident * ghost
    | Por of pattern * pattern
    | Pcast of pattern * pty
    | Pscope of qualid * pattern
    | Pparen of pattern
    | Pghost of pattern
  [@@deriving show {with_path=false}]

  type binder = position * ident option * ghost * pty option
  [@@deriving show {with_path=false}]
  type param  = position * ident option * ghost * pty
  [@@deriving show {with_path=false}]

  type constant = Constant.constant
  let pp_constant = Constant.print_def

  type term = Ptree.term = {
    term_desc : term_desc;
    term_loc  : position;
  }

  and term_desc = Ptree.term_desc =
    | Ttrue
    | Tfalse
    | Tconst of constant
    | Tident of qualid
    | Tasref of qualid
    | Tidapp of qualid * term list
    | Tapply of term * term
    | Tinfix of term * ident * term
    | Tinnfix of term * ident * term
    | Tbinop of term * (Dterm.dbinop[@printer opaque]) * term
    | Tbinnop of term * (Dterm.dbinop[@printer opaque]) * term
    | Tnot of term
    | Tif of term * term * term
    | Tquant of (Dterm.dquant[@printer opaque]) * binder list * term list list * term
    | Teps of ident * pty * term
    | Tattr of attr * term
    | Tlet of ident * term * term
    | Tcase of term * (pattern * term) list
    | Tcast of term * pty
    | Ttuple of term list
    | Trecord of (qualid * term) list
    | Tupdate of term * (qualid * term) list
    | Tscope of qualid * term
    | Tat of term * ident
  [@@deriving show {with_path=false}]

  (** {2 Program expressions} *)

  type invariant = term list
  [@@deriving show {with_path=false}]

  type variant = (term * qualid option) list
  [@@deriving show {with_path=false}]

  type pre = term
  [@@deriving show {with_path=false}]
  type post = position * (pattern * term) list
  [@@deriving show {with_path=false}]
  type xpost = position * (qualid * (pattern * term) option) list
  [@@deriving show {with_path=false}]

  type spec = Ptree.spec = {
    sp_pre     : pre list;
    sp_post    : post list;
    sp_xpost   : xpost list;
    sp_reads   : qualid list;
    sp_writes  : term list;
    sp_alias   : (term * term) list;
    sp_variant : variant;
    sp_checkrw : bool;
    sp_diverge : bool;
    sp_partial : bool;
  }
  [@@deriving show {with_path=false}]

  type rs_kind = Expr.rs_kind =
    | RKnone    (* non-pure symbol *)
    | RKlocal   (* local let-function *)
    | RKfunc    (* top-level let-function *)
    | RKpred    (* top-level let-predicate *)
    | RKlemma   (* top-level or local let-lemma *)
  [@@deriving show {with_path=false}]

  type mask = Ity.mask =
    | MaskVisible
    | MaskTuple of mask list
    | MaskGhost
  [@@deriving show {with_path=false}]

  type expr = Ptree.expr = {
    expr_desc : expr_desc;
    expr_loc  : position;
  }

  and expr_desc = Ptree.expr_desc =
    | Eref
    | Etrue
    | Efalse
    | Econst of constant
    (** lambda-calculus *)
    | Eident of qualid
    | Easref of qualid
    | Eidapp of qualid * expr list
    | Eapply of expr * expr
    | Einfix of expr * ident * expr
    | Einnfix of expr * ident * expr
    | Elet of ident * ghost * rs_kind * expr * expr
    | Erec of fundef list * expr
    | Efun of binder list * pty option * pattern * mask * spec * expr
    | Eany of param list * rs_kind * pty option * pattern * mask * spec
    | Etuple of expr list
    | Erecord of (qualid * expr) list
    | Eupdate of expr * (qualid * expr) list
    | Eassign of (expr * qualid option * expr) list
    (** control *)
    | Esequence of expr * expr
    | Eif of expr * expr * expr
    | Ewhile of expr * invariant * variant * expr
    | Eand of expr * expr
    | Eor of expr * expr
    | Enot of expr
    | Ematch of expr * reg_branch list * exn_branch list
    | Eabsurd
    | Epure of term
    | Eidpur of qualid
    | Eraise of qualid * expr option
    | Eexn of ident * pty * mask * expr
    | Eoptexn of ident * mask * expr
    | Efor of ident * expr * (Expr.for_direction[@printer opaque]) * expr * invariant * expr
    (** annotations *)
    | Eassert of (Expr.assertion_kind[@printer opaque]) * term
    | Escope of qualid * expr
    | Elabel of ident * expr
    | Ecast of expr * pty
    | Eghost of expr
    | Eattr of attr * expr

  and reg_branch = pattern * expr

  and exn_branch = qualid * pattern option * expr

  and fundef = ident * ghost * rs_kind *
               binder list * pty option * pattern * mask * spec * expr
  [@@deriving show { with_path=false}]

  type field = Ptree.field = {
    f_loc     : position;
    f_ident   : ident;
    f_pty     : pty;
    f_mutable : bool;
    f_ghost   : bool
  }
  [@@deriving show { with_path=false}]

  type type_def = Ptree.type_def =
    | TDalias     of pty
    | TDalgebraic of (position * ident * param list) list
    | TDrecord    of field list
    | TDrange     of BigInt.t * BigInt.t [@printer opaque]
                       | TDfloat     of int * int
  [@@deriving show { with_path=false}]

  type visibility = Ptree.visibility = Public | Private | Abstract (** = Private + ghost fields *)
  [@@deriving show { with_path=false}]

  type type_decl = Ptree.type_decl = {
    td_loc    : position;
    td_ident  : ident;
    td_params : ident list;
    td_vis    : visibility; (** records only *)
    td_mut    : bool;       (** records or abstract types *)
    td_inv    : invariant;  (** records only *)
    td_wit    : expr option;
    td_def    : type_def;
  }
  [@@deriving show { with_path=false}]

  type logic_decl = Ptree.logic_decl = {
    ld_loc    : position;
    ld_ident  : ident;
    ld_params : param list;
    ld_type   : pty option;
    ld_def    : term option;
  }
  [@@deriving show { with_path=false}]

  type ind_decl = Ptree.ind_decl = {
    in_loc    : position;
    in_ident  : ident;
    in_params : param list;
    in_def    : (position * ident * term) list;
  }
  [@@deriving show { with_path=false}]

  (** Arguments of `meta` declarations *)
  type metarg = Ptree.metarg =
    | Mty  of pty
    | Mfs  of qualid
    | Mps  of qualid
    | Max  of qualid
    | Mlm  of qualid
    | Mgl  of qualid
    | Mval of qualid
    | Mstr of string
    | Mint of int
  [@@deriving show { with_path=false}]

  (** The possible `clone` substitution elements *)
  type clone_subst = Ptree.clone_subst =
    | CStsym  of qualid * ident list * pty
    | CSfsym  of qualid * qualid
    | CSpsym  of qualid * qualid
    | CSvsym  of qualid * qualid
    | CSxsym  of qualid * qualid
    | CSprop  of Decl.prop_kind[@printer opaque]
          | CSaxiom of qualid
    | CSlemma of qualid
    | CSgoal  of qualid
  [@@deriving show { with_path=false}]

  (** top-level declarations *)
  type decl = Ptree.decl =
    | Dtype of type_decl list
    (** Type declaration *)
    | Dlogic of logic_decl list
    (** `function` and `predicate`, mutually recursively declared *)
    | Dind of (Decl.ind_sign[@printer opaque]) * ind_decl list
    (** inductive or co-inductive predicate *)
    | Dprop of (Decl.prop_kind[@printer opaque]) * ident * term
    (** propositions: `lemma` or `goal` or `axiom` *)
    | Dlet of ident * ghost * rs_kind * expr
    (** global program variable *)
    | Drec of fundef list
    (** program functions, mutually recursively defined *)
    | Dexn of ident * pty * mask
    (** declaration of global exceptions *)
    | Dmeta of ident * metarg list
    (** `meta` *)
    | Dcloneexport of position * qualid * clone_subst list
    (** `clone` *)
    | Duseexport of qualid
    (** `use` *)
    | Dcloneimport of position * bool * qualid * ident option * clone_subst list
    (** `clone import ... as ...` *)
    | Duseimport of position * bool * (qualid * ident option) list
    (** `use import ... as ...` *)
    | Dimport of qualid
    (** `import` *)
    | Dscope of position * bool * ident * decl list
    (** `scope` *)
  [@@deriving show { with_path=false}]

  type mlw_file = Ptree.mlw_file =
    | Modules of (ident * decl list) list
    | Decls of decl list
  [@@deriving show { with_path=false}]
end

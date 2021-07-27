(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

(** Data structures *)

type binders = (Ty.t * int) Symbols.Map.t (*int tag in globally unique *)

type t

type decl_kind =
  | Dtheory
  | Daxiom
  | Dgoal
  | Dpredicate of t
  | Dfunction of t

type view = private {
  f: Symbols.t;
  xs: t list;
  ty: Ty.t;
  bind : bind_kind;
  tag: int;
  vars : (Ty.t * int) Symbols.Map.t; (* vars to types and nb of occurences *)
  vty : Ty.Svty.t;
  depth: int;
  nb_nodes : int;
  pure : bool;
  mutable neg : t option
}

and bind_kind =
  | B_none
  | B_lemma of quantified
  | B_skolem of quantified
  | B_let of letin

and quantified = private {
  name : string;
  main : t;
  toplevel : bool;
  user_trs : trigger list;
  binders : binders;
  (* These fields should be (ordered) lists ! important for skolemization *)
  sko_v : t list;
  sko_vty : Ty.t list;
  loc : Loc.t; (* location of the "GLOBAL" axiom containing this quantified
                  formula. It forms with name a unique id *)
  kind : decl_kind;
}

and letin = private {
  let_v: Symbols.t;
  let_e : t;
  in_e : t;
  let_sko : t; (* fresh symb. with free vars *)
  is_bool : bool;
}

and semantic_trigger =
  | Interval of t * Symbols.bound * Symbols.bound
  | MapsTo of Var.t * t
  | NotTheoryConst of t
  | IsTheoryConst of t
  | LinearDependency of t * t

and trigger = (*private*) {
  content : t list;
  (* this field is filled (with a part of 'content' field) by theories
     when assume_th_elt is called *)
  semantic : semantic_trigger list;
  hyp : t list;
  t_depth : int;
  from_user : bool;
  guard : t option
}

module Set : Set.S with type elt = t

module Map : Map.S with type key = t

type subst = t Symbols.Map.t * Ty.subst

type term_view = private
  | Term of view
  | Not_a_term of {is_lit : bool}

type lit_view = private
  | Eq of t * t
  | Eql of t list
  | Distinct of t list
  | Builtin of bool * Symbols.builtin * t list
  | Pred of t * bool
  | Not_a_lit of { is_form : bool }

type form_view = private
  | Unit of t*t  (* unit clauses *)
  | Clause of t*t*bool      (* a clause (t1 or t2) bool <-> is implication *)
  | Iff of t * t
  | Xor of t * t
  | Literal of t   (* an atom *)
  | Lemma of quantified   (* a lemma *)
  | Skolem of quantified  (* lazy skolemization *)
  | Let of letin (* a binding of an expr *)
  | Not_a_form

(** different views of an expression *)

val term_view : t -> term_view
val lit_view  : t -> lit_view
val form_view : t -> form_view


(** pretty printing *)

val print : Format.formatter -> t -> unit
val print_list : Format.formatter -> t list -> unit
val print_list_sep : string -> Format.formatter -> t list -> unit
val print_triggers : Format.formatter -> trigger list -> unit

(** Comparison and hashing functions *)

val compare : t -> t -> int
val equal : t -> t -> bool
val hash  : t -> int
val uid   : t -> int
val compare_subst : subst -> subst -> int
val equal_subst : subst -> subst -> bool
val compare_quant : quantified -> quantified -> int
val compare_let : letin -> letin -> int

(** Some auxiliary functions *)

val mk_binders : Set.t -> binders
val free_vars : t -> (Ty.t * int) Symbols.Map.t -> (Ty.t * int) Symbols.Map.t
val free_type_vars : t -> Ty.Svty.t
val is_ground : t -> bool
val id : t -> int
val size : t -> int
val depth : t -> int
val is_positive : t -> bool
val neg : t -> t
val is_fresh : t -> bool
val is_fresh_skolem : t -> bool
val is_int : t -> bool
val is_real : t -> bool
val type_info : t -> Ty.t


(** Labeling and models *)

val add_label : Hstring.t -> t -> unit
val label : t -> Hstring.t
val is_in_model : t -> bool
val name_of_lemma : t -> string
val name_of_lemma_opt : t option -> string
val print_tagged_classes : Format.formatter -> Set.t list -> unit


(** smart constructors for terms *)

val mk_term : Symbols.t -> t list -> Ty.t -> t
val vrai : t
val faux : t
val void : t
val int : string -> t
val real : string -> t
val bitv : string -> Ty.t -> t
val fresh_name : Ty.t -> t
val pred : t -> t

(** smart constructors for literals *)

val mk_eq : iff:bool -> t -> t -> t
val mk_distinct : iff:bool -> t list -> t
val mk_builtin : is_pos:bool -> Symbols.builtin -> t list -> t

(** simple smart constructors for formulas *)

val mk_or  : t -> t -> bool -> int -> t
val mk_and : t -> t -> bool -> int -> t
val mk_imp : t -> t -> int -> t
val mk_iff : t -> t -> int -> t
val mk_if : t -> t -> t -> int -> t
val mk_xor : t -> t -> int -> t
val mk_ite : t -> t -> t -> int -> t

(** Substitutions *)

val apply_subst : subst -> t -> t
val apply_subst_trigger : subst -> trigger -> trigger

(** Subterms, and related stuff *)

(** [sub_term acc e] returns the acc augmented with the term and all
    its sub-terms. Returns the acc if e is not a term. Does not go
    through literals (except positive uninterpreted predicates
    application) and formulas *)
val sub_terms : Set.t -> t -> Set.t

(** [max_pure_subterms e] returns the maximal pure terms of the given
    expression *)
val max_pure_subterms : t -> Set.t

(** returns the maximal terms of the given literal. Assertion
    failure if not a literal (should replace the assertion failure
    with a better error) **)
val max_terms_of_lit : t -> Set.t

(** returns the maximal ground terms of the given literal. Assertion
    failure if not a literal **)
val max_ground_terms_of_lit : t -> Set.t

(** traverses a formula recursively and collects its atoms. Only
    ground atoms are kept if ~only_ground is true *)
val atoms_rec_of_form :
  only_ground:bool -> t -> Set.t -> Set.t

(** traverses a formula recursively and collects its maximal ground
    terms *)
val max_ground_terms_rec_of_form : t -> Set.t


(** skolemization and other smart constructors for formulas **)

val make_triggers:
  t -> binders -> decl_kind -> Util.matching_env -> trigger list

val resolution_triggers: is_back:bool -> quantified -> trigger list

val mk_forall :
  string -> (* name *)
  Loc.t -> (* location in the original file *)
  binders -> (* quantified variables *)
  trigger list -> (* triggers *)
  t -> (* quantified formula *)
  int -> (* id, for the GUI *)
  toplevel:bool -> (* for future triggers computation in presence of vty *)
  decl_kind:decl_kind ->
  t

val mk_exists :
  string -> (* name *)
  Loc.t -> (* location in the original file *)
  binders -> (* quantified variables *)
  trigger list -> (* triggers *)
  t -> (* quantified formula *)
  int -> (* id, for the GUI *)
  toplevel:bool -> (* for future triggers computation in presence of
                      vty, and to construct a toplevel forall that
                      cover vtys *)
  decl_kind:decl_kind ->
  t

val mk_let : Symbols.t -> t -> t -> int -> t

val mk_match : t -> (Typed.pattern * t) list -> t

val skolemize : quantified -> t

val elim_let : recursive:bool -> letin -> t

val elim_iff : t -> t -> int -> with_conj:bool -> t

(*val purify_literal : t -> t*)
val purify_form : t -> t

type gformula = {
  ff: t;
  nb_reductions : int;
  trigger_depth : int;
  age: int;
  lem: t option;
  origin_name : string;
  from_terms : t list;
  mf: bool;
  gf: bool;
  gdist : int; (* dist to goal *)
  hdist : int; (* dist to hypotheses *)
  theory_elim : bool;
}

type th_elt =
  {
    th_name : string;
    ax_name : string;
    ax_form : t;
    extends : Util.theories_extensions;
    axiom_kind : Util.axiom_kind;
  }

val print_th_elt : Format.formatter -> th_elt -> unit

val is_pure : t -> bool

val const_term : t -> bool
(** return true iff the given argument is a term without arguments *)

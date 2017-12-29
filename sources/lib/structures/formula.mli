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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

type t

type binders = (Ty.t * int) Symbols.Map.t (*int tag in globally unique *)

type semantic_trigger =
| Interval of Term.t * Symbols.bound * Symbols.bound
| MapsTo of Hstring.t * Term.t
| NotTheoryConst of Term.t
| IsTheoryConst of Term.t
| LinearDependency of Term.t * Term.t

type trigger = {
  content : Term.t list;

  (* this field is filled (with a part of 'content' field) by theories
     when assume_th_elt is called *)
  semantic : semantic_trigger list;
  hyp : t list;
  depth : int;
  from_user : bool;
  guard : Literal.LT.t option
}

type quantified = {
  name : string;
  main : t;

  triggers : trigger list;
  backward_triggers : trigger list Lazy.t;
  forward_triggers : trigger list Lazy.t;

  binders : binders;   (* quantified variable *)

  (* These fields should be (ordered) lists ! important for skolemization *)
  free_v : Term.t list; (* free variables in main *)
  free_vty : Ty.t list; (* free type variables in main *)
  loc : Loc.t; (* location of the "GLOBAL" axiom containing this quantified
                  formula. It forms with name a unique id *)
}

and llet = {
  let_var: Symbols.t;
  let_subst : Term.subst;
  let_term : Term.t;
  let_f : t;
}

and view =
    Unit of t*t  (* unit clauses *)
  | Clause of t*t*bool      (* a clause (t1 or t2) bool <-> is implication *)
  | Literal of Literal.LT.t   (* an atom *)
  | Lemma of quantified   (* a lemma *)
  | Skolem of quantified  (* lazy skolemization *)
  | Let of llet (* a binding of a term *)


type gformula = {
  f: t;
  nb_reductions : int;
  trigger_depth : int;
  age: int;
  lem: t option;
  origin_name : string;
  from_terms : Term.t list;
  mf: bool;
  gf: bool;
  gdist : int; (* dist to goal *)
  hdist : int; (* dist to hypotheses *)
  theory_elim : bool;
}

val mk_binders : Term.Set.t -> binders

val mk_not : t -> t
val mk_and : t -> t -> bool -> int -> t (* bool <-> is implication (neg) *)
val mk_or : t -> t -> bool -> int -> t (* bool <-> is implication *)
val mk_imp : t -> t -> int -> t
val mk_if : Term.t -> t -> t -> int -> t
val mk_iff : t -> t -> int -> t
val mk_lit : Literal.LT.t -> int -> t
val mk_forall :
  string -> (* name *)
  Loc.t -> (* location in the original file *)
  binders -> (* quantified variables *)
  trigger list -> (* triggers *)
  t -> (* quantified formula *)
  int -> (* id, for the GUI *)
  (Term.t list * Ty.t list) option ->
  (* free_vars and free_vty: they are computed if None is given *)
  t

val mk_exists :
  string -> (* name *)
  Loc.t -> (* location in the original file *)
  binders -> (* quantified variables *)
  trigger list -> (* triggers *)
  t -> (* quantified formula *)
  int -> (* id, for the GUI *)
  (Term.t list * Ty.t list) option ->
  (* free_vars and free_vty: they are computed if None is given *)
  t

val mk_let : Term.Set.t -> Symbols.t -> Term.t -> t -> int -> t

val add_label : Hstring.t -> t -> unit
val label : t -> Hstring.t
val is_in_model : t -> bool

val view : t -> view
val size : t -> int
val id : t -> int

val print : Format.formatter -> t -> unit

val ground_terms_rec : t -> Term.Set.t
val atoms_rec :
  only_ground:bool -> t -> Literal.LT.Set.t -> Literal.LT.Set.t
val free_vars : t -> Ty.t Symbols.Map.t

val apply_subst : Term.subst -> t -> t

val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int
val vrai : t
val faux : t

val skolemize : quantified -> t
val type_variables: t -> Ty.Set.t
val max_term_depth : t -> int

module Set : Set.S with type elt = t
module Map : Map.S with type key = t

val name_of_lemma : t -> string
val name_of_lemma_opt : t option -> string

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

type answer = Yes of Explanation.t * Term.Set.t list | No

type 'a ac = {h: Symbols.t ; t: Ty.t ; l: ('a * int) list; distribute: bool}

type 'a literal = LTerm of Literal.LT.t | LSem of 'a Literal.view

type instances = (Formula.t list * Formula.gformula * Explanation.t) list

type theory =
| Th_arith
| Th_sum
| Th_arrays
| Th_UF

type lit_origin =
| Subst
| CS of theory * Numbers.Q.t
| NCS of theory * Numbers.Q.t
| Other

type 'a input =
  'a Literal.view * Literal.LT.t option * Explanation.t * lit_origin

type 'a fact = 'a literal * Explanation.t * lit_origin

type 'a facts = {
  equas     : 'a fact Queue.t;
  diseqs  : 'a fact Queue.t;
  ineqs   : 'a fact Queue.t;
  mutable touched : 'a Util.MI.t;
}

type 'a result = {
  assume : 'a fact list;
  remove: Literal.LT.t list;
}

type 'a solve_pb = { sbt : ('a * 'a) list; eqs : ('a * 'a) list }

module type RELATION = sig
  type t
  type r
  type uf
  val empty : Term.Set.t list -> t

  val assume : t -> uf -> (r input) list -> t * r result
  val query  : t -> uf -> r input -> answer

  val case_split :
    t -> uf -> for_model:bool -> (r Literal.view * bool * lit_origin) list
  (** case_split env returns a list of equalities *)

  val add : t -> uf -> r -> Term.t -> t
  (** add a representant to take into account *)

  val instantiate :
    do_syntactic_matching:bool ->
    Matching_types.info Term.Map.t * Term.t list Term.Map.t Term.Subst.t ->
    t -> uf -> (Formula.t -> Formula.t -> bool) ->
    t * instances

  val print_model : Format.formatter -> t -> (Term.t * r) list -> unit

  val new_terms : t -> Term.Set.t

  val assume_th_elt : t -> Commands.th_elt -> t

  val retrieve_used_context :
    t -> Explanation.t -> Formula.t list * Formula.t list
end

module type SHOSTAK = sig

  (**Type of terms of the theory*)
  type t
  (**Type of representants of terms of the theory*)
  type r
  (** Name of the theory*)
  val name : string
  (** return true if the symbol is owned by the theory*)
  val is_mine_symb : Symbols.t -> bool

  (** Give a representant of a term of the theory*)
  val make : Term.t -> r * Literal.LT.t list

  val term_extract : r -> Term.t option * bool (* original term ? *)

  val color : (r ac) -> r

  val type_info : t -> Ty.t

  val embed : r -> t
  val is_mine : t -> r

  (** Give the leaves of a term of the theory *)
  val leaves : t -> r list
  val subst : r -> r -> t -> r

  val compare : r -> r -> int

  (* tests if two values are equal (using tags) *)
  val equal : t -> t -> bool

  val hash : t -> int
  (** solve r1 r2, solve the equality r1=r2 and return the substitution *)

  val solve : r -> r ->  r solve_pb -> r solve_pb

  val print : Format.formatter -> t -> unit

  val fully_interpreted : Symbols.t -> bool

  val abstract_selectors : t -> (r * r) list -> r * (r * r) list

  (* the returned bool is true when the returned term in a constant of the
     theory. Otherwise, the term contains aliens that should be assigned
     (eg. records). In this case, it's a unit fact, not a decision
  *)
  val assign_value :
    r -> r list -> (Term.t * r) list -> (Term.t * bool) option

  (* choose the value to print and how to print it for the given term.
     The second term is its representative. The list is its equivalence class
  *)
  val choose_adequate_model : Term.t -> r -> (Term.t * r) list -> r * string

end

module type X = sig
  type r

  val make : Term.t -> r * Literal.LT.t list

  val type_info : r -> Ty.t

  val str_cmp : r -> r -> int

  val hash_cmp : r -> r -> int

  val equal : r -> r -> bool

  val hash : r -> int

  val leaves : r -> r list

  val subst : r -> r -> r -> r

  val solve : r -> r ->  (r * r) list

  val term_embed : Term.t -> r

  val term_extract : r -> Term.t option * bool (* original term ? *)

  val ac_embed : r ac -> r

  val ac_extract : r -> (r ac) option

  val color : (r ac) -> r

  val fully_interpreted : Symbols.t -> bool

  val is_a_leaf : r -> bool

  val print : Format.formatter -> r -> unit

  val abstract_selectors : r -> (r * r) list -> r * (r * r) list

  val top : unit -> r
  val bot : unit -> r

  val is_solvable_theory_symbol : Symbols.t -> bool

  (* the returned bool is true when the returned term in a constant of the
     theory. Otherwise, the term contains aliens that should be assigned
     (eg. records). In this case, it's a unit fact, not a decision
  *)
  val assign_value :
    r -> r list -> (Term.t * r) list -> (Term.t * bool) option

  (* choose the value to print and how to print it for the given term.
     The second term is its representative. The list is its equivalence class
  *)
  val choose_adequate_model : Term.t -> r -> (Term.t * r) list -> r * string
end

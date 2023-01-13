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

type 'a ac =
  {h: Symbols.t ; t: Ty.t ; l: ('a * int) list; distribute: bool}

type 'a solve_pb = { sbt : ('a * 'a) list; eqs : ('a * 'a) list }

module type SHOSTAK = sig

  (** {1 Types} *)

  type t
  (** Type of semantic values of the theory. *)

  type r
  (** Type of alien semantic values. *)

  val name : string
  (** Name of the theory. *)

  val is_mine_symb : Symbols.t -> Ty.t -> bool
  (** [is_mine_symb sy ty] returns [true] if the symbol [sy] and the type [ty]
      are owned by the theory. *)

  val make : Expr.t -> r * Expr.t list
  (** [make e] produces a semantic value of a term [e] of the theory. *)

  val term_extract : t -> Expr.t option * bool (* original term ? *)

  val color : (r ac) -> r

  val type_info : t -> Ty.t
  (** [type_info t] gives the type of the semantic value [t]. *)

  val embed : r -> t
  val is_mine : t -> r

  val leaves : t -> r list
  (** [leaves t] gives the list of leaves of the semantic value [t].
      These leaves are alien semantic values. *)

  val subst : r -> r -> t -> r

  val compare : t -> t -> int
  (** [compare t1 t2] compares the two semantic values [t1] and [t2]. *)

  val equal : t -> t -> bool
  (** [equal t1 t2] tests if two terms of the theory are equal using
      their hashes. *)

  val hash : t -> int
  (** [hash t] computes the hash of the semantic value [t]. *)

  val solve : r -> r -> pb:r solve_pb -> r solve_pb
  (** [solve r1 r2 acc] solves the equation [r1 = r2] and returns
      the substitution. The accumulator [acc] is used in the function {!v}. *)

  val print : Format.formatter -> t -> unit

  val fully_interpreted : Symbols.t -> bool

  val abstract_selectors : t -> (r * r) list -> r * (r * r) list

  (* the returned bool is true when the returned term in a constant of the
     theory. Otherwise, the term contains aliens that should be assigned
     (eg. records). In this case, it's a unit fact, not a decision
  *)
  val assign_value :
    r -> r list -> (Expr.t * r) list -> (Expr.t * bool) option

  (* choose the value to print and how to print it for the given term.
     The second term is its representative. The list is its equivalence class
  *)
  val choose_adequate_model : Expr.t -> r -> (Expr.t * r) list -> r * string

end

module type X = sig
  type r
  (** Type of semantic values of the theory. *)

  val save_cache : unit -> unit
  (** saves the module's current cache *)

  val reinit_cache : unit -> unit
  (** restores the module's cache *)

  val make : Expr.t -> r * Expr.t list
  (** [make e] produces a semantic value from the term [e]. *)

  val type_info : r -> Ty.t
  (** [type_info r] gives the type of the semantic value [r]. *)

  val str_cmp : r -> r -> int

  val hash_cmp : r -> r -> int

  val equal : r -> r -> bool

  val hash : r -> int
  (** [hash r] computes the hash of the semantic value [r]. *)

  val leaves : r -> r list

  val subst : r -> r -> r -> r

  val solve : r -> r ->  (r * r) list

  val term_embed : Expr.t -> r

  val term_extract : r -> Expr.t option * bool (* original term ? *)

  val ac_embed : r ac -> r

  val ac_extract : r -> (r ac) option

  val color : (r ac) -> r

  val fully_interpreted : Symbols.t -> Ty.t -> bool

  val is_a_leaf : r -> bool

  val print : Format.formatter -> r -> unit

  val abstract_selectors : r -> (r * r) list -> r * (r * r) list

  val top : unit -> r
  val bot : unit -> r

  val is_solvable_theory_symbol : Symbols.t -> Ty.t -> bool

  (* the returned bool is true when the returned term in a constant of the
     theory. Otherwise, the term contains aliens that should be assigned
     (eg. records). In this case, it's a unit fact, not a decision
  *)
  val assign_value :
    r -> r list -> (Expr.t * r) list -> (Expr.t * bool) option

  (* choose the value to print and how to print it for the given term.
     The second term is its representative. The list is its equivalence class
  *)
  val choose_adequate_model : Expr.t -> r -> (Expr.t * r) list -> r * string
end

(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                            *)
(*  This software is governed by the CeCILL  license under French law and     *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*  The latest releases of Alt-Ergo are distributed under the terms of        *)
(*  OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  The Alt-Ergo theorem prover                                               *)
(*                                                                            *)
(*  Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*  Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                            *)
(*  CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  More details can be found in the directory licenses/                      *)
(*                                                                            *)
(******************************************************************************)

type 'a ac =
  {h: Symbols.t ; t: Ty.t ; l: ('a * int) list; distribute: bool}

type 'a solve_pb = { sbt : ('a * 'a) list; eqs : ('a * 'a) list }

module type SHOSTAK = sig

  (**Type of terms of the theory*)
  type t

  (**Type of representants of terms of the theory*)
  type r

  (** Name of the theory*)
  val name : string

  (** return true if the symbol and the type are owned by the theory*)
  val is_mine_symb : Symbols.t -> Ty.t -> bool

  (** Give a representant of a term of the theory*)
  val make : Expr.t -> r * Expr.t list

  val term_extract : r -> Expr.t option * bool (* original term ? *)

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
    r -> r list -> (Expr.t * r) list -> (Expr.t * bool) option

  (* choose the value to print and how to print it for the given term.
     The second term is its representative. The list is its equivalence class
  *)
  val choose_adequate_model : Expr.t -> r -> (Expr.t * r) list -> r * string

end

module type X = sig
  type r

  val make : Expr.t -> r * Expr.t list

  val type_info : r -> Ty.t

  val str_cmp : r -> r -> int

  val hash_cmp : r -> r -> int

  val equal : r -> r -> bool

  val hash : r -> int

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

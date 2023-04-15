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

open Types

module type S = sig

  module P : Polynome.T
  module MP : Map.S with type key = polynome

  type t = {
    ple0 : polynome;
    is_le : bool;
    dep : (Numbers.Q.t * polynome * bool) Util.MI.t;
    expl : Explanation.t;
    age : Numbers.Z.t;
  }

  module MINEQS : sig
    type mp = (t * Numbers.Q.t) MP.t
    val empty : mp
    val is_empty : mp -> bool
    val younger : t -> t -> bool
    val insert : t -> mp -> mp
    val ineqs_of : mp -> t list
    val add_to_map : mp -> t list -> mp
    val iter : (polynome -> (t * Numbers.Q.t) -> unit) -> mp -> unit
    val fold : (polynome -> (t * Numbers.Q.t) -> 'a -> 'a) -> mp -> 'a -> 'a
  end

  val current_age : unit -> Numbers.Z.t
  val incr_age : unit -> unit

  val create_ineq :
    polynome -> polynome -> bool -> Expr.t option -> Explanation.t -> t

  val print_inequation : Format.formatter -> t -> unit

  val fourierMotzkin :
    ('are_eq -> 'acc -> r option -> t list -> 'acc) -> 'are_eq -> 'acc ->
    MINEQS.mp -> 'acc

  val fmSimplex :
    ('are_eq -> 'acc -> r option -> t list -> 'acc) -> 'are_eq -> 'acc ->
    MINEQS.mp -> 'acc

  val available :
    ('are_eq -> 'acc -> r option -> t list -> 'acc) -> 'are_eq -> 'acc ->
    MINEQS.mp -> 'acc

  val reset_age_cpt : unit -> unit
  (** Resets the age counter to zero *)

end


module FM
    (P : Polynome.T)
  : S with module P = P

module type Container_SIG = sig
  module Make
      (P : Polynome.T)
    : S with module P = P
end



val get_current : unit -> (module Container_SIG)
(** returns the current activated 'inequalities reasoner'. The default value is
    the Fourier-Motzkin module.
    When the selected reasoner is an external plugin, the first call of this
    function will attemp to dynamically load it **)

val set_current : (module Container_SIG) -> unit
(** sets a new 'inequalities reasoner'. This function is intended to be used
    by dynamically loaded plugins **)

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

exception Not_a_num
exception Maybe_zero

module type S = sig
  include Sig.X
  val mult : r -> r -> r
end

module type T = sig

  type r
  type t

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int

  val create : (Numbers.Q.t * r) list -> Numbers.Q.t -> Ty.t-> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mult : t -> t -> t
  val mult_const : Numbers.Q.t -> t -> t
  val add_const : Numbers.Q.t -> t -> t
  val div : t -> t -> t * bool
  val modulo : t -> t -> t

  val is_const : t -> Numbers.Q.t option
  val is_empty : t -> bool
  val find : r -> t -> Numbers.Q.t
  val choose : t -> Numbers.Q.t * r
  val subst : r -> t -> t -> t
  val remove : r -> t -> t
  val to_list : t -> (Numbers.Q.t * r) list * Numbers.Q.t
  val leaves : t -> r list

  val print : Format.formatter -> t -> unit
  val type_info : t -> Ty.t
  val is_monomial : t -> (Numbers.Q.t * r * Numbers.Q.t) option

  (* PPMC des denominateurs des coefficients excepte la constante *)
  val ppmc_denominators : t -> Numbers.Q.t
  (* PGCD des numerateurs des coefficients excepte la constante *)
  val pgcd_numerators : t -> Numbers.Q.t
  (* retourne un polynome sans constante et sa constante
     et la constante multiplicative:
     normal_form p = (p',c,d) <=> p = (p' + c) * d *)
  val normal_form : t -> t * Numbers.Q.t * Numbers.Q.t
  (* comme normal_form mais le signe est aussi normalise *)
  val normal_form_pos : t -> t * Numbers.Q.t * Numbers.Q.t

  val abstract_selectors : t -> (r * r) list -> t * (r * r) list

  val separate_constant : t -> t * Numbers.Q.t
end

module type EXTENDED_Polynome = sig
  include T
  val extract : r -> t option
  val embed : t -> r
end

module Make (X : S) : T with type r = X.r


(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) 2013-2023 --- OCamlPro SAS                                  *)
(*                                                                            *)
(*  This file is distributed under the terms of the OCamlPro Non-Commercial   *)
(*  License version 2.0                                                       *)
(*                                                                            *)
(*  AS AN EXCEPTION, Gold members of the Alt-Ergo's Club can distribute this  *)
(*  file under the terms of the Apache Software License version 2             *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
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
(******************************************************************************)

include Sig.X

val hcons : Types.r -> Types.r


module REFS : sig

  val leaves_ref : ( Types.r -> Types.r list ) ref
  val equal_ref : ( Types.r -> Types.r -> bool ) ref
  val term_extract_ref : ( Types.r -> Types.expr option * bool ) ref
  val save_cache_ref : ( unit -> unit ) ref
  val reinit_cache_ref : ( unit -> unit ) ref
  val make_ref : ( Types.expr -> Types.r * Types.expr list ) ref
  val type_info_ref : ( Types.r -> Ty.t ) ref
  val str_cmp_ref : ( Types.r -> Types.r -> int ) ref
  val hash_cmp_ref : ( Types.r -> Types.r -> int ) ref
  val hash_ref : ( Types.r -> int ) ref
  val subst_ref : ( Types.r -> Types.r -> Types.r -> Types.r ) ref
  val solve_ref : ( Types.r -> Types.r -> (Types.r * Types.r) list ) ref
  val term_embed_ref : ( Types.expr -> Types.r ) ref
  val ac_embed_ref : ( Types.r Types.ac -> Types.r ) ref
  val ac_extract_ref : ( Types.r -> Types.r Types.ac option ) ref
  val color_ref : ( Types.r Types.ac -> Types.r ) ref
  val fully_interpreted_ref : ( Types.symbol -> Ty.t -> bool ) ref
  val is_a_leaf_ref : ( Types.r -> bool ) ref
  val print_ref : ( Format.formatter -> Types.r -> unit ) ref
  val abstract_selectors_ref :
    ( Types.r ->
      (Types.r * Types.r) list -> Types.r * (Types.r * Types.r) list) ref
  val top_ref : ( unit -> Types.r ) ref
  val bot_ref : ( unit -> Types.r ) ref
  val is_solvable_theory_symbol_ref : ( Types.symbol -> Ty.t -> bool ) ref
  val assign_value_ref :
    ( Types.r ->
      Types.r list ->
      (Types.expr * Types.r) list -> (Types.expr * bool) option
    ) ref
  val choose_adequate_model_ref :
    ( Types.expr ->
      Types.r -> (Types.expr * Types.r) list -> Types.r * string
    ) ref

  val hcons_ref : ( Types.r -> Types.r ) ref

end

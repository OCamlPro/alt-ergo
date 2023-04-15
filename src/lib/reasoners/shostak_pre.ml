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

module REFS = struct

  let leaves_ref = ref (fun _ -> assert false)
  let equal_ref = ref (fun _ -> assert false)
  let term_extract_ref = ref (fun _ -> assert false)
  let save_cache_ref = ref (fun _ -> assert false)
  let reinit_cache_ref = ref (fun _ -> assert false)
  let make_ref = ref (fun _ -> assert false)
  let type_info_ref = ref (fun _ -> assert false)
  let str_cmp_ref = ref (fun _ -> assert false)
  let hash_cmp_ref = ref (fun _ -> assert false)
  let hash_ref = ref (fun _ -> assert false)
  let subst_ref = ref (fun _ -> assert false)
  let solve_ref = ref (fun _ -> assert false)
  let term_embed_ref = ref (fun _ -> assert false)
  let ac_embed_ref = ref (fun _ -> assert false)
  let ac_extract_ref = ref (fun _ -> assert false)
  let color_ref = ref (fun _ -> assert false)
  let fully_interpreted_ref = ref (fun _ -> assert false)
  let is_a_leaf_ref = ref (fun _ -> assert false)
  let print_ref = ref (fun _ -> assert false)
  let abstract_selectors_ref = ref (fun _ -> assert false)
  let top_ref = ref (fun _ -> assert false)
  let bot_ref = ref (fun _ -> assert false)
  let is_solvable_theory_symbol_ref = ref (fun _ -> assert false)
  let assign_value_ref = ref (fun _ -> assert false)
  let choose_adequate_model_ref = ref (fun _ -> assert false)

  let hcons_ref = ref (fun _ -> assert false)

end

open REFS

module FUNS : Sig.X = struct
  let leaves x = !leaves_ref x
  let equal x y = !equal_ref x y
  let term_extract x = !term_extract_ref x
  let save_cache x = !save_cache_ref x
  let reinit_cache x = !reinit_cache_ref x
  let make x = !make_ref x
  let type_info x = !type_info_ref x
  let str_cmp x y = !str_cmp_ref x y
  let hash_cmp x y = !hash_cmp_ref x y
  let hash x = !hash_ref x
  let subst x y z = !subst_ref x y z
  let solve x y = !solve_ref x y
  let term_embed x = !term_embed_ref x
  let ac_embed x = !ac_embed_ref x
  let ac_extract x = !ac_extract_ref x
  let color x = !color_ref x
  let fully_interpreted x y = !fully_interpreted_ref x y
  let is_a_leaf x = !is_a_leaf_ref x
  let print x y = !print_ref x y
  let abstract_selectors x y = !abstract_selectors_ref x y
  let top x = !top_ref x
  let bot x = !bot_ref x
  let is_solvable_theory_symbol x = !is_solvable_theory_symbol_ref x
  let assign_value x y z = !assign_value_ref x y z
  let choose_adequate_model x y z = !choose_adequate_model_ref x y z
end

include FUNS

let hcons v = !hcons_ref v

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

open Options
open Format

type 'a abstract = unit

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak (X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name           = "Farrays"
  let is_mine_symb _ _ = false
  let fully_interpreted _ = assert false
  let type_info _    = assert false
  let color _        = assert false
  let print _ _      = assert false
  let embed _        = assert false
  let is_mine _      = assert false
  let compare _ _    = assert false
  let equal _ _      = assert false
  let hash _         = assert false
  let leaves _       = assert false
  let subst _ _ _    = assert false
  let make _         = assert false
  let term_extract _ = None, false
  let abstract_selectors _ _ = assert false
  let solve _ _ = assert false
  let assign_value r _ eq =
    if List.exists (fun (t,_) -> (Expr.depth t) = 1) eq then None
    else
      match X.term_extract r with
      | Some _, true ->
        Some (Expr.fresh_name (X.type_info r), false)
      | _ -> assert false

  let choose_adequate_model _ _ l =
    let acc =
      List.fold_left
        (fun acc (s, r) ->
           if (Expr.depth s) <> 1 then acc
           else
             match acc with
             | Some(s', _) when Expr.compare s' s > 0 -> acc
             | _ -> Some (s, r)
        ) None l
    in
    match acc with
    | Some (_, r) ->
      ignore (flush_str_formatter ());
      fprintf str_formatter "%a" X.print r; (* it's a EUF constant *)
      r, flush_str_formatter ()

    | _ -> assert false

end

(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

type 'a abstract = unit

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak (X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name           = "Ite"
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
  let assign_value _ _ _ = assert false
  let choose_adequate_model _ _ _ = assert false
end


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

type 'a abstract =
  | Constr of
      { c_name : Hstring.t ; c_ty : Ty.t ; c_args : (Hstring.t * 'a) list }
  | Select of { d_name : Hstring.t ; d_ty : Ty.t ; d_arg : 'a }
  | Tester of { t_name : Hstring.t ; t_arg : 'a }
  (* tester is currently not used to build values *)

  | Alien of 'a

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak
    (X : ALIEN) : Sig.SHOSTAK with type r = X.r and type t = X.r abstract

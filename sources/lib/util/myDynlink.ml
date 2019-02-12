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

(** A wrapper of the Dynlink module: we use Dynlink except when we want to
    generate a static (native) binary **)

[@@@ocaml.warning "-60"]
module DummyDL = struct

  type error = string

  [@@@ocaml.warning "-38"]
  exception Error of error

  [@@@ocaml.warning "-32"]
  let error_message s = s

  [@@@ocaml.warning "-32"]
  let loadfile _ = ()

end

include Dynlink

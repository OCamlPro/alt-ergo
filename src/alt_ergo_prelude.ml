(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(** Open this module in every module to hide polymorphic versions of
    the Stdlib. **)
let (<>) (a: int) (b: int) = a <> b
let (=)  (a: int) (b: int) = a = b
let (<)  (a: int) (b: int) = a < b
let (>)  (a: int) (b: int) = a > b
let (<=) (a: int) (b: int) = a <= b
let (>=) (a: int) (b: int) = a >= b

let compare  (a: int) (b: int) = Stdlib.compare a b

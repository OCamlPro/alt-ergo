(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2021 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

type 'a log =
  lkey:string ->
  ('a, Format.formatter, unit) format ->
  'a

(** Registers a log key. *)
val register_log : string -> unit

(** Activates log messages for the given key.
    Only logs called with activated keys will be displayed. *)
val activate_log : string -> unit

(** Activates all the log messages *)
val activate_all : unit -> unit

(** Prints on the formatter in argument the message if the
    lkey has been activated in the options *)
val log :
  lkey:string ->
  Format.formatter ->
  ('a, Format.formatter, unit) format ->
  'a

(** Log on the standard formatter. *)
val feedback : 'a log

(** Log on the debug formatter *)
val debug : 'a log

(** Log on the error formatter. *)
val error : 'a log

(** Log on the warning formatter. *)
val warn : 'a log

(** Log on the model formatter. *)
val model : 'a log

(** Log on the unsat_cr formatter. *)
val unsat_cr : 'a log

(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

(** {1 Printer module} *)

(** {2 Printer} *)

(** Print message on the standard formatter accessible with
    {!val:Options.get_fmt_std} and set by default to stdout *)
val print_std : ('a, Format.formatter, unit) format -> 'a

(** Print error message on the error formatter accessible with
    {!val:Options.get_fmt_err} and set by default to stderr.
    Prints only if error (true by default) is true.
    If header is set, prints a header "[Error]". *)
val print_err :
  ?header:bool -> ?error:bool -> ('a, Format.formatter, unit) format -> 'a

(** Print warning message on the warning formatter accessible with
    {!val:Options.get_fmt_wrn} and set by default to stderr.
    Prints only if warning (true by default) is true.
    If header is set, prints a header "[Warning]". *)
val print_wrn :
  ?header:bool -> ?warning:bool -> ('a, Format.formatter, unit) format -> 'a

(** Print debug message on the debug formatter accessible with
    {!val:Options.get_fmt_dbg} and set by default to stderr.
    Prints only if debug (true by default) is true.
    If header is set, prints a header "[Debug][<module_name>][<function_name>]"
    if module_name and function_name are set. *)
val print_dbg :
  ?header:bool -> ?debug:bool ->
  ?module_name:string ->
  ?function_name:string ->
  ('a, Format.formatter, unit) format -> 'a

(** If debug (true by default) is true, then flush the debug formatter *)
val flush_dbg : ?debug:bool -> unit -> unit

(** Print verbose message on the verbose formatter accessible with
    {!val:Options.get_fmt_vrb} and set by default to stderr.
    Prints only if verbose (true by default) is true. *)
val print_vrb :
  ?verbose:bool -> ('a, Format.formatter, unit) format -> 'a

(** Print message on the given formatter. *)
val print_fmt :
  Format.formatter -> ('a, Format.formatter, unit) format -> 'a


(** {2 Utils} *)

(** Initialisation function used to add colors to the formatters *)
val init_colors : unit -> unit

(** Initialisation function used to configure formatters corresponding
    of the output format set.
    Add ";" at the beginning of the lines if output is set to smtlib2 *)
val init_output_format : unit -> unit

(** Print list without separator *)
val pp_list_no_space :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a list -> unit


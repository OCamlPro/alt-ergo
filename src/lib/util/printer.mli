(*********************************************************************************)
(*                                                                               *)
(*     Alt-Ergo: The SMT Solver For Software Verification                        *)
(*     Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                               *)
(*     This software is governed by the CeCILL  license under French law and     *)
(*     abiding by the rules of distribution of free software.  You can  use,     *)
(*     modify and/ or redistribute the software under the terms of the CeCILL    *)
(*     license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*     "http://www.cecill.info".                                                 *)
(*                                                                               *)
(*     As a counterpart to the access to the source code and  rights to copy,    *)
(*     modify and redistribute granted by the license, users are provided only   *)
(*     with a limited warranty  and the software's author,  the holder of the    *)
(*     economic rights,  and the successive licensors  have only  limited        *)
(*     liability.                                                                *)
(*                                                                               *)
(*     In this respect, the user's attention is drawn to the risks associated    *)
(*     with loading,  using,  modifying and/or developing or reproducing the     *)
(*     software by the user in light of its specific status of free software,    *)
(*     that may mean  that it is complicated to manipulate,  and  that  also     *)
(*     therefore means  that it is reserved for developers  and  experienced     *)
(*     professionals having in-depth computer knowledge. Users are therefore     *)
(*     encouraged to load and test the software's suitability as regards their   *)
(*     requirements in conditions enabling the security of their systems and/or  *)
(*     data to be ensured and,  more generally, to use and operate it in the     *)
(*     same conditions as regards security.                                      *)
(*                                                                               *)
(*     The fact that you are presently reading this means that you have had      *)
(*     knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*     The latest releases of Alt-Ergo are distributed under the terms of        *)
(*     OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                               *)
(*     As an exception, Alt-Ergo Club members at the Gold level can              *)
(*     use this file under the terms of the Apache Software License              *)
(*     version 2.0.                                                              *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     The Alt-Ergo theorem prover                                               *)
(*                                                                               *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                               *)
(*     CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     More details can be found in the directory licenses/                      *)
(*                                                                               *)
(*********************************************************************************)

(** {1 Printer module} *)

(** {2 Printer} *)

(** Print message on the standard formatter accessible with
    {!val:Options.get_fmt_std} and set by default to stdout
    The std formatter is flushed after the print if flushed is set *)
val print_std : ?flushed:bool -> ('a, Format.formatter, unit) format -> 'a

(** Print error message on the error formatter accessible with
    {!val:Options.get_fmt_err} and set by default to stderr.
    Prints only if error (true by default) is true.
    If header is set, prints a header "[Error]".
    The err formatter is flushed after the print if flushed is set *)
val print_err :
  ?flushed:bool ->
  ?header:bool ->
  ?error:bool ->
  ('a, Format.formatter, unit) format -> 'a

(** Print warning message on the warning formatter accessible with
    {!val:Options.get_fmt_wrn} and set by default to stderr.
    Prints only if warning (true by default) is true.
    If header is set, prints a header "[Warning]".
    The wrn formatter is flushed after the print if flushed is set *)
val print_wrn :
  ?flushed:bool ->
  ?header:bool ->
  ?warning:bool ->
  ('a, Format.formatter, unit) format -> 'a

(** Print debug message on the debug formatter accessible with
    {!val:Options.get_fmt_dbg} and set by default to stderr.
    If header is set, prints a header "[Debug][<module_name>][<function_name>]"
    if module_name and function_name are set.
    The dbg formatter is flushed after the print if flushed is set *)
val print_dbg :
  ?flushed:bool ->
  ?header:bool ->
  ?module_name:string ->
  ?function_name:string ->
  ('a, Format.formatter, unit) format -> 'a

(** Print message on the given formatter.
    The given formatter is flushed after the print if flushed is set*)
val print_fmt :
  ?flushed:bool ->
  Format.formatter ->
  ('a, Format.formatter, unit) format -> 'a


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

(** {2 Status Printer} *)

(** Print unsat status message from the frontend on the standard output.
    If validity_mode is set, the status print :
    `Valid (<time>s) (<steps> steps) (goal <goal_name>)`
    else, we print `unsat`.
    If a location is given, we report it only in validity_mode before printing
    the status. *)
val print_status_unsat :
  ?validity_mode:bool ->
  Loc.t option ->
  float option ->
  int option ->
  string option -> unit

(** Print sat status message from the frontend on the standard output.
    If validity_mode is set, the status print :
    `Invalid (<time>s) (<steps> steps) (goal <goal_name>)`
    else, we print `sat`.
    If a location is given, we report it only in validity_mode before printing
    the status. *)
val print_status_sat :
  ?validity_mode:bool ->
  Loc.t option ->
  float option ->
  int option ->
  string option -> unit

(** Print unknown status message from the frontend on the standard output.
    If validity_mode is set, the status print :
    `I don't Know (<time>s) (<steps> steps) (goal <goal_name>)`
    else, we print `unknown`.
    If a location is given, we report it only in validity_mode before printing
    the status. *)
val print_status_unknown :
  ?validity_mode:bool ->
  Loc.t option ->
  float option ->
  int option ->
  string option -> unit

(** Print timeout status message from the frontend on the standard output.
    If validity_mode is set, the status print :
    `Timeout (<time>s) (<steps> steps) (goal <goal_name>)`
    else, we print `timeout`.
    If a location is given, we report it only in validity_mode before printing
    the status. *)
val print_status_timeout :
  ?validity_mode:bool ->
  Loc.t option ->
  float option ->
  int option ->
  string option -> unit

(** Print inconsistent status message from the frontend on the standard output.
    If validity_mode is set, the status print :
    `Inconsistent assumption (<time>s) (<steps> steps) (goal <goal_name>)`
    else, we print nothing.
    If a location is given, we report it only in validity_mode before printing
    the status. *)
val print_status_inconsistent :
  ?validity_mode:bool ->
  Loc.t option ->
  float option ->
  int option ->
  string option -> unit

(** Print preprocess status message from the frontend on the standard output.
    If validity_mode is set, the status print :
    `Preprocess (<time>s) (<steps> steps)`
    else, we print nothing. *)
val print_status_preprocess :
  ?validity_mode:bool ->
  float option ->
  int option -> unit
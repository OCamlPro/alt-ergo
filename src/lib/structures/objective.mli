(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2022-2024 --- OCamlPro SAS                           *)
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

module Function : sig
  type index

  type t = private {
    e : Expr.t;
    (** Term that represents the objective function. *)

    is_max : bool;
    (** Determine if we want to maximize or minimize this objective function. *)

    index : index;
    (** Unique identifier from the input. This field is used as a priority
        index. *)
  }
  (** Type of an objective function. *)

  val mk : is_max:bool -> Expr.t -> t

  val pp : t Fmt.t
  (** [pp ppf o] prints the objective function [o] on the formatter [ppf]
      using the SMT-LIB format. *)

  val reinit_cnt : unit -> unit
  (** Reinitializes the internal counter used to produce unique indexes. *)
end

module Value : sig
  type limit_kind =
    | Above
    | Below
    (** Type used to discriminate between limits from above or below. *)

  type t =
    | Minfinity
    | Pinfinity
    | Value of Expr.t
    | Limit of limit_kind * Expr.t
    (** This case occurs when we try to optimize a strict bound. For instance,
        we have a constraint of the form [x < 2], there is no maximum for [x]
        but [2] is an upper bound. So [2] is a limit from below of the possible
        model values. *)

    | Unknown
    (** The value of the objective function has not yet been determined. *)

  val pp : t Fmt.t
end

module Model : sig
  type t

  val empty : t
  (** The empty model without objective functions. *)

  val is_empty : t -> bool
  (** [is_empty mdl] checks if the model doesn't contain any objective
      function. *)

  val fold : (Function.t -> Value.t -> 'b -> 'b) -> t -> 'b -> 'b
  (** Iterator on the objective functions in decreasing order of priority. *)

  val add : Function.t -> Value.t -> t -> t
  (** [add fn v] adds or updates the value of the objective function [fn]. *)

  val pp : t Fmt.t
  (** [pp ppf mdl] prints the model [mdl] using the MaxSMT format. *)

  val functions : t -> Function.t list
  (** [functions mdl] returns the list of objective functions of the model
      [mdl] in decreasing order of priority. *)

  val next_unknown : t -> Function.t option
  (** [next_unknown ~for_model mdl] returns the next optimization in
      decreasing order of priority whose the value is [Unknown]. *)

  val has_no_limit : t -> bool
  (** [has_no_limit mdl] checks if all the objective functions in the model
      [mdl] have a finite value or unknown value. *)
end

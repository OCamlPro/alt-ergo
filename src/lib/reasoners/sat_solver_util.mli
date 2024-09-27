(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type 'a sat_module = (module Sat_solver_sig.S with type t = 'a)

type any_sat_module = (module Sat_solver_sig.S)

type lbool = False | True | Unknown

val pp_lbool : lbool Fmt.t

exception Wrong_model of Explanation.t
exception No_model

val get_value : 'a sat_module -> 'a -> Expr.t list -> Expr.t list option
(** [get_value (module SAT) env l] returns the model values of the expressions
    of [l] in the current generated model of [env].

    @return [None] if the model generation is not enabled or the
            environment is already unsatisfiable before calling this function.
    @raise Wrong_model if the solver found a contradiction in the current
           model.
    @raise No_model if the solver didn't produce a model but the model
           generation is enabled. *)

val get_assignment : 'a sat_module -> 'a -> Expr.t list -> lbool list
(** [get_assignment (module SAT) env l] returns the status of the literals [l]
    in the current boolean model of [env].

    The status is [unknown] if the literal isn't a subformula of the user
    input.

    @raise invalid_argument if one of the expressions of [l] isn't a
           literal. *)

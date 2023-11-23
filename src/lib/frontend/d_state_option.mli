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

(** The Dolmen state option manager. Each module defined below is linked to
    an option that can be set, fetched et reset independently from the
    Options module, which is used as a static reference. *)

module type Accessor = sig
  (** The data saved in the state. *)
  type t

  (** Returns the option stored in the state. If it has not been registered,
      fetches the default option in the module Options. *)
  val get : D_loop.Typer.state -> t
end

module type S = sig
  include Accessor

  (** Sets the option on the dolmen state. *)
  val set : t -> D_loop.Typer.state -> D_loop.Typer.state

  (** Resets the option to its default value in Options. *)
  val reset : D_loop.Typer.state -> D_loop.Typer.state
end

(** Option for enabling/disabling the get-assignment instruction. *)
module ProduceAssignment : S with type t = bool

(** Option for enabling/disabling the optimization engine. *)
module Optimize : S with type t = bool

(** The Sat solver used. When set, updates the SatSolverModule defined below. *)
module SatSolver : S with type t = Util.sat_solver

(** The Sat solver module used for the calculation. This option's value depends
    on SatSolver: when SatSolver is updated, this one also is. *)
module SatSolverModule : Accessor with type t = (module Sat_solver_sig.S)

(** Option for setting the max number of steps. Interfaces with the toplevel
    Steps module.
    The [set] function may raise Invalid_arg from the Steps.set_steps_bound call
    if the new option value is lower than the current number of steps. *)
module Steps : S with type t = int

(** Initializes the state with options that requires some preprocessing. *)
val init : D_loop.Typer.state -> D_loop.Typer.state

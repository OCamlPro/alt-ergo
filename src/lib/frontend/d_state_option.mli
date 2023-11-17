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

module type S = sig
  (** The type of options. It should match the type in the module Options. *)
  type k

  (** The data saved in the state. May differ from the saved option. *)
  type t

  (** Sets the option on the dolmen state, with a transformation from k to t. *)
  val set : k -> D_loop.Typer.state -> D_loop.Typer.state

  (** Returns the option stored in the state. If it has not been registered,
      fetches the default option in the module Options. *)
  val get : D_loop.Typer.state -> t

  (** Resets the option to its default value in Options. *)
  val reset : D_loop.Typer.state -> D_loop.Typer.state
end

module ProduceAssignment : S with type k = bool and type t = bool
module Optimize : S with type k = bool and type t = bool
module SatSolver : S with type k = Util.sat_solver
                      and type t = Util.sat_solver * (module Sat_solver_sig.S)

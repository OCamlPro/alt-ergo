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

module O = Options
module State = D_loop.State
module Typer = D_loop.Typer

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

let create_opt
    (type t)
    ?(on_update=(fun _ _ -> Fun.id))
    (key : string)
    (get : unit -> t) : (module S with type t = t) =
  (module struct
    type nonrec t = t

    let key = State.create_key ~pipe:"" key

    let set opt st =
      st
      |> on_update key opt
      |> State.set key opt

    let reset st = set (get ()) st

    let get st =
      try State.get key st with
      | State.Key_not_found _ -> get ()
  end)

module ProduceAssignment =
  (val (create_opt "produce_assignment" (fun _ -> false)))

module Optimize =
  (val (create_opt "optimize" O.get_optimize))

let get_sat_solver
    ?(sat = O.get_sat_solver ())
    ?(no_th = O.get_no_theory ())
    () =
  let module SatCont =
    (val (Sat_solver.get sat) : Sat_solver_sig.SatContainer) in
  let module TH = (val Sat_solver.get_theory ~no_th) in
  (module SatCont.Make(TH) : Sat_solver_sig.S)

module SatSolverModule =
  (val (create_opt "sat_solver_module" (fun _ -> get_sat_solver ())))

let msatsolver =
  let on_update _ sat st =
    SatSolverModule.set (get_sat_solver ~sat ()) st
  in
  (create_opt ~on_update "sat_solver" O.get_sat_solver)

module SatSolver = (val msatsolver)

(* Some options can be initialized to gain some performance. *)
let options_requiring_initialization = [
  (module SatSolverModule : S);
]

let init st =
  List.fold_left
    (fun st (module S : S) -> S.reset st)
    st
    options_requiring_initialization

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

  (** Clears the option from the state. *)
  val clear : D_loop.Typer.state -> D_loop.Typer.state
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

    let unsafe_get st = State.get key st

    let clear st = State.update_opt key (fun _ -> None) st

    let get st =
      try unsafe_get st with
      | State.Key_not_found _ -> get ()
  end)

(* The current mode of the sat solver. Serves as a flag for some options that
   cannot be updated outside start mode. *)
module Mode = (val (create_opt "start_mode") (fun _ -> Util.Start))

(* Similar to `create_opt`, except we fail if we set the option while we are not
   in start mode. *)
let create_opt_only_start_mode
    (type t)
    ?(on_update=(fun _ _ -> Fun.id))
    (key : string)
    (get : unit -> t) : (module S with type t = t) =
  let on_update k opt st =
    match Mode.get st with
    | Util.Start -> on_update k opt st
    | curr_mode -> Errors.invalid_set_option curr_mode key
  in
  create_opt ~on_update key get

(* Any mode options. *)

module StrictMode =
  (val (create_opt "strict_mode" O.get_strict_mode))

(* Start mode options. *)

module ProduceAssignment =
  (val (create_opt_only_start_mode "produce_assignment" (fun _ -> false)))

let get_sat_solver
    ?(sat = O.get_sat_solver ())
    ?(no_th = O.get_no_theory ())
    () =
  let module SatCont =
    (val (Sat_solver.get sat) : Sat_solver_sig.SatContainer) in
  let module TH = (val Sat_solver.get_theory ~no_th) in
  (module SatCont.Make(TH) : Sat_solver_sig.S)

module SatSolverModule =
  (val (
     create_opt_only_start_mode
       "sat_solver_module"
       (fun _ -> get_sat_solver ())))

let msatsolver =
  let on_update _ sat st =
    SatSolverModule.set (get_sat_solver ~sat ()) st
  in
  (create_opt_only_start_mode ~on_update "sat_solver" O.get_sat_solver)

module SatSolver = (val msatsolver)

let msteps =
  let on_update _ sat st = Steps.set_steps_bound sat; st in
  (create_opt_only_start_mode ~on_update "steps_bound" O.get_steps_bound)

module Steps = (val msteps)

(* Some options can be initialized to gain some performance. *)
let options_requiring_initialization = [
  (module SatSolverModule : S);
]

let init st =
  List.fold_left
    (fun st (module S : S) -> S.set (S.get (S.clear st)) st)
    st
    options_requiring_initialization

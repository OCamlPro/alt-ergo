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

type 'a hook =
  'a D_loop.State.key ->
  old:'a ->
  new_:'a ->
  D_loop.Typer.state ->
  D_loop.Typer.state

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
  val set : t -> Typer.state -> Typer.state

  (** Clears the option from the state. *)
  val clear : Typer.state -> Typer.state
end

module type S_with_hooks = sig
  include S

  val reset_hooks : unit -> unit

  val add_hook : t hook -> unit
end

let create_opt
    (type t)
    ?on_update
    (key : string)
    (default_get : unit -> t) : (module S_with_hooks with type t = t) =
  (module struct
    type nonrec t = t

    let on_update_base =
      match on_update with
      | None -> []
      | Some f -> [f]

    let on_update_list = ref on_update_base

    let key = State.create_key ~pipe:"" key

    let apply_hooks ~old ~new_ st =
      List.fold_left
        (fun acc f -> f key ~old ~new_ acc)
        st
        !on_update_list

    let unsafe_get st = State.get key st

    let get st =
      try unsafe_get st with
      | State.Key_not_found _ -> default_get ()

    let set new_ st =
      let old = get st in
      let st = apply_hooks ~old ~new_ st in
      State.set key new_ st

    let clear st =
      let old = get st in
      let new_ = default_get () in
      st
      |> apply_hooks ~old ~new_
      |> State.update_opt key (fun _ -> None)

    let reset_hooks () = on_update_list := on_update_base

    let add_hook h = on_update_list := h :: !on_update_list
  end)

(* The current mode of the sat solver. Serves as a flag for some options that
   cannot be updated outside start mode. *)
module Mode = (val (create_opt "start_mode") (fun _ -> Util.Start))

(* Similar to `create_opt`, except we fail if we set the option while we are not
   in start mode. *)
let create_opt_only_start_mode
    (type t)
    ?(on_update=(fun _ ~old:_ ~new_:_ -> Fun.id))
    (key : string)
    (get : unit -> t) : (module S_with_hooks with type t = t) =
  let on_update k ~old ~new_ st =
    match Mode.get st with
    | Util.Start -> on_update k ~old ~new_ st
    | curr_mode -> Errors.invalid_set_option curr_mode key
  in
  create_opt ~on_update key get

(* Any mode options. *)

module Optimize =
  (val (create_opt "optimize" O.get_optimize))

(* Start mode options. *)

module ProduceAssignment =
  (val (create_opt_only_start_mode "produce_assignment" (fun _ -> false)))

module type Sat_solver_api = sig
  module SAT : Sat_solver_sig.S
  module FE : Frontend.S with type sat_env = SAT.t

  val env : FE.env
end

let get_sat_solver
    ?(sat = O.get_sat_solver ())
    ?(no_th = O.get_no_theory ())
    () : (module Sat_solver_api) =
  let module SatCont =
    (val (Sat_solver.get sat) : Sat_solver_sig.SatContainer) in
  let module TH = (val Sat_solver.get_theory ~no_th) in
  let module SAT : Sat_solver_sig.S = SatCont.Make(TH) in
  let module FE : Frontend.S with type sat_env = SAT.t = Frontend.Make (SAT) in
  (module struct
    module SAT = SAT
    module FE = FE

    let env = FE.init_env (Frontend.init_all_used_context ())
  end)

module SatSolverModule =
  (val (
     create_opt_only_start_mode
       "sat_solver_module"
       (fun _ -> get_sat_solver ())))

let msatsolver =
  let on_update _ ~old:_ ~new_ st =
    SatSolverModule.set (get_sat_solver ~sat:new_ ()) st
  in
  (create_opt_only_start_mode ~on_update "sat_solver" O.get_sat_solver)

module SatSolver = (val msatsolver)

let msteps =
  let on_update _ ~old:_ ~new_ st = Steps.set_steps_bound new_; st in
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

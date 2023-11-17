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

module type Input = sig
  type k

  type t

  val get : unit -> k

  val key : string

  val on_update : k -> unit

  val map : k -> t
end

module type S = sig
  type k

  type t

  val set : k -> Typer.state -> Typer.state

  val get : Typer.state -> t

  val reset : Typer.state -> Typer.state
end

module Make(O:Input) : S with type k = O.k and type t = O.t = struct
  type k = O.k
  type t = O.t

  let key = State.create_key ~pipe:"" O.key

  let set opt st =
    let st = State.set key (O.map opt) st in
    O.on_update opt;
    st

  let get st =
    try State.get key st with
    | State.Key_not_found _ -> O.map (O.get ())

  let reset = set (O.get ())
end

let create_opt
    (type k)
    (type t)
    ?(on_update=ignore)
    key
    (get : unit -> k)
    (map : (k -> t)) =
  (module (
     Make (
     struct
       type nonrec k = k
       type nonrec t = t
       let key = key
       let get = get
       let on_update = on_update
       let map = map
     end)
   ) : S with type k = k and type t = t)

module ProduceAssignment =
  (val (create_opt "produce_assignment" (fun _ -> false)) Fun.id)

module Optimize =
  (val (create_opt "optimize" O.get_optimize) Fun.id)

let msatsolver =
  let map s =
    let module SatCont =
      (val (Sat_solver.get s) : Sat_solver_sig.SatContainer) in
    let module TH =
      (val
        (if Options.get_no_theory() then (module Theory.Main_Empty : Theory.S)
         else (module Theory.Main_Default : Theory.S)) : Theory.S ) in
    s,
    (module SatCont.Make(TH) : Sat_solver_sig.S)
  in
  (create_opt "sat_solver" O.get_sat_solver map)

module SatSolver = (val msatsolver)

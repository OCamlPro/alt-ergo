(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2024 --- OCamlPro SAS                           *)
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
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module TimerTable : sig
  (** The table of timers (module -> function -> float). *)
  type t

  (** Clears the table. *)
  val clear : t -> unit

  (** Creates a new type of tables. *)
  val create : unit -> t

  (** Returns the time stored in the table. If it has never been
      stored, returns 0.. *)
  val get : t -> Self.mod_ -> Self.fn -> float

  (** Sets the time spend to a given function in a given module.. *)
  val set : t -> Self.mod_ -> Self.fn -> float -> unit

  (** Gets the total time spent in a given module. *)
  val get_sum : t -> Self.mod_ -> float
end = struct
  type t = float array array

  let create () =
    Array.init
      (Self.max_mod_ + 1)
      (fun _ -> Array.init (Self.max_fn + 1) (fun _ -> 0.))

  let clear =
    Array.iter (fun a -> Array.iteri (fun j _ -> a.(j) <- 0.) a)

  let get t m f =
    t.(Self.mod__to_enum m).(Self.fn_to_enum f)

  let set t m f v =
    t.(Self.mod__to_enum m).(Self.fn_to_enum f) <- v

  let get_sum t m =
    Array.fold_left (+.) 0. t.(Self.mod__to_enum m)
end

type t = {
  (* current time *)
  mutable cur_u : float;

  (* current activated (module x function) for time profiling *)
  mutable cur_t : (Self.mod_ * Self.fn * int);

  (* stack of suspended (module x function)s callers *)
  mutable stack : (Self.mod_ * Self.fn * int) list;

  (* table of timers for each combination "" *)
  z : TimerTable.t ;
}

let cpt_id = ref 0
let fresh_id () = incr cpt_id; !cpt_id

(** return a new empty env **)
let empty () =
  { cur_t = (M_None, F_none, 0);
    cur_u = 0.0;
    stack = [];
    z = TimerTable.create ()
  }

(** reset the references of the given env to empty **)
let reset env =
  TimerTable.clear env.z;
  env.cur_t <- (M_None, F_none, 0);
  env.cur_u <- 0.0;
  env.stack <- [];
  cpt_id := 0

let accumulate env cur m f =
  TimerTable.set env.z m f (cur -. env.cur_u)

let accumulate_cumulative_mode name env m f cur =
  if Options.get_cumulative_time_profiling() then
    begin
      if Options.get_debug () then
        Printer.print_dbg ~flushed:false
          "@[<v 2>%s time of %s , %s@ "
          name (Self.show_mod_ m) (Self.show_fn f);
      List.iter
        (fun (m, f, _) ->
           if Options.get_debug () then
             Printer.print_dbg ~flushed:false ~header:false
               "also update time of %s , %s@ "
               (Self.show_mod_ m) (Self.show_fn f);
           accumulate env cur m f
        )env.stack;
      if Options.get_debug () then
        Printer.print_dbg ~header:false "@]"
    end

(** save the current timer and start the timer m x f **)
let start env m f =
  let cur = MyUnix.cur_time() in
  accumulate_cumulative_mode "start" env m f cur;
  begin
    match env.cur_t with
    | (M_None, _, _) -> ()
    | kd ->
      accumulate env cur m f;
      env.stack <- kd :: env.stack
  end;
  env.cur_t <- (m, f, fresh_id());
  env.cur_u <- cur

(** pause the timer "m x f" and restore the former timer **)
let pause env m f =
  let cur = MyUnix.cur_time() in
  accumulate_cumulative_mode "pause" env m f cur;
  accumulate env cur m f;
  env.cur_u <- cur;
  match env.stack with
  | [] ->
    env.cur_t <- (M_None, F_none, 0)
  | kd::st ->
    env.cur_t <- kd;
    env.stack <- st

(** update the value of the current timer **)
let update env =
  let cur = MyUnix.cur_time() in
  let m, f, _ = env.cur_t in
  accumulate_cumulative_mode "update" env m f cur;
  accumulate env cur m f;
  env.cur_u <- cur

(** Returns the value of the timer associated to the module and function. *)
let get_value env m f = TimerTable.get env.z m f

(** get the sum of the "Self.fn" timers for the given "Self.mod_" **)
let get_sum env m = TimerTable.get_sum env.z m

let current_timer env = env.cur_t

let get_stack env = env.stack

let (timer_start : (Self.mod_ -> Self.fn -> unit) ref) =
  ref (fun _ _ -> ())

let (timer_pause : (Self.mod_ -> Self.fn -> unit) ref) =
  ref (fun _ _ -> ())

let set_timer_start f = assert (Options.get_timers ()); timer_start := f
let set_timer_pause f = assert (Options.get_timers ()); timer_pause := f

let with_timer mod_ fun_ f =
  if not @@ Options.get_timers () then f ()
  else begin
    !timer_start mod_ fun_;
    Fun.protect ~finally:(fun _ -> !timer_pause mod_ fun_) f
  end

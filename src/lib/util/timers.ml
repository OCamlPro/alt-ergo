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

type ty_module =
  | M_None
  | M_Typing
  | M_Sat
  | M_Match
  | M_CC
  | M_UF
  | M_Arith
  | M_Arrays
  | M_Sum
  | M_Records
  | M_AC
  | M_Expr
  | M_Triggers
  | M_Simplex
  | M_Ite

let all_modules = [
  M_None;
  M_Typing;
  M_Sat;
  M_Match;
  M_CC;
  M_UF;
  M_Arith;
  M_Arrays;
  M_Sum;
  M_Records;
  M_AC;
  M_Expr;
  M_Triggers;
  M_Simplex;
  M_Ite
]


type ty_function =
  | F_add
  | F_add_lemma
  | F_add_predicate
  | F_add_terms
  | F_are_equal
  | F_assume
  | F_class_of
  | F_leaves
  | F_make
  | F_m_lemmas
  | F_m_predicates
  | F_query
  | F_solve
  | F_subst
  | F_union
  | F_unsat
  | F_none
  | F_new_facts
  | F_apply_subst
  | F_instantiate

let all_functions = [
  F_add;
  F_add_lemma;
  F_add_predicate;
  F_add_terms;
  F_are_equal;
  F_assume;
  F_class_of;
  F_leaves;
  F_make;
  F_m_lemmas;
  F_m_predicates;
  F_query;
  F_solve;
  F_subst;
  F_union;
  F_unsat;
  F_none;
  F_new_facts;
  F_apply_subst;
  F_instantiate;
]


let string_of_ty_module k = match k with
  | M_None     -> "None"
  | M_Typing   -> "Typing"
  | M_Sat      -> "Sat"
  | M_Match    -> "Match"
  | M_CC       -> "CC"
  | M_UF       -> "UF"
  | M_Arith    -> "Arith"
  | M_Arrays   -> "Arrays"
  | M_Sum      -> "Sum"
  | M_Records  -> "Records"
  | M_AC       -> "AC"
  | M_Expr     -> "Expr"
  | M_Triggers -> "Triggers"
  | M_Simplex  -> "Simplex"
  | M_Ite      -> "Ite"

let string_of_ty_function f = match f with
  | F_add           -> "add"
  | F_add_lemma     -> "add_lemma"
  | F_assume        -> "assume"
  | F_class_of      -> "class_of"
  | F_leaves        -> "leaves"
  | F_make          -> "make"
  | F_m_lemmas      -> "m_lemmas"
  | F_m_predicates  -> "m_predicates"
  | F_query         -> "query"
  | F_solve         -> "solve"
  | F_subst         -> "subst"
  | F_union         -> "union"
  | F_unsat         -> "unsat"
  | F_add_predicate -> "add_predicate"
  | F_add_terms     -> "add_terms"
  | F_are_equal     -> "are_equal"
  | F_none          -> "none"
  | F_new_facts     -> "new_facts"
  | F_apply_subst   -> "apply_subst"
  | F_instantiate   -> "instantiate"

module TimerTable = struct
  module FTbl = Hashtbl.Make(
    struct
      type t = ty_function

      let hash = function
        | F_add           -> 0
        | F_add_lemma     -> 1
        | F_assume        -> 2
        | F_class_of      -> 3
        | F_leaves        -> 4
        | F_make          -> 5
        | F_m_lemmas      -> 6
        | F_m_predicates  -> 7
        | F_query         -> 8
        | F_solve         -> 9
        | F_subst         -> 10
        | F_union         -> 11
        | F_unsat         -> 12
        | F_add_predicate -> 13
        | F_add_terms     -> 14
        | F_are_equal     -> 15
        | F_none          -> 16
        | F_new_facts     -> 17
        | F_apply_subst   -> 18
        | F_instantiate   -> 19

      let equal t t' = hash t = hash t'
    end)

  module MTbl = Hashtbl.Make(
    struct
      type t = ty_module

      let hash =
        function
        | M_None     -> 0
        | M_Typing   -> 1
        | M_Sat      -> 2
        | M_Match    -> 3
        | M_CC       -> 4
        | M_UF       -> 5
        | M_Arith    -> 6
        | M_Arrays   -> 7
        | M_Sum      -> 8
        | M_Records  -> 9
        | M_AC       -> 10
        | M_Expr     -> 11
        | M_Triggers -> 12
        | M_Simplex  -> 13
        | M_Ite      -> 14

      let equal t t' = hash t = hash t'
    end)

  type t = float FTbl.t MTbl.t

  let create = MTbl.create

  let clear = MTbl.clear

  (** Returns the timer value associated to the module [m]
      and the function [f]. *)
  let get t m f =
    match MTbl.find_opt t m with
    | None -> 0.
    | Some t ->
      match FTbl.find_opt t f with
      | None -> 0.
      | Some f -> f

  (** Sets the timer value associated to the module [m]
      and the function [f]. *)
  let set t m f v =
    let ftbl =
      match MTbl.find_opt t m with
      | None ->
        let new_tbl = FTbl.create 1 in
        MTbl.add t m new_tbl;
        new_tbl
      | Some tbl -> tbl
    in
    FTbl.add ftbl f v

  let get_sum t m =
    match MTbl.find_opt t m with
    | None -> 0.
    | Some ft -> FTbl.fold (fun _ -> (+.)) ft 0.
end

type t = {
  (* current time *)
  mutable cur_u : float;

  (* current activated (module x function) for time profiling *)
  mutable cur_t : (ty_module * ty_function * int);

  (* stack of suspended (module x function)s callers *)
  mutable stack : (ty_module * ty_function * int) list;

  (* table of timers for each combination "" *)
  z : TimerTable.t ;
  (*h:(ty_module, float ref) Hashtbl.t;*)
}

let cpt_id = ref 0
let fresh_id () = incr cpt_id; !cpt_id

(** return a new empty env **)
let empty () =
  { cur_t = (M_None, F_none, 0);
    cur_u = 0.0;
    stack = [];
    z = TimerTable.create 5
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
          name (string_of_ty_module m) (string_of_ty_function f);
      List.iter
        (fun (m, f, _) ->
           if Options.get_debug () then
             Printer.print_dbg ~flushed:false ~header:false
               "also update time of %s , %s@ "
               (string_of_ty_module m) (string_of_ty_function f);
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

(** get the sum of the "ty_function" timers for the given "ty_module" **)
let get_sum env m = TimerTable.get_sum env.z m

let current_timer env = env.cur_t

let get_stack env = env.stack

let (timer_start : (ty_module -> ty_function -> unit) ref) =
  ref (fun _ _ -> ())

let (timer_pause : (ty_module -> ty_function -> unit) ref) =
  ref (fun _ _ -> ())

let set_timer_start f = assert (Options.get_timers ()); timer_start := f
let set_timer_pause f = assert (Options.get_timers ()); timer_pause := f

let exec_timer_start kd msg = !timer_start kd msg
let exec_timer_pause kd = !timer_pause kd

(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

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

let mtag k = match k with
  | M_None   -> 0
  | M_Typing -> 1
  | M_Sat    -> 2
  | M_Match  -> 3
  | M_CC     -> 4
  | M_UF     -> 5
  | M_Arith  -> 6
  | M_Arrays -> 7
  | M_Sum    -> 8
  | M_Records-> 9
  | M_AC     -> 10
  | M_Expr-> 11
  | M_Triggers->12
  | M_Simplex->13

let nb_mtag = 14

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

let ftag f = match f with
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

let nb_ftag = 20

let string_of_ty_module k = match k with
  | M_None   -> "None"
  | M_Typing -> "Typing"
  | M_Sat    -> "Sat"
  | M_Match  -> "Match"
  | M_CC     -> "CC"
  | M_UF     -> "UF"
  | M_Arith  -> "Arith"
  | M_Arrays -> "Arrays"
  | M_Sum    -> "Sum"
  | M_Records-> "Records"
  | M_AC     -> "AC"
  | M_Expr-> "Expr"
  | M_Triggers->"Triggers"
  | M_Simplex->"Simplex"

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

type t = {
  (* current time *)
  mutable cur_u : float;

  (* current activated (module x function) for time profiling *)
  mutable cur_t : (ty_module * ty_function * int);

  (* stack of suspended (module x function)s callers *)
  mutable stack : (ty_module * ty_function * int) list;

  (* table of timers for each combination "" *)
  z : (float array) array;
  (*h:(ty_module, float ref) Hashtbl.t;*)
}

let cpt_id = ref 0
let fresh_id () = incr cpt_id; !cpt_id

(** return a new empty env **)
let empty () =
  { cur_t = (M_None, F_none, 0);
    cur_u = 0.0;
    stack = [];
    z = Array.init nb_mtag (fun _ -> Array.make nb_ftag 0.);
  }


(** reset the references of the given env to empty **)
let reset env =
  for i = 0 to nb_mtag - 1 do
    let a = env.z.(i) in for j = 0 to nb_ftag - 1 do a.(j) <- 0. done
  done;
  env.cur_t <- (M_None, F_none, 0);
  env.cur_u <- 0.0;
  env.stack <- [];
  cpt_id := 0

let accumulate env cur m f =
  let mt = mtag m in
  let ft = ftag f in
  env.z.(mt).(ft) <- env.z.(mt).(ft) +. (cur -. env.cur_u)

let accumulate_cumulative_mode name env m f cur =
  if Options.get_cumulative_time_profiling() then
    begin
      Printer.print_dbg ~flushed:false ~debug:(Options.get_debug ())
        "@[<v 2>%s time of %s , %s@ "
        name (string_of_ty_module m) (string_of_ty_function f);
      List.iter
        (fun (m, f, _) ->
           Printer.print_dbg ~flushed:false ~header:false
             ~debug:(Options.get_debug ())
             "also update time of %s , %s@ "
             (string_of_ty_module m) (string_of_ty_function f);
           accumulate env cur m f
        )env.stack;
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

(** get the value of the timer "m x f" **)
let get_value env m f = env.z.(mtag m).(ftag f)

(** get the sum of the "ty_function" timers for the given "ty_module" **)
let get_sum env m =
  let cpt = ref 0. in
  Array.iter (fun v -> cpt := !cpt +. v) env.z.(mtag m);
  !cpt

let current_timer env = env.cur_t

let get_stack env = env.stack

let get_timers_array env = env.z

let all_functions =
  let l =
    [ F_add;
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
  in
  assert (List.length l = nb_ftag);
  l

let all_modules =
  let l =
    [ M_None;
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
    ]
  in
  assert (List.length l = nb_mtag);
  l


let (timer_start : (ty_module -> ty_function -> unit) ref) =
  ref (fun _ _ -> ())

let (timer_pause : (ty_module -> ty_function -> unit) ref) =
  ref (fun _ _ -> ())

let set_timer_start f = assert (Options.get_timers ()); timer_start := f
let set_timer_pause f = assert (Options.get_timers ()); timer_pause := f

let exec_timer_start kd msg = !timer_start kd msg
let exec_timer_pause kd = !timer_pause kd

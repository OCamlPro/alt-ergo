(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
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

module SE = Expr.Set
module MS = Map.Make(String)

type inst_info = {
  loc : Loc.t;
  kept : int;
  ignored : int;
  all_insts : SE.t;
  confl : int;
  decided : int;
  consumed : SE.t;
  all : SE.t;
  produced : SE.t;
  _new : SE.t;
}

type t = {
  mutable decisions : int;
  mutable assumes : int;
  mutable assumes_current_lvl : int;
  mutable queries : int;
  mutable instantiation_rounds : int;
  mutable instances : int;
  mutable decision_lvl : int;
  mutable instantiation_lvl : int;
  (* 4 kinds of conflicts *)
  mutable th_conflicts : int;
  mutable b_conflicts : int;
  mutable bcp_th_conflicts : int;
  mutable bcp_b_conflicts : int;
  mutable bcp_mix_conflicts : int;
  (* 4 kinds of red/elim *)
  mutable t_red : int;
  mutable b_red : int;
  mutable t_elim : int;
  mutable b_elim : int;
  mutable instances_map : inst_info MS.t;
  mutable instances_map_printed : bool;
  timers : Timers.t
}

type mode =
  | Stats
  | Timers
  | CallTree
  | FunctionsTimers
  | Instances

let mode = ref Stats

let max_nb_prints = 30

let nb_prints = ref max_nb_prints

let initial_info = ref true

let state = lazy {
  decisions = 0;
  assumes = 0;
  assumes_current_lvl = 0;
  queries = 0;
  instantiation_rounds = 0;
  instances = 0;
  decision_lvl = 0;
  instantiation_lvl = 0;

  th_conflicts = 0;
  b_conflicts = 0;
  bcp_th_conflicts = 0;
  bcp_b_conflicts = 0;
  bcp_mix_conflicts = 0;

  t_red = 0;
  b_red = 0;
  t_elim = 0;
  b_elim = 0;

  instances_map = MS.empty;
  instances_map_printed = false;
  timers = Timers.empty ()
}

(** Calls the continuation only when the profiling is on.
    This allows to only force the state when the profiling is on. *)
let if_profiling f =
  if Options.get_profiling () then
    f (Lazy.force state)

let get_timers () = (Lazy.force state).timers

let set_sigprof () =
  let tm =
    let v = Options.get_profiling_period () in
    if (Float.compare v 0.) > 0 then v else -. v
  in
  ignore
    (Unix.setitimer Unix.ITIMER_PROF
       { Unix.it_value = tm; Unix.it_interval = 0. })

(* update functions of the internal state *)

let assume nb =
  if_profiling @@ fun state ->
  state.assumes <- nb + state.assumes;
  state.assumes_current_lvl <- nb + state.assumes_current_lvl

let query () =
  if_profiling @@ fun state ->
  state.queries <- state.queries + 1

let instances l =
  if_profiling @@ fun state ->
  state.instances <- state.instances + List.length l

let instantiation ilvl =
  if_profiling @@ fun state ->
  state.instantiation_rounds <- state.instantiation_rounds + 1;
  state.instantiation_lvl <- state.instantiation_lvl + 1;
  if not (state.instantiation_lvl = ilvl) then begin
    Printer.print_err
      "state.instantiation_lvl = %d et ilvl = %d"
      state.instantiation_lvl ilvl;
    assert false
  end

let bool_conflict () =
  if_profiling @@ fun state ->
  state.b_conflicts <- state.b_conflicts + 1

let theory_conflict () =
  if_profiling @@ fun state ->
  state.th_conflicts <- state.th_conflicts + 1

let bcp_conflict b1 b2 =
  if_profiling @@ fun state ->
  if b1 && b2 then
    state.bcp_b_conflicts <- state.bcp_b_conflicts + 1
  else if (not b1) && (not b2) then
    state.bcp_th_conflicts <- state.bcp_th_conflicts + 1
  else
    state.bcp_mix_conflicts <- state.bcp_mix_conflicts + 1

let red b =
  if_profiling @@ fun state ->
  if b then
    state.b_red <- state.b_red + 1
  else
    state.t_red <- state.t_red + 1

let elim b =
  if_profiling @@ fun state ->
  if b then
    state.b_elim <- state.b_elim + 1
  else
    state.t_elim <- state.t_elim + 1

let reset_ilevel n =
  if_profiling @@ fun state -> state.instantiation_lvl <- n

let reset_dlevel n =
  if_profiling @@ fun state -> state.decision_lvl <- n

let empty_inst_info loc =
  {
    loc = loc;
    kept = 0;
    ignored = 0;
    confl = 0;
    decided = 0;
    all_insts = SE.empty;
    consumed = SE.empty;
    all  = SE.empty;
    produced  = SE.empty;
    _new  = SE.empty;
  }

let new_instance_of axiom inst loc kept =
  if_profiling @@ fun state ->
  let () = state.instances_map_printed <- false in
  let ii =
    try MS.find axiom state.instances_map
    with Not_found -> empty_inst_info loc
  in
  assert (ii.loc == loc);
  let ii =
    if kept then
      {ii with kept = ii.kept + 1; all_insts = SE.add inst ii.all_insts}
    else
      {ii with ignored = ii.ignored + 1}
  in
  state.instances_map <- MS.add axiom ii state.instances_map

let conflicting_instance axiom loc =
  if_profiling @@ fun state ->
  let ii =
    try MS.find axiom state.instances_map
    with Not_found -> empty_inst_info loc
  in
  let ii = {ii with confl = ii.confl + 1} in
  assert (ii.loc == loc);
  state.instances_map <- MS.add axiom ii state.instances_map

let decision_on_instance axiom_name =
  if_profiling @@ fun state ->
  try
    let ii =
      MS.find axiom_name state.instances_map
    in
    let ii = {ii with decided = ii.decided + 1} in
    (*assert (ii.loc == loc);*)
    state.instances_map <- MS.add axiom_name ii state.instances_map
  with Not_found -> ()


let decision d origin =
  if_profiling @@ fun state ->
  state.decisions <- state.decisions + 1;
  state.decision_lvl <- state.decision_lvl + 1;
  if state.decision_lvl <> d then begin
    Printer.print_err
      "state.decision_lvl = %d et d = %d"
      state.decision_lvl d;
    assert false
  end;
  state.assumes_current_lvl <- 0;
  decision_on_instance origin


let register_produced_terms axiom loc consumed all produced _new =
  if_profiling @@ fun state ->
  let ii =
    try MS.find axiom state.instances_map
    with Not_found -> empty_inst_info loc
  in
  assert (ii.loc == loc);
  let ii =
    {ii with
     consumed = SE.union ii.consumed consumed;
     all      = SE.union ii.all all;
     produced = SE.union ii.produced produced;
     _new     = SE.union ii._new _new }
  in
  state.instances_map <- MS.add axiom ii state.instances_map

(******************************************************************************
   printing the internal state
 ******************************************************************************)

let string_resize s i =
  let sz = max 0 (i - (String.length s)) in
  let tmp = String.make sz ' ' in
  s ^ tmp

let int_resize n i = string_resize (Format.sprintf "%d" n) i

let float_resize f i = string_resize (Format.sprintf "%f" f) i

let percent total a =
  (string_of_int (int_of_float (a *. 100. /. total))) ^ "%"

let current_timer () = Timers.current_timer (get_timers ())

(* Profiling columns:
   - Name
   - Description
   - Length of the cell
   - Is the column linked to a statistic (Some true), a timer (Some false) or
     not (None)?
   - Data formatter
     Todo(Steven): use Pierre's solution with Printbox
*)
let columns : (string * string * int * bool option * 'a) list =
  [
    "GTimer", "Global timer", 11, None,
    (fun _ gtime sz -> float_resize gtime sz);

    "Steps", "Number of Steps", 14, None,
    (fun steps gtime sz ->
       let avg = int_of_float ((float_of_int steps) /. gtime) in
       Format.sprintf "%s~%s"
         (string_resize (Format.sprintf "%d" steps) (sz-7))
         (string_resize (Format.sprintf "%d/s" avg) 6)
    );

    "Case splits", "Number of Case Splits", 14, None,
    (fun _ gtime sz ->
       let avg = int_of_float (float_of_int (Steps.cs_steps()) /. gtime) in
       Format.sprintf "%s~%s"
         (string_resize (Format.sprintf "%d" (Steps.cs_steps())) (sz-7))
         (string_resize (Format.sprintf "%d/s" avg) 6)
    );

    "Mod.", "Current active module", 7, None,
    (fun _ _ sz ->
       let kd, _msg, _ = current_timer () in
       string_resize (Timers.string_of_ty_module kd) sz);

    "Module Id", "Each call to a module is tagged with a fresh Id", 10, None,
    (fun _ _ sz ->
       let _kd, _msg, id = current_timer () in
       int_resize id sz);

    (*-----------------------------------------------------------------*)

    "ilvl", "Current Instantiaton level", 6, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.instantiation_lvl sz);

    "#i rnds", "Number of intantiation rounds", 8, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.instantiation_rounds sz);


    "#insts", "Number of generated instances", 8, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.instances sz);

    "i/r", "AVG number of generated instances per instantiation rounds",
    8, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize
         (state.instances / (max 1 state.instantiation_rounds)) sz);

    "dlvl", "Current Decision level", 6, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.decision_lvl sz);

    "#decs", "Number of decisions", 6, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.decisions sz);

    "T-asm", "Number of calls to Theory.assume", 6, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.assumes sz);

    "T/d", "Number of Theory.assume after last decision", 6, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.assumes_current_lvl sz);

    "T-qr", "Number of calls to Theory.query", 15, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.queries sz);

    "B-R", "Number of reduced clauses by Boolean propagation", 6, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.b_red sz);

    "B-E", "Number of eliminated clauses by Boolean propagation", 6,
    Some true, (fun _ _ sz ->
        let state = Lazy.force state in
        int_resize state.b_elim sz);

    "T-R", "Number of reduced clauses by Theory propagation", 6, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.t_red sz);

    "T-E", "Number of eliminated clauses by Theory propagation", 6,
    Some true, (fun _ _ sz ->
        let state = Lazy.force state in
        int_resize state.t_elim sz);

    "B-!",  "Number of direct Boolean conflicts", 5, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.b_conflicts sz);

    "T-!", "Number of direct Theory conflicts" , 5, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.th_conflicts sz);

    "B>!", "Number of Boolean conflicts deduced by BCP", 5, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.bcp_b_conflicts sz);

    "T>!", "Number of Theory conflicts deduced by BCP", 5, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.bcp_th_conflicts sz);

    "M>!", "Number of Mix conflicts deduced by BCP", 5, Some true,
    (fun _ _ sz ->
       let state = Lazy.force state in
       int_resize state.bcp_mix_conflicts sz);

    (*-----------------------------------------------------------------*)
    "SAT", "Time spent in SAT module(s)", 16, Some false,
    (fun _ gtime sz ->
       let curr = Timers.get_sum (get_timers ()) Timers.M_Sat in
       Format.sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "Matching", "Time spent in Matching module(s)", 16, Some false,
    (fun _ gtime sz ->
       let curr = Timers.get_sum (get_timers ()) Timers.M_Match in
       Format.sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "CC", "Time spent in CC module(s)", 16, Some false,
    (fun _ gtime sz ->
       let curr = Timers.get_sum (get_timers ()) Timers.M_CC in
       Format.sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4)
    );

    "Arith", "Time spent in Arith module(s)", 16, Some false,
    (fun _ gtime sz ->
       let curr = Timers.get_sum (get_timers ()) Timers.M_Arith in
       Format.sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "Arrays", "Time spent in Arrays module(s)", 16, Some false,
    (fun _ gtime sz ->
       let curr = Timers.get_sum (get_timers ()) Timers.M_Arrays in
       Format.sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "AC", "Time spent in AC module(s)", 16, Some false,
    (fun _ gtime sz ->
       let curr = Timers.get_sum (get_timers ()) Timers.M_AC in
       Format.sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "Total", "Time spent in 'supervised' module(s)", 11, Some false,
    (fun _ _ sz ->
       let timers = get_timers () in
       let tsat = Timers.get_sum timers Timers.M_Sat in
       let tmatch = Timers.get_sum timers Timers.M_Match in
       let tcc = Timers.get_sum timers Timers.M_CC in
       let tarith = Timers.get_sum timers Timers.M_Arith in
       let tarrays = Timers.get_sum timers Timers.M_Arrays in
       let tac = Timers.get_sum timers Timers.M_AC in
       let total = tsat+.tmatch+.tcc+.tarith+.tarrays+.tac in
       float_resize total sz);
  ]

let print_initial_info fmt =
  if !initial_info then begin
    initial_info := false;
    let max =
      List.fold_left (fun z (id,_, _,_,_) -> max z (String.length id))
        0 columns
    in
    List.iter
      (fun (id, descr, _, _, _) ->
         Format.fprintf fmt "%s : %s@." (string_resize id max) descr
      )columns
  end

let stats_limit, timers_limit =
  let aux tmp sz =
    tmp := Format.sprintf "%s%s|" !tmp (String.make (max 0 sz) '-');
  in
  let tmp_s = ref "|" in
  let tmp_t = ref "|" in
  List.iter
    (fun (_, _, sz, opt, _) ->
       match opt with
       | Some true  -> aux tmp_s sz
       | Some false -> aux tmp_t sz
       | _          -> aux tmp_s sz; aux tmp_t sz
    )
    columns;
  !tmp_s, !tmp_t

let print_header header fmt =
  let pp_stats =
    match !mode with Stats -> true | Timers -> false | _ -> assert false
  in
  if header || !nb_prints >= max_nb_prints then begin
    nb_prints := 0;
    Format.fprintf fmt "%s@." (if pp_stats then stats_limit else timers_limit);
    List.iter
      (fun (id, _, sz, opt, _) ->
         match opt with
         | Some b when b != pp_stats -> ()
         | _ -> Format.fprintf fmt "|%s" (string_resize id sz)
      )columns;
    Format.fprintf fmt "|@.";
    Format.fprintf fmt "%s@." (if pp_stats then stats_limit else timers_limit)
  end;
  incr nb_prints

let print_stats header steps fmt =
  print_header header fmt;
  let gtime = Options.Time.value() in
  List.iter
    (fun (_, _, sz, opt, func) ->
       match opt with
       | Some false -> ()
       | _ -> Format.fprintf fmt "|%s" (func steps gtime sz)
    ) columns;
  Format.fprintf fmt "|@."

let print_timers header steps fmt =
  Timers.update (get_timers ());
  print_header header fmt;
  let gtime = Options.Time.value() in
  List.iter
    (fun (_, _, sz, opt, func) ->
       match opt with
       | Some true -> ()
       | _ -> Format.fprintf fmt "|%s" (func steps gtime sz)
    )columns;
  Format.fprintf fmt "|@."

let print_instances_generation forced _steps fmt =
  let state = Lazy.force state in
  let (@@) a b = if a <> 0 then a else b in
  if not forced && state.instances_map_printed then
    Format.fprintf fmt "[Instances profiling] No change since last print@."
  else
    let () = state.instances_map_printed <- true in
    if not forced then ignore(Sys.command("clear"));
    Format.fprintf fmt "[Instances profiling] ...@.";
    let insts =
      MS.fold
        (fun name ii acc ->
           let f1 = float_of_int ii.kept in
           let f2 = float_of_int ii.ignored in
           let ratio = f1 /. (f1 +. f2) in
           let all_card = SE.cardinal ii.all_insts in
           (name, ii, all_card, ratio) :: acc)
        state.instances_map []
    in
    let insts =
      List.fast_sort (fun (_, i1, c1, _) (_, i2, c2, _) ->
          (i1.decided - i2.decided) @@
          (c1 - c2) @@
          (i1.kept - i2.kept) @@
          (i1.confl - i2.confl) @@
          (i1.ignored - i2.ignored) @@
          (SE.cardinal i1._new - SE.cardinal i2._new)
        ) insts
    in
    List.iter
      (let open Format in
       fun (name, i, card, r) ->
         fprintf fmt "ratio kept/all: %s| " (float_resize r 8);
         fprintf fmt "<> insts: %s| " (int_resize card 5);
         fprintf fmt "kept: %s| " (int_resize i.kept 7);
         fprintf fmt "ignored: %s| " (int_resize i.ignored 7) ;
         fprintf fmt "decided: %s| " (int_resize i.decided 4);
         fprintf fmt "conflicted: %s| " (int_resize i.confl 4);
         fprintf fmt "consumed: %s| "
           (int_resize (SE.cardinal i.consumed) 5);
         fprintf fmt "produced: %s| "
           (int_resize (SE.cardinal i.produced) 5);
         fprintf fmt "new: %s|| "
           (int_resize (SE.cardinal i._new) 5);
         fprintf fmt "%s" (string_resize name 30);
         fprintf fmt "@."
      )insts;
    ()

let print_call_tree _forced _steps fmt =
  let timers = get_timers () in
  let stack = Timers.get_stack timers in
  List.iter
    (fun (k, f, id) ->
       Format.fprintf fmt "(%s, %s, %s) --> "
         (string_resize (Timers.string_of_ty_module k) 5)
         (string_resize (Timers.string_of_ty_function f) 10)
         (int_resize id 7)
    )(List.rev stack);
  let m, f, id = Timers.current_timer timers in
  Format.fprintf fmt "(%s, %s, %s)@."
    (string_resize (Timers.string_of_ty_module m) 5)
    (string_resize (Timers.string_of_ty_function f) 10)
    (int_resize id 7)

let switch fmt =
  let next, next_msg = match !mode with
    | Stats    -> Timers, "Time"
    | Timers   -> CallTree, "CallTree"
    | CallTree -> FunctionsTimers, "Functions Timers"
    | FunctionsTimers -> Instances, "Instances generation"
    | Instances -> Stats, "Stats"
  in
  Format.fprintf fmt
    "@.>>> Switch to %s profiling. Use \"Ctrl + AltGr + \\\" to exit\n"
    next_msg;
  nb_prints := max_nb_prints;
  mode := next


let float_print =
  let open Format in
  fun fmt v ->
    if Float.equal v 0. then fprintf fmt "--     "
    else if Float.compare v 10. < 0 then fprintf fmt "%0.5f" v
    else if Float.compare v 100. < 0 then fprintf fmt "%0.4f" v
    else fprintf fmt "%0.3f" v

let line_of_module =
  let open Format in
  fun timers fmt f ->
    fprintf fmt "%s " (string_resize (Timers.string_of_ty_function f) 13);
    let cpt = ref 0. in
    List.iter
      (fun m ->
         let v = Timers.get_value timers m f in
         cpt := !cpt +. v;
         fprintf fmt "| %a  " float_print v
      ) Timers.all_modules;
    fprintf fmt "| %a        |@." float_print !cpt


let line_of_sum_module =
  let open Format in
  fun fmt timers ->
    for _ = 0 to 206 do fprintf fmt "-" done;
    fprintf fmt "|@.";
    fprintf fmt "%s " (string_resize "" 13);
    List.iter
      (fun m ->
         fprintf fmt "| %a  " float_print (Timers.get_sum timers m))
      Timers.all_modules;
    fprintf fmt "| GTimer %a |@." float_print (Options.Time.value())

let timers_table =
  let open Format in
  fun forced fmt ->
    if not forced then ignore(Sys.command("clear"));
    let timers = get_timers () in
    Timers.update timers;
    fprintf fmt "@.";
    fprintf fmt "              ";
    List.iter
      (fun f ->
         fprintf fmt"| %s" (string_resize (Timers.string_of_ty_module f) 9))
      Timers.all_modules;
    fprintf fmt "|@.";
    for _ = 0 to 206 do fprintf fmt "-" done;
    fprintf fmt "|@.";
    List.iter (line_of_module timers fmt) Timers.all_functions;
    line_of_sum_module fmt timers

let print =
  let open Format in
  fun all steps fmt ->
    print_initial_info fmt;
    set_sigprof();
    if all then begin
      let old_mode = !mode in
      mode := Stats;
      fprintf fmt "@.";
      print_stats true steps fmt;
      fprintf fmt "@.";
      mode := Timers;
      print_timers true steps fmt;
      fprintf fmt "@.";
      timers_table true fmt;
      fprintf fmt "@.";
      print_instances_generation true steps fmt;
      fprintf fmt "@.";
      mode := old_mode
    end
    else match !mode with
      | Stats           -> print_stats false steps fmt
      | Timers          -> print_timers false steps fmt
      | CallTree        -> print_call_tree false steps fmt
      | FunctionsTimers -> timers_table false fmt;
      | Instances       -> print_instances_generation false steps fmt


(******************************)
(* SMT get-statistics feature *)
(******************************)

(** The table in which we will put the statistics we want to display when
    the (get-statistics) instruction is performed. *)
let statistics_table : (string, (unit -> string)) Hashtbl.t = Hashtbl.create 7


let register_stat (key : string) (getter : unit -> string) =
  Hashtbl.add statistics_table key getter

let register_int_stat (key : string) (getter : unit -> int) =
  register_stat key (fun () -> string_of_int (getter ()))

let register_float_stat (key : string) (getter : unit -> float) =
  register_stat
    key
    (fun () ->
       Format.sprintf "%.9f" (getter ()))

let print_statistics fmt =
  Fmt.pf fmt "(@[<v 0>";
  Hashtbl.iter
    (fun key getter -> Fmt.pf fmt "@,:%s %s" key (getter ()))
    statistics_table;
  Fmt.pf fmt "@])@,"

(* Registering the statistics we want to display even when profiling is off. *)
let () =
  register_int_stat "steps" (fun () -> Steps.get_steps ())

let init () =
  let state = Lazy.force state in
  state.decisions <- 0;
  state.assumes <- 0;
  state.queries <- 0;
  state.instantiation_rounds <- 0;
  state.instances <- 0;
  state.decision_lvl <- 0;
  state.instantiation_lvl <- 0;
  state.assumes_current_lvl <- 0;
  state.th_conflicts <- 0;
  state.b_conflicts <- 0;
  state.bcp_th_conflicts <- 0;
  state.bcp_b_conflicts <- 0;
  state.bcp_mix_conflicts <- 0;
  state.t_red <- 0;
  state.b_red <- 0;
  state.t_elim <- 0;
  state.b_elim <- 0;
  state.instances_map <- MS.empty;
  state.instances_map_printed <- false;
  let timers = get_timers () in
  Timers.set_timer_start (Timers.start timers);
  Timers.set_timer_pause (Timers.pause timers);
  Timers.reset timers;
  set_sigprof ();
  (* Registering timer statistics. *)
  List.iter
    (fun (m : Timers.ty_module) ->
       let name = Format.sprintf "timer-%s" (Timers.string_of_ty_module m) in
       register_float_stat
         name
         (fun () -> Timers.get_sum state.timers m))
    Timers.all_modules

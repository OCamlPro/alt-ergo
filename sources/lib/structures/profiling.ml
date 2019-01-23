(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Format
open Options
module SE = Expr.Set

module MS = Map.Make(String)

type inst_info =
  {
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
  decisions : int ref;
  assumes : int ref;
  assumes_current_lvl : int ref;
  queries : int ref;
  instantiation_rounds : int ref;
  instances : int ref;
  decision_lvl : int ref;
  instantiation_lvl : int ref;

  (* 4 kinds of conflicts *)
  th_conflicts : int ref;
  b_conflicts : int ref;
  bcp_th_conflicts : int ref;
  bcp_b_conflicts : int ref;
  bcp_mix_conflicts : int ref;

  (* 4 kinds of red/elim *)
  t_red : int ref;
  b_red : int ref;
  t_elim : int ref;
  b_elim : int ref;
  (* first int: counter ok kept instances,
     second int: counter of removed instances*)
  instances_map : inst_info MS.t ref;
  instances_map_printed : bool ref
}

let state =
  { decisions = ref 0;
    assumes = ref 0;
    assumes_current_lvl = ref 0;
    queries = ref 0;
    instantiation_rounds = ref 0;
    instances = ref 0;
    decision_lvl = ref 0;
    instantiation_lvl = ref 0;

    th_conflicts = ref 0;
    b_conflicts = ref 0;
    bcp_th_conflicts = ref 0;
    bcp_b_conflicts = ref 0;
    bcp_mix_conflicts = ref 0;

    t_red  = ref 0;
    b_red  = ref 0;
    t_elim = ref 0;
    b_elim = ref 0;

    instances_map = ref MS.empty;
    instances_map_printed = ref false
  }

let set_sigprof () =
  let tm =
    let v = Options.profiling_period () in
    if Pervasives.(>) v 0. then v else -. v
  in
  ignore
    (Unix.setitimer Unix.ITIMER_PROF
       { Unix.it_value = tm; Unix.it_interval = 0. })

let init () =
  state.decisions := 0;
  state.assumes := 0;
  state.queries := 0;
  state.instantiation_rounds := 0;
  state.instances := 0;
  state.decision_lvl := 0;
  state.instantiation_lvl := 0;
  state.assumes_current_lvl := 0;
  state.th_conflicts := 0;
  state.b_conflicts := 0;
  state.bcp_th_conflicts := 0;
  state.bcp_b_conflicts := 0;
  state.bcp_mix_conflicts := 0;
  state.t_red  := 0;
  state.b_red  := 0;
  state.t_elim := 0;
  state.b_elim := 0;
  state.instances_map := MS.empty;
  state.instances_map_printed := false;
  set_sigprof ()

(* update functions of the internal state *)

let assume nb =
  state.assumes := nb + !(state.assumes);
  state.assumes_current_lvl := nb + !(state.assumes_current_lvl)

let query () =
  incr state.queries

let instances l =
  state.instances := !(state.instances) + List.length l

let instantiation ilvl =
  incr state.instantiation_rounds;
  incr state.instantiation_lvl;
  if not (!(state.instantiation_lvl) = ilvl) then begin
    Format.eprintf "state.instantiation_lvl = %d et ilvl = %d@."
      !(state.instantiation_lvl) ilvl;
    assert false
  end

let bool_conflict () =
  incr state.b_conflicts

let theory_conflict () =
  incr state.th_conflicts

let bcp_conflict b1 b2 =
  if b1 && b2 then incr state.bcp_b_conflicts
  else if (not b1) && (not b2) then incr state.bcp_th_conflicts
  else incr state.bcp_mix_conflicts

let red b = if b then incr state.b_red else incr state.t_red

let elim b = if b then incr state.b_elim else incr state.t_elim

let reset_ilevel n = state.instantiation_lvl := n

let reset_dlevel n = state.decision_lvl := n

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
  let () = state.instances_map_printed := false in
  let ii =
    try MS.find axiom !(state.instances_map)
    with Not_found -> empty_inst_info loc
  in
  assert (ii.loc == loc);
  let ii =
    if kept then
      {ii with kept = ii.kept + 1; all_insts = SE.add inst ii.all_insts}
    else
      {ii with ignored = ii.ignored + 1}
  in
  state.instances_map := MS.add axiom ii !(state.instances_map)

let conflicting_instance axiom loc =
  let ii =
    try MS.find axiom !(state.instances_map)
    with Not_found -> empty_inst_info loc
  in
  let ii = {ii with confl = ii.confl + 1} in
  assert (ii.loc == loc);
  state.instances_map := MS.add axiom ii !(state.instances_map)

let decision_on_instance axiom_name =
  try
    let ii =
      MS.find axiom_name !(state.instances_map)
    in
    let ii = {ii with decided = ii.decided + 1} in
    (*assert (ii.loc == loc);*)
    state.instances_map := MS.add axiom_name ii !(state.instances_map)
  with Not_found -> ()


let decision d origin =
  incr state.decisions;
  incr state.decision_lvl;
  if not (!(state.decision_lvl) = d) then begin
    Format.eprintf "state.decision_lvl = %d et d = %d@."
      !(state.decision_lvl) d;
    assert false
  end;
  state.assumes_current_lvl := 0;
  decision_on_instance origin


let register_produced_terms axiom loc consumed all produced _new =
  let ii =
    try MS.find axiom !(state.instances_map)
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
  state.instances_map := MS.add axiom ii !(state.instances_map)

(******************************************************************************
   printing the internal state
 ******************************************************************************)

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

let string_resize s i =
  let sz = max 0 (i - (String.length s)) in
  let tmp = String.make sz ' ' in
  s ^ tmp

let int_resize n i = string_resize (sprintf "%d" n) i

let float_resize f i = string_resize (sprintf "%f" f) i

let percent total a =
  (string_of_int (int_of_float (a *. 100. /. total))) ^ "%"

let columns =
  [
    "GTimer", "Global timer", 11, None,
    (fun _ gtime _ sz -> float_resize gtime sz);

    "Steps", "Number of Steps", 14, None,
    (fun steps gtime _ sz ->
       let avg = int_of_float (Int64.to_float steps /. gtime) in
       sprintf "%s~%s"
         (string_resize (sprintf "%Ld" steps) (sz-7))
         (string_resize (sprintf "%d/s" avg) 6)
    );

    "Case splits", "Number of Case Splits", 14, None,
    (fun _ gtime _ sz ->
       let avg = int_of_float (float_of_int (Options.cs_steps()) /. gtime) in
       sprintf "%s~%s"
         (string_resize (sprintf "%d" (Options.cs_steps())) (sz-7))
         (string_resize (sprintf "%d/s" avg) 6)
    );

    "Mod.", "Current active module", 7, None,
    (fun _ _ timers sz ->
       let kd, _msg, _ = Timers.current_timer timers in
       string_resize (Timers.string_of_ty_module kd) sz);

    "Module Id", "Each call to a module is tagged with a fresh Id", 10, None,
    (fun _ _ timers sz ->
       let _kd, _msg, id = Timers.current_timer timers in
       int_resize id sz);

    (*-----------------------------------------------------------------*)

    "ilvl", "Current Instantiaton level", 6, Some true,
    (fun _ _ _ sz -> int_resize !(state.instantiation_lvl) sz);

    "#i rnds", "Number of intantiation rounds", 8, Some true,
    (fun _ _ _ sz ->
       int_resize !(state.instantiation_rounds) sz);


    "#insts", "Number of generated instances", 8, Some true,
    (fun _ _ _ sz -> int_resize !(state.instances) sz);

    "i/r", "AVG number of generated instances per instantiation rounds",
    8, Some true,
    (fun _ _ _ sz ->
       int_resize
         (!(state.instances) / (max 1 !(state.instantiation_rounds))) sz);

    "dlvl", "Current Decision level", 6, Some true,
    (fun _ _ _ sz -> int_resize !(state.decision_lvl) sz);

    "#decs", "Number of decisions", 6, Some true,
    (fun _ _ _ sz -> int_resize !(state.decisions) sz);

    "T-asm", "Number of calls to Theory.assume", 6, Some true,
    (fun _ _ _ sz -> int_resize !(state.assumes) sz);

    "T/d", "Number of Theory.assume after last decision", 6, Some true,
    (fun _ _ _ sz -> int_resize !(state.assumes_current_lvl) sz);

    "T-qr", "Number of calls to Theory.query", 15, Some true,
    (fun _ _ _ sz -> int_resize !(state.queries) sz);

    "B-R", "Number of reduced clauses by Boolean propagation", 6, Some true,
    (fun _ _ _ sz -> int_resize !(state.b_red) sz);

    "B-E", "Number of eliminated clauses by Boolean propagation", 6,
    Some true, (fun _ _ _ sz -> int_resize !(state.b_elim) sz);

    "T-R", "Number of reduced clauses by Theory propagation", 6, Some true,
    (fun _ _ _ sz -> int_resize !(state.t_red) sz);

    "T-E", "Number of eliminated clauses by Theory propagation", 6,
    Some true, (fun _ _ _ sz -> int_resize !(state.t_elim) sz);

    "B-!",  "Number of direct Boolean conflicts", 5, Some true,
    (fun _ _ _ sz -> int_resize !(state.b_conflicts) sz);

    "T-!", "Number of direct Theory conflicts" , 5, Some true,
    (fun _ _ _ sz -> int_resize !(state.th_conflicts) sz);

    "B>!", "Number of Boolean conflicts deduced by BCP", 5, Some true,
    (fun _ _ _ sz -> int_resize !(state.bcp_b_conflicts) sz);

    "T>!", "Number of Theory conflicts deduced by BCP", 5, Some true,
    (fun _ _ _ sz -> int_resize !(state.bcp_th_conflicts) sz);

    "M>!", "Number of Mix conflicts deduced by BCP", 5, Some true,
    (fun _ _ _ sz -> int_resize !(state.bcp_mix_conflicts) sz);

    (*-----------------------------------------------------------------*)
    "SAT", "Time spent in SAT module(s)", 16, Some false,
    (fun _ gtime timers sz ->
       let curr = Timers.get_sum timers Timers.M_Sat in
       sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "Matching", "Time spent in Matching module(s)", 16, Some false,
    (fun _ gtime timers sz ->
       let curr = Timers.get_sum timers Timers.M_Match in
       sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "CC", "Time spent in CC module(s)", 16, Some false,
    (fun _ gtime timers sz ->
       let curr = Timers.get_sum timers Timers.M_CC in
       sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4)
    );

    "Arith", "Time spent in Arith module(s)", 16, Some false,
    (fun _ gtime timers sz ->
       let curr = Timers.get_sum timers Timers.M_Arith in
       sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "Arrays", "Time spent in Arrays module(s)", 16, Some false,
    (fun _ gtime timers sz ->
       let curr = Timers.get_sum timers Timers.M_Arrays in
       sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "Sum", "Time spent in Sum module(s)", 16, Some false,
    (fun _ gtime timers sz ->
       let curr = Timers.get_sum timers Timers.M_Sum in
       sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "Records", "Time spent in Records module(s)", 16, Some false,
    (fun _ gtime timers sz ->
       let curr = Timers.get_sum timers Timers.M_Records in
       sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "AC", "Time spent in AC module(s)", 16, Some false,
    (fun _ gtime timers sz ->
       let curr = Timers.get_sum timers Timers.M_AC in
       sprintf "%s~%s"
         (float_resize curr (sz - 5)) (string_resize (percent gtime curr) 4));

    "Total", "Time spent in 'supervised' module(s)", 11, Some false,
    (fun _ _ timers sz ->
       let tsat = Timers.get_sum timers Timers.M_Sat in
       let tmatch = Timers.get_sum timers Timers.M_Match in
       let tcc = Timers.get_sum timers Timers.M_CC in
       let tarith = Timers.get_sum timers Timers.M_Arith in
       let tarrays = Timers.get_sum timers Timers.M_Arrays in
       let tsum = Timers.get_sum timers Timers.M_Sum in
       let trecs = Timers.get_sum timers Timers.M_Records in
       let tac = Timers.get_sum timers Timers.M_AC in
       let total = tsat+.tmatch+.tcc+.tarith+.tarrays+.tsum+.trecs+.tac in
       float_resize total sz);
  ]

let print_initial_info () =
  if !initial_info then begin
    initial_info := false;
    let max =
      List.fold_left (fun z (id,_, _,_,_) -> max z (String.length id))
        0 columns
    in
    List.iter
      (fun (id, descr, _, _, _) ->
         fprintf fmt "%s : %s@." (string_resize id max) descr
      )columns
  end

let stats_limit, timers_limit =
  let aux tmp sz =
    tmp := sprintf "%s|" !tmp;
    for _ = 1 to sz do tmp := sprintf "%s-" !tmp done
  in
  let tmp_s = ref "" in
  let tmp_t = ref "" in
  List.iter
    (fun (_, _, sz, opt, _) ->
       match opt with
       | Some true  -> aux tmp_s sz
       | Some false -> aux tmp_t sz
       | _          -> aux tmp_s sz; aux tmp_t sz
    )columns;
  !tmp_s ^ "|", !tmp_t ^ "|"

let print_header header fmt =
  let pp_stats =
    match !mode with Stats -> true | Timers -> false | _ -> assert false in
  if header || !nb_prints >= max_nb_prints then begin
    nb_prints := 0;
    fprintf fmt "%s@." (if pp_stats then stats_limit else timers_limit);
    List.iter
      (fun (id, _, sz, opt, _) ->
         match opt with
         | Some b when b != pp_stats -> ()
         | _ -> fprintf fmt "|%s" (string_resize id sz)
      )columns;
    fprintf fmt "|@.";
    fprintf fmt "%s@." (if pp_stats then stats_limit else timers_limit)
  end;
  incr nb_prints

let print_stats header steps fmt timers =
  print_header header fmt;
  let gtime = Options.Time.value() in
  List.iter
    (fun (_, _, sz, opt, func) ->
       match opt with
       | Some false -> ()
       | _ -> fprintf fmt "|%s" (func steps gtime timers sz)
    )columns;
  fprintf fmt "|@."

let print_timers header steps fmt timers =
  Timers.update timers;
  print_header header fmt;
  let gtime = Options.Time.value() in
  List.iter
    (fun (_, _, sz, opt, func) ->
       match opt with
       | Some true -> ()
       | _ -> fprintf fmt "|%s" (func steps gtime timers sz)
    )columns;
  fprintf fmt "|@."

(* unused
   let report2 axiom fmt (b,e) =
   let open Lexing in
   let l = b.pos_lnum in
   let fc = b.pos_cnum - b.pos_bol + 1 in
   let lc = e.pos_cnum - b.pos_bol + 1 in
   fprintf fmt "(Sub) Axiom \"%s\", line %d, characters %d-%d:"
    axiom l fc lc
*)

(* unused
   let report3 fmt (b,e) =
   let open Lexing in
   let l = b.pos_lnum in
   let fc = b.pos_cnum - b.pos_bol + 1 in
   let lc = e.pos_cnum - b.pos_bol + 1 in
   fprintf fmt "line %d, chars %d-%d." l fc lc
*)

let (@@) a b = if a <> 0 then a else b

let print_instances_generation forced _steps _timers =
  if not forced && !(state.instances_map_printed) then
    fprintf fmt "[Instances profiling] No change since last print@."
  else
    let () = state.instances_map_printed := true in
    if not forced then ignore(Sys.command("clear"));
    fprintf fmt "[Instances profiling] ...@.";
    let insts =
      MS.fold
        (fun name ii acc ->
           let f1 = float_of_int ii.kept in
           let f2 = float_of_int ii.ignored in
           let ratio = f1 /. (f1 +. f2) in
           let all_card = SE.cardinal ii.all_insts in
           (name, ii, all_card, ratio) :: acc)
        !(state.instances_map) []
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
      (fun (name, i, card, r) ->
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
         (*fprintf fmt "%s | " (string_resize name 30);
           fprintf fmt "%a@." report3 i.loc (* too long *) *)
         fprintf fmt "@."
      )insts;
    (*if forced then
      let () = fprintf fmt "digraph v{@." in
      fprintf fmt "size=\"10,7.5\"@.";
      fprintf fmt "ratio=\"fill\"@.";
      fprintf fmt "rotate=90@.";
      fprintf fmt "fontsize=\"12pt\"@.";
      fprintf fmt "rankdir = TB@." ;
      let terms = ref SE.empty in
      List.iter
      (fun (name, i, _) ->
      SE.iter
      (fun t ->
      fprintf fmt "\"%d\" -> \"%s\";@." (T.hash t) name
      )i.consumed;
      terms := SE.union !terms i.consumed;
      SE.iter
      (fun t ->
      fprintf fmt "\"%s\" -> \"%d\";@." name (T.hash t)
      )i._new;
      terms := SE.union !terms i._new;
      fprintf fmt "\"%s\" [fillcolor=yellow];@." name;
      )insts;
      SE.iter
      (fun t ->
      fprintf fmt "\"%d\" [fillcolor=green];@." (T.hash t);
      )!terms;
      fprintf fmt "}@."*)
    (*
      if forced then
      let () = fprintf fmt "digraph v{@." in
      fprintf fmt "size=\"10,7.5\"@.";
      fprintf fmt "ratio=\"fill\"@.";
      fprintf fmt "rotate=90@.";
      fprintf fmt "fontsize=\"12pt\"@.";
      fprintf fmt "rankdir = TB@." ;
      List.iter
      (fun (s1, i1, _) ->
      List.iter
      (fun (s2, i2, _) ->
      if SE.is_empty (SE.inter i1.produced i2.consumed) then ()
      else fprintf fmt "\"%s\" -> \"%s\";@." s1 s2
      )insts
      )insts;
      fprintf fmt "}@."*)
    ()

let print_call_tree _forced _steps timers =
  let stack = Timers.get_stack timers in
  List.iter
    (fun (k, f, id) ->
       fprintf fmt "(%s, %s, %s) --> "
         (string_resize (Timers.string_of_ty_module k) 5)
         (string_resize (Timers.string_of_ty_function f) 10)
         (int_resize id 7)
    )(List.rev stack);
  let m, f, id = Timers.current_timer timers in
  fprintf fmt "(%s, %s, %s)@."
    (string_resize (Timers.string_of_ty_module m) 5)
    (string_resize (Timers.string_of_ty_function f) 10)
    (int_resize id 7)

let switch () =
  let next, next_msg = match !mode with
    | Stats    -> Timers, "Time"
    | Timers   -> CallTree, "CallTree"
    | CallTree -> FunctionsTimers, "Functions Timers"
    | FunctionsTimers -> Instances, "Instances generation"
    | Instances -> Stats, "Stats"
  in
  fprintf fmt
    "@.>>> Switch to %s profiling. Use \"Ctrl + AltGr + \\\" to exit\n"
    next_msg;
  nb_prints := max_nb_prints;
  mode := next


let float_print fmt v =
  if Pervasives.(=) v 0. then fprintf fmt "--     "
  else if Pervasives.(<) v 10. then fprintf fmt "%0.5f" v
  else if Pervasives.(<) v 100. then fprintf fmt "%0.4f" v
  else fprintf fmt "%0.3f" v

let line_of_module arr f =
  fprintf fmt "%s " (string_resize (Timers.string_of_ty_function f) 13);
  let cpt = ref 0. in
  List.iter
    (fun m ->
       let v = arr.(Timers.mtag m).(Timers.ftag f) in
       cpt := !cpt +. v;
       fprintf fmt "| %a  " float_print v
    ) Timers.all_modules;
  fprintf fmt "| %a        |@." float_print !cpt


let line_of_sum_module timers =
  for _ = 0 to 206 do fprintf fmt "-" done;
  fprintf fmt "|@.";
  fprintf fmt "%s " (string_resize "" 13);
  List.iter
    (fun m ->
       fprintf fmt "| %a  " float_print (Timers.get_sum timers m))
    Timers.all_modules;
  fprintf fmt "| GTimer %a |@." float_print (Options.Time.value())

let timers_table forced timers =
  if not forced then ignore(Sys.command("clear"));
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
  let arr_timers = Timers.get_timers_array timers in
  List.iter
    (line_of_module arr_timers)
    Timers.all_functions;
  line_of_sum_module timers

let print all steps timers fmt =
  print_initial_info ();
  set_sigprof();
  if all then begin
    mode := Stats;
    fprintf fmt "@.";
    print_stats true steps fmt timers;
    fprintf fmt "@.";
    mode := Timers;
    print_timers true steps fmt timers;
    fprintf fmt "@.";
    timers_table true timers;
    fprintf fmt "@.";
    print_instances_generation true steps timers;
    fprintf fmt "@.";
  end
  else match !mode with
    | Stats           -> print_stats false steps fmt timers
    | Timers          -> print_timers false steps fmt timers
    | CallTree        -> print_call_tree false steps timers
    | FunctionsTimers -> timers_table false timers;
    | Instances       -> print_instances_generation false steps timers


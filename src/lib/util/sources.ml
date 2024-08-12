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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

let ac = Logs.Src.create ~doc:"Ac" "AltErgoLib.Ac"
let adt = Logs.Src.create ~doc:"Adt" "AltErgoLib.Adt"
let adt_rel = Logs.Src.create ~doc:"Adt_rel" "AltErgoLib.Adt_rel"
let arith = Logs.Src.create ~doc:"Arith" "AltErgoLib.Arith"
let arrays_rel = Logs.Src.create ~doc:"Arrays_rel" "AltErgoLib.Arrays_rel"
let bitv = Logs.Src.create ~doc:"Bitv" "AltErgoLib.Bitv"
let bitv_rel = Logs.Src.create ~doc:"Bitv_rel" "AltErgoLib.Bitv_rel"
let cc = Logs.Src.create ~doc:"Cc" "AltErgoLib.Cc"
let combine = Logs.Src.create ~doc:"combine" "AltErgoLib.combine"
let commands = Logs.Src.create ~doc:"Commands" "AltErgoLib.commands"
let constr = Logs.Src.create ~doc:"Constr" "AltErgoLib.constr"
let explanation =
  Logs.Src.create ~doc:"explanations" "AltErgoLib.explanation"
let fm = Logs.Src.create ~doc:"fm" "AltErgoLib.fm"
let intervals = Logs.Src.create ~doc:"Intervals" "AltErgoLib.Intervals"
let interval_calculus =
  Logs.Src.create ~doc:"IntervalCalculus" "AltErgoLib.IntervalCalculus"
let fpa = Logs.Src.create ~doc:"fpa" "AltErgoLib.fpa"
let gc_debug = Logs.Src.create ~doc:"Gc_debug" "AltErgoLib.Gc_debug"
let interpretation =
  Logs.Src.create ~doc:"Interpretation" "AltErgoLib.Interpretation"
let ite_rel = Logs.Src.create ~doc:"Ite_rel" "AltErgoLib.Ite_rel"
let matching = Logs.Src.create ~doc:"Matching" "AltErgoLib.Matching"
let model = Logs.Src.create ~doc:"Model" "AltErgoLib.Model"
let optimize = Logs.Src.create ~doc:"Optimize" "AltErgoLib.Optimize"
let sat = Logs.Src.create ~doc:"Sat" "AltErgoLib.Sat"
let split = Logs.Src.create ~doc:"Split" "AltErgoLib.Split"
let triggers = Logs.Src.create ~doc:"Triggers" "AltErgoLib.Triggers"
let types = Logs.Src.create ~doc:"Types" "AltErgoLib.Types"
let typing = Logs.Src.create ~doc:"Typing" "AltErgoLib.Typing"
let uf = Logs.Src.create ~doc:"Uf" "AltErgoLib.Uf"
let unsat_core = Logs.Src.create ~doc:"Unsat_core" "AltErgoLib.Unsat_core"
let use = Logs.Src.create ~doc:"Use" "AltErgoLib.Use"
let warnings = Logs.Src.create ~doc:"Warnings" "AltErgoLib.Warnings"

let all = [
  ac;
  adt;
  adt_rel;
  arith;
  arrays_rel;
  bitv;
  bitv_rel;
  cc;
  combine;
  commands;
  constr;
  explanation;
  fm;
  intervals;
  fpa;
  gc_debug;
  interpretation;
  intervals;
  interval_calculus;
  ite_rel;
  matching;
  model;
  optimize;
  sat;
  split;
  triggers;
  types;
  typing;
  uf;
  unsat_core;
  use;
  warnings
]

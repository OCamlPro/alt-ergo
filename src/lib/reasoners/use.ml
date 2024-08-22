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

module E = Expr
module SE = E.Set

module SA =
  Set.Make
    (struct
      type t = E.t * Explanation.t
      let compare (s1,_) (s2,_) = E.compare s1 s2
    end)

module X = Shostak.Combine

module MX = Shostak.MXH

let src = Logs.Src.create ~doc:"Use" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

type t = (SE.t * SA.t) MX.t
type r = X.r

let inter_tpl (x1,y1) (x2,y2) =
  Options.exec_thread_yield ();
  SE.inter x1 x2, SA.inter y1 y2

let union_tpl (x1,y1) (x2,y2) =
  Options.exec_thread_yield ();
  SE.union x1 x2, SA.union y1 y2

let one, _ = X.make (E.mk_term (Symbols.name ~ns:Internal "@bottom") [] Ty.Tint)
let leaves r =
  match X.leaves r with [] -> [one] | l -> l

let find k m = try MX.find k m with Not_found -> (SE.empty,SA.empty)

let add_term k t mp =
  let g_t,g_a = find k mp in MX.add k (SE.add t g_t,g_a) mp

let up_add g t rt lvs =
  let g = if MX.mem rt g then g else MX.add rt (SE.empty, SA.empty) g in
  match E.term_view t with
  | { E.xs = []; _ } -> g
  | _ -> List.fold_left (fun g x -> add_term x t g) g lvs

let congr_add g lvs =
  match lvs with
    []    -> SE.empty
  | x::ls ->
    List.fold_left
      (fun acc y -> SE.inter (fst(find y g)) acc)
      (fst(find x g)) ls

let up_close_up g p v =
  let lvs = leaves v in
  let g_p = find p g in
  List.fold_left (fun gg l -> MX.add l (union_tpl g_p (find l g)) gg) g lvs

let congr_close_up g p touched =
  let inter = function
      [] -> (SE.empty, SA.empty)
    | rx::l ->
      List.fold_left (fun acc x ->inter_tpl acc (find x g))(find rx g) l
  in
  List.fold_left
    (fun (st,sa) tch -> union_tpl (st,sa)(inter (leaves tch)))
    (find p g) touched

let print g =
  if Options.get_debug_use () then
    begin
      let sterms fmt = SE.iter (Format.fprintf fmt "%a " E.print) in
      let satoms fmt =
        SA.iter
          (fun (a,e) ->
             Format.fprintf fmt "%a %a" E.print a Explanation.print e)
      in
      let print_sterms_and_atoms fmt (st,sa) =
        match SE.is_empty st,SA.is_empty sa with
        | true, true -> Format.fprintf fmt ""
        | false, true -> Format.fprintf fmt " is used by {%a}" sterms st
        | true,false -> Format.fprintf fmt " is used by {%a}" satoms sa
        | false, false ->
          Format.fprintf fmt " is used by {%a} and {%a}" sterms st satoms sa
      in
      Printer.print_dbg
        ~module_name:"Use" ~function_name:"print"
        "@[<v 2>gamma :@ ";
      MX.iter
        (fun t (st,sa) ->
           Printer.print_dbg ~header:false "%a " X.print t;
           Printer.print_dbg ~header:false "%a@ "
             print_sterms_and_atoms (st,sa);
        ) g;
      Printer.print_dbg ~header:false "@]"
    end

let mem = MX.mem
let add = MX.add
let empty = MX.empty

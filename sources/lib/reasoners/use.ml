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

open Options
open Format

module E = Expr
module SE = E.Set

module SA =
  Set.Make
    (struct
      type t = E.t * Explanation.t
      let compare (s1,_) (s2,_) = E.compare s1 s2
    end)

module X = Shostak.Combine

module MX = Map.Make(struct type t = X.r let compare = X.hash_cmp end)

type t = (SE.t * SA.t) MX.t
type r = X.r

let inter_tpl (x1,y1) (x2,y2) =
  Options.exec_thread_yield ();
  SE.inter x1 x2, SA.inter y1 y2

let union_tpl (x1,y1) (x2,y2) =
  Options.exec_thread_yield ();
  SE.union x1 x2, SA.union y1 y2

let one, _ = X.make (E.mk_term (Symbols.name "@bottom") [] Ty.Tint)
let leaves r =
  match X.leaves r with [] -> [one] | l -> l

let find k m = try MX.find k m with Not_found -> (SE.empty,SA.empty)

let add_term k t mp =
  let g_t,g_a = find k mp in MX.add k (SE.add t g_t,g_a) mp

let up_add g t rt lvs =
  let g = if MX.mem rt g then g else MX.add rt (SE.empty, SA.empty) g in
  match E.term_view t with
  | E.Term { E.xs = []; _ } -> g
  | E.Term _ -> List.fold_left (fun g x -> add_term x t g) g lvs
  | _ -> assert false

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
  if debug_use () then
    begin
      let sterms fmt = SE.iter (fprintf fmt "%a " E.print) in
      let satoms fmt =
        SA.iter
          (fun (a,e) ->
             fprintf fmt "%a %a" E.print a Explanation.print e)
      in
      fprintf fmt "@{<C.Bold>[use]@} gamma :\n";
      MX.iter
        (fun t (st,sa) ->
           fprintf fmt "%a is used by {%a} and {%a}\n"
             X.print t sterms st satoms sa
        ) g
    end

let mem = MX.mem
let add = MX.add
let empty = MX.empty

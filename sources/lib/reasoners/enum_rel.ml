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

module A  = Xliteral
module L  = List
module Hs = Hstring

type 'a abstract = 'a Enum.abstract = Cons of Hs.t * Ty.t |  Alien of 'a

module X = Shostak.Combine
module Sh = Shostak.Enum
open Sh

module Ex = Explanation

module MX = Map.Make(struct type t = X.r let compare = X.hash_cmp end)
module HSS = Set.Make (struct type t=Hs.t let compare = Hs.compare end)

module LR = Uf.LX

type t = { mx : (HSS.t * Ex.t) MX.t; classes : Expr.Set.t list;
           size_splits : Numbers.Q.t }

let empty classes = { mx = MX.empty; classes = classes;
                      size_splits = Numbers.Q.one }

(*BISECT-IGNORE-BEGIN*)
module Debug = struct

  let assume bol r1 r2 =
    if debug_sum () then
      fprintf fmt "[Sum.Rel] we assume %a %s %a@."
        X.print r1 (if bol then "=" else "<>") X.print r2

  let print_env env =
    if debug_sum () then begin
      fprintf fmt "--SUM env ---------------------------------@.";
      MX.iter
        (fun r (hss, ex) ->
           fprintf fmt "%a ::= " X.print r;
           begin
             match HSS.elements hss with
               []      -> ()
             | hs :: l ->
               fprintf fmt " %s" (Hs.view hs);
               L.iter (fun hs -> fprintf fmt " | %s" (Hs.view hs)) l
           end;
           fprintf fmt " : %a@." Ex.print ex;

        ) env.mx;
      fprintf fmt "-------------------------------------------@.";
    end

  let case_split r r' =
    if debug_sum () then
      fprintf fmt "[case-split] %a = %a@." X.print r X.print r'

  let no_case_split () =
    if debug_sum () then fprintf fmt "[case-split] sum: nothing@."

  let add r =
    if debug_sum () then fprintf fmt "Sum.Rel.add: %a@." X.print r

end
(*BISECT-IGNORE-END*)

let values_of r = match X.type_info r with
  | Ty.Tsum (_,l) ->
    Some (List.fold_left (fun st hs -> HSS.add hs st) HSS.empty l)
  | _ -> None

let add_diseq hss sm1 sm2 dep env eqs =
  match sm1, sm2 with
  | Alien r , Cons(h,ty)
  | Cons (h,ty), Alien r  ->
    let enum, ex = try MX.find r env.mx with Not_found -> hss, Ex.empty in
    let enum = HSS.remove h enum in
    let ex = Ex.union ex dep in
    if HSS.is_empty enum then raise (Ex.Inconsistent (ex, env.classes))
    else
      let env = { env with mx = MX.add r (enum, ex) env.mx } in
      if HSS.cardinal enum = 1 then
        let h' = HSS.choose enum in
        env,
        (Sig_rel.LSem (LR.mkv_eq r (is_mine (Cons(h',ty)))),
         ex, Th_util.Other)::eqs
      else env, eqs

  | Alien r1, Alien r2 ->
    let enum1,ex1= try MX.find r1 env.mx with Not_found -> hss,Ex.empty in
    let enum2,ex2= try MX.find r2 env.mx with Not_found -> hss,Ex.empty in

    let eqs =
      if HSS.cardinal enum1 = 1 then
        let ex = Ex.union dep ex1 in
        let h' = HSS.choose enum1 in
        let ty = X.type_info r1 in
        (Sig_rel.LSem (LR.mkv_eq r1 (is_mine (Cons(h',ty)))),
         ex, Th_util.Other)::eqs
      else eqs
    in
    let eqs =
      if HSS.cardinal enum2 = 1 then
        let ex = Ex.union dep ex2 in
        let h' = HSS.choose enum2 in
        let ty = X.type_info r2 in
        (Sig_rel.LSem (LR.mkv_eq r2 (is_mine (Cons(h',ty)))),
         ex, Th_util.Other)::eqs
      else eqs
    in
    env, eqs

  |  _ -> env, eqs

let add_eq hss sm1 sm2 dep env eqs =
  match sm1, sm2 with
  | Alien r, Cons(h,_)
  | Cons (h,_), Alien r  ->
    let enum, ex = try MX.find r env.mx with Not_found -> hss, Ex.empty in
    let ex = Ex.union ex dep in
    if not (HSS.mem h enum) then raise (Ex.Inconsistent (ex, env.classes));
    {env with mx = MX.add r (HSS.singleton h, ex) env.mx} , eqs

  | Alien r1, Alien r2   ->
    let enum1,ex1 =
      try MX.find r1 env.mx with Not_found -> hss, Ex.empty in
    let enum2,ex2 =
      try MX.find r2 env.mx with Not_found -> hss, Ex.empty in
    let ex = Ex.union dep (Ex.union ex1 ex2) in
    let diff = HSS.inter enum1 enum2 in
    if HSS.is_empty diff then raise (Ex.Inconsistent (ex, env.classes));
    let mx = MX.add r1 (diff, ex) env.mx in
    let env = {env with mx = MX.add r2 (diff, ex) mx } in
    if HSS.cardinal diff = 1 then
      let h' = HSS.choose diff in
      let ty = X.type_info r1 in
      env, (Sig_rel.LSem (LR.mkv_eq r1 (is_mine (Cons(h',ty)))),
            ex, Th_util.Other)::eqs
    else env, eqs

  |  _ -> env, eqs

let count_splits env la =
  let nb =
    List.fold_left
      (fun nb (_,_,_,i) ->
         match i with
         | Th_util.CS (Th_util.Th_sum, n) -> Numbers.Q.mult nb n
         | _ -> nb
      )env.size_splits la
  in
  {env with size_splits = nb}

let add_aux env r =
  Debug.add r;
  match embed r, values_of r with
  | Alien r, Some hss ->
    if MX.mem r env.mx then env else
      { env with mx = MX.add r (hss, Ex.empty) env.mx }
  | _ -> env

(* needed for models generation because fresh terms are not
   added with function add *)
let add_rec env r = List.fold_left add_aux env (X.leaves r)

let assume env uf la =
  let env = count_splits env la in
  let classes = Uf.cl_extract uf in
  let env = { env with classes = classes } in
  let aux bol r1 r2 dep env eqs = function
    | None     -> env, eqs
    | Some hss ->
      Debug.assume bol r1 r2;
      if bol then
        add_eq hss (embed r1) (embed r2) dep env eqs
      else
        add_diseq hss (embed r1) (embed r2) dep env eqs
  in
  Debug.print_env env;
  let env, eqs =
    List.fold_left
      (fun (env,eqs) -> function
         | A.Eq(r1,r2), _, ex, _ ->
           (* needed for models generation because fresh terms are not
              added with function add *)
           let env = add_rec (add_rec env r1) r2 in
           aux true  r1 r2 ex env eqs (values_of r1)

         | A.Distinct(false, [r1;r2]), _, ex, _ ->
           (* needed for models generation because fresh terms are not
              added with function add *)
           let env = add_rec (add_rec env r1) r2 in
           aux false r1 r2 ex env eqs (values_of r1)

         | _ -> env, eqs

      ) (env,[]) la
  in
  env, { Sig_rel.assume = eqs; remove = [] }

let add env _ r _ = add_aux env r

let case_split env _ ~for_model =
  let acc = MX.fold
      (fun r (hss, _) acc ->
         let sz = HSS.cardinal hss in
         if sz = 1 then acc
         else match acc with
           | Some (n,_,_) when n <= sz -> acc
           | _ -> Some (sz, r, HSS.choose hss)
      ) env.mx None
  in
  match acc with
  | Some (n,r,hs) ->
    let n = Numbers.Q.from_int n in
    if for_model ||
       Numbers.Q.compare
         (Numbers.Q.mult n env.size_splits) (max_split ()) <= 0  ||
       Numbers.Q.sign  (max_split ()) < 0 then
      let r' = is_mine (Cons(hs,X.type_info r)) in
      Debug.case_split r r';
      [LR.mkv_eq r r', true, Th_util.CS(Th_util.Th_sum, n)]
    else []
  | None ->
    Debug.no_case_split ();
    []

let query env uf a_ex =
  try ignore(assume env uf [a_ex]); None
  with Ex.Inconsistent (expl, classes) -> Some (expl, classes)

let assume env uf la =
  if Options.timers() then
    try
      Timers.exec_timer_start Timers.M_Sum Timers.F_assume;
      let res =assume env uf la in
      Timers.exec_timer_pause Timers.M_Sum Timers.F_assume;
      res
    with e ->
      Timers.exec_timer_pause Timers.M_Sum Timers.F_assume;
      raise e
  else assume env uf la

let query env uf la =
  if Options.timers() then
    try
      Timers.exec_timer_start Timers.M_Sum Timers.F_query;
      let res = query env uf la  in
      Timers.exec_timer_pause Timers.M_Sum Timers.F_query;
      res
    with e ->
      Timers.exec_timer_pause Timers.M_Sum Timers.F_query;
      raise e
  else query env uf la


let print_model _ _ _ = ()

let new_terms _ = Expr.Set.empty

let instantiate ~do_syntactic_matching:_ _ env _ _  = env, []
let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Sum ->
    failwith "This Theory does not support theories extension"
  | _ -> t

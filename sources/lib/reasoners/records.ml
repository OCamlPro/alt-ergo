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

open Format
open Options
open Sig
module Hs = Hstring
module E = Expr


type 'a abstract =
  | Record of (Hs.t * 'a abstract) list * Ty.t
  | Access of Hs.t * 'a abstract * Ty.t
  | Other of 'a * Ty.t

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak (X : ALIEN) = struct

  module XS = Set.Make(struct type t = X.r let compare = X.hash_cmp end)

  let name = "records"

  type t = X.r abstract
  type r = X.r

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let rec print fmt = function
      | Record (lbs, _) ->
        fprintf fmt "{";
        let _ = List.fold_left
            (fun first (lb, e) ->
               fprintf fmt "%s%s = %a"
                 (if first then "" else "; ") (Hs.view lb) print e;
               false
            ) true lbs in
        fprintf fmt "}"
      | Access(a, e, _) ->
        fprintf fmt "%a.%s" print e (Hs.view a)
      | Other(t, _) -> X.print fmt t

  end
  (*BISECT-IGNORE-END*)

  let print = Debug.print

  let rec raw_compare r1 r2 =
    match r1, r2 with
    | Other (u1, ty1), Other (u2, ty2) ->
      let c = Ty.compare ty1 ty2 in
      if c <> 0 then c else X.str_cmp u1 u2
    | Other _, _ -> -1
    | _, Other _ -> 1
    | Access (s1, u1, ty1), Access (s2, u2, ty2) ->
      let c = Ty.compare ty1 ty2 in
      if c <> 0 then c
      else
        let c = Hs.compare s1 s2 in
        if c <> 0 then c
        else raw_compare u1 u2
    | Access _, _ -> -1
    | _, Access _ -> 1
    | Record (lbs1, ty1), Record (lbs2, ty2) ->
      let c = Ty.compare ty1 ty2 in
      if c <> 0 then c else raw_compare_list lbs1 lbs2

  and raw_compare_list l1 l2 =
    match l1, l2 with
    | [], [] -> 0
    | [], _ -> 1
    | _, [] -> -1
    | (_, x1)::l1, (_, x2)::l2 ->
      let c = raw_compare x1 x2 in
      if c<>0 then c else raw_compare_list l1 l2

  let rec normalize v =
    match v with
    | Record (lbs, ty) ->
      begin
        let lbs_n = List.map (fun (lb, x) -> lb, normalize x) lbs in
        match lbs_n with
        | (lb1, Access(lb2, x, _)) :: l when Hs.equal lb1 lb2 ->
          if List.for_all
              (function
                | (lb1, Access(lb2, y, _)) ->
                  Hs.equal lb1 lb2 && raw_compare x y = 0
                | _ -> false) l
          then x
          else Record (lbs_n, ty)
        | _ -> Record (lbs_n, ty)
      end
    | Access (a, x, ty) ->
      begin
        match normalize x with
        | Record (lbs, _) -> Hs.list_assoc a lbs
        | x_n -> Access (a, x_n, ty)
      end
    | Other _ -> v

  let embed r =
    match X.extract r with
    | Some p -> p
    | None -> Other(r, X.type_info r)

  let compare_mine t u = raw_compare (normalize t) (normalize u)

  let compare x y = compare_mine (embed x) (embed y)

  let rec equal r1 r2 =
    match r1, r2 with
    | Other (u1, ty1), Other (u2, ty2) ->
      Ty.equal ty1 ty2 && X.equal u1 u2

    | Access (s1, u1, ty1), Access (s2, u2, ty2) ->
      Hs.equal s1 s2 && Ty.equal ty1 ty2 && equal u1 u2

    | Record (lbs1, ty1), Record (lbs2, ty2) ->
      Ty.equal ty1 ty2 && equal_list lbs1 lbs2

    | Other _, _ | _, Other _  | Access _, _ | _, Access _ -> false

  and equal_list l1 l2 =
    try List.for_all2 (fun (_,r1) (_,r2) -> equal r1 r2) l1 l2
    with Invalid_argument _ -> false

  let is_mine t =
    match normalize t with
    | Other(r, _) -> r
    | x -> X.embed x

  let type_info = function
    | Record (_, ty) | Access (_, _, ty) | Other (_, ty) -> ty

  let make t =
    let rec make_rec t ctx =
      let { E.f; xs; ty; _ } =
        match E.term_view t with
        | E.Not_a_term _ -> assert false
        | E.Term tt -> tt
      in
      match f, ty with
      | Symbols.Op (Symbols.Record), Ty.Trecord { Ty.lbs; _ } ->
        assert (List.length xs = List.length lbs);
        let l, ctx =
          List.fold_right2
            (fun x (lb, _) (l, ctx) ->
               let r, ctx = make_rec x ctx in
               let tyr = type_info r in
               let dlb = E.mk_term (Symbols.Op (Symbols.Access lb)) [t] tyr in
               let c = E.mk_eq ~iff:false dlb x in
               (lb, r)::l, c::ctx
            )
            xs lbs ([], ctx)
        in
        Record (l, ty), ctx
      | Symbols.Op (Symbols.Access a), _ ->
        begin
          match xs with
          | [x] ->
            let r, ctx = make_rec x ctx in
            Access (a, r, ty), ctx
          | _ -> assert false
        end

      | _, _ ->
        let r, ctx' = X.make t in
        Other (r, ty), ctx'@ctx
    in
    let r, ctx = make_rec t [] in
    let is_m = is_mine r in
    is_m, ctx

  let color _ = assert false

  let embed r =
    match X.extract r with
    | Some p -> p
    | None -> Other(r, X.type_info r)

  let xs_of_list = List.fold_left (fun s x -> XS.add x s) XS.empty

  let leaves t =
    let rec leaves t =
      match normalize t with
      | Record (lbs, _) ->
        List.fold_left (fun s (_, x) -> XS.union (leaves x) s) XS.empty lbs
      | Access (_, x, _) -> leaves x
      | Other (x, _) -> xs_of_list (X.leaves x)
    in
    XS.elements (leaves t)

  let rec hash  = function
    | Record (lbs, ty) ->
      List.fold_left
        (fun h (lb, x) -> 17 * hash x + 13 * Hs.hash lb + h)
        (Ty.hash ty) lbs
    | Access (a, x, ty) ->
      19 * hash x + 17 * Hs.hash a + Ty.hash ty
    | Other (x, ty) ->
      Ty.hash ty + 23 * X.hash x

  let rec subst_rec p v r =
    match r with
    | Other (t, _) ->
      embed (if X.equal p t then v else X.subst p v t)
    | Access (a, t, ty) ->
      Access (a, subst_rec p v t, ty)
    | Record (lbs, ty) ->
      let lbs = List.map (fun (lb, t) -> lb, subst_rec p v t) lbs in
      Record (lbs, ty)

  let subst p v r = is_mine (subst_rec p v r)

  let is_mine_symb sy _ty = match sy with
    | Symbols.Op (Symbols.Record | Symbols.Access _) -> true
    | _ -> false

  let abstract_access field e ty acc =
    let xe = is_mine e in
    let abs_right_xe, acc =
      try List.assoc xe acc, acc
      with Not_found ->
        let left_abs_xe2, acc = X.abstract_selectors xe acc in
        match X.type_info left_abs_xe2 with
        | (Ty.Trecord { Ty.lbs; _ }) as tyr ->
          let flds =
            List.map
              (fun (lb,ty) -> lb, embed (X.term_embed (E.fresh_name ty))) lbs
          in
          let record = is_mine (Record (flds, tyr)) in
          record, (left_abs_xe2, record) :: acc
        | _ -> assert false
    in
    let abs_access = normalize (Access (field, embed abs_right_xe, ty)) in
    is_mine abs_access, acc

  let abstract_selectors v acc =
    match v with
    (* Handled by combine. Should not happen! *)
    | Other _ -> assert false

    (* This is not a selector *)
    | Record (fields,ty) ->
      let flds, acc =
        List.fold_left
          (fun (flds,acc) (lbl,e) ->
             let e, acc = X.abstract_selectors (is_mine e) acc in
             (lbl, embed e)::flds, acc
          )([], acc) fields
          [@ocaml.ppwarning "TODO: should not rebuild if not changed !"]
      in
      is_mine (Record (List.rev flds, ty)), acc

    (* Selector ! Interesting case !*)
    | Access (field, e, ty) -> abstract_access field e ty acc


  (* Shostak'pair solver adapted to records *)

  (* unused --
     let mk_fresh_record x info =
     let ty = type_info x in
     let lbs = match ty with Ty.Trecord r -> r.Ty.lbs | _ -> assert false in
     let lbs =
      List.map
        (fun (lb, ty) ->
           match info with
           | Some (a, v) when Hs.equal lb a -> lb, v
           | _ -> let n = embed (X.term_embed (E.fresh_name ty)) in lb, n)
        lbs
     in
     Record (lbs, ty), lbs
  *)

  (* unused --
     let rec occurs x = function
     | Record (lbs, _) ->
      List.exists (fun (_, v) -> occurs x v) lbs
     | Access (_, v, _) -> occurs x v
     | Other _ as v -> compare_mine x v = 0 (* XXX *)
  *)

  (* unused --
     let rec subst_access x s e =
     match e with
     | Record (lbs, ty) ->
      Record (List.map (fun (n,e') -> n, subst_access x s e') lbs, ty)
     | Access (lb, e', _) when compare_mine x e' = 0 ->
      Hs.list_assoc lb s
     | Access (lb', e', ty) -> Access (lb', subst_access x s e', ty)
     | Other _ -> e
  *)

  let fully_interpreted _ = false

  let rec term_extract r =
    match X.extract r with
    | Some v -> begin match v with
        | Record (lbs, ty) ->
          begin
            try
              let lbs =
                List.map
                  (fun (_, r) ->
                     match term_extract (is_mine r) with
                     | None, _ -> raise Not_found
                     | Some t, _ -> t)
                  lbs
              in
              Some (E.mk_term (Symbols.Op Symbols.Record) lbs ty), false
            with Not_found -> None, false
          end
        | Access (a, r, ty) ->
          begin
            match X.term_extract (is_mine r) with
            | None, _ -> None, false
            | Some t, _ ->
              Some (E.mk_term (Symbols.Op (Symbols.Access a)) [t] ty), false
          end
        | Other (r, _) -> X.term_extract r
      end
    | None -> X.term_extract r


  let orient_solved p v pb =
    if List.mem p (X.leaves v) then raise Util.Unsolvable;
    { pb with sbt = (p,v) :: pb.sbt }

  let solve r1 r2 pb =
    match embed r1, embed r2 with
    | Record (l1, _), Record (l2, _) ->
      let eqs =
        List.fold_left2
          (fun eqs (a,b) (x,y) ->
             assert (Hs.compare a x = 0);
             (is_mine y, is_mine b) :: eqs
          )pb.eqs l1 l2
      in
      {pb with eqs=eqs}

    | Other _, Other _    ->
      if X.str_cmp r1 r2 > 0 then { pb with sbt = (r1,r2)::pb.sbt }
      else { pb with sbt = (r2,r1)::pb.sbt }

    | Other _, Record _  -> orient_solved r1 r2 pb
    | Record _, Other _  -> orient_solved r2 r1 pb
    | Access _ , _ -> assert false
    | _ , Access _ -> assert false

  let make t =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Records Timers.F_make;
        let res = make t in
        Timers.exec_timer_pause Timers.M_Records Timers.F_make;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Records Timers.F_make;
        raise e
    else make t

  let solve r1 r2 pb =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Records Timers.F_solve;
        let res = solve r1 r2 pb in
        Timers.exec_timer_pause Timers.M_Records Timers.F_solve;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Records Timers.F_solve;
        raise e
    else solve r1 r2 pb

  let assign_value t _ eq =
    match embed t with
    | Access _ -> None

    | Record (_, ty) ->
      if List.exists (fun (t,_) -> (Expr.depth t) = 1) eq
      then None
      else Some (Expr.fresh_name ty, false)

    | Other (_,ty) ->
      match ty with
      | Ty.Trecord { Ty.lbs; _ } ->
        let rev_lbs = List.rev_map (fun (_, ty) -> Expr.fresh_name ty) lbs in
        let s = E.mk_term (Symbols.Op Symbols.Record) (List.rev rev_lbs) ty in
        Some (s, false) (* false <-> not a case-split *)
      | _ -> assert false

  let choose_adequate_model _ _ l =
    let acc =
      List.fold_left
        (fun acc (s, r) ->
           if (Expr.depth s) <> 1 then acc
           else
             match acc with
             | Some(s', _) when Expr.compare s' s > 0 -> acc
             | _ -> Some (s, r)
        ) None l
    in
    match acc with
    | Some (_,r) ->
      ignore (flush_str_formatter ());
      fprintf str_formatter "%a" X.print r; (* it's a EUF constant *)
      r, flush_str_formatter ()
    | _ -> assert false

end


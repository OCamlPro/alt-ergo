(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Options
open Format

module Ex = Explanation
module F = Formula
module MF = F.Map
module Sy = Symbols
module MS = Sy.Map


module EM = Instances.EM
module Hs = Hstring
module MH = Hs.Map
module T = Term

type t = {
  lems_track :
    ((F.quantified * Sy.t MS.t * Ex.t) list) MF.t;
}

let empty = {
  lems_track = MF.empty
}

type status =
  | Ok of { hs : Hs.t; t : Term.t; is_neg : bool; is_grd : bool; ex : Ex.t }
  | Ignore
  | Fail

type info =
  {term : Term.t;
   ex : Explanation.t;
   form : F.t;
   lems : (F.quantified * Sy.t MS.t * Ex.t) list;
  }

let mk_gf f name mf gf =
  { F.f = f;
    origin_name = name;
    gdist = -1;
    hdist = -1;
    nb_reductions = 0;
    trigger_depth = max_int;
    age= 0;
    lem= None;
    from_terms = [];
    mf= mf;
    gf= gf;
    theory_elim = true; }

exception Not_sat of t

let match_term env pp tt inst tbox sols check_unsat known_inst =
  (* XXX : TODO : Check that E-matching is activated and that, we only have
     uninterpreted equality. Ie. no arith symbols ... to say SAT *)
  if debug_sat () then
    fprintf fmt "match_term: %a vs %a@."
      Term.print pp.term Term.print tt.term;
  match EM.match_one_term inst tbox pp.term tt.term with
  | [] -> ()
  | l ->
    (*if not check_unsat then raise (Not_sat env);*)
    let res =
      List.fold_left
        (fun acc {Matching_types.sbs ; sty} ->
           List.fold_left
             (fun acc (q, renaming, ex) ->
                if debug_sat () then
                  fprintf fmt "main = %a@." F.print q.F.main;
                let sbs =
                  Term.Subst.fold
                    (fun k t acc ->
                       try
                         let sy = MS.find k renaming in
                         Term.Subst.add sy t acc
                       with Not_found ->
                         assert (not (MS.mem k q.F.binders));
                         acc
                    )sbs Term.Subst.empty
                in
                let sbt = sbs, sty in
                let m = F.apply_subst sbt q.F.main in
                if debug_sat () then begin
                  fprintf fmt "m  = %a@." F.print m;
                  fprintf fmt "sbt = %a@."
                    (Term.Subst.print Term.print) sbs;
                end;
                if F.equal m q.F.main then
                  acc (*what to do ?*)
                else
                  let triggers =
                    List.rev_map (F.apply_subst_trigger sbt)
                      (List.rev q.F.triggers)
                  in (* [] *)
                  (*test disabling triggers for reso. instances ? *)
                  let g =
                    F.mk_forall
                      q.F.name q.F.loc q.F.binders triggers m 0 None
                  in
                  if known_inst g then acc
                  else begin
                    if debug_sat () then
                      fprintf fmt "inst %a@." F.print g;
                    (mk_gf g q.F.name true false, ex) :: acc
                  end
             )acc pp.lems
        )!sols l
    in
    (*if debug_sat () then
      fprintf fmt "PB is UNK 1 (match %a against %a)@."
        Term.print pp.term Term.print tt.term;
      if debug_sat () then fprintf fmt "correct ? @.";*)
    if not check_unsat && res != [] then raise (Not_sat env);
    sols := res

let extract_pred f ex =
  match F.view f with
  | F.Literal a ->
    begin match Literal.LT.view a, Literal.LT.is_ground a with
      | Literal.Pred(t, is_neg), is_grd ->
        begin match T.view t with
          (* should we exclude bool vars ? and fail ?*)
          | {T.f = Sy.Name(hs, _)} -> Ok { hs; t; is_neg; is_grd; ex}
          | _ -> if is_grd then Ignore else Fail
        end
      | _, is_grd -> if is_grd then Ignore else Fail
    end
  | _ -> Ignore

let literals_of_gamma env gamma check_unsat =
  MF.fold
    (fun f (gf,ex,_,_) acc ->
       match extract_pred f ex with
       | Ignore ->
         acc

       | Fail ->
         if check_unsat then acc
         else begin
           if debug_sat () then
             fprintf fmt "PB is UNK 2 (unsupported pred %a)@."
               F.print f;
           raise (Not_sat env)
         end

       | Ok { hs; t; is_neg; is_grd; ex } ->
         let pos_g, pos_n, neg_g, neg_n =
           try MH.find hs acc with Not_found -> [], [], [], []
         in
         let lems = try MF.find f env.lems_track with Not_found -> [] in
         if debug_sat () then
           fprintf fmt "%d lems for %a@." (List.length lems) F.print f;
         let e = { term = t; form =f; ex; lems } in
         let hs_acc = match is_neg, is_grd with
           | false, true  -> e::pos_g, pos_n, neg_g, neg_n
           | false, false -> pos_g, e::pos_n, neg_g, neg_n
           | true , true  -> pos_g, pos_n, e::neg_g, neg_n
           | true , false -> pos_g, pos_n, neg_g, e::neg_n
         in
         MH.add hs hs_acc acc
    ) gamma MH.empty

let no_common_vars {term=p} {term=t} =
  let vp = T.vars_of p MS.empty in
  let vt = T.vars_of t MS.empty in
  let res = MS.for_all (fun sy _ -> not (MS.mem sy vp)) vt
  in
  (*fprintf fmt "NCV = %b@." res;*)
  res


let check_if_sat env gamma tbox inst ~check_unsat known_inst =
  let mh = literals_of_gamma env gamma check_unsat in
  (*let tbox = Th.get_case_split_env env.tbox in*)
  (*let inst = Inst.matching_env env.inst in*)
  let sols = ref [] in
  if debug_sat () then
    fprintf fmt "[check_if_sat] %d hs to consider@." (MH.cardinal mh);
  MH.iter
    (fun hs (pos_g, pos_n, neg_g, neg_n) ->
       if debug_sat () then begin
         fprintf fmt "hs = %s has:@." (Hs.view hs);
         fprintf fmt "   %d pos_g@." (List.length pos_g);
         fprintf fmt "   %d pos_n@." (List.length pos_n);
         fprintf fmt "   %d neg_g@." (List.length neg_g);
         fprintf fmt "   %d neg_n@." (List.length neg_n);
       end;
       match pos_g, pos_n, neg_g, neg_n with
       | [], [], _, _ | _, _, [], [] | _, [], _, [] ->
         if debug_sat () then
           fprintf fmt "for hs = %s : sat 1@." (Hs.view hs)

       | _, [], _, _ ->
         List.iter
           (fun p ->
              List.iter (fun t ->
                  match_term env p t inst tbox sols check_unsat known_inst)
                pos_g)
           neg_n;
         if debug_sat () then
           fprintf fmt "for hs = %s : sat 2@." (Hs.view hs);


       | _, _, _, [] ->
         List.iter
           (fun p ->
              List.iter (fun t ->
                  match_term env p t inst tbox sols check_unsat known_inst)
                neg_g)
           pos_n;
         if debug_sat () then
           fprintf fmt "for hs = %s : sat 3@." (Hs.view hs);

       | _ ->
         (* should do better for nground vs nground *)
         if check_unsat then ()
         else begin
           if debug_sat () then
             fprintf fmt "PB is UNK 3 (hs = %s)@." (Hs.view hs);
           raise (Not_sat env)
         end
    )mh;
  begin
    if debug_sat () then
      if !sols == [] then
        fprintf fmt "PB is SAT@."
      else
        fprintf fmt "PB generated %d instances@." (List.length !sols);
  end;
  !sols

let check_if_unsat env gamma tbox inst known_inst =
  let check_unsat = true in
  let mh = literals_of_gamma env gamma check_unsat in
  (*let tbox = Th.get_case_split_env env.tbox in
    let inst = Inst.matching_env env.inst in*)
  let sols = ref [] in
  if debug_sat () then
    fprintf fmt "[check_if_unsat] %d hs to consider@." (MH.cardinal mh);
  MH.iter
    (fun hs (pos_g, pos_n, neg_g, neg_n) ->
       if debug_sat () then begin
         fprintf fmt "hs = %s has:@." (Hs.view hs);
         fprintf fmt "   %d pos_g@." (List.length pos_g);
         fprintf fmt "   %d pos_n@." (List.length pos_n);
         fprintf fmt "   %d neg_g@." (List.length neg_g);
         fprintf fmt "   %d neg_n@." (List.length neg_n);
       end;

       (* pos_n vs neg_n x 2 *)
       (* to be tested : may be not efficient *)
       if Options.enable_inst_gen () = 2 then
         List.iter
           (fun p ->
              List.iter (fun t ->
                  if no_common_vars p t then begin
                    match_term env p t inst tbox sols check_unsat known_inst;
                    match_term env t p inst tbox sols check_unsat known_inst
                  end
                )
                pos_n)
           neg_n;

       if Options.enable_inst_gen () = 1 || Options.enable_inst_gen () = 2 then
         begin
           (* pos_g vs neg_n *)
           List.iter
             (fun p ->
                List.iter (fun t ->
                    match_term env p t inst tbox sols check_unsat known_inst)
                  pos_g)
             neg_n;

           (* neg_g vs pos_n *)
           List.iter
             (fun p ->
                List.iter (fun t ->
                    match_term env p t inst tbox sols check_unsat known_inst)
                  neg_g)
             pos_n;
         end
    )mh;
  if debug_sat () then
    fprintf fmt "[check_if_unsat] PB generated %d instances@."
      (List.length !sols);
  !sols


let resolution env gamma tbox inst known_inst =
  let inst_gen = Options.enable_inst_gen () in
  if inst_gen <> 1 && inst_gen <> 2 then []
  else
    try check_if_unsat env gamma tbox inst known_inst
    with
    | Util.Timeout as e -> raise e
    | e ->
      fprintf fmt "%s@." (Printexc.to_string e);
      assert false


let add_lems_track env xxx q renaming ex =
  let l = try MF.find xxx env.lems_track with Not_found -> [] in
  {(*env with*)
    lems_track = MF.add xxx ((q, renaming, ex) :: l) env.lems_track}

let update_lems_track f l env =
  try
    let parent = MF.find f env.lems_track in
    let lems_track =
      List.fold_left
        (fun lems_track g -> MF.add g parent lems_track)
        env.lems_track l
    in
    Some {(*env with*) lems_track}
  with Not_found -> None

let renamed_vars {F.main; binders} =
  let renaming = ref Symbols.Map.empty in
  let sbt =
    Symbols.Map.fold
      (fun sy (ty, _) sbt ->
         let k = Symbols.var (Hstring.fresh_string()) in
         let t = Term.make k [] ty in
         renaming := Symbols.Map.add k sy !renaming;
         Symbols.Map.add sy t sbt

      )binders Symbols.Map.empty
  in
  let res = F.apply_subst (sbt, Ty.esubst) main in
  if debug_sat () then
    fprintf fmt "renamed vars of:@.%a@.@.is@.@.%a@.@."
      F.print main F.print res;
  res, !renaming


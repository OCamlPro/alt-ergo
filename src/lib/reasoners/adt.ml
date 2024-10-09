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

module Sy = Symbols
module E  = Expr

open Alias.Dolmen

let src = Logs.Src.create ~doc:"Adt" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

type 'a abstract =
  | Constr of {
      c_name : DE.term_cst;
      c_ty : Ty.t;
      c_args : (DE.term_cst * 'a) list
    }
  (* [Cons { c_name; c_ty; c_args }] reprensents the application of the
     constructor [c_name] of the ADT [ty] with the arguments [c_args]. *)

  | Select of { d_name : DE.term_cst ; d_ty : Ty.t ; d_arg : 'a }
  (* [Select { d_name; d_ty; d_arg }] represents the destructor [d_name] of
     the ADT [d_ty] on the ADT value [d_arg]. *)

  | Alien of 'a
  (* [Alien r] represents a uninterpreted ADT semantic value. *)

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end


(* TODO: can this function be replace with Ty.assoc_destrs ?? *)
let constr_of_destr ty dest =
  if Options.get_debug_adt () then
    Printer.print_dbg
      ~module_name:"Adt" ~function_name:"constr_of_destr"
      "ty = %a" Ty.print ty;
  match ty with
  | Ty.Tadt (s, params) ->
    begin
      let cases = Ty.type_body s params in
      try
        List.find
          (fun { Ty.destrs; _ } ->
             List.exists (fun (d, _) -> DE.Term.Const.equal dest d) destrs
          ) cases
      with Not_found -> assert false (* invariant *)
    end
  | _ -> assert false


module Shostak (X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  module SX = Set.Make(struct type t = r let compare = X.hash_cmp end)

  let name = "Adt"

  let timer = Timers.M_Adt

  [@@ocaml.ppwarning "XXX: IsConstr not interpreted currently. Maybe \
                      it's OK"]
  let is_mine_symb sy =
    not (Options.get_disable_adts ()) &&
    match sy with
    | Sy.Op Sy.Constr _ -> true
    | Sy.Op Sy.Destruct _ ->
      (* A destructor is partially interpreted by the ADT theory.
         If we assume the tester of the constructor associated with
         this destructor, we propagate the non-guarded version of the
         destructor. See the documentation of [env.selectors] in [Adt_rel]. *)
      false
    | _ -> false

  let embed r =
    match X.extract r with
    | Some c -> c
    | None -> Alien r

  let pp_field ppf (lbl, v) =
    Fmt.pf ppf "%a : %a" DE.Term.Const.print lbl X.print v

  let print ppf = function
    | Alien x ->
      X.print ppf x

    | Constr { c_name; c_args; _ } ->
      Fmt.pf ppf "%a@[(%a@])"
        DE.Term.Const.print c_name
        Fmt.(list ~sep:semi pp_field) c_args

    | Select d ->
      Fmt.pf ppf "%a#!!%a" X.print d.d_arg DE.Term.Const.print d.d_name


  let is_mine u =
    match u with
    | Alien r -> r
    | Constr _ ->
      X.embed u
      [@ocaml.ppwarning "TODO: canonize Constr(list of selects)"]

    | Select { d_arg; d_name; _ } ->
      match embed d_arg with
      | Constr c ->
        begin
          try snd @@ List.find
              (fun (lbl, _) -> DE.Term.Const.equal d_name lbl) c.c_args
          with Not_found ->
            Printer.print_err "is_mine %a failed" print u;
            assert false
        end
      | _ -> X.embed u

  let equal s1 s2 =
    match s1, s2 with
    | Alien r1, Alien r2 -> X.equal r1 r2
    | Constr c1, Constr c2 ->
      DE.Term.Const.equal c1.c_name c2.c_name &&
      Ty.equal c1.c_ty c2.c_ty &&
      begin
        try
          List.iter2
            (fun (hs1, v1) (hs2, v2) ->
               assert (DE.Term.Const.equal hs1 hs2);
               if not (X.equal v1 v2) then raise Exit
            ) c1.c_args c2.c_args;
          true
        with
        | Exit -> false
        | _ -> assert false
      end

    | Select d1, Select d2 ->
      DE.Term.Const.equal d1.d_name d2.d_name &&
      Ty.equal d1.d_ty d2.d_ty &&
      X.equal d1.d_arg d2.d_arg

    | _ -> false

  let make t =
    assert (not @@ Options.get_disable_adts ());
    if Options.get_debug_adt () then
      Printer.print_dbg
        ~module_name:"Adt" ~function_name:"make"
        "make %a" E.print t;
    let { E.f; xs; ty; _ } = E.term_view t in
    let sx, ctx =
      List.fold_left
        (fun (args, ctx) s ->
           let rs, ctx' = X.make s in
           rs :: args, List.rev_append ctx' ctx
        )([], []) xs
    in
    let xs = List.rev sx in
    match f, xs, ty with
    | Sy.Op Sy.Constr hs, _, Ty.Tadt (name, params) ->
      let cases = Ty.type_body name params in
      let case_hs =
        try Ty.assoc_destrs hs cases with Not_found -> assert false
      in
      let c_args =
        try
          List.rev @@
          List.fold_left2
            (fun c_args v (lbl, _) -> (lbl, v) :: c_args)
            [] xs case_hs
        with Invalid_argument _ -> assert false
      in
      is_mine @@ Constr {c_name = hs; c_ty = ty; c_args}, ctx

    | Sy.Op Sy.Destruct _, [_], _ -> X.term_embed t, ctx
    (* No risk !
         if equal sel (embed sel_x) then X.term_embed t, ctx
         else sel_x, ctx (* canonization OK *)
    *)

    | Sy.Op Sy.Constr _, _, Ty.Trecord _ ->
      Fmt.failwith "unexpected record constructor %a@." E.print t

    | _ -> assert false

  let hash x =
    abs @@ match x with
    | Alien r ->
      X.hash r

    | Constr { c_name ; c_ty ; c_args } ->
      List.fold_left
        (fun acc (_, r) -> acc * 7 + X.hash r)
        (DE.Term.Const.hash c_name + 7 * Ty.hash c_ty) c_args

    | Select { d_name ; d_ty ; d_arg } ->
      ((DE.Term.Const.hash d_name + 11 * Ty.hash d_ty)) * 11 + X.hash d_arg

  let leaves r =
    match r with
    | Alien r | Select { d_arg = r; _ } ->
      X.leaves r

    | Constr { c_args; _ } ->
      SX.elements @@
      List.fold_left
        (fun sx (_, r) ->
           List.fold_left (fun sx x -> SX.add x sx) sx (X.leaves r)
        )
        SX.empty c_args

  let is_constant r =
    match r with
    | Alien r | Select { d_arg = r; _ } ->
      X.is_constant r

    | Constr { c_args; _ } ->
      List.for_all (fun (_, r) -> X.is_constant r) c_args

  [@@ocaml.ppwarning "TODO: not sure"]
  let fully_interpreted _ =
    false (* not sure *)
(*
    not (get_disable_adts ()) &&
    match sb with
    | Sy.Op (Sy.Constr _) -> true
    | Sy.Op Sy.Destruct (_, guarded) -> not guarded
    | _ -> false
*)

  let type_info = function
    | Alien r -> X.type_info r
    | Constr { c_ty ; _ } ->  c_ty
    | Select { d_ty  ; _ } -> d_ty

  let compare s1 s2 =
    match embed s1, embed s2 with
    | Alien r1, Alien r2 -> X.str_cmp r1 r2
    | Alien _, _ -> 1
    | _, Alien _ -> -1

    | Constr c1, Constr c2 ->
      let c = DE.Term.Const.compare c1.c_name c2.c_name in
      if c <> 0 then c
      else
        let c = Ty.compare c1.c_ty c2.c_ty in
        if c <> 0 then c
        else
          begin
            try
              List.iter2
                (fun (hs1, v1) (hs2, v2) ->
                   assert (DE.Term.Const.equal hs1 hs2);
                   let c = X.str_cmp v1 v2 in
                   if c <> 0 then raise (Util.Cmp c);
                )c1.c_args c2.c_args;
              0
            with
            | Util.Cmp c -> c
            | _ -> assert false
          end
    | Constr _, _ -> 1
    | _, Constr _ -> -1

    | Select d1, Select d2 ->
      let c = DE.Term.Const.compare d1.d_name d2.d_name in
      if c <> 0 then c
      else
        let c = Ty.compare d1.d_ty d2.d_ty in
        if c <> 0 then c
        else X.str_cmp d1.d_arg d2.d_arg

  let abstract_selectors p acc =
    match p with
    | Alien _ -> assert false (* handled in Combine *)
    | Constr { c_args; _ } ->
      let same = ref true in
      let acc, _ =
        List.fold_left (fun (acc, l) (lbl, x) ->
            let y, acc = X.abstract_selectors x acc in
            same := !same && x == y;
            acc, (lbl, y) :: l
          ) (acc, []) c_args
      in
      if !same then is_mine p, acc
      else
        is_mine p, acc
        [@ocaml.ppwarning "TODO: abstract Selectors: case to test"]
    (* assert false
       should probably reconstruct a new 'p' using args
    *)

    | Select ({ d_arg; _ } as s)
      [@ocaml.ppwarning "TODO: abstract Selectors"] ->
      (* no need to abstract THIS selector. It's necessiraly
         toplevel in ADTs *)
      (*
         /!\ All this is not clear ! should review this code ==>
         Keep in mind that this is a non guarded select; the only one that
         is interpreted
      *)
      let s_arg, acc = X.abstract_selectors d_arg acc in
      if not (X.equal s_arg d_arg)
         [@ocaml.ppwarning "TODO: abstract Selectors"] then
        assert false;
      let x = is_mine @@ Select {s with d_arg=s_arg} in
      begin match embed x  with
        | Select ({ d_name; d_arg; _ } as s) ->
          let {Ty.constr ; destrs} =
            constr_of_destr (X.type_info d_arg) d_name
          in
          let xs = List.map (fun (_, ty) -> E.fresh_name ty) destrs in
          let cons =
            E.mk_term (Sy.constr constr) xs (X.type_info d_arg)
          in
          if Options.get_debug_adt () then
            Printer.print_dbg ~flushed:false
              ~module_name:"Adt" ~function_name:"abstract_selectors"
              "abstr with equality %a == %a@ "
              X.print d_arg E.print cons;
          let cons, _ = make cons in
          let acc = (d_arg, cons) :: acc in
          let xx = is_mine @@ Select {s with d_arg = cons} in
          if Options.get_debug_adt () then
            Printer.print_dbg ~header:false
              "%a becomes %a" X.print x  X.print xx;
          xx, acc

        | _ ->
          x, acc

      end

  let is_alien_of e x =
    List.exists (fun y -> X.equal x y) (X.leaves e)

  let solve r1 r2 pb =
    if Options.get_debug_adt () then
      Printer.print_dbg
        ~module_name:"Adt" ~function_name:"solve"
        "solve %a = %a" X.print r1 X.print r2;
    assert (not @@ Options.get_disable_adts ());
    match embed r1, embed r2 with
    | Select _, _ | _, Select _ -> assert false (* should be eliminated *)
    | Alien _, Alien _ ->
      Sig.{ pb with
            sbt = (if X.str_cmp r1 r2 > 0 then r1, r2 else r2, r1) :: pb.sbt }

    | Alien r, Constr _ ->
      if is_alien_of r2 r then raise Util.Unsolvable;
      Sig.{ pb with sbt = (r, r2) :: pb.sbt }

    | Constr _, Alien r ->
      if is_alien_of r1 r then raise Util.Unsolvable;
      Sig.{ pb with sbt = (r, r1) :: pb.sbt }

    | Constr c1, Constr c2 ->
      if not (DE.Term.Const.equal c1.c_name c2.c_name) then
        raise Util.Unsolvable;
      try
        Sig.{pb with
             eqs =
               List.fold_left2
                 (fun eqs (hs1, v1) (hs2, v2) ->
                    assert (DE.Term.Const.equal hs1 hs2);
                    (v1, v2) :: eqs
                 )pb.eqs c1.c_args c2.c_args
            }
      with Invalid_argument _ -> assert false

  let subst p v s =
    (*TODO: detect when there are no changes to improve *)
    assert (not @@ Options.get_disable_adts ());
    match s with
    | Alien r -> if X.equal p r then v else X.subst p v r
    | Constr c ->
      is_mine @@
      Constr
        { c with
          c_args = List.map (fun (lbl, u) -> lbl, X.subst p v u) c.c_args }

    | Select d ->
      is_mine @@ Select { d with d_arg = X.subst p v d.d_arg }


  let color _        = assert false

  let term_extract _ = None, false


  let assign_value _ _ _ =
    (* Model generation is performed by the case-split mechanism
       in [Adt_rel]. *)
    None

  let to_model_term r =
    match embed r with
    | Constr { c_name; c_ty; c_args } ->
      let args =
        My_list.try_map (fun (_, arg) -> X.to_model_term arg) c_args
      in
      Option.bind args @@ fun args ->
      Some (E.mk_constr c_name args c_ty)

    | Select _ -> None
    | Alien a -> X.to_model_term a
end

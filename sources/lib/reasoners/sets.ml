(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

open Options
open Format
open Sig

type 'a abstract = unit

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak (X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name           = "Sets"
  let is_mine_symb _ = false
  let fully_interpreted sb = assert false
  let type_info _    = assert false
  let color _        = assert false
  let print _ _      = assert false
  let embed _        = assert false
  let is_mine _      = assert false
  let compare _ _    = assert false
  let equal _ _      = assert false
  let hash _         = assert false
  let leaves _       = assert false
  let subst _ _ _    = assert false
  let make _         = assert false
  let term_extract _ = None, false
  let abstract_selectors p acc = assert false
  let solve r1 r2 = assert false
  let assign_value r _ eq =
    assert false
(*
    if List.exists (fun (t,_) -> (Term.view t).Term.depth = 1) eq then None
    else
      match X.term_extract r with
      | Some t, true ->
        Some (Term.fresh_name (X.type_info r), false)
      | _ -> assert false
*)

  let choose_adequate_model t _ l =
    assert false
(*
    let acc =
      List.fold_left
        (fun acc (s, r) ->
          if (Term.view s).Term.depth <> 1 then acc
          else
            match acc with
            | Some(s', r') when Term.compare s' s > 0 -> acc
            | _ -> Some (s, r)
        ) None l
    in
    match acc with
    | Some (_, r) ->
      ignore (flush_str_formatter ());
      fprintf str_formatter "%a" X.print r; (* it's a EUF constant *)
      r, flush_str_formatter ()

    | _ -> assert false
*)
end


module Relation (X : ALIEN) (Uf : Uf.S) = struct
  type r = X.r
  type uf = Uf.t

  module T = Term
  module MapT = T.Map
  module SetT = T.Set
  module Hs = Hstring
  module Sy = Symbols
  module Ex = Explanation
  module A = Literal.LT

  type set_aux =
  | Empty
  | Alien  of T.t
  | Single of T.t
  | Union  of set list
  | Power of set
  (* nothing elses for the moment *)

  and set = { set : set_aux; ty : Ty.t; term : Term.t}

  type pred =
  | True
  | False
  | Mem of Term.t * set
  | Is_empty of set
  | Subset of set * set
  | Eq of set * set

  type set_class = EMPTY | ADD | UNION | POWER | OTHER
  type pred_class = MEM | SUBSET | EQ | IS_EMPTY | OTHER

  type t =
    {
      t_make : set MapT.t;
      p_make : pred MapT.t;
      uf : uf;
      newt : Term.Set.t;
    }

  let empty_uf = Uf.empty ()

  let empty _ =
    {
      t_make = MapT.empty;
      p_make = MapT.empty;
      uf = empty_uf;
      newt = Term.Set.empty
    }

  let is_set_type =
    let set = Hs.make "set" in
    fun ty ->
      match ty with
      | Ty.Text ([_], hs) -> Hs.equal set hs
      | _ -> false


  let rec compare_set (a:set) (b:set) =
    let c = Ty.compare a.ty b.ty in
    if c <> 0 then c
    else
      match a.set, b.set with
      | Empty, Empty -> 0
      | Empty, _ -> -1
      | _, Empty -> 1

      | Alien a, Alien b -> T.compare a b
      | Alien _, _ -> -1
      | _, Alien _ -> 1

      | Union a, Union b ->
        begin
          let tmp = ref 0 in
          try
            List.iter2
              (fun a b ->
                let c = compare_set a b in
                if c <> 0 then (tmp := c; raise Exit)
              ) a b;
            0
          with Invalid_argument _ -> List.length a - List.length b
          | Exit -> !tmp
        end
      | Union _, _ -> -1
      | _, Union _ -> 1

      | Single a, Single b -> T.compare a b
      | Single _, _ -> -1
      | _, Single _ -> 1
      | Power a, Power b -> compare_set a b

  module Sset = Set.Make(struct type t = set let compare = compare_set end)


  let class_of_set =
    let union = Hs.make "union" in
    let empty = Hs.make "empty" in
    let add   = Hs.make "add" in
    let power   = Hs.make "power" in
    fun hs ->
      if Hs.equal hs empty then EMPTY
      else if Hs.equal hs add then ADD
      else if Hs.equal hs union then UNION
      else if Hs.equal hs power then POWER
      else OTHER

  let class_of_pred =
    let mem = Hs.make "mem" in
    let subset = Hs.make "subset" in
    let is_empty = Hs.make "is_empty" in
    let eq   = Hs.make "infix_eqeq" in
    fun sy ->
      match sy with
      | Sy.Name(hs,_) ->
        if Hs.equal hs mem then MEM
        else if Hs.equal hs subset then SUBSET
        else if Hs.equal hs eq then EQ
        else if Hs.equal hs is_empty then IS_EMPTY
        else OTHER
      | _ -> OTHER

  let empty_set =
    let empty_hs = Sy.name "empty" in
    fun ty -> T.make empty_hs [] ty

  let normalize_union ty l t =
    let sset =
      List.fold_left
        (fun sset s ->
          if not (Ty.equal ty s.ty) then Sset.add s sset
          else
            match s.set with
            | Empty -> sset
            | Union l -> List.fold_right Sset.add l sset (* XXX *)
            | _ -> Sset.add s sset
        )Sset.empty l
    in
    match Sset.elements sset with
    | [] -> {set=Empty; ty; term = t}
    | [e] -> {e with term = t} (*XXX keep outer term to be correct*)
    | l  -> {set = Union l; ty; term = t}


  let normalize_power ty s t =
    match s.set with
    | Empty    -> {ty; set = Empty; term = t}
    | _ -> {ty; set = Power s; term = t}


  let rec make_set env t =
    try MapT.find t env.t_make
    with Not_found ->
      if false then fprintf fmt "  should make_set from %a@." T.print t;
      match T.view t with
        {T.f = Sy.Name(hs,_); xs; ty} ->
          begin match xs, class_of_set hs with
          | _    , OTHER -> {set = Alien t; ty; term = t}
          | []   , EMPTY -> {set = Empty; ty; term = t}
          | [_;_], UNION ->
            normalize_union ty (List.rev_map (make_set env) xs) t

          | [u]  , POWER -> normalize_power ty (make_set env u) t
          | [e;s], ADD ->
            normalize_union ty
              [{set = Single e; ty; term=e}; make_set env s] t
          | _ -> assert false
          end
      | {T.ty} -> {set = Alien t; ty; term = t}

  let rec has_single s =
    match s.set with
    | Empty -> false
    | Alien _ -> false
    | Power _ -> false (*!*)
    | Single e' -> true
    | Union l -> List.exists has_single l

  let rec mem_elt e s =
    match s.set with
    | Empty -> false
    | Power _ -> false (*!*)
    | Alien _ -> false
    | Single e' -> T.equal e e'
    | Union l -> List.exists (fun s -> mem_elt e s) l

  let rec mem_set e s =
    match s.set with
    | Empty -> false
    | Single _ -> false
    | Power _ -> false (*!*)
    | Alien e' -> T.equal e e'
    | Union l -> List.exists (fun s -> mem_elt e s) l

  let rec subset s1 s2 =
    match s1.set with
    | Empty -> true
    | Power _ -> false (*!*)
    | Single t -> mem_elt t s2
    | Alien s -> mem_set s s2
    | Union l -> List.for_all (fun z -> subset z s2) l

  let make_mem t e s_term env =
    assert (is_set_type (T.type_info s_term));
    let s = try MapT.find s_term env.t_make with Not_found -> assert false in
    let v =
      if s.set == Empty then False
      else
        if mem_elt e s then True
        else
          match s.set with
          | Union l ->
            let l =
              List.fold_left
                (fun acc x ->
                  match x.set with
                  | Single t ->
                    begin
                      match Uf.are_distinct env.uf e t with
                      | Yes (ex,_) when Ex.has_no_bj ex -> acc
                      | _ -> x :: acc
                    end
                  | Union _ -> assert false
                  | _ -> x :: acc
                )[] l
            in
            let s = normalize_union s.ty l s_term in
            if s.set == Empty then False
            else
              Mem (e, s)

          | Single t ->
            begin match Uf.are_distinct env.uf e t with
            | Yes (ex,_) when Ex.has_no_bj ex -> False
            | _ -> Mem (e, s)
            end
          | _ -> Mem (e, s)
    in
    {env with p_make = MapT.add t v env.p_make}

  let make_subset env t s1 s2 =
    assert (is_set_type (T.type_info s1));
    assert (is_set_type (T.type_info s2));
    let s1 = try MapT.find s1 env.t_make with Not_found -> assert false in
    let s2 = try MapT.find s2 env.t_make with Not_found -> assert false in
    let v =
      if compare_set s1 s2 = 0 then True
      else if subset s1 s2 then True
      else Subset(s1, s2)
    in
    {env with p_make = MapT.add t v env.p_make}


  let make_eqeq env t s1 s2 =
    assert (is_set_type (T.type_info s1));
    assert (is_set_type (T.type_info s2));
    let s1 = try MapT.find s1 env.t_make with Not_found -> assert false in
    let s2 = try MapT.find s2 env.t_make with Not_found -> assert false in
    let c = compare_set s1 s2 in
    let v =
      if c = 0 then True
      else if subset s1 s2 && subset s2 s1 then True
      else
        let s1, s2 = if c > 0 then s1, s2 else s2, s1 in
        Eq(s1, s2)
    in
    {env with p_make = MapT.add t v env.p_make}


  let make_is_empty env t s =
    assert (is_set_type (T.type_info s));
    let s = try MapT.find s env.t_make with Not_found -> assert false in
    let v =
      if s.set == Empty then True
      else
        if has_single s then False
        else Is_empty s
    in
    {env with p_make = MapT.add t v env.p_make}


  let make_pred env t f xs ty =
    match class_of_pred f, xs with
    | MEM, [e;s] -> make_mem t e s env

    | SUBSET, [s1;s2] -> make_subset env t s1 s2
    | EQ, [s1;s2] -> make_eqeq env t s1 s2

    | IS_EMPTY, [s] -> make_is_empty env t s

    | (MEM | SUBSET | EQ | IS_EMPTY), _ -> assert false
    | OTHER, _ -> env

  let add env uf r t =
    let env = {env with uf} in
    if MapT.mem t env.t_make || MapT.mem t env.p_make then env
    else
      let {T.f; xs; ty} = T.view t in
      if is_set_type ty then
        let () =
          if false then fprintf fmt "@.add set type %a@." T.print t
        in
        {env with t_make = MapT.add t (make_set env t) env.t_make}
      else
        if ty == Ty.Tbool then
          let () =
            if false then fprintf fmt "@.add bool %a@." T.print t
          in
          make_pred env t f xs ty
        else
          env

  let verb = 0

  let rec print_set fmt s =
    match s.set with
    | Empty -> fprintf fmt "Empty"
    | Alien s -> fprintf fmt "%a" T.print s
    | Single e -> fprintf fmt "{%a}" T.print e
    | Power e -> fprintf fmt "Power(%a)" print_set e
    | Union ([]|[_]) -> assert false
    | Union (e::l) ->
      fprintf fmt "(%a) " print_set e;
      List.iter (fprintf fmt "U (%a)" print_set) l

  let print_pred fmt p =
    match p with
    | True -> fprintf fmt "True"
    | False -> fprintf fmt "False"
    | Mem(e,s) -> fprintf fmt "Mem(%a, %a)" T.print e print_set s
    | Subset(s1,s2) -> fprintf fmt "Subset(%a, %a)" print_set s1 print_set s2
    | Eq(s1,s2) -> fprintf fmt "EqEq(%a, %a)" print_set s1 print_set s2
    | Is_empty s -> fprintf fmt "Is_Empty(%a)" print_set s

  let print_t_make env =
    fprintf fmt "@.[t_make]@.";
    MapT.iter
      (fun t set ->
        fprintf fmt "%a ~~> %a@." T.print t print_set set
      )env.t_make

  let print_p_make env =
    fprintf fmt "@.[p_make]@.";
    MapT.iter
      (fun t p ->
        fprintf fmt "%a ~~> %a@." T.print t print_pred p
      )env.p_make

  let print_env env =
    if verb >= 3 then begin
      fprintf fmt "@.=================================================";
      fprintf fmt "=================================================@.";
      print_t_make env;
      print_p_make env;
      fprintf fmt "@.=================================================";
      fprintf fmt "=================================================@.";
    end

  let mem_singleton v =
    match v with
    | Mem(e, s) ->
      begin
        match s.set with
        | Single e' -> Some (A.mk_eq e e')
        | _ -> None
      end
    | _ -> None

  let mem_sy = Sy.name "mem"
  let subset_sy = Sy.name "subset"
  let is_empty_sy = Sy.name "is_empty"

  let make_is_empty s =
    let t = Term.make is_empty_sy [s.term] Ty.Tbool in
    A.mk_pred t false


  let make_subset_pred newt s1 s2 =
    let t = T.make subset_sy [s1; s2] Ty.Tbool in
    newt := T.Set.add t !newt;
    A.mk_pred t false

  let deduce_not_mem_union newt e l expl asm =
    List.iter
      (fun x ->
        match x.set with
        | Union _ -> assert false
        | Empty -> assert false
        | Single e' ->
          let ded = A.neg (A.mk_eq e e') in
          asm :=  (LTerm ded, expl, Sig.Other) :: !asm
        | Alien _ | Power _ ->
          let x = x.term in (* XXX *)
          let pred = T.make mem_sy [e;x] Ty.Tbool in
          newt := T.Set.add pred !newt;
          let pred = A.mk_pred pred true in
          asm := (LTerm pred, expl, Sig.Other) :: !asm
      )l

  let deductions_from_assume newt env a expl p is_neg v asm =
    if verb >= 1 then
      fprintf fmt "assumed: %a ~~~~> %s(%a)@.@."
        A.print a (if is_neg then "not" else "") print_pred v;
    match v with
    | True  -> if is_neg then raise (Exception.Inconsistent (expl, []))
    | False -> if not is_neg then raise (Exception.Inconsistent (expl, []))

    (* MEM cases *)
    | Mem(e, {set = Single e'}) ->
      let eq = A.mk_eq e e' in
      let ded = if is_neg then A.neg eq else eq in
      asm := (LTerm ded, expl, Sig.Other) :: !asm

    | Mem(e, {set = Union l}) when is_neg ->
       deduce_not_mem_union newt e l expl asm

    | Mem(e, {set = Power j}) ->
      let p = make_subset_pred newt e j.term in
      let p = if is_neg then A.neg p else p in
      if verb >= 1 then fprintf fmt "deduce 1: %a@.@." A.print p;
      asm := (LTerm p, expl, Sig.Other) :: !asm

    | Mem (e, {set = Alien _}) -> ()

    (* Is_Empty cases *)
    | Is_empty ({set = Alien _}) -> ()

    (* EQ cases *)
    | Eq(s1, {set=Empty}) ->
      let p = make_is_empty s1 in
      let p = if is_neg then A.neg p else p in
      if verb >= 1 then fprintf fmt "deduce 2: %a@.@." A.print p;
      asm := (LTerm p, expl, Sig.Other) :: !asm


    | Eq(s1, s2) when not is_neg ->
      let p1 = make_subset_pred newt s1.term s2.term in
      let p2 = make_subset_pred newt s2.term s1.term in
      if verb >= 1 then fprintf fmt "deduce 2: %a@.@." A.print p1;
      if verb >= 1 then fprintf fmt "deduce 3: %a@.@." A.print p2;
      asm := (LTerm p2, expl, Sig.Other) :: (LTerm p1, expl, Sig.Other) :: !asm

    | Eq(s1, s2) when is_neg ->
      if compare_set s1 s2 = 0 then
        raise (Exception.Inconsistent (expl, []));
      if verb >= 1 then fprintf fmt "TODO deduce disjunction@.@.";

    | _ ->
      if verb >= 1 then fprintf fmt "next@."(*;
      assert false*)

  let assume env uf la =
    let env = {env with uf} in
    let new_t = ref env.newt in
    print_env env;
    let asm = ref [] in
    List.iter
      (fun (a, root, expl, orig) ->
        match root with
	| None -> ()
        | Some a ->
          match A.view a with
          | Literal.Eq _ | Literal.Builtin _ | Literal.Distinct _ -> ()
          | Literal.Pred(p, is_neg) ->
            try
              deductions_from_assume
                new_t env a expl p is_neg (MapT.find p env.p_make) asm
            with Not_found -> ()
      )la;
    let env = {env with newt = !new_t} in
    env, { assume = !asm; remove = []}

  let query env uf a_ex =
    try ignore (assume env uf [a_ex]);
        Sig.No
    with Exception.Inconsistent (ex, c) ->
      if verb >= 1 then fprintf fmt "query returned yes@.";
      Yes (ex, c)

  let case_split env _ ~for_model = []
  let print_model _ _ _ = ()
  let new_terms env = env.newt

  let instantiate ~do_syntactic_matching _ env uf _ = env, []
  let retrieve_used_context _ _ = [], []

  let assume_th_elt t th_elt = t
end

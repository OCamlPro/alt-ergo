(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) 2013-2023 --- OCamlPro SAS                                  *)
(*                                                                            *)
(*  This file is distributed under the terms of the OCamlPro Non-Commercial   *)
(*  License version 2.0                                                       *)
(*                                                                            *)
(*  AS AN EXCEPTION, Gold members of the Alt-Ergo's Club can distribute this  *)
(*  file under the terms of the Apache Software License version 2             *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
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
(******************************************************************************)

open Types

module H = Hashtbl.Make(Expr)

(*** Combination module of Shostak theories ***)

[@@@ocaml.warning "-60"]
module CX : sig
  include Sig.X
  val init : unit -> unit
end = struct

  module CX = Shostak_pre

  (* begin: Hashconsing modules and functions *)

  module View = struct

    type elt = Types.r

    let set_id tag r = { r with id=tag }

    let hash r =
      let res = match r.v with
        | ARITH x   -> 1 + 10 * Arith.hash x
        | RECORDS x   -> 2 + 10 * Records.hash x
        | BITV x   -> 3 + 10 * Bitv.hash x
        | ARRAYS x   -> 4 + 10 * Arrays.hash x
        | ENUM x   -> 5 + 10 * Enum.hash x
        | ADT x   -> 6 + 10 * Adt.hash x
        | ITE x   -> 7 + 10 * Ite.hash x
        | AC ac  -> 9 + 10 * Ac.hash ac
        | TERM t -> 8 + 10 * Expr.hash t
      in
      abs res

    let eq  r1 r2 =
      match r1.v, r2.v with
      | ARITH x, ARITH y -> Arith.equal x y
      | RECORDS x, RECORDS y -> Records.equal x y
      | BITV x, BITV y -> Bitv.equal x y
      | ARRAYS x, ARRAYS y -> Arrays.equal x y
      | ENUM x, ENUM y -> Enum.equal x y
      | ADT x, ADT y -> Adt.equal x y
      | ITE x, ITE y -> Ite.equal x y
      | TERM x  , TERM y  -> Expr.equal x y
      | AC x    , AC    y -> Ac.equal x y
      | _ -> false

    let initial_size = 9001

    let disable_weaks () = Options.get_disable_weaks ()

  end

  module HC = Hconsing.Make(View)

  let save_cache () =
    HC.save_cache ()

  let reinit_cache () =
    HC.reinit_cache ()

  let hcons v = HC.make v
  let () = Shostak_pre.REFS.hcons_ref := hcons

  (* end: Hconsing modules and functions *)

  let equal a b = a.id = b.id

  (* Constraint that must be maintained: all theories should have Xi < TERM < AC *)
  let theory_num x = match x with
    | AC _    -> -1
    | TERM  _ -> -2
    | ARITH _    -> -3
    | RECORDS _    -> -4
    | BITV _    -> -5
    | ARRAYS _    -> -6
    | ENUM _    -> -7
    | ADT _    -> -8
    | ITE _    -> -9

  let compare_tag a b = theory_num a - theory_num b

  let str_cmp a b =
    if equal a b then 0
    else
      match a.v, b.v with
      | ARITH _, ARITH _ -> Arith.compare a b
      | RECORDS _, RECORDS _ -> Records.compare a b
      | BITV _, BITV _ -> Bitv.compare a b
      | ARRAYS _, ARRAYS _ -> Arrays.compare a b
      | ENUM _, ENUM _ -> Enum.compare a b
      | ADT _, ADT _ -> Adt.compare a b
      | ITE _, ITE _ -> Ite.compare a b
      | TERM x  , TERM y  -> Expr.compare x y
      | AC x    , AC y    -> Ac.compare x y
      | va, vb            -> compare_tag va vb

  let ac_embed ({ Sig.l; _ } as t) =
    match l with
    | []    ->
      assert false
    | [x, 1] -> x
    | l     ->
      let sort = List.fast_sort (fun (x,_) (y,_) -> str_cmp x y) in
      let ac = { t with Sig.l = List.rev (sort l) } in
      hcons {v = AC ac; id = -1000 (* dummy *)}

  let term_embed t = hcons {v = TERM t; id = -1000 (* dummy *)}

  let ac_extract = function
    | { v = AC t; _ }   -> Some t
    | _ -> None

  let term_extract r =
    match r.v with
    | ARITH _ -> Arith.term_extract r
    | RECORDS _ -> Records.term_extract r
    | BITV _ -> Bitv.term_extract r
    | ARRAYS _ -> Arrays.term_extract r
    | ENUM _ -> Enum.term_extract r
    | ADT _ -> Adt.term_extract r
    | ITE _ -> Ite.term_extract r
    | AC _ -> None, false (* SYLVAIN : TODO *)
    | TERM t -> Some t, true

  let top () = term_embed Expr.vrai
  let bot () = term_embed Expr.faux

  let type_info = function
    | { v = ARITH t; _ }   -> Arith.type_info t
    | { v = RECORDS t; _ }   -> Records.type_info t
    | { v = BITV t; _ }   -> Bitv.type_info t
    | { v = ARRAYS t; _ }   -> Arrays.type_info t
    | { v = ENUM t; _ }   -> Enum.type_info t
    | { v = ADT t; _ }   -> Adt.type_info t
    | { v = ITE t; _ }   -> Ite.type_info t
    | { v = AC x; _ }   -> Ac.type_info x
    | { v = TERM t; _ } -> Expr.type_info t

  (*** implementations before hash-consing semantic values

       let equal a b = CX.compare a b = 0

       let hash r = match r.v with
       | TERM  t -> Expr.hash t
       | AC x -> AC.hash x
       | ARITH x -> ARITH.hash x
       | RECORDS x -> RECORDS.hash x
       | BITV x -> BITV.hash x
       | ARRAYS x -> ARRAYS.hash x
       | ENUM x -> ENUM.hash x

   ***)

  let hash v = v.id

  let hash_cmp a b = a.id - b.id

  (*
    should be called hash_cmp and used where structural_compare is
    not needed

    let compare a b =
    let c = Stdlib.compare a.id b.id in
    let c' = Stdlib.compare b.id a.id in
    assert ((c = 0 && c' = 0) || (c*c' < 0));
    c
  *)

  module SX = Set.Make(struct type t = r let compare = hash_cmp end)

  let leaves r =
    match r.v with
    | ARITH t -> Arith.leaves t
    | RECORDS t -> Records.leaves t
    | BITV t -> Bitv.leaves t
    | ARRAYS t -> Arrays.leaves t
    | ENUM t -> Enum.leaves t
    | ADT t -> Adt.leaves t
    | ITE t -> Ite.leaves t
    | AC t -> r :: (Ac.leaves t)
    | TERM _ -> [r]

  let subst p v r =
    if equal p v then r
    else match r.v with
      | ARITH t   -> Arith.subst p v t
      | RECORDS t   -> Records.subst p v t
      | BITV t   -> Bitv.subst p v t
      | ARRAYS t   -> Arrays.subst p v t
      | ENUM t   -> Enum.subst p v t
      | ADT t   -> Adt.subst p v t
      | ITE t   -> Ite.subst p v t
      | AC t   -> if equal p r then v else Ac.subst p v t
      | TERM _ -> if equal p r then v else r

  let make t =
    let { f = sb; ty; _ } = Expr.term_view t in
    let not_restricted = not @@ Options.get_restricted () in
    match
      Arith.is_mine_symb sb ty,
      not_restricted && Records.is_mine_symb sb ty,
      not_restricted && Bitv.is_mine_symb sb ty,
      not_restricted && Arrays.is_mine_symb sb ty,
      not_restricted && Enum.is_mine_symb sb ty,
      not_restricted && Adt.is_mine_symb sb ty,
      not_restricted && Ite.is_mine_symb sb ty,
      Ac.is_mine_symb sb ty
    with
    | true  , false , false , false, false, false, false, false -> Arith.make t
    | false , true  , false , false, false, false, false, false -> Records.make t
    | false , false , true  , false, false, false, false, false -> Bitv.make t
    | false , false , false , true , false, false, false, false -> Arrays.make t
    | false , false , false , false, true , false, false, false -> Enum.make t
    | false , false , false , false, false, true , false, false -> Adt.make t
    | false , false , false , false, false, false, true , false -> Ite.make t
    | false , false , false , false, false, false, false, true  -> Ac.make t
    | false , false , false , false, false, false, false, false ->
      term_embed t, []
    | _ -> assert false

  let fully_interpreted sb ty =
    let not_restricted = not @@ Options.get_restricted () in
    match
      Arith.is_mine_symb sb ty,
      not_restricted && Records.is_mine_symb sb ty,
      not_restricted && Bitv.is_mine_symb sb ty,
      not_restricted && Arrays.is_mine_symb sb ty,
      not_restricted && Enum.is_mine_symb sb ty,
      not_restricted && Adt.is_mine_symb sb ty,
      not_restricted && Ite.is_mine_symb sb ty,
      Ac.is_mine_symb sb ty
    with
    | true  , false , false , false, false, false, false, false ->
      Arith.fully_interpreted sb
    | false , true  , false , false, false, false, false, false ->
      Records.fully_interpreted sb
    | false , false , true  , false, false, false, false, false ->
      Bitv.fully_interpreted sb
    | false , false , false , true , false, false, false, false ->
      Arrays.fully_interpreted sb
    | false , false , false , false, true , false, false, false ->
      Enum.fully_interpreted sb
    | false , false , false , false, false, true , false, false ->
      Adt.fully_interpreted sb
    | false , false , false , false, false, false, true , false ->
      Ite.fully_interpreted sb
    | false , false , false , false, false, false, false, true  ->
      Ac.fully_interpreted sb
    | false , false , false , false, false, false, false, false ->
      false
    | _ -> assert false

  let is_solvable_theory_symbol sb ty =
    Arith.is_mine_symb sb ty ||
    not (Options.get_restricted ()) &&
    (Records.is_mine_symb sb ty ||
     Bitv.is_mine_symb sb ty ||
     Arrays.is_mine_symb sb ty ||
     Enum.is_mine_symb sb ty)


  let is_a_leaf r = match r.v with
    | TERM _ | AC _ -> true
    | _ -> false

  let color ac =
    match ac.Sig.l with
    | [] -> assert false
    | [r,1] -> r
    | _ ->
      let ty = ac.Sig.t in
      match
        Arith.is_mine_symb ac.Sig.h ty,
        Records.is_mine_symb ac.Sig.h ty,
        Bitv.is_mine_symb ac.Sig.h ty,
        Arrays.is_mine_symb ac.Sig.h ty,
        Enum.is_mine_symb ac.Sig.h ty,
        Adt.is_mine_symb ac.Sig.h ty,
        Ite.is_mine_symb ac.Sig.h ty,
        Ac.is_mine_symb ac.Sig.h ty with
      (*AC.is_mine may say F if Options.get_no_ac is set to F dynamically *)
      | true  , false , false , false, false, false, false, false -> Arith.color ac
      | false , true  , false , false, false, false, false, false -> Records.color ac
      | false , false , true  , false, false, false, false, false -> Bitv.color ac
      | false , false , false , true , false, false, false, false -> Arrays.color ac
      | false , false , false , false, true , false, false, false -> Enum.color ac
      | false , false , false , false, false, true , false, false -> Adt.color ac
      | false , false , false , false, false, false, true , false -> Ite.color ac
      | _  -> ac_embed ac


  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer

    let print fmt (r : r) =
      let open Format in
      if Options.get_term_like_pp () then begin
        match r.v with
        | ARITH t    -> fprintf fmt "%a" Arith.print t
        | RECORDS t    -> fprintf fmt "%a" Records.print t
        | BITV t    -> fprintf fmt "%a" Bitv.print t
        | ARRAYS t    -> fprintf fmt "%a" Arrays.print t
        | ENUM t    -> fprintf fmt "%a" Enum.print t
        | ADT t    -> fprintf fmt "%a" Adt.print t
        | ITE t    -> fprintf fmt "%a" Ite.print t
        | TERM t  -> fprintf fmt "%a" Expr.print t
        | AC t    -> fprintf fmt "%a" Ac.print t
      end
      else begin
        match r.v with
        | ARITH t    -> fprintf fmt "ARITH(%s):[%a]" Arith.name Arith.print t
        | RECORDS t    -> fprintf fmt "RECORDS(%s):[%a]" Records.name Records.print t
        | BITV t    -> fprintf fmt "BITV(%s):[%a]" Bitv.name Bitv.print t
        | ARRAYS t    -> fprintf fmt "ARRAYS(%s):[%a]" Arrays.name Arrays.print t
        | ENUM t    -> fprintf fmt "ENUM(%s):[%a]" Enum.name Enum.print t
        | ADT t    -> fprintf fmt "ADT(%s):[%a]" Adt.name Adt.print t
        | ITE t    -> fprintf fmt "ITE(%s):[%a]" Ite.name Ite.print t
        | TERM t  -> fprintf fmt "FT:[%a]" Expr.print t
        | AC t    -> fprintf fmt "Ac:[%a]" Ac.print t
      end

    let print_sbt msg sbs =
      let c = ref 0 in
      let print fmt (p,v) =
        incr c;
        Format.fprintf fmt "<%d) %a |-> %a@ "
          !c print p print v
      in
      if Options.get_debug_combine () then
        print_dbg
          ~module_name:"Shostak" ~function_name:"print_sbt"
          "@[<v 2>%s subst:@ %a@]"
          msg
          (pp_list_no_space print) sbs

    let debug_abstraction_result oa ob (a : r) b acc =
      let c = ref 0 in
      let print_pair fmt (p,v) =
        incr c;
        Format.fprintf fmt "(%d) %a |-> %a@ "
          !c print p print v
      in
      if Options.get_debug_combine () then
        print_dbg
          ~module_name:"Shostak" ~function_name:"abstraction_result"
          "@[<v 0>== get_debug_abstraction_result ==@ \
           Initial equaliy:   %a = %a@ \
           abstracted equality: %a = %a@ \
           @[<v 2>selectors elimination result:@ \
           %a@]@]"
          print oa print ob print a print b
          (pp_list_no_space print_pair) acc

    let solve_one a b =
      if Options.get_debug_combine () then
        print_dbg
          ~module_name:"Shostak" ~function_name:"solve_one"
          "solve one %a = %a" print a print b

    let debug_abstract_selectors a =
      if Options.get_debug_combine () then
        print_dbg
          ~module_name:"Shostak" ~function_name:"abstract_selectors"
          "abstract selectors of %a" print a

    let assert_have_mem_types tya tyb =
      assert (
        not (Options.get_enable_assertions()) ||
        if not (Ty.compare tya tyb = 0) then (
          print_err "@[<v 0>@ Tya = %a  and @ Tyb = %a@]"
            Ty.print tya Ty.print tyb;
          false)
        else true)

  end
  (*BISECT-IGNORE-END*)

  let print = Debug.print

  let abstract_selectors a acc =
    Debug.debug_abstract_selectors a;
    match a.v with
    | ARITH a   -> Arith.abstract_selectors a acc
    | RECORDS a   -> Records.abstract_selectors a acc
    | BITV a   -> Bitv.abstract_selectors a acc
    | ARRAYS a   -> Arrays.abstract_selectors a acc
    | ENUM a   -> Enum.abstract_selectors a acc
    | ADT a   -> Adt.abstract_selectors a acc
    | ITE a   -> Ite.abstract_selectors a acc
    | TERM _ -> a, acc
    | AC a   -> Ac.abstract_selectors a acc

  let abstract_equality a b =
    let aux r acc =
      match r.v with
      | AC ({ l = args; _ } as ac) ->
        let args, acc =
          List.fold_left
            (fun (args, acc) (r, i) ->
               let r, acc = abstract_selectors r acc in
               (r, i) :: args, acc
            )([],acc) args
        in
        ac_embed {ac with l = Ac.compact args}, acc
      | _     -> abstract_selectors r acc
    in
    let a', acc = aux a [] in
    let b', acc = aux b acc in
    a', b', acc

  let apply_subst r l = List.fold_left (fun r (p,v) -> CX.subst p v r) r l

  let triangular_down sbs =
    List.fold_right (fun (p,v) nsbs -> (p, apply_subst v nsbs) :: nsbs) sbs []

  let make_idemp a b sbs =
    Debug.print_sbt "Non triangular" sbs;
    let sbs = triangular_down sbs in
    let sbs = triangular_down (List.rev sbs) in (* triangular up *)
    let original = List.fold_right SX.add (leaves a) SX.empty in
    let original = List.fold_right SX.add (leaves b) original in
    let sbs =
      List.filter (fun (p,_) ->
          match p.v with
          | AC _ -> true | TERM _ -> SX.mem p original
          | _ ->
            Printer.print_err "%a" print p;
            assert false
        )sbs
    in
    Debug.print_sbt "Triangular and cleaned" sbs;
    (*
      This assert is not TRUE because of AC and distributivity of '*'
      assert (not (Options.get_enable_assertions()) ||
      equal (apply_subst a sbs) (apply_subst b sbs));
    *)
    sbs

  let apply_subst_right r sbt =
    List.fold_right (fun (p,v)r  -> subst p v r) sbt r

  let solve_uninterpreted r1 r2 (pb : r Sig.solve_pb) = (* r1 != r2*)
    if Options.get_debug_combine () then
      Printer.print_dbg
        "solve uninterpreted %a = %a" print r1 print r2;
    if str_cmp r1 r2 > 0 then { pb with sbt = (r1,r2)::pb.sbt }
    else { pb with sbt = (r2,r1)::pb.sbt }

  let rec solve_list (pb : r Sig.solve_pb) =
    match pb.eqs with
    | [] ->
      Debug.print_sbt "Should be triangular and cleaned" pb.sbt;
      pb.sbt
    | (a,b) :: eqs ->
      let pb = {pb with eqs=eqs} in
      Debug.solve_one a b;
      let ra = apply_subst_right a pb.sbt in
      let rb = apply_subst_right b pb.sbt in
      if equal ra rb then solve_list pb
      else
        let tya = type_info ra in
        let tyb = type_info rb in
        Debug.assert_have_mem_types tya tyb;
        let pb = match tya with
          | Ty.Tint | Ty.Treal -> Arith.solve ra rb pb
          | Ty.Trecord _       -> Records.solve ra rb pb
          | Ty.Tbitv _         -> Bitv.solve ra rb pb
          | Ty.Tsum _          -> Enum.solve ra rb pb
          (*| Ty.Tunit           -> pb *)
          | Ty.Tadt _ when not (Options.get_disable_adts()) -> Adt.solve ra rb pb
          | _                  -> solve_uninterpreted ra rb pb
        in
        solve_list pb
        [@ocaml.ppwarning "TODO: a simple way of handling equalities \
                           with void and unit is to add this case is \
                           the solver!"]

  let solve_abstracted oa ob a b sbt =
    Debug.debug_abstraction_result oa ob a b sbt;
    let ra = apply_subst_right a sbt in
    let rb = apply_subst_right b sbt in
    let sbt' = solve_list { sbt=[] ; eqs=[ra,rb] } in
    match sbt', sbt with
    | [], _::_ -> [] (* the original equality was trivial *)
    | _ -> make_idemp oa ob (List.rev_append sbt sbt')

  let solve  a b =
    if CX.equal a b then []
    else
      let a', b', acc = abstract_equality a b in
      let sbs = solve_abstracted a b a' b' acc in
      List.fast_sort
        (fun (p1, _) (p2, _) ->
           let c = CX.str_cmp p2 p1 in
           assert (c <> 0);
           c
        )sbs

  let is_bool_const r = equal r (top()) || equal r (bot())

  let assign_value r distincts eq =
    let opt = match r.v, type_info r with
      | _, Ty.Tint
      | _, Ty.Treal     -> Arith.assign_value r distincts eq
      | _, Ty.Trecord _ -> Records.assign_value r distincts eq
      | _, Ty.Tbitv _   -> Bitv.assign_value r distincts eq
      | _, Ty.Tfarray _ -> Arrays.assign_value r distincts eq
      | _, Ty.Tsum _    -> Enum.assign_value r distincts eq
      | _, Ty.Tadt _    when not (Options.get_disable_adts()) ->
        Adt.assign_value r distincts eq

      | TERM _t, Ty.Tbool ->
        if is_bool_const r then None
        else
          begin
            let eq = List.filter (fun (_t, r) -> is_bool_const r) eq in
            match eq with
            | (e,_r)::_ -> Some (e, false) (* false <-> not a case-split *)
            | [] ->
              let dist = List.filter (fun r -> is_bool_const r) distincts in
              match dist with
              | {v = TERM e; _}::_ ->
                Some (Expr.neg e, true) (* safety: consider it as case-split *)
              | _::_ ->
                assert false
              | [] ->
                Some (Expr.faux, true) (* true <-> make a case split *)
          end

      | TERM t, ty      -> (* case disable_adts() handled here *)
        if Expr.const_term t ||
           List.exists (fun (t,_) -> Expr.const_term t) eq then None
        else Some (Expr.fresh_name ty, false) (* false <-> not a case-split *)
      | _               -> assert false
    in
    if Options.get_debug_interpretation () then
      Printer.print_dbg
        ~module_name:"Shostak" ~function_name:"assign_value"
        "assign value to representative %a : %s"
        print r
        (match opt with
         | None -> Format.asprintf "None"
         | Some(res, _is_cs) -> Format.asprintf "%a" Expr.print res);
    opt

  let choose_adequate_model t rep l =
    let r, pprint =
      match Expr.type_info t with
      | Ty.Tint
      | Ty.Treal     -> Arith.choose_adequate_model t rep l
      | Ty.Tbitv _   -> Bitv.choose_adequate_model t rep l
      | Ty.Tsum _    -> Enum.choose_adequate_model t rep l
      | Ty.Tadt _    when not (Options.get_disable_adts()) ->
        Adt.choose_adequate_model t rep l
      | Ty.Trecord _ -> Records.choose_adequate_model t rep l
      | Ty.Tfarray _ -> Arrays.choose_adequate_model t rep l
      | Ty.Tbool ->
        (* case split is now supposed to be done for internal bools if
           needed as well *)
        assert (is_bool_const rep);
        rep, Format.asprintf "%a" print rep
      | _            ->
        let acc =
          List.fold_left
            (fun acc (s, r) ->
               if Expr.const_term s then
                 match acc with
                 | Some(s', _) when Expr.compare s' s > 0 -> acc
                 | _ -> Some (s, r)
               else
                 acc
            ) None l
        in
        let r =
          match acc with
          | Some (_,r) -> r
          | None ->
            match term_extract rep with
            | Some t, true when Expr.const_term t -> rep
            | _ ->
              let print_aux fmt (t,r) =
                Format.fprintf fmt "> impossible case: %a -- %a@ "
                  Expr.print t
                  print r
              in
              if Options.get_debug_interpretation () then
                Printer.print_dbg
                  ~module_name:"Shostak" ~function_name:"choose_adequate_model"
                  "@[<v 2>What to choose for term %a with rep %a?\
                   %a@]"
                  Expr.print t
                  print rep
                  (Printer.pp_list_no_space print_aux) l;
              assert false
        in
        r, Format.asprintf "%a" print r (* it's a EUF constant *)
    in
    if Options.get_debug_interpretation () then
      Printer.print_dbg
        ~module_name:"Shostak" ~function_name:"choose_adequate_model"
        "%a selected as a model for %a"
        print r Expr.print t;
    r, pprint

  let init () =
    let open Shostak_pre.REFS in
    leaves_ref := leaves ;
    equal_ref := equal ;
    term_extract_ref := term_extract ;
    save_cache_ref := save_cache ;
    reinit_cache_ref := reinit_cache ;
    make_ref := make ;
    type_info_ref := type_info ;
    str_cmp_ref := str_cmp ;
    hash_cmp_ref := hash_cmp ;
    hash_ref := hash ;
    subst_ref := subst ;
    solve_ref := solve ;
    term_embed_ref := term_embed ;
    ac_embed_ref := ac_embed ;
    ac_extract_ref := ac_extract ;
    color_ref := color ;
    fully_interpreted_ref := fully_interpreted ;
    is_a_leaf_ref := is_a_leaf ;
    print_ref := print ;
    abstract_selectors_ref := abstract_selectors ;
    top_ref := top ;
    bot_ref := bot ;
    is_solvable_theory_symbol_ref := is_solvable_theory_symbol ;
    assign_value_ref := assign_value ;
    choose_adequate_model_ref := choose_adequate_model ;
    ()

end

module Combine = struct
  include CX

  let make, save_cache, reinit_cache =
    let cache = H.create 1024 in
    let cache_copy = ref None in
    let make t =
      match H.find_opt cache t with
      | None -> let res = make t in H.add cache t res; res
      | Some res -> res
    in
    let save_cache_aux () =
      save_cache ();
      cache_copy := (Some (H.copy cache));
    in
    let reinit_cache_aux () =
      reinit_cache ();
      H.clear cache;
      H.iter (H.add cache) (Option.get !cache_copy)
    in
    make, save_cache_aux, reinit_cache_aux

end

module Arith = Arith
module Records = Records
module Bitv = Bitv
module Arrays = Arrays
module Enum = Enum
module Adt = Adt
module Ite = Ite
module Polynome = Polynome
module Ac = Ac

(** map of semantic values using Combine.hash_cmp *)
module MXH =
  Map.Make(struct type t = Types.r let compare = Combine.hash_cmp end)

(** set of semantic values using Combine.hash_cmp *)
module SXH =
  Set.Make(struct type t = Types.r let compare = Combine.hash_cmp end)

(** map of semantic values using structural compare Combine.str_cmp *)
module MXS =
  Map.Make(struct type t = Types.r let compare = Combine.hash_cmp end)

(** set of semantic values using structural compare Combine.str_cmp *)
module SXS =
  Set.Make(struct type t = Types.r let compare = Combine.hash_cmp end)

let init () =
  CX.init ()

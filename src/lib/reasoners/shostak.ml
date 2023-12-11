(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(*** Combination module of Shostak theories ***)

[@@@ocaml.warning "-60"]
module rec CX : sig
  include Sig.X

  val top : unit -> r
  val bot : unit -> r

  val extract1 : r -> ARITH.t option
  val embed1 : ARITH.t -> r

  val extract2 : r -> RECORDS.t option
  val embed2 : RECORDS.t -> r

  val extract3 : r -> BITV.t option
  val embed3 : BITV.t -> r

  val extract4 : r -> ARRAYS.t option
  val embed4 : ARRAYS.t -> r

  val extract5 : r -> ENUM.t option
  val embed5 : ENUM.t -> r

  val extract6 : r -> ADT.t option
  val embed6 : ADT.t -> r

  val extract7 : r -> ITE.t option
  val embed7 : ITE.t -> r

end =
struct

  type rview =
    | Term of Expr.t
    | Ac of AC.t
    | Arith of ARITH.t
    | Records of RECORDS.t
    | Bitv of BITV.t
    | Arrays of ARRAYS.t
    | Enum of ENUM.t
    | Adt of ADT.t
    | Ite of ITE.t

  type r = {v : rview ; id : int}

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer

    let print fmt r =
      let open Format in
      if Options.get_term_like_pp () then begin
        match r.v with
        | Arith t -> fprintf fmt "%a" ARITH.print t
        | Records t -> fprintf fmt "%a" RECORDS.print t
        | Bitv t -> fprintf fmt "%a" BITV.print t
        | Arrays t -> fprintf fmt "%a" ARRAYS.print t
        | Enum t -> fprintf fmt "%a" ENUM.print t
        | Adt t -> fprintf fmt "%a" ADT.print t
        | Ite t -> fprintf fmt "%a" ITE.print t
        | Term t -> fprintf fmt "%a" Expr.print t
        | Ac t -> fprintf fmt "%a" AC.print t
      end
      else begin
        match r.v with
        | Arith t ->
          fprintf fmt "Arith(%s):[%a]" ARITH.name ARITH.print t
        | Records t ->
          fprintf fmt "Records(%s):[%a]" RECORDS.name RECORDS.print t
        | Bitv t ->
          fprintf fmt "Bitv(%s):[%a]" BITV.name BITV.print t
        | Arrays t ->
          fprintf fmt "Arrays(%s):[%a]" ARRAYS.name ARRAYS.print t
        | Enum t ->
          fprintf fmt "Enum(%s):[%a]" ENUM.name ENUM.print t
        | Adt t ->
          fprintf fmt "Adt(%s):[%a]" ADT.name ADT.print t
        | Ite t ->
          fprintf fmt "Ite(%s):[%a]" ITE.name ITE.print t
        | Term t ->
          fprintf fmt "FT:[%a]" Expr.print t
        | Ac t ->
          fprintf fmt "Ac:[%a]" AC.print t
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

    let debug_abstraction_result oa ob a b acc =
      let c = ref 0 in
      let print fmt (p,v) =
        incr c;
        Format.fprintf fmt "(%d) %a |-> %a@ "
          !c CX.print p CX.print v
      in
      if Options.get_debug_combine () then
        print_dbg
          ~module_name:"Shostak" ~function_name:"abstraction_result"
          "@[<v 0>== get_debug_abstraction_result ==@ \
           Initial equaliy:   %a = %a@ \
           abstracted equality: %a = %a@ \
           @[<v 2>selectors elimination result:@ \
           %a@]@]"
          CX.print oa CX.print ob CX.print a CX.print b
          (pp_list_no_space print) acc

    let solve_one a b =
      if Options.get_debug_combine () then
        print_dbg
          ~module_name:"Shostak" ~function_name:"solve_one"
          "solve one %a = %a" CX.print a CX.print b

    let debug_abstract_selectors a =
      if Options.get_debug_combine () then
        print_dbg
          ~module_name:"Shostak" ~function_name:"abstract_selectors"
          "abstract selectors of %a" CX.print a

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


  (* begin: Hashconsing modules and functions *)

  module View = struct

    type elt = r

    let set_id tag r = { r with id=tag }

    let hash r =
      let res = match r.v with
        | Arith x -> 1 + 10 * ARITH.hash x
        | Records x -> 2 + 10 * RECORDS.hash x
        | Bitv x -> 3 + 10 * BITV.hash x
        | Arrays x -> 4 + 10 * ARRAYS.hash x
        | Enum x -> 5 + 10 * ENUM.hash x
        | Adt x -> 6 + 10 * ADT.hash x
        | Ite x -> 7 + 10 * ITE.hash x
        | Ac ac -> 9 + 10 * AC.hash ac
        | Term t -> 8 + 10 * Expr.hash t
      in
      abs res

    let eq  r1 r2 =
      match r1.v, r2.v with
      | Arith x, Arith y -> ARITH.equal x y
      | Records x, Records y -> RECORDS.equal x y
      | Bitv x, Bitv y -> BITV.equal x y
      | Arrays x, Arrays y -> ARRAYS.equal x y
      | Enum x, Enum y -> ENUM.equal x y
      | Adt x, Adt y -> ADT.equal x y
      | Ite x, Ite y -> ITE.equal x y
      | Term x, Term y -> Expr.equal x y
      | Ac x, Ac y -> AC.equal x y
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

  (* end: Hconsing modules and functions *)

  let embed1 x = hcons {v = Arith x; id = -1000 (* dummy *)}
  let embed2 x = hcons {v = Records x; id = -1000 (* dummy *)}
  let embed3 x = hcons {v = Bitv x; id = -1000 (* dummy *)}
  let embed4 x = hcons {v = Arrays x; id = -1000 (* dummy *)}
  let embed5 x = hcons {v = Enum x; id = -1000 (* dummy *)}
  let embed6 x = hcons {v = Adt x; id = -1000 (* dummy *)}
  let embed7 x = hcons {v = Ite x; id = -1000 (* dummy *)}

  let ac_embed ({ Sig.l; _ } as t) =
    match l with
    | []    ->
      assert false
    | [x, 1] -> x
    | l     ->
      let sort = List.fast_sort (fun (x,_) (y,_) -> CX.str_cmp x y) in
      let ac = { t with Sig.l = List.rev (sort l) } in
      hcons {v = Ac ac; id = -1000 (* dummy *)}

  let term_embed t = hcons {v = Term t; id = -1000 (* dummy *)}

  let extract1 = function { v=Arith r; _ } -> Some r | _ -> None
  let extract2 = function { v=Records r; _ } -> Some r | _ -> None
  let extract3 = function { v=Bitv r; _ } -> Some r | _ -> None
  let extract4 = function { v=Arrays r; _ } -> Some r | _ -> None
  let extract5 = function { v=Enum r; _ } -> Some r | _ -> None
  let extract6 = function { v=Adt r; _ } -> Some r | _ -> None
  let extract7 = function { v=Ite r; _ } -> Some r | _ -> None

  let ac_extract = function
    | { v = Ac t; _ }   -> Some t
    | _ -> None

  let term_extract r =
    match r.v with
    | Arith _ -> ARITH.term_extract r
    | Records _ -> RECORDS.term_extract r
    | Bitv _ -> BITV.term_extract r
    | Arrays _ -> ARRAYS.term_extract r
    | Enum _ -> ENUM.term_extract r
    | Adt _ -> ADT.term_extract r
    | Ite _ -> ITE.term_extract r
    | Ac _ -> None, false (* SYLVAIN : TODO *)
    | Term t -> Some t, true

  let to_const_term r =
    let res =
      match r.v with
      | Arith _ -> ARITH.to_const_term r
      | Records _ -> RECORDS.to_const_term r
      | Bitv _ -> BITV.to_const_term r
      | Arrays _ -> ARRAYS.to_const_term r
      | Enum _ -> ENUM.to_const_term r
      | Adt _ -> ADT.to_const_term r
      | Ite _ -> ITE.to_const_term r
      | Term t when Expr.is_model_term t -> Some t
      | Ac _ | Term _ -> None
    in
    Option.bind res @@ fun t ->
    assert (Expr.is_model_term t);
    Some t

  let top () = term_embed Expr.vrai
  let bot () = term_embed Expr.faux

  let type_info = function
    | { v = Arith t; _ } -> ARITH.type_info t
    | { v = Records t; _ } -> RECORDS.type_info t
    | { v = Bitv t; _ } -> BITV.type_info t
    | { v = Arrays t; _ } -> ARRAYS.type_info t
    | { v = Enum t; _ } -> ENUM.type_info t
    | { v = Adt t; _ } -> ADT.type_info t
    | { v = Ite t; _ } -> ITE.type_info t
    | { v = Ac x; _ } -> AC.type_info x
    | { v = Term t; _ } -> Expr.type_info t

  (* Constraint that must be maintained:
     all theories should have Xi < Term < Ac *)
  let theory_num x = match x with
    | Ac _ -> -1
    | Term  _ -> -2
    | Arith _ -> -3
    | Records _ -> -4
    | Bitv _ -> -5
    | Arrays _ -> -6
    | Enum _ -> -7
    | Adt _ -> -8
    | Ite _ -> -9

  let compare_tag a b = theory_num a - theory_num b

  let str_cmp a b =
    if CX.equal a b then 0
    else
      match a.v, b.v with
      | Arith _, Arith _ -> ARITH.compare a b
      | Records _, Records _ -> RECORDS.compare a b
      | Bitv _, Bitv _ -> BITV.compare a b
      | Arrays _, Arrays _ -> ARRAYS.compare a b
      | Enum _, Enum _ -> ENUM.compare a b
      | Adt _, Adt _ -> ADT.compare a b
      | Ite _, Ite _ -> ITE.compare a b
      | Term x, Term y -> Expr.compare x y
      | Ac x, Ac y -> AC.compare x y
      | va, vb -> compare_tag va vb

  (*** implementations before hash-consing semantic values

       let equal a b = CX.compare a b = 0

       let hash r = match r.v with
       | Term  t -> Expr.hash t
       | Ac x -> AC.hash x
       | Arith x -> ARITH.hash x
       | Records x -> RECORDS.hash x
       | Bitv x -> BITV.hash x
       | Arrays x -> ARRAYS.hash x
       | Enum x -> ENUM.hash x

   ***)

  let equal a b = a.id = b.id

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

  module SX = Set.Make(struct type t = r let compare = CX.hash_cmp end)

  let leaves r =
    match r.v with
    | Arith t -> ARITH.leaves t
    | Records t -> RECORDS.leaves t
    | Bitv t -> BITV.leaves t
    | Arrays t -> ARRAYS.leaves t
    | Enum t -> ENUM.leaves t
    | Adt t -> ADT.leaves t
    | Ite t -> ITE.leaves t
    | Ac t -> r :: (AC.leaves t)
    | Term _ -> [r]

  let is_constant r =
    match r.v with
    | Arith t -> ARITH.is_constant t
    | Records t -> RECORDS.is_constant t
    | Bitv t -> BITV.is_constant t
    | Arrays t -> ARRAYS.is_constant t
    | Enum t -> ENUM.is_constant t
    | Adt t -> ADT.is_constant t
    | Ite t -> ITE.is_constant t
    | Term t ->
      begin
        let Expr.{ f; xs; _ } = Expr.term_view t in
        (* We don't use [Expr.is_model_term] here to ensure that [t] is a
           constant term because most of model terms are represented by
           semantic values of builtin theories. Constant terms not managed by
           builtin theories have to be considered as constant semantic
           values. In particular, this code enforces the invariant:
             [e] is a model term ==> [X.make e] is a constant semantic value. *)
        match f, xs with
        | Symbols.(True | False | Void | Name _), [] -> true
        | _ -> false
      end
    | Ac _ -> false

  let subst p v r =
    if equal p v then r
    else match r.v with
      | Arith t -> ARITH.subst p v t
      | Records t -> RECORDS.subst p v t
      | Bitv t -> BITV.subst p v t
      | Arrays t -> ARRAYS.subst p v t
      | Enum t -> ENUM.subst p v t
      | Adt t -> ADT.subst p v t
      | Ite t -> ITE.subst p v t
      | Ac t -> if equal p r then v else AC.subst p v t
      | Term _ -> if equal p r then v else r

  let make t =
    let { Expr.f = sb; ty; _ } = Expr.term_view t in
    let not_restricted = not @@ Options.get_restricted () in
    match
      ARITH.is_mine_symb sb ty,
      not_restricted && RECORDS.is_mine_symb sb ty,
      not_restricted && BITV.is_mine_symb sb ty,
      not_restricted && ARRAYS.is_mine_symb sb ty,
      not_restricted && ENUM.is_mine_symb sb ty,
      not_restricted && ADT.is_mine_symb sb ty,
      not_restricted && ITE.is_mine_symb sb ty,
      AC.is_mine_symb sb ty
    with
    | true  , false , false , false, false, false, false, false ->
      ARITH.make t
    | false , true  , false , false, false, false, false, false ->
      RECORDS.make t
    | false , false , true  , false, false, false, false, false ->
      BITV.make t
    | false , false , false , true , false, false, false, false ->
      ARRAYS.make t
    | false , false , false , false, true , false, false, false ->
      ENUM.make t
    | false , false , false , false, false, true , false, false ->
      ADT.make t
    | false , false , false , false, false, false, true , false ->
      ITE.make t
    | false , false , false , false, false, false, false, true  ->
      AC.make t
    | false , false , false , false, false, false, false, false ->
      term_embed t, []
    | _ -> assert false

  let fully_interpreted sb ty =
    let not_restricted = not @@ Options.get_restricted () in
    match
      ARITH.is_mine_symb sb ty,
      not_restricted && RECORDS.is_mine_symb sb ty,
      not_restricted && BITV.is_mine_symb sb ty,
      not_restricted && ARRAYS.is_mine_symb sb ty,
      not_restricted && ENUM.is_mine_symb sb ty,
      not_restricted && ADT.is_mine_symb sb ty,
      not_restricted && ITE.is_mine_symb sb ty,
      AC.is_mine_symb sb ty
    with
    | true  , false , false , false, false, false, false, false ->
      ARITH.fully_interpreted sb
    | false , true  , false , false, false, false, false, false ->
      RECORDS.fully_interpreted sb
    | false , false , true  , false, false, false, false, false ->
      BITV.fully_interpreted sb
    | false , false , false , true , false, false, false, false ->
      ARRAYS.fully_interpreted sb
    | false , false , false , false, true , false, false, false ->
      ENUM.fully_interpreted sb
    | false , false , false , false, false, true , false, false ->
      ADT.fully_interpreted sb
    | false , false , false , false, false, false, true , false ->
      ITE.fully_interpreted sb
    | false , false , false , false, false, false, false, true  ->
      AC.fully_interpreted sb
    | false , false , false , false, false, false, false, false ->
      false
    | _ -> assert false

  let is_solvable_theory_symbol sb ty =
    ARITH.is_mine_symb sb ty ||
    not (Options.get_restricted ()) &&
    (RECORDS.is_mine_symb sb ty ||
     BITV.is_mine_symb sb ty ||
     ARRAYS.is_mine_symb sb ty ||
     ENUM.is_mine_symb sb ty)


  let is_a_leaf r = match r.v with
    | Term _ | Ac _ -> true
    | _ -> false

  let color ac =
    match ac.Sig.l with
    | [] -> assert false
    | [r,1] -> r
    | _ ->
      let ty = ac.Sig.t in
      match
        ARITH.is_mine_symb ac.Sig.h ty,
        RECORDS.is_mine_symb ac.Sig.h ty,
        BITV.is_mine_symb ac.Sig.h ty,
        ARRAYS.is_mine_symb ac.Sig.h ty,
        ENUM.is_mine_symb ac.Sig.h ty,
        ADT.is_mine_symb ac.Sig.h ty,
        ITE.is_mine_symb ac.Sig.h ty,
        AC.is_mine_symb ac.Sig.h ty with
      (*AC.is_mine may say F if Options.get_no_ac is set to F dynamically *)
      | true  , false , false , false, false, false, false, false ->
        ARITH.color ac
      | false , true  , false , false, false, false, false, false ->
        RECORDS.color ac
      | false , false , true  , false, false, false, false, false ->
        BITV.color ac
      | false , false , false , true , false, false, false, false ->
        ARRAYS.color ac
      | false , false , false , false, true , false, false, false ->
        ENUM.color ac
      | false , false , false , false, false, true , false, false ->
        ADT.color ac
      | false , false , false , false, false, false, true , false ->
        ITE.color ac
      | _  -> ac_embed ac

  let abstract_selectors a acc =
    Debug.debug_abstract_selectors a;
    match a.v with
    | Arith a -> ARITH.abstract_selectors a acc
    | Records a -> RECORDS.abstract_selectors a acc
    | Bitv a -> BITV.abstract_selectors a acc
    | Arrays a -> ARRAYS.abstract_selectors a acc
    | Enum a -> ENUM.abstract_selectors a acc
    | Adt a -> ADT.abstract_selectors a acc
    | Ite a -> ITE.abstract_selectors a acc
    | Term _ -> a, acc
    | Ac a -> AC.abstract_selectors a acc

  let abstract_equality a b =
    let aux r acc =
      match r.v with
      | Ac ({ l = args; _ } as ac) ->
        let args, acc =
          List.fold_left
            (fun (args, acc) (r, i) ->
               let r, acc = abstract_selectors r acc in
               (r, i) :: args, acc
            )([],acc) args
        in
        ac_embed {ac with l = AC.compact args}, acc
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
    let original = List.fold_right SX.add (CX.leaves a) SX.empty in
    let original = List.fold_right SX.add (CX.leaves b) original in
    let sbs =
      List.filter (fun (p,_) ->
          match p.v with
          | Ac _ -> true | Term _ -> SX.mem p original
          | _ ->
            Printer.print_err "%a" CX.print p;
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
    List.fold_right (fun (p,v)r  -> CX.subst p v r) sbt r

  let solve_uninterpreted r1 r2 (pb : r Sig.solve_pb) = (* r1 != r2*)
    if Options.get_debug_combine () then
      Printer.print_dbg
        "solve uninterpreted %a = %a" print r1 print r2;
    if CX.str_cmp r1 r2 > 0 then { pb with sbt = (r1,r2)::pb.sbt }
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
      if CX.equal ra rb then solve_list pb
      else
        let tya = CX.type_info ra in
        let tyb = CX.type_info rb in
        Debug.assert_have_mem_types tya tyb;
        let pb = match tya with
          | Ty.Tint | Ty.Treal -> ARITH.solve ra rb pb
          | Ty.Trecord _       -> RECORDS.solve ra rb pb
          | Ty.Tbitv _         -> BITV.solve ra rb pb
          | Ty.Tsum _          -> ENUM.solve ra rb pb
          (*| Ty.Tunit           -> pb *)
          | Ty.Tadt _ when not (Options.get_disable_adts()) ->
            ADT.solve ra rb pb
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
      | _, Ty.Treal     -> ARITH.assign_value r distincts eq
      | _, Ty.Trecord _ -> RECORDS.assign_value r distincts eq
      | _, Ty.Tbitv _   -> BITV.assign_value r distincts eq
      | _, Ty.Tfarray _ -> ARRAYS.assign_value r distincts eq
      | _, Ty.Tsum _    -> ENUM.assign_value r distincts eq
      | _, Ty.Tadt _    when not (Options.get_disable_adts()) ->
        ADT.assign_value r distincts eq

      | Term _t, Ty.Tbool ->
        if is_bool_const r then None
        else
          begin
            let eq = List.filter (fun (_t, r) -> is_bool_const r) eq in
            match eq with
            | (e,_r)::_ -> Some (e, false) (* false <-> not a case-split *)
            | [] ->
              let dist = List.filter (fun r -> is_bool_const r) distincts in
              match dist with
              | {v = Term e; _}::_ ->
                Some (Expr.neg e, true) (* safety: consider it as case-split *)
              | _::_ ->
                assert false
              | [] ->
                Some (Expr.faux, true) (* true <-> make a case split *)
          end

      | Term t, ty      -> (* case disable_adts() handled here *)
        if Expr.is_model_term t ||
           List.exists (fun (t,_) -> Expr.is_model_term t) eq then None
        else Some (Expr.fresh_name ty, false) (* false <-> not a case-split *)
      | _               ->
        (* There is no model-generation support for the AC symbols yet.
           The function [AC.assign_value] always returns [None]. *)
        AC.assign_value r distincts eq
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
end

and TARITH : Polynome.T
  with type r = CX.r =
  Arith.Type(CX)

and ARITH : Sig.SHOSTAK
  with type t = TARITH.t
   and type r = CX.r =
  Arith.Shostak
    (CX)
    (struct
      include TARITH
      let extract = CX.extract1
      let embed =  CX.embed1
    end)

and RECORDS : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Records.abstract =
  Records.Shostak
    (struct
      include CX
      let extract = extract2
      let embed = embed2
    end)

and BITV : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Bitv.abstract =
  Bitv.Shostak
    (struct
      include CX
      let extract = extract3
      let embed = embed3
    end)

and ARRAYS : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Arrays.abstract =
  Arrays.Shostak
    (struct
      include CX
      let extract = extract4
      let embed = embed4
    end)

and ENUM : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Enum.abstract =
  Enum.Shostak
    (struct
      include CX
      let extract = extract5
      let embed = embed5
    end)

and ADT : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Adt.abstract =
  Adt.Shostak
    (struct
      include CX
      let extract = extract6
      let embed = embed6
    end)

and ITE : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Ite.abstract =
  Ite.Shostak
    (struct
      include CX
      let extract = extract7
      let embed = embed7
    end)

(* Its signature is not Sig.SHOSTAK because it does not provide a solver *)
and AC : Ac.S
  with type r = CX.r =
  Ac.Make(CX)

module Combine = struct
  include CX

  module H = Ephemeron.K1.Make(Expr)

  let make, save_cache, reinit_cache =
    let cache = ref (H.create 1024) in
    let cache_copy = ref None in
    let make t =
      match H.find !cache t with
      | r -> r
      | exception Not_found ->
        let r = make t in
        H.add !cache t r;
        r
    in
    let save_cache_aux () =
      save_cache ();
      cache_copy := (Some (H.copy !cache));
    in
    let reinit_cache_aux () =
      reinit_cache ();
      cache := H.copy (Option.get !cache_copy);
    in
    make, save_cache_aux, reinit_cache_aux

  let top = top ()
  let bot = bot ()
end

module Arith = ARITH
module Records = RECORDS
module Bitv = BITV
module Arrays = ARRAYS
module Enum = ENUM
module Adt = ADT
module Ite = ITE
module Polynome = TARITH
module Ac = AC

(** map of semantic values using Combine.hash_cmp *)
module MXH =
  Map.Make(struct type t = Combine.r let compare = Combine.hash_cmp end)

(** set of semantic values using Combine.hash_cmp *)
module SXH =
  Set.Make(struct type t = Combine.r let compare = Combine.hash_cmp end)

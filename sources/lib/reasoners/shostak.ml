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

(*** Combination module of Shostak theories ***)

[@@@ocaml.warning "-60"]
module rec CX : sig
  include Sig.X

  val extract1 : r -> X1.t option
  val embed1 : X1.t -> r

  val extract2 : r -> X2.t option
  val embed2 : X2.t -> r

  val extract3 : r -> X3.t option
  val embed3 : X3.t -> r

  val extract4 : r -> X4.t option
  val embed4 : X4.t -> r

  val extract5 : r -> X5.t option
  val embed5 : X5.t -> r

  val extract6 : r -> X6.t option
  val embed6 : X6.t -> r

  val extract7 : r -> X7.t option
  val embed7 : X7.t -> r

end =
struct

  type rview =
    | Term  of Expr.t
    | Ac    of AC.t
    | X1    of X1.t
    | X2    of X2.t
    | X3    of X3.t
    | X4    of X4.t
    | X5    of X5.t
    | X6    of X6.t
    | X7    of X7.t

  type r = {v : rview ; id : int}

  (* begin: Hashconsing modules and functions *)

  module View = struct

    type elt = r

    let set_id tag r = { r with id=tag }

    let hash r =
      let res = match r.v with
        | X1 x   -> 1 + 10 * X1.hash x
        | X2 x   -> 2 + 10 * X2.hash x
        | X3 x   -> 3 + 10 * X3.hash x
        | X4 x   -> 4 + 10 * X4.hash x
        | X5 x   -> 5 + 10 * X5.hash x
        | X6 x   -> 6 + 10 * X6.hash x
        | X7 x   -> 7 + 10 * X7.hash x
        | Ac ac  -> 9 + 10 * AC.hash ac
        | Term t -> 8 + 10 * Expr.hash t
      in
      abs res

    let eq  r1 r2 =
      match r1.v, r2.v with
      | X1 x, X1 y -> X1.equal x y
      | X2 x, X2 y -> X2.equal x y
      | X3 x, X3 y -> X3.equal x y
      | X4 x, X4 y -> X4.equal x y
      | X5 x, X5 y -> X5.equal x y
      | X6 x, X6 y -> X6.equal x y
      | X7 x, X7 y -> X7.equal x y
      | Term x  , Term y  -> Expr.equal x y
      | Ac x    , Ac    y -> AC.equal x y
      | _ -> false

    let initial_size = 9001

    let disable_weaks () = Options.disable_weaks ()

  end

  module HC = Hconsing.Make(View)

  let hcons v = HC.make v

  (* end: Hconsing modules and functions *)

  let embed1 x = hcons {v = X1 x; id = -1000 (* dummy *)}
  let embed2 x = hcons {v = X2 x; id = -1000 (* dummy *)}
  let embed3 x = hcons {v = X3 x; id = -1000 (* dummy *)}
  let embed4 x = hcons {v = X4 x; id = -1000 (* dummy *)}
  let embed5 x = hcons {v = X5 x; id = -1000 (* dummy *)}
  let embed6 x = hcons {v = X6 x; id = -1000 (* dummy *)}
  let embed7 x = hcons {v = X7 x; id = -1000 (* dummy *)}

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

  let extract1 = function { v=X1 r; _ } -> Some r | _ -> None
  let extract2 = function { v=X2 r; _ } -> Some r | _ -> None
  let extract3 = function { v=X3 r; _ } -> Some r | _ -> None
  let extract4 = function { v=X4 r; _ } -> Some r | _ -> None
  let extract5 = function { v=X5 r; _ } -> Some r | _ -> None
  let extract6 = function { v=X6 r; _ } -> Some r | _ -> None
  let extract7 = function { v=X7 r; _ } -> Some r | _ -> None

  let ac_extract = function
    | { v = Ac t; _ }   -> Some t
    | _ -> None

  let term_extract r =
    match r.v with
    | X1 _ -> X1.term_extract r
    | X2 _ -> X2.term_extract r
    | X3 _ -> X3.term_extract r
    | X4 _ -> X4.term_extract r
    | X5 _ -> X5.term_extract r
    | X6 _ -> X6.term_extract r
    | X7 _ -> X7.term_extract r
    | Ac _ -> None, false (* SYLVAIN : TODO *)
    | Term t -> Some t, true

  let top () = term_embed Expr.vrai
  let bot () = term_embed Expr.faux

  let type_info = function
    | { v = X1 t; _ }   -> X1.type_info t
    | { v = X2 t; _ }   -> X2.type_info t
    | { v = X3 t; _ }   -> X3.type_info t
    | { v = X4 t; _ }   -> X4.type_info t
    | { v = X5 t; _ }   -> X5.type_info t
    | { v = X6 t; _ }   -> X6.type_info t
    | { v = X7 t; _ }   -> X7.type_info t
    | { v = Ac x; _ }   -> AC.type_info x
    | { v = Term t; _ } -> Expr.type_info t

  (* Xi < Term < Ac *)
  let theory_num x = match x with
    | Ac _    -> -1
    | Term  _ -> -2
    | X1 _    -> -3
    | X2 _    -> -4
    | X3 _    -> -5
    | X4 _    -> -6
    | X5 _    -> -7
    | X6 _    -> -8
    | X7 _    -> -9

  let compare_tag a b = theory_num a - theory_num b

  let str_cmp a b =
    if CX.equal a b then 0
    else
      match a.v, b.v with
      | X1 _, X1 _ -> X1.compare a b
      | X2 _, X2 _ -> X2.compare a b
      | X3 _, X3 _ -> X3.compare a b
      | X4 _, X4 _ -> X4.compare a b
      | X5 _, X5 _ -> X5.compare a b
      | X6 _, X6 _ -> X6.compare a b
      | X7 _, X7 _ -> X7.compare a b
      | Term x  , Term y  -> Expr.compare x y
      | Ac x    , Ac y    -> AC.compare x y
      | va, vb            -> compare_tag va vb

  (*** implementations before hash-consing semantic values

       let equal a b = CX.compare a b = 0

       let hash r = match r.v with
       | Term  t -> Expr.hash t
       | Ac x -> AC.hash x
       | X1 x -> X1.hash x
       | X2 x -> X2.hash x
       | X3 x -> X3.hash x
       | X4 x -> X4.hash x
       | X5 x -> X5.hash x

   ***)

  let equal a b = a.id = b.id

  let hash v = v.id

  let hash_cmp a b = a.id - b.id

  (*
    should be called hash_cmp and used where structural_compare is
    not needed

    let compare a b =
    let c = Pervasives.compare a.id b.id in
    let c' = Pervasives.compare b.id a.id in
    assert ((c = 0 && c' = 0) || (c*c' < 0));
    c
  *)

  module SX = Set.Make(struct type t = r let compare = CX.hash_cmp end)

  let leaves r =
    match r.v with
    | X1 t -> X1.leaves t
    | X2 t -> X2.leaves t
    | X3 t -> X3.leaves t
    | X4 t -> X4.leaves t
    | X5 t -> X5.leaves t
    | X6 t -> X6.leaves t
    | X7 t -> X7.leaves t
    | Ac t -> r :: (AC.leaves t)
    | Term _ -> [r]

  let subst p v r =
    if equal p v then r
    else match r.v with
      | X1 t   -> X1.subst p v t
      | X2 t   -> X2.subst p v t
      | X3 t   -> X3.subst p v t
      | X4 t   -> X4.subst p v t
      | X5 t   -> X5.subst p v t
      | X6 t   -> X6.subst p v t
      | X7 t   -> X7.subst p v t
      | Ac t   -> if equal p r then v else AC.subst p v t
      | Term _ -> if equal p r then v else r

  let make t =
    let { Expr.f = sb; ty; _ } =
      match Expr.term_view t with
      | Expr.Not_a_term _ -> assert false
      | Expr.Term tt -> tt
    in
    match
      X1.is_mine_symb sb ty,
      not (restricted ()) && X2.is_mine_symb sb ty,
      not (restricted ()) && X3.is_mine_symb sb ty,
      not (restricted ()) && X4.is_mine_symb sb ty,
      not (restricted ()) && X5.is_mine_symb sb ty,
      not (restricted ()) && X6.is_mine_symb sb ty,
      not (restricted ()) && X7.is_mine_symb sb ty,
      AC.is_mine_symb sb ty
    with
    | true  , false , false , false, false, false, false, false -> X1.make t
    | false , true  , false , false, false, false, false, false -> X2.make t
    | false , false , true  , false, false, false, false, false -> X3.make t
    | false , false , false , true , false, false, false, false -> X4.make t
    | false , false , false , false, true , false, false, false -> X5.make t
    | false , false , false , false, false, true , false, false -> X6.make t
    | false , false , false , false, false, false, true , false -> X7.make t
    | false , false , false , false, false, false, false, true  -> AC.make t
    | false , false , false , false, false, false, false, false ->
      term_embed t, []
    | _ -> assert false

  let fully_interpreted sb ty =
    match
      X1.is_mine_symb sb ty,
      not (restricted ()) && X2.is_mine_symb sb ty,
      not (restricted ()) && X3.is_mine_symb sb ty,
      not (restricted ()) && X4.is_mine_symb sb ty,
      not (restricted ()) && X5.is_mine_symb sb ty,
      not (restricted ()) && X6.is_mine_symb sb ty,
      not (restricted ()) && X7.is_mine_symb sb ty,
      AC.is_mine_symb sb ty
    with
    | true  , false , false , false, false, false, false, false ->
      X1.fully_interpreted sb
    | false , true  , false , false, false, false, false, false ->
      X2.fully_interpreted sb
    | false , false , true  , false, false, false, false, false ->
      X3.fully_interpreted sb
    | false , false , false , true , false, false, false, false ->
      X4.fully_interpreted sb
    | false , false , false , false, true , false, false, false ->
      X5.fully_interpreted sb
    | false , false , false , false, false, true , false, false ->
      X6.fully_interpreted sb
    | false , false , false , false, false, false, true , false ->
      X7.fully_interpreted sb
    | false , false , false , false, false, false, false, true  ->
      AC.fully_interpreted sb
    | false , false , false , false, false, false, false, false ->
      false
    | _ -> assert false

  let is_solvable_theory_symbol sb ty =
    X1.is_mine_symb sb ty ||
    not (restricted ()) &&
    ((*X2.is_mine_symb sb || print records*)
      X3.is_mine_symb sb ty ||
      X4.is_mine_symb sb ty ||
      X5.is_mine_symb sb ty)(* ||
                               AC.is_mine_symb sb*)


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
        X1.is_mine_symb ac.Sig.h ty,
        X2.is_mine_symb ac.Sig.h ty,
        X3.is_mine_symb ac.Sig.h ty,
        X4.is_mine_symb ac.Sig.h ty,
        X5.is_mine_symb ac.Sig.h ty,
        X6.is_mine_symb ac.Sig.h ty,
        X7.is_mine_symb ac.Sig.h ty,
        AC.is_mine_symb ac.Sig.h ty with
      (*AC.is_mine may say F if Options.no_ac is set to F dynamically *)
      | true  , false , false , false, false, false, false, false -> X1.color ac
      | false , true  , false , false, false, false, false, false -> X2.color ac
      | false , false , true  , false, false, false, false, false -> X3.color ac
      | false , false , false , true , false, false, false, false -> X4.color ac
      | false , false , false , false, true , false, false, false -> X5.color ac
      | false , false , false , false, false, true , false, false -> X6.color ac
      | false , false , false , false, false, false, true , false -> X7.color ac
      | _  -> ac_embed ac


  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let print fmt r =
      if term_like_pp () then
        match r.v with
        | X1 t    -> fprintf fmt "%a" X1.print t
        | X2 t    -> fprintf fmt "%a" X2.print t
        | X3 t    -> fprintf fmt "%a" X3.print t
        | X4 t    -> fprintf fmt "%a" X4.print t
        | X5 t    -> fprintf fmt "%a" X5.print t
        | X6 t    -> fprintf fmt "%a" X6.print t
        | X7 t    -> fprintf fmt "%a" X7.print t
        | Term t  -> fprintf fmt "%a" Expr.print t
        | Ac t    -> fprintf fmt "%a" AC.print t
      else
        match r.v with
        | X1 t    -> fprintf fmt "X1(%s):[%a]" X1.name X1.print t
        | X2 t    -> fprintf fmt "X2(%s):[%a]" X2.name X2.print t
        | X3 t    -> fprintf fmt "X3(%s):[%a]" X3.name X3.print t
        | X4 t    -> fprintf fmt "X4(%s):[%a]" X4.name X4.print t
        | X5 t    -> fprintf fmt "X5(%s):[%a]" X5.name X5.print t
        | X6 t    -> fprintf fmt "X6(%s):[%a]" X6.name X6.print t
        | X7 t    -> fprintf fmt "X7(%s):[%a]" X7.name X7.print t
        | Term t  -> fprintf fmt "FT:[%a]" Expr.print t
        | Ac t    -> fprintf fmt "Ac:[%a]" AC.print t

    let print_sbt msg sbs =
      if debug_combine () then begin
        let c = ref 0 in
        fprintf fmt "%s subst:@." msg;
        List.iter
          (fun (p,v) ->
             incr c;
             fprintf fmt " %d) %a |-> %a@." !c print p print v) sbs;
        fprintf fmt "@."
      end

    let debug_abstraction_result oa ob a b acc =
      if debug_combine () then begin
        fprintf fmt "@.== debug_abstraction_result ==@.";
        fprintf fmt "@.Initial equaliy:   %a = %a@." CX.print oa CX.print ob;
        fprintf fmt "abstracted equality: %a = %a@." CX.print a CX.print b;
        fprintf fmt "selectors elimination result:@.";
        let cpt = ref 0 in
        List.iter
          (fun (p,v) ->
             incr cpt;
             fprintf fmt "\t(%d) %a |-> %a@." !cpt CX.print p CX.print v
          )acc;
        fprintf fmt "@."
      end

    let solve_one a b =
      if debug_combine () then
        fprintf fmt "solve one %a = %a@." CX.print a CX.print b

    let debug_abstract_selectors a =
      if debug_combine () then
        fprintf fmt "abstract selectors of %a@." CX.print a

    let assert_have_mem_types tya tyb =
      assert (
        not (Options.enable_assertions()) ||
        if not (Ty.compare tya tyb = 0) then (
          fprintf fmt "@.Tya = %a  and @.Tyb = %a@.@."
            Ty.print tya Ty.print tyb;
          false)
        else true)

  end
  (*BISECT-IGNORE-END*)

  let print = Debug.print

  let abstract_selectors a acc =
    Debug.debug_abstract_selectors a;
    match a.v with
    | X1 a   -> X1.abstract_selectors a acc
    | X2 a   -> X2.abstract_selectors a acc
    | X3 a   -> X3.abstract_selectors a acc
    | X4 a   -> X4.abstract_selectors a acc
    | X5 a   -> X5.abstract_selectors a acc
    | X6 a   -> X6.abstract_selectors a acc
    | X7 a   -> X7.abstract_selectors a acc
    | Term _ -> a, acc
    | Ac a   -> AC.abstract_selectors a acc

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
            Format.eprintf "Ici: %a@." CX.print p;
            assert false
        )sbs
    in
    Debug.print_sbt "Triangular and cleaned" sbs;
    (*
      This assert is not TRUE because of AC and distributivity of '*'
      assert (not (Options.enable_assertions()) ||
      equal (apply_subst a sbs) (apply_subst b sbs));
    *)
    sbs

  let apply_subst_right r sbt =
    List.fold_right (fun (p,v)r  -> CX.subst p v r) sbt r

  let solve_uninterpreted r1 r2 pb = (* r1 != r2*)
    if debug_combine () then
      fprintf fmt "solve uninterpreted %a = %a@." print r1 print r2;
    if CX.str_cmp r1 r2 > 0 then { pb with sbt = (r1,r2)::pb.sbt }
    else { pb with sbt = (r2,r1)::pb.sbt }

  let rec solve_list pb =
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
          | Ty.Tint | Ty.Treal -> X1.solve ra rb pb
          | Ty.Trecord _       -> X2.solve ra rb pb
          | Ty.Tbitv _         -> X3.solve ra rb pb
          | Ty.Tsum _          -> X5.solve ra rb pb
          (*| Ty.Tunit           -> pb *)
          | Ty.Tadt _ when not (Options.disable_adts()) -> X6.solve ra rb pb
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

  let assign_value r distincts eq =
    let opt = match r.v, type_info r with
      | _, Ty.Tint
      | _, Ty.Treal     -> X1.assign_value r distincts eq
      | _, Ty.Trecord _ -> X2.assign_value r distincts eq
      | _, Ty.Tbitv _   -> X3.assign_value r distincts eq
      | _, Ty.Tfarray _ -> X4.assign_value r distincts eq
      | _, Ty.Tsum _    -> X5.assign_value r distincts eq
      | _, Ty.Tadt _    when not (Options.disable_adts()) ->
        X6.assign_value r distincts eq
      | Term t, ty      -> (* case disable_adts() handled here *)
        if (Expr.depth t) = 1 ||
           List.exists (fun (t,_) -> (Expr.depth t) = 1) eq then None
        else Some (Expr.fresh_name ty, false) (* false <-> not a case-split *)
      | _               -> assert false
    in
    if debug_interpretation() then
      begin
        fprintf fmt "[combine] assign value to representative %a : " print r;
        match opt with
        | None -> fprintf fmt "None@."
        | Some(res, _is_cs) -> fprintf fmt " %a@." Expr.print res
      end;
    opt

  let choose_adequate_model t rep l =
    let r, pprint =
      match Expr.type_info t with
      | Ty.Tint
      | Ty.Treal     -> X1.choose_adequate_model t rep l
      | Ty.Tbitv _   -> X3.choose_adequate_model t rep l
      | Ty.Tsum _    -> X5.choose_adequate_model t rep l
      | Ty.Tadt _    when not (Options.disable_adts()) ->
        X6.choose_adequate_model t rep l
      | Ty.Trecord _ -> X2.choose_adequate_model t rep l
      | Ty.Tfarray _ -> X4.choose_adequate_model t rep l
      | _            ->
        let acc =
          List.fold_left
            (fun acc (s, r) ->
               if (Expr.depth s) <= 1 then
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
            | Some t, true when (Expr.depth t) = 1 -> rep
            | _ ->
              if debug_interpretation() then begin
                fprintf fmt "[Combine.choose_adequate_model] ";
                fprintf fmt "What to choose for term %a with rep %a ??@."
                  Expr.print t print rep;
                List.iter
                  (fun (t, r) ->
                     fprintf fmt "  > impossible case: %a -- %a@."
                       Expr.print t print r
                  )l;
              end;
              assert false
        in
        ignore (flush_str_formatter ());
        fprintf str_formatter "%a" print r; (* it's a EUF constant *)
        r, flush_str_formatter ()
    in
    if debug_interpretation() then
      fprintf fmt "[combine] %a selected as a model for %a@."
        print r Expr.print t;
    r, pprint

end

and TX1 : Polynome.T
  with type r = CX.r =
  Arith.Type(CX)

and X1 : Sig.SHOSTAK
  with type t = TX1.t
   and type r = CX.r =
  Arith.Shostak
    (CX)
    (struct
      include TX1
      let extract = CX.extract1
      let embed =  CX.embed1
    end)

and X2 : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Records.abstract =
  Records.Shostak
    (struct
      include CX
      let extract = extract2
      let embed = embed2
    end)

and X3 : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Bitv.abstract =
  Bitv.Shostak
    (struct
      include CX
      let extract = extract3
      let embed = embed3
    end)

and X4 : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Arrays.abstract =
  Arrays.Shostak
    (struct
      include CX
      let extract = extract4
      let embed = embed4
    end)

and X5 : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Enum.abstract =
  Enum.Shostak
    (struct
      include CX
      let extract = extract5
      let embed = embed5
    end)

and X6 : Sig.SHOSTAK
  with type r = CX.r
   and type t = CX.r Adt.abstract =
  Adt.Shostak
    (struct
      include CX
      let extract = extract6
      let embed = embed6
    end)

and X7 : Sig.SHOSTAK
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

module Combine = CX
module Arith = X1
module Records = X2
module Bitv = X3
module Arrays = X4
module Enum = X5
module Adt = X6
module Ite = X7
module Polynome = TX1
module Ac = AC

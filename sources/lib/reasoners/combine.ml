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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Format
open Options
open Sig

(*** Combination module of Shostak theories ***)

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

end =
struct

  type rview =
    | Term  of Term.t
    | Ac    of AC.t
    | X1    of X1.t
    | X2    of X2.t
    | X3    of X3.t
    | X4    of X4.t
    | X5    of X5.t

  type r = {v : rview ; id : int}

  (* begin: Hashconsing modules and functions *)

  module View = struct

    type elt = r

    let set_id tag r = { r with id=tag }

    let hash r =
      match r.v with
      | X1 x   -> 1 + 8 * X1.hash x
      | X2 x   -> 2 + 8 * X2.hash x
      | X3 x   -> 3 + 8 * X3.hash x
      | X4 x   -> 4 + 8 * X4.hash x
      | X5 x   -> 5 + 8 * X5.hash x
      | Ac ac  -> 7 + 8 * AC.hash ac
      | Term t -> 6 + 8 * Term.hash t

    let eq  r1 r2 =
      match r1.v, r2.v with
      | X1 x, X1 y -> X1.equal x y
      | X2 x, X2 y -> X2.equal x y
      | X3 x, X3 y -> X3.equal x y
      | X4 x, X4 y -> X4.equal x y
      | X5 x, X5 y -> X5.equal x y
      | Term x  , Term y  -> Term.equal x y
      | Ac x    , Ac    y -> AC.equal x y
      | _ -> false

    let initial_size = 4096

    let disable_weaks () = Options.disable_weaks ()

  end

  module HC = Hconsing.Make(View)

  let hcons v = HC.make v

  (* end: Hconsinging modules and functions *)

  let embed1 x = hcons {v = X1 x; id = -1000 (* dummy *)}
  let embed2 x = hcons {v = X2 x; id = -1000 (* dummy *)}
  let embed3 x = hcons {v = X3 x; id = -1000 (* dummy *)}
  let embed4 x = hcons {v = X4 x; id = -1000 (* dummy *)}
  let embed5 x = hcons {v = X5 x; id = -1000 (* dummy *)}

  let ac_embed ({Sig.l = l} as t) =
    match l with
    | []    ->
      assert false
    | [x, 1] -> x
    | l     ->
      let sort = List.fast_sort (fun (x,n) (y,m) -> CX.str_cmp x y) in
      let ac = { t with Sig.l = List.rev (sort l) } in
      hcons {v = Ac ac; id = -1000 (* dummy *)}

  let term_embed t = hcons {v = Term t; id = -1000 (* dummy *)}

  let extract1 = function {v=X1 r} -> Some r | _ -> None
  let extract2 = function {v=X2 r} -> Some r | _ -> None
  let extract3 = function {v=X3 r} -> Some r | _ -> None
  let extract4 = function {v=X4 r} -> Some r | _ -> None
  let extract5 = function {v=X5 r} -> Some r | _ -> None

  let ac_extract = function
    | {v = Ac t}   -> Some t
    | _ -> None

  let term_extract r =
    match r.v with
    | X1 _ -> X1.term_extract r
    | X2 _ -> X2.term_extract r
    | X3 _ -> X3.term_extract r
    | X4 _ -> X4.term_extract r
    | X5 _ -> X5.term_extract r
    | Ac _ -> None, false (* SYLVAIN : TODO *)
    | Term t -> Some t, true

  let top () = term_embed Term.vrai
  let bot () = term_embed Term.faux

  let is_an_eq a =
    match Literal.LT.view a with Literal.Builtin _ -> false | _ -> true

  let is_int v =
    let ty  = match v with
      | X1 x -> X1.type_info x
      | X2 x -> X2.type_info x
      | X3 x -> X3.type_info x
      | X4 x -> X4.type_info x
      | X5 x -> X5.type_info x
      | Term t -> (Term.view t).Term.ty
      | Ac x -> AC.type_info x
    in
    ty == Ty.Tint

  let type_info = function
    | {v=X1 t}   -> X1.type_info t
    | {v=X2 t}   -> X2.type_info t
    | {v=X3 t}   -> X3.type_info t
    | {v=X4 t}   -> X4.type_info t
    | {v=X5 t}   -> X5.type_info t
    | {v=Ac x}   -> AC.type_info x
    | {v=Term t} -> let {Term.ty = ty} = Term.view t in ty

  (* Xi < Term < Ac *)
  let theory_num x = match x with
    | Ac _    -> -1
    | Term  _ -> -2
    | X1 _    -> -3
    | X2 _    -> -4
    | X3 _    -> -5
    | X4 _    -> -6
    | X5 _    -> -7

  let compare_tag a b = theory_num a - theory_num b

  let str_cmp a b =
    if CX.equal a b then 0
    else
      match a.v, b.v with
      | X1 x, X1 y -> X1.compare a b
      | X2 x, X2 y -> X2.compare a b
      | X3 x, X3 y -> X3.compare a b
      | X4 x, X4 y -> X4.compare a b
      | X5 x, X5 y -> X5.compare a b
      | Term x  , Term y  -> Term.compare x y
      | Ac x    , Ac    y -> AC.compare x y
      | va, vb            -> compare_tag va vb

  (*** implementations before hash-consing semantic values

  let equal a b = CX.compare a b = 0

  let hash r = match r.v with
    | Term  t -> Term.hash t
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
    | Ac t   -> if equal p r then v else AC.subst p v t
    | Term _ -> if equal p r then v else r

  let make t =
    let {Term.f=sb} = Term.view t in
    match
      X1.is_mine_symb sb,
      not (restricted ()) && X2.is_mine_symb sb,
      not (restricted ()) && X3.is_mine_symb sb,
      not (restricted ()) && X4.is_mine_symb sb,
      not (restricted ()) && X5.is_mine_symb sb,
      AC.is_mine_symb sb
    with
    | true  , false , false, false, false, false -> X1.make t
    | false , true  , false, false, false, false -> X2.make t
    | false , false , true , false, false, false -> X3.make t
    | false , false , false, true , false, false -> X4.make t
    | false , false , false, false, true , false -> X5.make t
    | false , false , false, false, false, true  -> AC.make t
    | false , false , false, false, false, false -> term_embed t, []
    | _ -> assert false

  let fully_interpreted sb =
    match
      X1.is_mine_symb sb,
      not (restricted ()) && X2.is_mine_symb sb,
      not (restricted ()) && X3.is_mine_symb sb,
      not (restricted ()) && X4.is_mine_symb sb,
      not (restricted ()) && X5.is_mine_symb sb,
      AC.is_mine_symb sb
    with
    | true  , false , false, false, false, false -> X1.fully_interpreted sb
    | false , true  , false, false, false, false -> X2.fully_interpreted sb
    | false , false , true , false, false, false -> X3.fully_interpreted sb
    | false , false , false, true , false, false -> X4.fully_interpreted sb
    | false , false , false, false, true , false -> X5.fully_interpreted sb
    | false , false , false, false, false, true  -> AC.fully_interpreted sb
    | false , false , false, false, false, false -> false
    | _ -> assert false

  let is_solvable_theory_symbol sb =
    X1.is_mine_symb sb ||
      not (restricted ()) &&
      ((*X2.is_mine_symb sb || print records*)
         X3.is_mine_symb sb ||
         X4.is_mine_symb sb ||
         X5.is_mine_symb sb)(* ||
         AC.is_mine_symb sb*)


  let is_a_leaf r = match r.v with
    | Term _ | Ac _ -> true
    | _ -> false

  let color ac =
    match ac.Sig.l with
    | [] -> assert false
    | [r,1] -> r
    | _ ->
      match
        X1.is_mine_symb ac.Sig.h,
        X2.is_mine_symb ac.Sig.h,
        X3.is_mine_symb ac.Sig.h,
        X4.is_mine_symb ac.Sig.h,
        X5.is_mine_symb ac.Sig.h,
        AC.is_mine_symb ac.Sig.h with
	| true  , false , false, false, false, false -> X1.color ac
	| false , true  , false, false, false, false -> X2.color ac
	| false , false , true , false, false, false -> X3.color ac
	| false , false , false, true , false, false -> X4.color ac
	| false , false , false, false, true, false -> X5.color ac
        (*AC.is_mine may say F if Options.no_ac is set to F dynamically *)
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
        | Term t  -> fprintf fmt "%a" Term.print t
        | Ac t    -> fprintf fmt "%a" AC.print t
      else
        match r.v with
        | X1 t    -> fprintf fmt "X1(%s):[%a]" X1.name X1.print t
        | X2 t    -> fprintf fmt "X2(%s):[%a]" X2.name X2.print t
        | X3 t    -> fprintf fmt "X3(%s):[%a]" X3.name X3.print t
        | X4 t    -> fprintf fmt "X3(%s):[%a]" X4.name X4.print t
        | X5 t    -> fprintf fmt "X3(%s):[%a]" X5.name X5.print t
        | Term t  -> fprintf fmt "FT:[%a]" Term.print t
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

    let solve a b =
      if debug_combine () then
        fprintf fmt "@.[combine] I solve %a = %a:@." print a print b

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
    | Term _ -> a, acc
    | Ac a   -> AC.abstract_selectors a acc

  let abstract_equality a b =
    let aux r acc =
      match r.v with
      | Ac ({l=args} as ac) ->
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
      List.filter (fun (p,v) ->
        match p.v with
        | Ac _ -> true | Term _ -> SX.mem p original
        | _ -> assert false
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

  let merge_sbt sbt1 sbt2 = sbt1 @ sbt2

  let solve_uninterpreted r1 r2 pb = (* r1 != r2*)
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
            [@ocaml.ppwarning "TODO: a simple way of handling equalities \
with void and unit is to add this case is the solver !"]
          (*| Ty.Tunit           -> pb *)
          | _                  -> solve_uninterpreted ra rb pb
        in
        solve_list pb

  let solve_abstracted oa ob a b sbt =
    Debug.debug_abstraction_result oa ob a b sbt;
    let ra = apply_subst_right a sbt in
    let rb = apply_subst_right b sbt in
    let sbt' = solve_list { sbt=[] ; eqs=[ra,rb] } in
    match sbt', sbt with
    | [], _::_ -> [] (* the original equality was trivial *)
    | _ -> make_idemp oa ob (List.rev_append sbt sbt')

  let solve  a b =
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
      | Term t, ty      ->
        if (Term.view t).Term.depth = 1 ||
          List.exists (fun (t,_) -> (Term.view t).Term.depth = 1) eq then None
        else Some (Term.fresh_name ty, false) (* false <-> not a case-split *)
      | _               -> assert false
    in
    if debug_interpretation() then
      begin
        fprintf fmt "[combine] assign value to representative %a : " print r;
        match opt with
        | None -> fprintf fmt "None@."
        | Some(res, is_cs) -> fprintf fmt " %a@." Term.print res
      end;
    opt

  let choose_adequate_model t rep l =
    let r, pprint =
      match Term.type_info t with
      | Ty.Tint
      | Ty.Treal     -> X1.choose_adequate_model t rep l
      | Ty.Tbitv _   -> X3.choose_adequate_model t rep l
      | Ty.Tsum _    -> X5.choose_adequate_model t rep l
      | Ty.Trecord _ -> X2.choose_adequate_model t rep l
      | Ty.Tfarray _ -> X4.choose_adequate_model t rep l
      | _            ->
        let acc =
          List.fold_left
            (fun acc (s, r) ->
              if (Term.view s).Term.depth <= 1 then
                match acc with
                | Some(s', r') when Term.compare s' s > 0 -> acc
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
            | Some t, true when (Term.view t).Term.depth = 1 -> rep
            | _ ->
              if debug_interpretation() then begin
                fprintf fmt "[Combine.choose_adequate_model] ";
                fprintf fmt "What to choose for term %a with rep %a ??@."
                  Term.print t print rep;
                List.iter
                  (fun (t, r) ->
                    fprintf fmt "  > impossible case: %a -- %a@."
                      Term.print t print r
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
        print r Term.print t;
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
 and type t = CX.r Sum.abstract =
        Sum.Shostak
          (struct
            include CX
            let extract = extract5
            let embed = embed5
           end)

(* Its signature is not Sig.SHOSTAK because it does not provide a solver *)
and AC : Ac.S
 with type r = CX.r =
  Ac.Make(CX)


(*** Instantiation of Uf.Make and Use.Make with CX ***)

module Uf : Uf.S with type r = CX.r = Uf.Make(CX)
module Use = Use.Make(CX)

(*** Combination module of Relations ***)

module Rel1 : Sig.RELATION
  with type r = CX.r and type uf = Uf.t =
         Arith.Relation (CX)(Uf)
    (struct
      include TX1
      let extract = CX.extract1
      let embed =  CX.embed1
     end)

module Rel2 : Sig.RELATION
  with type r = CX.r and type uf = Uf.t =
         Records.Relation
           (struct
             include CX
             let extract = extract2
             let embed = embed2
            end)(Uf)


module Rel3 : Sig.RELATION
  with type r = CX.r and type uf = Uf.t =
         Bitv.Relation
           (struct
             include CX
             let extract = extract3
             let embed = embed3
            end)(Uf)


module Rel4 : Sig.RELATION
  with type r = CX.r and type uf = Uf.t =
         Arrays.Relation
           (struct
             include CX
             let extract = extract4
             let embed = embed4
            end)(Uf)


module Rel5 : Sig.RELATION
  with type r = CX.r and type uf = Uf.t =
         Sum.Relation
           (struct
             include CX
             let extract = extract5
             let embed = embed5
            end)(Uf)


module Relation : Sig.RELATION with type r = CX.r and type uf = Uf.t = struct
  type r = CX.r
  type uf = Uf.t

  type t = {
    r1: Rel1.t;
    r2: Rel2.t;
    r3: Rel3.t;
    r4: Rel4.t;
    r5: Rel5.t;
  }

  let empty classes = {
    r1=Rel1.empty classes;
    r2=Rel2.empty classes;
    r3=Rel3.empty classes;
    r4=Rel4.empty classes;
    r5=Rel5.empty classes;
  }

  let (|@|) l1 l2 =
    if l1 == [] then l2
    else if l2 == [] then l1
    else List.rev_append l1 l2

  let assume env uf sa =
    Options.exec_thread_yield ();
    let env1, { assume = a1; remove = rm1} =
      Rel1.assume env.r1 uf sa in
    let env2, { assume = a2; remove = rm2} =
      Rel2.assume env.r2 uf sa in
    let env3, { assume = a3; remove = rm3} =
      Rel3.assume env.r3 uf sa in
    let env4, { assume = a4; remove = rm4} =
      Rel4.assume env.r4 uf sa in
    let env5, { assume = a5; remove = rm5} =
      Rel5.assume env.r5 uf sa in
    {r1=env1; r2=env2; r3=env3; r4=env4; r5=env5},
    { assume = a1 |@| a2 |@| a3 |@| a4 |@| a5;
      remove = rm1 |@| rm2 |@| rm3 |@| rm4 |@| rm5;}

  let assume_th_elt env th_elt =
    Options.exec_thread_yield ();
    let env1 = Rel1.assume_th_elt env.r1 th_elt in
    let env2 = Rel2.assume_th_elt env.r2 th_elt in
    let env3 = Rel3.assume_th_elt env.r3 th_elt in
    let env4 = Rel4.assume_th_elt env.r4 th_elt in
    let env5 = Rel5.assume_th_elt env.r5 th_elt in
    {r1=env1; r2=env2; r3=env3; r4=env4; r5=env5}

  let query env uf a =
    Options.exec_thread_yield ();
    match Rel1.query env.r1 uf a with
      | Yes _ as ans -> ans
      | No ->
	match Rel2.query env.r2 uf a with
	  | Yes _ as ans -> ans
	  | No ->
	    match
              Rel3.query env.r3 uf a with
		| Yes _ as ans -> ans
		| No ->
		  match
                    Rel4.query
                      env.r4 uf a with
		        | Yes _ as ans -> ans
		        | No ->
                          Rel5.query
                            env.r5 uf a

  let case_split env uf ~for_model =
    Options.exec_thread_yield ();
    let seq1 = Rel1.case_split env.r1 uf for_model in
    let seq2 = Rel2.case_split env.r2 uf for_model in
    let seq3 = Rel3.case_split env.r3 uf for_model in
    let seq4 = Rel4.case_split env.r4 uf for_model in
    let seq5 = Rel5.case_split env.r5 uf for_model in
    let l = seq1 |@| seq2 |@| seq3 |@| seq4 |@| seq5 in
    List.sort
      (fun (_,_,sz1) (_,_,sz2) ->
        match sz1, sz2 with
        | CS(_,sz1), CS(_,sz2) -> Numbers.Q.compare sz1 sz2
        | _ -> assert false
      )l


  let add env uf r t =
    Options.exec_thread_yield ();
    {r1=Rel1.add env.r1 uf r t;
     r2=Rel2.add env.r2 uf r t;
     r3=Rel3.add env.r3 uf r t;
     r4=Rel4.add env.r4 uf r t;
     r5=Rel5.add env.r5 uf r t;
    }


  let instantiate ~do_syntactic_matching t_match env uf selector =
    Options.exec_thread_yield ();
    let r1, l1 =
      Rel1.instantiate ~do_syntactic_matching t_match env.r1 uf selector in
    let r2, l2 =
      Rel2.instantiate ~do_syntactic_matching t_match env.r2 uf selector in
    let r3, l3 =
      Rel3.instantiate ~do_syntactic_matching t_match env.r3 uf selector in
    let r4, l4 =
      Rel4.instantiate ~do_syntactic_matching t_match env.r4 uf selector in
    let r5, l5 =
      Rel5.instantiate ~do_syntactic_matching t_match env.r5 uf selector in
    {r1=r1; r2=r2; r3=r3; r4=r4; r5=r5},
    l5 |@| l4 |@| l3 |@| l2 |@| l1

  let retrieve_used_context env dep =
    Options.exec_thread_yield ();
    let r1, l1 = Rel1.retrieve_used_context env.r1 dep in
    let r2, l2 = Rel2.retrieve_used_context env.r2 dep in
    let r3, l3 = Rel3.retrieve_used_context env.r3 dep in
    let r4, l4 = Rel4.retrieve_used_context env.r4 dep in
    let r5, l5 = Rel5.retrieve_used_context env.r5 dep in
    r5 |@| r4 |@| r3 |@| r2 |@| r1,
    l5 |@| l4 |@| l3 |@| l2 |@| l1

  let print_model fmt env rs =
    Rel1.print_model fmt env.r1 rs;
    Rel2.print_model fmt env.r2 rs;
    Rel3.print_model fmt env.r3 rs;
    Rel4.print_model fmt env.r4 rs;
    Rel5.print_model fmt env.r5 rs


  let new_terms env =
    let t1 = Rel1.new_terms env.r1 in
    let t2 = Rel2.new_terms env.r2 in
    let t3 = Rel3.new_terms env.r3 in
    let t4 = Rel4.new_terms env.r4 in
    let t5 = Rel5.new_terms env.r5 in
    Term.Set.union t1
      (Term.Set.union t2
         (Term.Set.union t3
            (Term.Set.union t4 t5)))

end

module Shostak = CX

module Sy = Symbols
module E = Expr

(* lets_counter is used to order 'let' constructs before they are added to the
   'lets' map. This way, we keep their order in the original expression, and
   reconstruct them correctly in mk_lifted. *)
let lets_counter = ref 0

let add_let sy e (lets: (E.t * int) Sy.Map.t) =
  incr lets_counter;
  Sy.Map.add sy (e, !lets_counter) lets

let rec purify_term (t: E.t) lets =
  if t.pure then t, lets
  else
    match t.f, t.bind with
    | Sy.Let, B_let { let_v; let_e; in_e; _ } ->
      (* let_e is purified when processing the lets map *)
      let in_e , lets = purify_term in_e  lets in
      in_e, add_let let_v let_e lets

    | (Sy.Lit _ | Sy.Form _), _ ->
      let fresh_sy = Sy.fresh ~is_var:true "Pur-F" in
      E.mk_term fresh_sy [] t.ty , add_let fresh_sy t lets

    | _ -> (* detect ITEs *)
      match t.xs with
      | [_;_;_] when Sy.is_ite t.f ->
        let fresh_sy = Sy.fresh ~is_var:true "Pur-Ite" in
        E.mk_term fresh_sy [] t.ty , add_let fresh_sy t lets

      | _ ->
        let xs, lets =
          List.fold_left (fun (acc, lets) t ->
              let t', lets' = purify_term t lets in
              t' :: acc, lets'
            ) ([], lets) (List.rev t.xs)
        in
        E.mk_term t.f xs t.ty, lets

and purify_generic mk l =
  let l, lets =
    List.fold_left (fun (acc, lets) t ->
        let t', lets' = purify_term t lets in
        t' :: acc, lets'
      )([], Sy.Map.empty) (List.rev l)
  in
  mk_lifted (mk l) lets

and purify_eq l =
  purify_generic (fun l ->
      match l with
      | [] | [_] ->
        failwith "unexpected expression in purify_eq"
      | [a; b] -> E.mk_eq ~iff:true a b
      | l -> E.mk_nary_eq l
    ) l

and purify_distinct l =
  purify_generic (fun l -> E.mk_distinct ~iff:true l) l

and purify_builtin neg pred l =
  purify_generic (fun l -> E.mk_builtin ~is_pos:neg pred l) l

and purify_predicate p is_neg =
  purify_generic (fun l ->
      match l with
      | [e] -> if is_neg then E.neg e else e
      | _ -> failwith "unexpected expression in purify_predicate"
    ) [p]

and purify_literal (e: E.t) =
  if List.for_all E.is_pure e.xs then e (* this is OK for lits and terms *)
  else match E.lit_view e with
    | Eq {lhs; rhs} ->
      assert (lhs.ty != Ty.Tbool);
      (* TODO: translate to iff *)
      purify_eq [lhs; rhs]
    | Eql l      -> purify_eq l
    | Distinct l -> purify_distinct l
    | Builtin (neg,prd,l) -> purify_builtin neg prd l
    | Pred (p, is_neg) -> purify_predicate p is_neg

and purify_form (e: E.t) =
  assert (e.ty == Ty.Tbool);
  if E.is_pure e then e (* non negated predicates *)
  else
    match e.f with
    | Sy.True | Sy.False | Sy.Var _ | Sy.In _ -> e
    | Sy.Name _ -> (* non negated predicates with impure parts *)
      let e, lets = purify_term e Sy.Map.empty in
      mk_lifted e lets
    | Sy.Let -> (* let on forms *)
      begin match e.xs, e.bind with
        | [], B_let ({let_v; let_e; in_e; _}) ->
          if let_e.pure && in_e.pure then e
          else
            let let_e', lets = purify_non_toplevel_ite let_e Sy.Map.empty in
            let in_e' = purify_form in_e in
            if let_e == let_e' && in_e == in_e' then e
            else
              mk_lifted
                (E.mk_let let_v let_e in_e)
                lets
        | _, (B_lemma _ | B_skolem _ | B_none | B_let _) ->
          failwith "unexpected expression in purify_form"
      end

    (* When e is an access to a functional array
       in which the stored values are booleans *)
    | Sy.Op Get ->
      begin match e.xs with
        | [fa; i] ->
          let fa', lets =
            if E.is_pure fa then fa, Sy.Map.empty
            else
              purify_term fa Sy.Map.empty
          in
          let i', lets =
            if E.is_pure i then i, lets
            else
              match i.ty with
              | Ty.Tbool -> purify_form i, lets
              | _ -> purify_term i lets
          in
          if i == i' && fa == fa' then e
          else mk_lifted (E.mk_term e.f [fa'; i'] e.ty) lets
        | _ -> failwith "unexpected expression in purify_form"
      end

    | Sy.Void | Sy.Int _ | Sy.Real _ | Sy.Bitv _ | Sy.Op _ | Sy.MapsTo _ ->
      failwith "unexpected expression in purify_form: not a formula"

    | Sy.Lit _ -> purify_literal e
    | Sy.Form x ->
      begin match x, e.xs, e.bind with
        | Sy.F_Unit imp, [a;b], _ ->
          let a' = purify_form a in
          let b' = purify_form b in
          if a == a' && b == b' then e else E.mk_and a' b' imp
        | Sy.F_Clause imp, [a;b], _ ->
          let a' = purify_form a in
          let b' = purify_form b in
          if a == a' && b == b' then e else E.mk_or a' b' imp
        | Sy.F_Iff, [a;b], _ ->
          let a' = purify_form a in
          let b' = purify_form b in
          if a == a' && b == b' then e else E.mk_iff a' b'
        | Sy.F_Xor, [a;b], _ ->
          let a' = purify_form a in
          let b' = purify_form b in
          if a == a' && b == b' then e else E.mk_xor a' b'
        | Sy.F_Lemma, [],
          B_lemma {name; main; toplevel; user_trs; binders; loc; kind; _} ->
          let m = purify_form main in
          if m == main then e
          else E.mk_forall ~name ~loc binders user_trs main ~toplevel
              ~decl_kind:kind
        | Sy.F_Skolem, [],
          B_skolem {name; main; toplevel; user_trs; binders; loc; kind; _} ->
          let m = purify_form main in
          if m == main then e
          else
            E.neg @@ E.mk_forall ~name ~loc binders user_trs (E.neg m) ~toplevel
              ~decl_kind:kind
        | (Sy.F_Unit _ | Sy.F_Clause _ | Sy.F_Iff
          | Sy.F_Xor | Sy.F_Skolem | Sy.F_Lemma),
          _, _ ->
          failwith "unexpected expression in purify_form"
      end

and mk_lifted e lets =
  let ord_lets =  (*beware of ordering: to be checked *)
    List.fast_sort
      (fun (_, (_,cpt1)) (_,(_,cpt2)) -> cpt1 - cpt2) (Sy.Map.bindings lets)
  in
  List.fold_left
    (fun acc (let_v, (let_e, _cpt)) ->
       let let_e, lets = purify_non_toplevel_ite let_e Sy.Map.empty in
       assert (let_e.ty != Ty.Tbool || Sy.Map.is_empty lets);
       mk_lifted (E.mk_let let_v let_e acc) lets
    )e ord_lets

and purify_non_toplevel_ite e lets =
  match e.f, e.xs with
  | _, [c; th; el] when Sy.is_ite e.f ->
    let c = purify_form c in
    let th, lets = purify_non_toplevel_ite th lets in
    let el, lets = purify_non_toplevel_ite el lets in
    E.mk_term e.f [c; th; el] e.ty, lets

  | (Sy.Form _ | Sy.Lit _), _ -> purify_form e, lets
  | _ -> purify_term e lets
(*
let purify_literal a =
  Purification.lets_counter := 0;
  Purification.purify_literal a
*)

let purify_form f =
  lets_counter := 0;
  purify_form f


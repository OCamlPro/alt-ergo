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

module Sy = Symbols
module E = Expr

type sort_var = A | B | C
(* The variables used by the bitvector solver can be split into three
   categories that have associated invariants.

   These invariants are recalled in the functions that make use of them, but the
   outline is as follows. The solver works with *partitioned multi-equations*.
   A partitioned multi-equation is an equality: X == e1 = e2 = ... = en
   where X is a term (or an alien) and e1, e2, ..., en are terms in the
   bitvector algebra, that may contain variables.

   The solver maintains a system of partitioned multi-equations. In the system,
   there is at most one multi-equation for each variable X (while building the
   system, the multi-equations are initially split into binary equations [X = e]
   where this restriction does not apply technically; in this representation,
   all the right-hand side of equalities involving the same left-hand side
   should be treated as part of the same multi-equation).

   Then, we maintain the invariants that, within the system:

   - Each A variable appears at most once (this is used to represent portions
      of a term that are irrelevant to a particular constraint)

   - Each B variable appears in at most one *equation* (i.e. a single term
      [ei]), but appears *multiple times* in that equation (never only once)

   - Each C variable appears at most once in each multi-equation, but appears
      in several (more precisely, two) distinct multi-equations. *)

let pp_sort ppf = function
  | A -> Format.fprintf ppf "a"
  | B -> Format.fprintf ppf "b"
  | C -> Format.fprintf ppf "c"

let compare_sort s1 s2 =
  match s1, s2 with
  | A, A | B, B | C, C -> 0
  | A, (B | C) | B, C -> -1
  | C, (A | B) | B, A -> 1

type tvar = { var : int ; sorte : sort_var }

let pp_tvar ppf { var; sorte } =
  Format.fprintf ppf "%a_%d" pp_sort sorte var

type 'a alpha_term = {
  bv : 'a;
  sz : int;
}

let equal_alpha_term eq { bv = bv1; sz = sz1 } {bv = bv2; sz = sz2 } =
  Int.equal sz1 sz2 && eq bv1 bv2

type 'a signed = { value : 'a ; negated : bool }

let pp_signed pp ppf { value; negated } =
  if negated then Format.fprintf ppf "(bvnot %a)" pp value else pp ppf value

let hash_signed hash { value; negated } =
  if negated then 3 * hash value else hash value

let equal_signed eq { value = v1; negated = n1 } { value = v2 ; negated = n2 } =
  Bool.equal n1 n2 && eq v1 v2

let compare_signed cmp
    { value = v1; negated = n1 } { value = v2; negated = n2 }
  =
  let c = Bool.compare n1 n2 in
  if c <> 0 then c else cmp v1 v2

let pos value = { value ; negated = false }

let neg' value = { value; negated = true }

let snot v = { v with negated = not v.negated }

type 'a simple_term_aux =
  | Cte of bool
  | Other of 'a signed
  | Ext of 'a signed * int * int * int (*// id * size * i * j //*)

let equal_simple_term_aux eq l r =
  match l, r with
  | Cte b1, Cte b2 -> Bool.equal b1 b2
  | Other o1, Other o2 -> equal_signed eq o1 o2
  | Ext (o1, s1, i1, j1), Ext (o2, s2, i2, j2) ->
    i1 = i2 && j1 = j2 && s1 = s2 && equal_signed eq o1 o2
  | _, _ -> false

type 'a simple_term = ('a simple_term_aux) alpha_term

let equal_simple_term eq = equal_alpha_term (equal_simple_term_aux eq)

type 'a abstract =  ('a simple_term) list

let equal_abstract eq = Lists.equal (equal_simple_term eq)

(* for the solver *)

type solver_simple_term_aux =
  | S_Cte of bool
  | S_Var of tvar * bool (* (var, negated) *)

let negate_ssta = function
  | S_Cte b -> S_Cte (not b)
  | S_Var (tv, neg) -> S_Var (tv, not neg)

let equal_solver_simple_term_aux st1 st2 =
  match st1, st2 with
  | S_Cte b1, S_Cte b2 -> Bool.equal b1 b2
  | S_Var (t1, neg1), S_Var (t2, neg2) ->
    Bool.equal neg1 neg2 && t1.var = t2.var
  | S_Cte _, S_Var _ | S_Var _, S_Cte _ -> false

type solver_simple_term = solver_simple_term_aux alpha_term

let negate_sst sst = { sst with bv = negate_ssta sst.bv }

let negate_sstl = List.map negate_sst

let equal_solver_simple_term =
  equal_alpha_term equal_solver_simple_term_aux

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

let compare_alpha_term cmp a1 a2 =
  if a1.sz <> a2.sz then a1.sz - a2.sz else cmp a1.bv a2.bv

type bvbinop = Bv_and | Bv_or

module Shostak(X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name = "bitv"

  let is_mine_symb sy _ =
    match sy with
    | Sy.Bitv _
    | Sy.Op (
        Concat | Extract _ | BVExtend _ | BV2Nat | Nat2BV _
        | BV_repeat _ | BV_rotate _
        | BVnot | BVand | BVor | BVxor | BVnand | BVnor | BVxnor | BVcomp
        | BVneg | BVadd | BVsub | BVmul | BVshl | BVlshr
      ) -> true
    | _ -> false

  let embed r =
    match X.extract r with
    | None ->
      begin
        match X.type_info r with
        | Ty.Tbitv n -> [{bv = Other (pos r) ; sz = n}]
        | _  -> assert false
      end
    | Some b -> b

  (* Note: we must use [x.str_cmp] here because this is used in
     [compare_abstract] which in turn is used by [compare], which is the
     implementation called by [X.str_cmp] itself. *)
  let compare_simple_term = compare_alpha_term (fun st1 st2 ->
      match st1, st2 with
      | Cte b1, Cte b2 -> Bool.compare b1 b2
      | Cte false , _ | _ , Cte true -> -1
      | _ , Cte false | Cte true,_ -> 1

      | Other t1 , Other t2 -> compare_signed X.str_cmp t1 t2
      | _ , Other _ -> -1
      | Other _ , _ -> 1

      | Ext(t1,s1,i1,_) , Ext(t2,s2,i2,_) ->
        let c1 = compare s1 s2 in
        if c1<>0 then c1
        else let c2 = compare i1 i2 in
          if c2 <> 0 then c2 else compare_signed X.str_cmp t1 t2
    )

  let compare_abstract = Lists.compare compare_simple_term

  (* Compare two simple terms. The [equalities_propagation] function below
     requires that : [false ≤ st ≤ true] for all simple terms [st]. *)
  let compare_solver_simple_term = compare_alpha_term (fun st1 st2 ->
      match st1, st2 with
      | S_Cte b1, S_Cte b2 -> Bool.compare b1 b2
      | S_Cte false, _ | _, S_Cte true -> -1
      | _ , S_Cte false | S_Cte true,_ -> 1
      | S_Var (_, true), S_Var (_, false) -> -1
      | S_Var (_, false), S_Var (_, true) -> 1
      | S_Var (v1, b1), S_Var (v2, b2) ->
        let c1 = compare_sort v1.sorte v2.sorte
        in if c1 <> 0 then c1 else compare v1.var v2.var
    )

  module ST_Set = Set.Make (
    struct
      type t = solver_simple_term
      let compare = compare_solver_simple_term
    end)

  module Canonizer = struct

    type term_aux  =
      | I_Cte of bool
      | I_Other of X.r signed
      | I_Ext of term * int * int
      | I_Comp of term * term

    and term = term_aux alpha_term

    let rec negate_aux = function
      | I_Cte b -> I_Cte (not b)
      | I_Other r -> I_Other { r with negated = not r.negated }
      | I_Ext (t, i, j) -> I_Ext (negate t, i, j)
      | I_Comp (t1, t2) -> I_Comp (negate t1, negate t2)

    and negate { bv; sz } = { bv = negate_aux bv; sz }

    let to_i_ast biv =
      let f_aux st =
        {sz = st.sz;
         bv = match st.bv with
           | Cte b -> I_Cte b
           | Other tt -> I_Other tt
           | Ext(tt,siz,i,j)  ->
             let tt' = { sz = siz ; bv = I_Other tt }
             in I_Ext(tt',i,j)
        } in
      List.fold_left
        (fun acc st ->
           let tmp = f_aux st
           in { bv = I_Comp(acc,tmp) ; sz = acc.sz + tmp.sz }
        ) (f_aux (List.hd biv)) (List.tl biv)

    let mk_i_comp t1 t2 sz =
      { bv = I_Comp (t1, t2); sz }

    let rec compare_term_aux t1 t2 = match t1, t2 with
      | I_Cte true, I_Cte true
      | I_Cte false, I_Cte false -> 0
      | I_Cte true, I_Cte _ -> 1
      | I_Cte _, I_Cte _ -> -1

      | I_Other xterm1, I_Other xterm2 ->
        compare_signed X.str_cmp xterm1 xterm2

      | I_Ext (t, i, j), I_Ext (t', i', j') ->
        if i <> i' then i - i'
        else if j <> j' then j - j'
        else compare_term t t'

      | I_Comp (t1, t2), I_Comp (t1', t2') ->
        let cmp = compare_term t1 t1' in
        if cmp = 0 then compare_term t2 t2' else cmp

      | I_Cte _, (I_Other _ | I_Ext _ | I_Comp _ ) -> 1
      | I_Other _, (I_Ext _ | I_Comp _ ) -> 1
      | I_Ext _, I_Comp _ -> 1

      | I_Comp _, (I_Cte _ | I_Other _ | I_Ext _) -> -1
      | I_Ext _, (I_Cte _ | I_Other _) -> -1
      | I_Other _, I_Cte _ -> -1

    and compare_term t1 t2 = compare_alpha_term compare_term_aux t1 t2

    (** **)
    let rec alpha t = match t.bv with
      |I_Cte _ -> [t]
      |I_Other _ -> [t]
      |I_Comp (t1,t2) -> (alpha t1)@(alpha t2)
      |I_Ext(t',i,j) ->
        begin
          match t'.bv with
          |I_Cte _ -> [{t' with sz = j-i+1}]
          |I_Other _ -> [t]
          |I_Ext(t'',k,_) ->
            alpha {t with bv = I_Ext(t'',i+k,j+k)}

          |I_Comp(_,v) when j < v.sz ->
            alpha{t with bv =I_Ext(v,i,j)}

          |I_Comp(u,v) when i >= v.sz ->
            alpha{t with bv=I_Ext(u,i-v.sz,j-v.sz)}

          |I_Comp(u,v) ->
            (alpha {sz = j-v.sz+1 ; bv = I_Ext(u,0,j-v.sz)})
            @(alpha{sz = v.sz-i ; bv = I_Ext(v,i,v.sz-1)})
        end

    (** **)
    let rec beta lt =
      let simple_t st = match st.bv with
        |I_Cte b -> {bv = Cte b ; sz = st.sz}
        |I_Other x -> {bv = Other x ; sz = st.sz}
        |I_Ext(t',i,j) ->
          begin
            match t'.bv with
            |I_Other v ->
              let siz = j-i+1
              in {sz=siz ;
                  bv =if siz=t'.sz then Other v else Ext(v,t'.sz,i,j)}
            |I_Comp _ |I_Ext _ |I_Cte _ -> assert false
          end
        |I_Comp(_,_) -> assert false

      in match lt with
      |[] -> [] (*on peut passer de 2 elts a 0 elts*)
      |[s] -> [simple_t s]
      |s::t::tl' ->
        begin
          match s.bv, t.bv with
          | I_Cte true, I_Cte true | I_Cte false, I_Cte false ->
            beta({s with sz=s.sz+t.sz}::tl')
          | I_Ext(d1,i,j), I_Ext(d2,k,l) when compare_term d1 d2 = 0 && l=i-1 ->
            let tmp = {sz = s.sz + t.sz ; bv = I_Ext(d1,k,j)}
            in if k=0 then (simple_t tmp)::(beta tl') else beta (tmp::tl')
          | _ -> (simple_t s)::(beta (t::tl'))
        end

    (** **)
    let sigma term = beta (alpha term)

    let bitv_to_icomp =
      List.fold_left (fun ac bt ->{ bv = I_Comp (ac,bt) ; sz = bt.sz + ac.sz })

    let string_to_bitv ?(neg = false) s ctx =
      let bitf = if neg then (fun b -> not b) else (fun b -> b) in
      let tmp = ref[] in
      String.iter (
        fun car ->
          tmp := (not @@ Char.equal  car '0',1)::(!tmp)
      ) s;
      let rec f_aux l acc = match l with
        | [] -> assert false
        | [(b,n)] -> { sz = n ; bv = I_Cte (bitf b) }::acc
        | (b1,n)::(b2,m)::r when Bool.equal b1 b2 -> f_aux ((b1,n+m)::r) acc
        | (b1,n)::(b2,m)::r ->
          (f_aux ((b2,m)::r)) ({ sz = n ; bv = I_Cte (bitf b1) }::acc)
      in
      let res = f_aux (!tmp) [] in
      bitv_to_icomp (List.hd res) (List.tl res), ctx

    let bit_of_expr t =
      match E.term_view t with
      | { f = Sy.Int s; _ } ->
        begin match Hstring.view s with
          | "1" -> Some true
          | "0" -> Some false
          | _ ->
            Util.failwith "Expeceted \"1\" or \"0\", but got \"%a\"" E.print t
        end
      | _ -> None

    let bit_e_neg neg t =
      if neg
      then E.mk_ite (E.mk_eq ~iff:false t E.izero) E.bvone E.bvzero
      else E.mk_ite (E.mk_eq ~iff:false t E.izero) E.bvzero E.bvone

    let bv_of_bool ?(neg = false) b =
      if (if neg then not b else b) then E.bvone else E.bvzero

    let mk_nthbv_eq bv_t n e =
      E.mk_eq ~iff:false (E.mk_bvextract n n bv_t) e

    let get_nth_eq_b bv_t cnt t_b =
      mk_nthbv_eq bv_t cnt (bv_of_bool t_b)

    let bitv_of_nat ?(neg = false) bv_t nat_t size ctx =
      let bitf = if neg then (fun b -> not b) else (fun b -> b) in
      let pow n =
        E.int Z.(pow ~$2 n |> to_string)
      in
      let mdiv nat_t n =
        E.mk_term (Sy.Op Sy.Modulo)
          [E.mk_term (Sy.Op Sy.Div) [nat_t; pow n] Ty.Tint; E.itwo] Ty.Tint
      in
      assert (size > 0);
      let rec aux ?prec cnt sz ctx =
        let ncnt = cnt + 1 in
        let val_t = mdiv nat_t cnt in
        let r, ctx' = X.make val_t in
        match X.term_extract r with
        | Some t, _ ->
          begin match bit_of_expr t with
            | Some t_b ->
              let nctx = ctx' @ ctx in
              begin match prec with
                | Some p_b when Bool.equal t_b p_b ->
                  if ncnt > size then { bv = I_Cte (bitf t_b); sz = sz}, nctx
                  else
                    aux
                      ?prec ncnt (sz + 1) (get_nth_eq_b bv_t cnt t_b :: nctx)
                | Some p_b ->
                  let t1 = { bv = I_Cte (bitf p_b); sz = sz} in
                  if ncnt > size then t1, nctx
                  else
                    let t2, nctx =
                      aux ~prec:t_b ncnt 1 (get_nth_eq_b bv_t cnt t_b :: nctx)
                    in
                    mk_i_comp t2 t1 (sz + t2.sz), nctx
                | None ->
                  assert (ncnt <= size);
                  let t, nctx =
                    aux ~prec:t_b ncnt 1 (get_nth_eq_b bv_t cnt t_b :: nctx)
                  in
                  t, nctx
              end
            | None ->
              let rv_t = bit_e_neg neg val_t in
              let bvv = E.fresh_name (Ty.Tbitv 1) in
              let eq = E.mk_eq ~iff:false bvv rv_t in
              let r = X.term_embed bvv in
              let nctx = eq :: ctx' @ ctx in
              let t1 = { bv = I_Other (pos r); sz = 1 } in
              if ncnt >= size then t1, nctx
              else
                let t2, nctx = aux ncnt 0 nctx in
                mk_i_comp t2 t1 (t2.sz + 1), nctx
          end
        | None, _ ->
          let rv_t = bit_e_neg neg val_t in
          let r, ctx' = X.make rv_t in
          let nctx = ctx' @ ctx in
          begin match prec with
            | Some b ->
              let t1 =
                mk_i_comp
                  { bv = I_Other (pos r); sz = 1}
                  { bv = I_Cte (bitf b); sz }
                  (sz + 1)
              in
              if ncnt > size then t1, nctx
              else
                let t2, nctx =
                  aux ncnt 0 (mk_nthbv_eq bv_t cnt rv_t :: nctx)
                in
                let t = mk_i_comp t2 t1 (sz + t2.sz + 1) in
                t, nctx
            | None ->
              let t1 = { bv = I_Other (pos r); sz = 1} in
              if ncnt > size then t1, nctx
              else
                let t2, nctx =
                  aux ncnt 0 (mk_nthbv_eq bv_t cnt rv_t :: nctx)
                in
                let t = mk_i_comp t2 t1 (t2.sz + 1) in
                t, nctx
          end
      in
      aux 0 0 ctx

    (** [mk_bvget_or_eq t cnt t1 cnt1 t2 cnt2]:
        t[cnt] = if t1[cnt1] = 0 then t2[cnt2] else 1 *)
    let mk_bvget_or_eq cnt nt t1 t2 =
      E.mk_eq ~iff:false (E.mk_bvextract cnt cnt nt) (
        E.mk_ite
          (E.mk_eq ~iff:false (E.mk_bvextract cnt cnt t1) E.bvzero)
          (E.mk_bvextract cnt cnt t2)
          E.bvone)

    (** [mk_bvget_and_eq t cnt t1 cnt1 t2 cnt2]:
        t[cnt] = if t1[cnt1] = 1 then t2[cnt2] else 0 *)
    let mk_bvget_and_eq cnt nt t1 t2 =
      E.mk_eq ~iff:false (E.mk_bvextract cnt cnt nt) (
        E.mk_ite
          (E.mk_eq ~iff:false (E.mk_bvextract cnt cnt t1) E.bvone)
          (E.mk_bvextract cnt cnt t2)
          E.bvzero
      )

    (** given two variables, adds to the context the equalities that correspond
        to the application of the semantics of the [bvor/bvand] operators.

        For example: given [t = bvor t1 t2] with [t], [t1] and [t2] being
        bit-vector varibles of size two, then what is added to the content is
        the following:
        [ t^{0,0} = ite (t1^{0,0} = [|0|], t2^{0,0}, [|1|]);
          t^{1,1} = ite (t1^{1,1} = [|0|], t2^{1,1}, [|1|]) ]

        On the other hand if [t = bvand t1 t2] then it is the following that is
        added to the context:
        [ t^{0,0} = ite (t1^{0,0} = [|1|], t2^{0,0}, [|0|]);
          t^{1,1} = ite (t1^{1,1} = [|1|], t2^{1,1}, [|0|]) ]
    *)
    let mk_o_eqs gcnt t op t1 t2 n ctx =
      let f =
        match op with
        | Bv_and -> mk_bvget_and_eq
        | Bv_or -> mk_bvget_or_eq
      in
      let rec aux ctx cnt =
        if cnt >= n then ctx else
          let eq = f (gcnt + cnt) t t1 t2 in
          aux (eq :: ctx) (cnt + 1)
      in
      aux ctx 0

    let extract_first_n t n =
      if t.sz = n then t, [] else
      if t.sz > n then
        match t.bv with
        | Cte b ->
          {bv = Cte b; sz = n},
          [{ bv = Cte b; sz = t.sz - n }]
        | Other o ->
          {bv = Ext (o, t.sz, t.sz - n, t.sz - 1); sz = n},
          [{bv = Ext (o, t.sz, 0, t.sz - n - 1); sz = t.sz - n}]
        | Ext (o, sz, i, j) ->
          {bv = Ext (o, sz, j - n + 1, j); sz = n},
          [{bv = Ext (o, sz, i, j - n); sz = t.sz - n}]
      else assert false

    let extend_term =
      (* let rec aux t =
         match t with
         | { bv = I_Cte b'; sz; } when Bool.equal b' b ->
         { bv = I_Cte b'; sz = sz + n; }
         | { bv = I_Comp (t1, t2); sz; } ->
         { bv = I_Comp (aux t1, t2); sz = sz + n; }
         | _ ->
         { bv = I_Comp ({ bv = I_Cte b; sz = n; }, t); sz = t.sz + n; }
         in
         aux t *)
      (* will be done during the call to sigma anyway *)
      fun b ?(neg = false) t k sz ->
      if not b
      then { bv = I_Comp ({ bv = I_Cte neg; sz = k}, t); sz }
      else
        let rtl = sigma t in
        match rtl with
        | [] -> assert false
        | hd :: tl ->
          match hd with
          | { bv = Cte b; _ } when neg ->
            to_i_ast ({ bv = Cte (not b); sz = k } :: rtl)

          | { bv = Cte b; sz } ->
            to_i_ast ({ bv = Cte b; sz = sz + k } :: tl)

          | { bv = Other o; sz } ->
            to_i_ast (
              List.rev_append (
                List.init k
                  (fun _ -> { bv = Ext (o, sz, sz-1, sz-1); sz = 1 })
              ) rtl)

          | { bv = Ext (o, sz', _, ub); _ } ->
            to_i_ast (
              List.rev_append (
                List.init k
                  (fun _ -> { bv = Ext (o, sz', ub, ub); sz = 1 })
              ) rtl)

    let repeat_term k t =
      let rec aux cnt acc =
        if cnt = 1 then acc else
          aux (k - 1 ) { bv = I_Comp (acc, t);  sz = acc.sz + t.sz }
      in
      aux k t

    let rec mk_rotate_left n i t =
      if i = 0 then t else
        mk_rotate_left n (i - 1) (
          E.mk_bvconcat
            (E.mk_bvextract 0 (n - 2) t)
            (E.mk_bvextract (n - 1) (n - 1) t)
            n
        )

    let rec mk_rotate_right n i t =
      if i = 0 then t else
        mk_rotate_right n (i - 1) (
          E.mk_bvconcat
            (E.mk_bvextract 0 0 t)
            (E.mk_bvextract 1 (n - 1) t)
            n
        )

    let mk_bitv_or n t1 t2 =
      E.mk_term (Sy.Op Sy.BVor) [t1; t2] (Ty.Tbitv n)

    let mk_bitv_and n t1 t2 =
      E.mk_bvnot n (mk_bitv_or n (E.mk_bvnot n t1) (E.mk_bvnot n t2))

    let mk_bitv_xor n t1 t2 =
      mk_bitv_or n
        (mk_bitv_and n t1 (E.mk_bvnot n t2))
        (mk_bitv_and n (E.mk_bvnot n t1) t2)

    let mk_bitv_xnor n t1 t2 =
      mk_bitv_or n
        (mk_bitv_and n t1 t2)
        (mk_bitv_and n (E.mk_bvnot n t1) (E.mk_bvnot n t2))

    let rec mk_bitv_comp n t1 t2 =
      if n = 1
      then mk_bitv_xnor 1 t1 t2
      else
        mk_bitv_and 1
          (mk_bitv_xnor 1
             (E.mk_bvextract (n-1) (n-1) t1)
             (E.mk_bvextract (n-1) (n-1) t2))
          (mk_bitv_comp (n-1)
             (E.mk_bvextract 0 (n-2) t1)
             (E.mk_bvextract 0 (n-2) t2))

    let mk_bvshl n x y =
      let x' = E.mk_bv2nat x in
      let y' = E.mk_bv2nat y in
      let y'' = E.mk_term (Sy.Op Sy.Pow) [E.itwo; y'] Ty.Tint in
      let natres = E.mk_term (Sy.Op Sy.Mult) [x'; y''] Ty.Tint in
      E.mk_nat2bv n natres

    let rec make_aux ?(neg = false) t' ctx =
      match E.term_view t' with
      | { E.f = Sy.Bitv s; _ } ->
        string_to_bitv ~neg s ctx

      | { E.f = Sy.Op Concat; xs = [t2;t1] ; ty = Ty.Tbitv n; _ } ->
        let r1, ctx = make_aux ~neg t1 ctx in
        let r2, ctx = make_aux ~neg t2 ctx in
        { bv = I_Comp (r2, r1) ; sz = n }, ctx

      | { E.f = Sy.Op Extract (i, j); xs = [x] ; ty = Ty.Tbitv sz; _ } ->
        let r, ctx = make_aux ~neg x ctx in
        { sz ; bv = I_Ext (r, i, j)}, ctx

      | { E.f = Sy.Op Nat2BV m; xs = [x] ; ty = Ty.Tbitv n; _ } ->
        assert (m = n);
        bitv_of_nat ~neg t' x n ctx

      | { E.f = Sy.Op BVnot; xs = [x] ; ty = Ty.Tbitv _; _ } ->
        make_aux ~neg:(not neg) x ctx

      | { E.f = Sy.Op BVor; xs = [x; y] ; ty = Ty.Tbitv _; _ } ->
        (* TODO: find a easy way to check if (x = y) or (x = not y) and
           simplify accordingly *)
        let r1, ctx' = make_aux ~neg x ctx in
        let r2, ctx'' = make_aux ~neg y ctx' in
        let r1' = sigma r1 in
        let r2' = sigma r2 in
        let bv, nctx =
          mk_bvbinop (if neg then Bv_and else Bv_or) r1' r2' t' x y ctx''
        in
        to_i_ast bv, nctx (* not great! *)

      | { E.f = Sy.Op BVExtend { sign = b; k }; xs = [ x ];
          ty = Ty.Tbitv n; _
        } ->
        let r1, ctx' = make_aux ~neg x ctx in
        extend_term b ~neg r1 k n,
        ctx'

      | { E.f = Sy.Op BV_repeat k; xs = [ x ]; ty = Ty.Tbitv _; _ } ->
        let r1, ctx' = make_aux ~neg x ctx in
        repeat_term k r1, ctx'

      | { E.f = Sy.Op BV_rotate k; xs = [ x ]; ty = Ty.Tbitv n; _ }
        when k > 0 ->
        make_aux ~neg (mk_rotate_right n k x) ctx

      | { E.f = Sy.Op BV_rotate k; xs = [ x ]; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (mk_rotate_left n (-k) x) ctx

      | { E.f = Sy.Op BVneg; xs = [ x ] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (E.mk_bvneg n x) ctx

      | { E.f = Sy.Op BVand; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (mk_bitv_and n x y) ctx

      | { E.f = Sy.Op BVxor; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (mk_bitv_xor n x y) ctx

      | { E.f = Sy.Op BVnand; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg:(not neg) (mk_bitv_and n x y) ctx

      | { E.f = Sy.Op BVnor; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg:(not neg) (mk_bitv_or n x y) ctx

      | { E.f = Sy.Op BVxnor; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (mk_bitv_xnor n x y) ctx

      | { E.f = Sy.Op BVcomp; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (mk_bitv_comp n x y) ctx

      | { E.f = Sy.Op BVadd; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (E.mk_bvadd n x y) ctx

      | { E.f = Sy.Op BVsub; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (E.mk_bvsub n x y) ctx

      | { E.f = Sy.Op BVmul; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (E.mk_bvmul n x y) ctx

      | { E.f = Sy.Op BVshl; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (mk_bvshl n x y) ctx

      | { E.f = Sy.Op BVlshr; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        let z = E.mk_term (Sy.Op Sy.Pow) [E.itwo; E.mk_bv2nat y] Ty.Tint in
        make_aux ~neg (
          E.mk_nat2bv n (E.mk_term (Sy.Op Sy.Div) [E.mk_bv2nat x; z] Ty.Tint)
        ) ctx

      | { E.ty = Ty.Tbitv n; _ } ->
        let mk = if neg then neg' else pos in
        let r', ctx' = X.make t' in
        {bv = I_Other (mk r'); sz = n}, ctx' @ ctx

      | _ -> Util.failwith "[Bitv] make: Unexpected term %a@." E.print t'

    and mk_bvbinop op r1 r2 res_e e1 e2 ctx =
      let rec aux cnt r1 r2 ctx =
        match r1, r2 with
        | h1 :: tl1, h2 :: tl2 ->
          let csz = min h1.sz h2.sz in
          let nh1, nl1 = extract_first_n h1 csz in
          let nh2, nl2 = extract_first_n h2 csz in
          let nrh, ctx = bv_binop_uniform cnt res_e op nh1 e1 nh2 e2 ctx in
          let r, ctx = aux (cnt + csz) (nl1 @ tl1) (nl2 @ tl2) ctx in
          nrh @ r, ctx
        | [], [] -> [], ctx
        | _ -> assert false
      in
      aux 0 r1 r2 ctx

    and bvor_os cnt t op t1 t2 sz ctx =
      let nt = E.fresh_name (Ty.Tbitv sz) in
      let rterm, nctx = make_aux nt ctx in
      let nctx = mk_o_eqs cnt t op t1 t2 sz nctx in
      let nr = sigma rterm in
      nr, E.mk_eq ~iff:false t nt :: nctx

    (* the calls to [bvor_os] is the only reason why we return lists and not
       abstract terms only although it is likely that all the returned lists
       have only one element *)
    and bv_binop_uniform cnt e op t1 e1 t2 e2 ctx:
      r simple_term_aux alpha_term list * E.t list =
      match t1, t2 with
      | ({ bv = Cte true; _ } as posbv), otherbv
      | otherbv, ({ bv = Cte true; _ } as posbv) -> (
          match op with
          | Bv_and -> [otherbv], ctx
          | Bv_or -> [posbv], ctx
        )
      | ({ bv = Cte false; _ } as negbv), otherbv
      | otherbv, ({ bv = Cte false; _ } as negbv) -> (
          match op with
          | Bv_and -> [negbv], ctx
          | Bv_or -> [otherbv], ctx
        )
      | { bv = Other _; sz }, { bv = Other _; _ }
      | { bv = Ext _; sz }, { bv = Ext _; _ }
      | { bv = Ext _; sz }, { bv = Other _; _ }
      | { bv = Other _; sz }, { bv = Ext _; _ } ->
        bvor_os cnt e op e1 e2 sz ctx
  end

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer

    let print_tvar fmt (tv,sz) =
      Format.fprintf fmt "%a[%d]" pp_tvar tv sz

    let print fmt ast =
      let open Format in
      match ast.bv with
      | Cte b -> fprintf fmt "%d[%d]" (if b then 1 else 0) ast.sz
      | Other t -> fprintf fmt "%a" (pp_signed X.print) t
      | Ext (t,_,i,j) ->
        fprintf fmt "%a" (pp_signed X.print) t;
        fprintf fmt "<%d,%d>" i j

    let[@warning "-32"] rec print_I_ast fmt ast =
      let open Canonizer in
      let open Format in
      match ast.bv with
      | I_Cte b -> fprintf fmt "%d[%d]" (if b then 1 else 0) ast.sz
      | I_Other t -> fprintf fmt "%a[%d]" (pp_signed X.print) t ast.sz
      | I_Ext (u,i,j) -> fprintf fmt "%a<%d,%d>" print_I_ast u i j
      | I_Comp(u,v) -> fprintf fmt "@[(%a * %a)@]" print_I_ast u print_I_ast v

    let print_C_ast fmt = function
        [] -> assert false
      | x::l -> print fmt x; List.iter (Format.fprintf fmt " @@ %a" print) l

    let print_s fmt ast = match ast.bv with
      | S_Cte b -> Format.fprintf fmt "%d[%d]" (if b then 1 else 0) ast.sz
      | S_Var (tv, n) ->
        if n then
          Format.fprintf fmt "(bvnot %a)" print_tvar (tv,ast.sz)
        else
          Format.fprintf fmt "%a" print_tvar (tv,ast.sz)

    let print_S_ast fmt = function
        [] -> assert false
      | x::l -> print_s fmt x; List.iter (Format.fprintf fmt " @@ %a" print_s) l

    let print_sliced_sys l =
      let print fmt (a,b) =
        Format.fprintf fmt " %a == %a@ " print a print b
      in
      if Options.get_debug_bitv () then
        Printer.print_dbg
          ~module_name:"Bitv"
          ~function_name:"slicing"
          "%a" (pp_list_no_space print) l

    let print_c_solve_res l =
      let print fmt (a,b) =
        Format.fprintf fmt " %a == %a@ " print a print_S_ast b
      in
      if Options.get_debug_bitv () then
        Printer.print_dbg
          ~module_name:"Bitv"
          ~function_name:"c_solve"
          "(map)c_solve :@ %a" (pp_list_no_space print) l

    let print_partition_res l =
      let print fmt (t,cte_l) =
        Format.fprintf fmt " %a%a@ " print t
          (fun fmt ->
             List.iter (fun l' -> Format.fprintf fmt " == %a" print_S_ast l'))
          cte_l
      in
      if Options.get_debug_bitv () then
        Printer.print_dbg
          ~module_name:"Bitv"
          ~function_name:"partition"
          "%a" (pp_list_no_space print) l

    let print_final_solution l =
      let print fmt (a,value) =
        Format.fprintf fmt " %a = %a@ " print a print_C_ast value
      in
      if Options.get_debug_bitv () then
        Printer.print_dbg
          ~module_name:"Bitv"
          ~function_name:"solution"
          "%a" (pp_list_no_space print) l
  end
  (*BISECT-IGNORE-END*)

  module Solver = struct

    exception Valid

    let add elt l = if List.mem elt l then l else elt::l

    let get_vars = List.fold_left
        (fun ac st -> match st.bv with
           |Other v |Ext(v,_,_,_) -> add v ac  |_ -> ac )[]

    (* [st_slice st siz] splits the simple term [st] in two parts, the first of
       which has size |siz|.

       If [st] is [[b0; ..; bn]] then [st_slice st size] is [(x, y)] where:

       - [x] is [[b0; ..; b(siz-1)]]
       - [y] is [[b(siz); ..; bn]] *)
    let st_slice st siz =
      let siz_bis = st.sz - siz in match st.bv with
      |Cte _ -> {st with sz = siz},{st with sz = siz_bis}
      |Other x ->
        let s1 = Ext(x,st.sz, siz_bis, st.sz - 1) in
        let s2 = Ext(x,st.sz, 0, siz_bis - 1) in
        {bv = s1 ; sz = siz},{bv = s2 ; sz = siz_bis}
      |Ext(x,s,p,q) ->
        let s1 = Ext(x,s,p+siz_bis,q) in
        let s2 = Ext(x,s,p,p+siz_bis-1) in
        {bv = s1 ; sz = siz},{bv = s2 ; sz = siz_bis}

    (* [slice t u] transforms the equality [t = u] between abstract terms (i.e.
       concatenations of simple terms) into an equivalent conjunction of
       equalities between simple terms.

       Requires: [t] and [u] must have the same total size.
       Ensures: there are no duplicates in the result (in particular, [x = y]
                and [y = x] cannot be both present)
       Ensures: there are no trivial equalities [x = x] in the result. *)
    let slice t u  =
      let f_add (s1,s2) acc =
        let b =
          equal_simple_term X.equal s1 s2
          || List.mem (s1,s2) acc || List.mem (s2,s1) acc
        in
        if b then acc else (s1,s2)::acc
      in let rec f_rec acc = function
          |[],[] | _,[] | [],_ -> assert false
          |[s1],[s2] ->if s1.sz<>s2.sz then assert false else f_add (s1,s2) acc
          |s1::r1,s2::r2  ->
            if s1.sz = s2.sz then f_rec (f_add (s1,s2) acc) (r1,r2)
            else begin
              if s1.sz > s2.sz then
                let (s11,s12) = st_slice s1 s2.sz
                in f_rec (f_add (s11,s2) acc) (s12::r1,r2)
              else
                let (s21,s22) = st_slice s2 s1.sz
                in f_rec (f_add (s1,s21) acc) (r1,s22::r2)
            end
      in f_rec [] (t,u)

    let fresh_var =
      let cpt = ref 0 in fun t -> incr cpt; { var = !cpt ; sorte = t}

    let fresh_bitv genre size =
      if size <= 0 then []
      else [ { bv = S_Var (fresh_var genre, false) ; sz = size } ]

    let negate_bitv = negate_sstl

    (* Orient the equality [b = st] where [b] is a boolean constant and [st] is
       uninterpreted ("Other") *)
    let cte_vs_other bol st = st , [{bv = S_Cte bol ; sz = st.sz}]

    (* Orient the equality [b = xt[s_xt]^{i,j}] where [b] is a boolean constant
       and [xt] is uninterpreted of size [s_xt].

       We introduce two A-variables [a1[i]] and [a2[s_xt-1-j]] and orient:

        [xt = a1 @ b[j - i + 1] @ a2]

       The A-variables are unconstrained by this equation and represent the
       remainder of the uninterpreted symbol before/after the extraction.

       (Note: [fresh_bitv] ensures that if either [a1] or [a2] has size [0], no
       variable is actually generated.) *)
    let cte_vs_ext bol xt s_xt i j =
      let a1  = fresh_bitv A i in
      let a2  = fresh_bitv A (s_xt - 1 - j) in
      let cte = [ {bv = S_Cte bol ; sz =j - i + 1 } ] in
      let var = { bv = Other xt ; sz = s_xt }
      in var, a2@cte@a1

    (* Orient the equality [st1 = st2] where both [st1] and [st2] are
       uninterpreted ("Other").

       We introduce a new C-variable [c] and orient:

        [st1 = c] and [st2 = c]

       [same_pol] is [true] if both terms have the same polarity (either both
       negated or both non-negated), and [false] if exactly one is negated, in
       which case the C variable is negated in one of the branches
       (arbitrarily).

       Requires: [size st1 = size st2]
       Requires: [st1] and [st2] are distinct (for the C variables invariant)
    *)
    let other_vs_other same_pol st1 st2 =
      let c = fresh_bitv C st1.sz in
      let c' = if same_pol then c else negate_bitv c in
      [ (st1,c) ; (st2,c') ]

    (* Orient the equality [st = xt[s_xt]^{i,j}] where [st] and [xt] are
       uninterpreted ("Other") and [xt] is uninterpreted of size [s_xt].

       We introduce a new C-variable [c] and two A-variables [a1[i]] and
       [a2[s_xt - 1 - j]] and orient:

        [st = c] and [xt = a1 @ c @ a2]

       Requires: [size st = j - i + 1]
       Requires: [st] and [xt] are distinct (for the C variables invariant ---
         but this is actually impossible because the sizes wouldn't match)
    *)
    let other_vs_ext same_pol st xt s_xt i j =
      let c  = fresh_bitv C st.sz in
      let a1 = fresh_bitv A i in
      let a2 = fresh_bitv A (s_xt - 1 - j) in
      let c' = if same_pol then c else negate_bitv c in
      let extr = { bv = Other xt ; sz = s_xt }
      in [ (st,c) ; (extr,a2 @ c' @ a1) ]

    (* Orient the equality [id[s]^{i,j} = id'[s']^{i',j'}].

       We introduce a C variable [c] and A variables a1, a1', a2, a2' and
       orient:

        [id = a2 @ c @ a1] and [id' = a2' @ c @ a1']

       The "shared" part is equal to the C variable.

       Requires: [id] and [id'] are distinct variables. This requirement ensures
         that we maintain the invariant of C variables that they never occur
         twice in the same multi-equation.
    *)
    let ext1_vs_ext2 same_pol (id,s,i,j) (id',s',i',j') = (* id != id' *)
      let c   = fresh_bitv (C) (j - i + 1) in
      let a1  = fresh_bitv A i  in
      let a1' = fresh_bitv A i' in
      let a2  = fresh_bitv A (s - 1 - j)   in
      let a2' = fresh_bitv A (s' - 1 - j') in
      let x_v = { sz = s  ; bv = Other id  } in
      let y_v = { sz = s' ; bv = Other id' } in
      let c' = if same_pol then c else negate_bitv c in
      [ (x_v , a2 @ c @ a1) ; (y_v , a2' @ c' @ a1') ]

    (* Orient the equality [xt[siz]^{i1, i1 + tai} = xt[siz]^{i2, i2 + tai}]

       The [overl] variable contains the number of overlapping bits.

       - If there are no overlapping bits, the two parts are independent.
          We create a fresh B-variable [b] and A-variables [a1], [a2] and [a3]
          and orient:

            [xt = a3 @ b @ a2 @ b @ a1]

          The B-variable is used for the common part that is repeated.

       - If there are overlapping bits, we create only the A variables [a1] and
          [a3] for the before/after parts, and we create two B variables.

          [b_box] is the total constraint size (from [i1] to [i2 + tai]).
          [nn_overl] is the number of *initial* non-overlapping bits (from [i1]
          to [i2]).

          The [b] vector is then split into two parts to properly align the
          repetition. The computation is:

            sz_b1 = b_box % nn_overl (size of b1)
            sz_b2 = nn_overl - sz_b1 (size of b2)
            a1[i] @ ((b1 @ b2) * (b_box/nn_overl)) @ b1 @ a2[siz - tai - i2]

          It will be more clear with an example:

             _ nn_overl = 3
            / \
            xxxxxxx???
            ???yyyyyyy
            \________/
              b_box = 10

          Which creates the following decomposition:

            $$$xxxxxxx???###
            $$$???yyyyyyy###
            \\\uvvuvvuvvu///
            where a1 = \\\, b1 = u, b2 = vv, a2 = ///

       Requires: [i1 < i2]
    *)
    let ext_vs_ext same_pol xt siz (i1,i2) tai =
      if i1 = i2 then begin
        assert (not same_pol);
        raise Util.Unsolvable
      end else
        let overl = i1 + tai -i2 in
        if overl <= 0 then begin
          let a1 = fresh_bitv A i1     in
          let a2 = fresh_bitv A (-overl) in
          let a3 = fresh_bitv A (siz - tai - i2) in
          let b  = fresh_bitv B tai in
          let b' = if same_pol then b else negate_bitv b in
          ({ bv = Other xt ; sz = siz } , a3 @ b @ a2 @ b' @ a1)
        end
        else begin
          let b_box = i2 + tai - i1 in
          let nn_overl = tai - overl in(* =i2-i1 >0 sinon egalite sytaxique*)
          let sz_b1 = b_box mod nn_overl in
          let a1 = fresh_bitv A i1                 in
          let a3 = fresh_bitv A (siz - tai - i2) in
          let b1 = fresh_bitv B sz_b1              in
          let b2 = fresh_bitv B (nn_overl - sz_b1 )in
          let acc = ref b1 in
          let cpt = ref nn_overl in
          (* There is already [b1] in [acc], so we need to flip the first one
             that is added by the loop. *)
          let odd = ref true in
          while !cpt <= b_box do
            let b1' = if !odd && not same_pol then negate_bitv b1 else b1 in
            let b2' = if not !odd && not same_pol then negate_bitv b2 else b2 in
            acc := b1' @ b2' @(!acc);
            cpt := !cpt + nn_overl;
            odd := not !odd
          done;
          ({ bv = Other xt ; sz = siz } , a3 @ (!acc) @ a1)
        end

    (* [sys_solve sys] orients a system of equations between simple terms.

       The resulting system contains equations between a simple term on the
       left, and a solver_simple_term on the right.  The solver_simple_term only
       involves *fresh* A, B, and C variables.

       Each uninterpreted symbol (variable or alien) appearing in the original
       system appears in the oriented system, possibly multiple times.

       In a single equation of the resulting system:

       - The A variables only refer to parts of the variable that were
          unconstrained in the original equation. Each A variable appears
          *exactly once* in the oriented system.
       - The B variables appear due to equalities involving multiple
          extractions of the same uninterpreted term. They appear in a single
          equation, but can appear *multiple times in a single equation*.
       - The C variables appear due to equalities involving multiple
          uninterpreted terms. They appear at most once in each equation, but
          can appear *in multiple equations*. They only appear in equations that
          have distinct left-hand-side.

       Requires (R1): there are no trivial equalities in [sys]
    *)
    let sys_solve sys =
      let c_solve (st1,st2) = match st1.bv,st2.bv with
        |Cte _, Cte _ -> raise Util.Unsolvable (* forcement un 1 et un 0 *)

        |Cte b, Other _ -> [cte_vs_other b st2]
        |Other _, Cte b -> [cte_vs_other b st1]

        |Cte b, Ext(xt,s_xt,i,j) -> [cte_vs_ext b xt s_xt i j]
        |Ext(xt,s_xt,i,j), Cte b -> [cte_vs_ext b xt s_xt i j]
        |Other o1, Other o2 when X.equal o1.value o2.value ->
          raise Util.Unsolvable
        |Other o1, Other o2 ->
          other_vs_other (Bool.equal o1.negated o2.negated) st1 st2

        |Other o, Ext(xt,s_xt,i,j) ->
          let same_pol = Bool.equal o.negated xt.negated in
          other_vs_ext same_pol st1 xt s_xt i j

        |Ext(xt,s_xt,i,j), Other o ->
          let same_pol = Bool.equal o.negated xt.negated in
          other_vs_ext same_pol st2 xt s_xt i j
        |Ext(id,s,i,j), Ext(id',s',i',j') ->
          let same_pol = Bool.equal id.negated id'.negated in
          if not (X.equal id.value id'.value)
          then ext1_vs_ext2 same_pol (id,s,i,j) (id',s',i',j')
          else [ext_vs_ext same_pol id s (if i<i' then (i,i') else (i',i)) (j - i + 1)]

      in List.flatten (List.map c_solve sys)


    (* [partition eq l] returns a list of pairs [(a, bs)] where [bs] contains
       all the [b] such that [(a, b)] occurs in the original list.

       When applied to oriented systems of equations returned by [sys_solve],
       this merges together all the equalities involving the same [simple_term]
       on the left. *)
    let partition eq l =
      let rec add acc (t,cnf) = match acc with
        |[] -> [(t,[cnf])]
        |(t',cnf')::r -> if eq t t' then (t',cnf::cnf')::r
          else (t',cnf')::(add r (t,cnf))
      in List.fold_left add [] l


    let slicing_pattern s_l =
      let rec f_aux l1 l2 = match (l1,l2) with
        |[],[] -> []
        |a::r1,b::r2 when a = b -> a::(f_aux r1 r2)
        |a::r1,b::r2 ->
          if a < b then a::(f_aux r1 ((b-a)::r2))
          else b::(f_aux ((a-b)::r1) r2)
        |_ -> assert false
      in List.fold_left f_aux (List.hd s_l)(List.tl s_l)

    (* [slice_var var pat_hd pat_tl] slices a variable to make it fit the
       pattern [pat_hd :: pat_tl].
       Returns the list of created fresh variables, the left over pattern and
       the sort of the variable (if it is not a constant). *)
    let slice_var var pat_hd pat_tl =
      let mk, tr =
        match var.bv with
        | S_Cte _ -> (fun sz -> { var with sz }), None
        | S_Var ({ sorte; _ }, ng) ->
          (fun sz -> { bv = S_Var (fresh_var sorte, ng); sz }), Some sorte
      in
      let rec aux cnt plist =
        match plist with
        | [] -> [], []
        | h :: t when cnt < h -> [ mk cnt ], (h - cnt) :: t
        | h :: t when cnt = h -> [ mk cnt ], t
        | h :: t ->
          let vl, ptail = aux (cnt - h) t in
          mk h :: vl, ptail
      in
      let fst_v = mk pat_hd in
      let cnt = var.sz - pat_hd in
      let vl, pat_tail = aux cnt pat_tl in
      fst_v :: vl, pat_tail, tr

    (* This is a helper function for [slice_vars].

       [apply_sub_rev sub changed acc pat rcomp] applies the substitution [sub]
       (which maps B-variable to lists of B-variables) to the composition
       [rcomp], which is stored in *reverse* order, and:

       - Updates [changed] if the substitution effectively changes a variable
       - Computes the resulting composition (in normal order) in [acc]
       - Computes the resulting pattern in [pat]

       If [changed', comp', pat' = apply_sub_rev sub false [] [] rcomp] then
       the following holds:

       - [pat' = List.map (fun bv -> bv.st) comp']
       - If [changed'] is [false], [comp' = List.rev rcomp]

       Note that the substitution can be recursive, so we must do a recursive
       call on the result of applying the substitution (we can't add [vl]
       to [acc], we must add [(`rev` vl)] to [r] instead). *)
    let rec apply_sub_rev sub changed acc pat = function
      | [] -> changed, acc, pat
      | v :: r ->
        match List.assoc v sub with
        | vl ->
          (* Note that this is [(`rev` vl) @ r] and not [vl @ r] because
             the composition is given in reverse order. *)
          apply_sub_rev sub true acc pat (List.rev_append vl r)
        | exception Not_found ->
          apply_sub_rev sub changed (v :: acc) (v.sz :: pat) r

    (* [slice_vars eq pat (c, req, subs)] slices the variables in [eq] according
       to the pattern [pat]. [eq] is a composition of simple terms.

       If the composition [eq] does not match the pattern in [pat]:
       - When variables in the composition are bigger than the expected pattern
          size, the variables are split into multiple parts, which fit the
          pattern.

          Splits involving A variables are not recorded, because A variables are
          guaranteed to have unique occurences.

          Splits involving B and C variables are accumulated in [subs], which
          is a pair [(b_sub, c_sub)] of substitutions for the B and C
          variables, respectively.

          Splits involving C variables can propagate to other compositions in
          the system, but not to the current composition, since C variables
          never occur twice in the same composition.

          On the other hand, splits involving B variables must be applied to the
          current composition. This may cause other B variable to be split and
          become *smaller* than the corresponding pattern, even if the pattern
          elements were all smaller than the corresponding variables initially.

       - When variables in the composition are smaller than the expected
          pattern size (see above), the pattern must be broken up. This is
          recorded in [c], and it means that the pattern must be re-applied to
          any composition it was already applied to, which can cause more
          slicing.

       Finally, the resulting (= sliced) composition is stored in [req], in
       *reverse* order.  Once the slicing is done, [req] is reversed and
       returned. We also apply the B-substitutions that were accumulated,
       because it is possible to have two occurences [b_1] and [b_2] of a
       B-variable where the second occurence [b_2] gets sliced, but the first
       occurence [b_1] has already been dealt with. We perform this "late"
       slicing for all B-variables at once at the end of the iteration.
    *)
    let rec slice_vars eq pat (c, req, subs)=
      match eq, pat with
      | [], [] ->
        (* If the slicing changed the pattern, or if applying the B-variables
           substitution changes the pattern, we must report it so that the whole
           system is re-sliced. *)
        let (bsub, csub) = subs in
        begin match bsub with
          | [] when not c -> List.rev req, csub, None
          | _ ->
            let c, eq, pat = apply_sub_rev bsub c [] [] req in
            eq, csub, if c then Some pat else None
        end
      | st :: eq, n :: pt when st.sz < n ->
        (* Since we start with a [slicing_pattern], this should only occur when
           a B-variable has been split into parts below.
           Therefore we assert that the variable is indeed a B variable and that
           list of substitutions for B variables is not empty. *)
        assert (not (Lists.is_empty (fst subs)));
        assert (match st.bv with S_Var ({ sorte = B; _ }, _) -> true | _ -> false);
        slice_vars eq (n - st.sz :: pt) (true, st :: req, subs)
      | st :: eq, n :: pt when st.sz = n ->
        slice_vars eq pt (c, st :: req, subs)
      | st :: eq, n :: pt ->
        let (nvar_list, pt', flag) = slice_var st n pt in
        begin match flag with
          | Some C ->
            (* A C variable got split: we must record the information in the
               C-substitution so that it gets to the instances of the variable
               in other multi-equations. *)
            let bsub, csub = subs in
            let subs = (bsub, (st, nvar_list) :: csub) in
            slice_vars eq pt' (c, List.rev_append nvar_list req, subs)
          | Some B ->
            (* A B variable got split: we must update the other occurences of
               the variable in the current composition. If there are other
               occurences before the current one, the information is recorded in
               the B-substitution, and we will also update it at the end. *)
            let eq = List.fold_right (fun st' acc ->
                if equal_solver_simple_term st' st then
                  nvar_list @ acc
                else
                  st' :: acc) eq [] in
            let bsub, csub = subs in
            let subs = ((st, nvar_list) :: bsub, csub) in
            slice_vars eq pt' (c, List.rev_append nvar_list req, subs)
          | None | Some A ->
            slice_vars eq pt' (c, List.rev_append nvar_list req, subs)
        end
      | [], _ :: _ | _ :: _, [] -> assert false

    (* [uniforme_slice vls] takes as argument the list of right-hand side
       concatenations associated with a single left-hand-side term in an
       equation system. We will call this a multi-equality.

       vls is a list of lists: each term in the multi-equality is a
       concatenation of solver_simple_terms.

       In particular, it satisfies the hypotheses that:

       - A and C variables occur *at most once* in the multi-equality (C
          variables may occur in multi-equality involving different left-hand
          sides).

       - B variables only appear in a single concatenation, but may (in fact,
          do) appear multiple times in that single concatenation.

       [uniforme_slice] returns a pair [(eqs, c_subs)] where:

       - [eqs] is a *uniform* multi-equality, that is, each concatenation in
          [eqs] has the same shape (the bitvector at any given position has the
          same size in all concatenations).  In particular, all concatenations
          have the same length.

          The concatenations in [eqs] satisfy the same requirements as above
          regarding the A, B and C variables; but some of the variables may have
          been replaced with a concatenation of smaller variables.

       - [c_subs] is a mapping from C variables to pairs of C variables, where
          the original C variable has been replaced by the concatenation of the
          new C variables. The original C variable must not be used anymore, and
          must be replaced with the concatenation instead.

          This mapping can be recursive: a C-variable [c] can be substituted
          with the concatenation [c1 @ c2] of two fresh C-variables, and then
          [c2] can be substituted with the concatenation [c3 @ c4]. *)
    let uniforme_slice eqs =
      let pat = slicing_pattern (List.map (List.map (fun bv -> bv.sz)) eqs) in
      let rec slice_vars_fix pat acc csub = function
        | [] -> acc, csub
        | eq :: eqs ->
          (* If the pattern changes, we must re-slice the whole system. This
             happens when one occurence of a B-variable gets sliced in a way
             that is not compatible with another occurence of the same
             B-variable. *)
          let eq, csub, pat' = slice_vars eq pat (false, [], ([], csub)) in
          match pat' with
          | None -> slice_vars_fix pat (eq :: acc) csub eqs
          | Some pat ->
            slice_vars_fix pat [] csub (List.rev_append acc (eq :: eqs))
      in
      slice_vars_fix pat [] [] eqs


    let apply_subs subs sys =
      let rec f_aux = function
        |[] -> []
        |v::r ->
          match List.assoc v subs with
          | vl -> vl @ f_aux r
          | exception Not_found -> v :: f_aux r
      in List.map (fun (t,vls) ->(t,List.map f_aux vls))sys

    (* [equations_slice parts] takes a partitioned system [parts], i.e. a list
       of pairs [(a, bs)] where [a] are uninterpreted terms and [bs] are
       multi-equations involving A, B and C variables.

       The usual conditions apply:

       - A variables occur at most once in the whole partitioned system
       - B variables occur in at most one composition of at most one
          multi-equation, but they appear multiple times within this
          single composition
       - C variables occur at most once in the multi-equation associated with a
          given uninterpreted term, but may occur in multi-equations associated
          with distinct uninterpreted terms.

       [equations_slice parts] returns a new system that is equivalent to the
       original system, but where each uninterpreted term is associated with a
      *uniform* multi-equation (see the definition of [uniforme_slice]).

       Note that [equations_slice] works recursively: trying to make an uniform
       multi-equation for a specific uninterpreted term may cause some of its
       C-variables to be split, which in turn can require re-slicing the other
       equations involving the original C-variable, even if they have already
       been sliced. Which can in turn cause re-slicing of the new C-variables,
       etc. *)
    let equations_slice parts =
      let rec slice_rec bw = function
        |[] -> bw
        |(t,vls)::r ->
          let (vls',subs) = uniforme_slice vls
          in if Lists.is_empty subs then slice_rec ((t,vls')::bw) r
          else
            begin
              let _bw = apply_subs subs bw in
              let _fw = apply_subs subs r in
              let eq (_, l1) (_, l2) =
                (* [apply_subs] does not change the left-hand sides *)
                Lists.equal (Lists.equal equal_solver_simple_term) l1 l2
              in
              if Lists.equal eq _bw bw
              then slice_rec ((t,vls')::bw) _fw
              else slice_rec [] (_bw@((t,vls'):: _fw))
            end
      in slice_rec [] parts

    (* [union_sets sets] performs (inefficiently) the union operation of an
       union-find data structure. Given an union-find data structure [sets]
       represented as a list of sets, it returns a new list [sets'] by merging
       all the sets in the original list that are not disjoint. *)
    let rec union_sets sets =
      (* [included e1 e2] returns [true] if the intersection of [e1] and [e2] is
         nonempty, and [false] otherwise. Confusingly, this *does not* mean that
         [e1] is included in [e2], but rather that [e1] and [e2] are not
         disjoint. Go figure. *)
      let included e1 e2 =
        try
          ST_Set.iter (fun at -> if ST_Set.mem at e2 then raise Exit)e1;
          false
        with Exit -> true
      in match sets with
      |[] -> []
      |st::tl ->
        let (ok,ko) = List.partition (included st) tl in
        if Lists.is_empty ok then st::union_sets tl
        else union_sets ((List.fold_left ST_Set.union st ok)::ko)

    (* [init_sets vals] takes as argument a uniform multi-equation [vals], and
       converts it into a union-of-sets representation.

       This is a sort of transposition. Given an *uniform* multi-equation:

        x1 @ ... @ xn ==
             ...      ==
        z1 @ ... @ zn

       we build a list where each position in the multi-equation is associated
       with the set of values at that position in the multi-equation:

        [[{x1, ..., z1}, ..., {xn, ..., zn}]]

       All the values in the same set must be equal. *)
    let init_sets vals =
      let acc = List.map (fun at -> ST_Set.singleton at) (List.hd vals) in
      let tl = (List.tl vals) in
      let f_aux = List.map2 (fun ac_e e -> ST_Set.add e ac_e)
      in List.fold_left f_aux acc tl

    (* [equalities_propagation eqs_slice] takes as argument a partitioned
       uniform system of equations [eqs_slice].

       This means that [eqs_slice] is a list of pairs [(t, eqs)] where [t] is
       an uninterpreted term ("Other") and [eqs] are uniform multi-equations
       associated with [t] (see [uniforme_slice] for the definition of uniform
       multi-equations).

       The usual restrictions on A, B and C variables apply:

       - A variables occur at most once in the whole system
       - B variables occur in at most one composition of at most one
          multi-equation, but occur multiple times within that one composition
       - C variables occur at most once in the multi-equation associated with a
          given term, but occur in multi-equations associated with multiple
          distinct terms

       [equalities_propagation] propagates the equalities implied by the
       [eqs_slic] system, and returns a list of pairs [(r, c)] where [c] is an
       equivalence class (represented by a set of simple terms) and [r] is the
       representative of that class.

       If there is a constant in the set, it is used as a representative;
       otherwise, the maximum variable according to [compare_solver_simple_term]
       is returned (preference is given to C > B > A variables, and amongst
       variables of the same sort, the youngest is preferred).

       The equivalence classes contain exactly all the terms occuring in the
       input system. *)
    let equalities_propagation eqs_slic =
      let init_sets = List.map (fun (_,vls) -> init_sets vls) eqs_slic in
      let init_sets = List.flatten init_sets
      in List.map
        (fun set ->
           let st1 = ST_Set.min_elt set and st2 = ST_Set.max_elt set
           in  match st1.bv , st2.bv with
           |S_Cte false, S_Cte true -> raise Util.Unsolvable
           |S_Cte false , _ -> st1,set
           |_ , _ -> st2,set
        ) (union_sets init_sets)

    (* [build_solution unif_slic sets] takes as argument a uniform system of
       multi-equations (see above) and a set of equivalence classes. It builds a
       solution to the uniform system by replacing each term with the
       concatenation of representatives for the corresponding multi-equation. *)
    let build_solution unif_slic sets =
      (* Check consistency: if a negated variable is in the same class as its
         non-negated counterpart, it is unsolvable. *)
      List.iter (fun (_, set) ->
          ST_Set.iter (fun st ->
              match st.bv with
              | S_Var (tv, true) ->
                if ST_Set.mem { st with bv = S_Var (tv, false) } set
                then raise Util.Unsolvable
              | _ -> ()) set) sets;
      let pos_sets, neg_sets =
        List.partition (fun (r, set) ->
            match r.bv with
            | S_Cte _ | S_Var (_, false) -> true
            | S_Var (_, true) -> false) sets
      in
      let pos_tvars =
        List.map (fun (r, set) ->
            let r =
              match r.bv with
              | S_Cte b -> Cte b
              | S_Var (_, false) ->
                let t = E.fresh_name (Ty.Tbitv r.sz) in
                Other (X.term_embed t |> pos)
              | S_Var (tv, true) ->
                assert false
            in
            (r, set)) pos_sets
      in
      let get_rep var tvars =
        fst(List.find ( fun(_,set)->ST_Set.mem var set ) tvars) in
      let neg_tvars =
        List.map (fun (r, set) ->
            match r.bv with
            | S_Var (tv, true) ->
              let r =
                try
                  match get_rep { r with bv = S_Var (tv, false) } pos_tvars with
                  | Cte b -> Cte (not b)
                  | Other x -> Other (snot x)
                  | Ext _ -> assert false
                with Not_found ->
                  let t = E.fresh_name (Ty.Tbitv r.sz) in
                  Other (X.term_embed t |> pos)
              in
              (r, set)
            | _ -> assert false) neg_sets
      in
      let tvars = pos_tvars @ neg_tvars in
      let get_rep var = get_rep var tvars in
      let to_external_ast v =
        {sz = v.sz;
         bv = match v.bv with
           |S_Cte b -> Cte b
           |S_Var _ -> get_rep v
        }in
      let rec cnf_max l = match l with
        |[] -> []
        |[elt]-> [elt]
        |a::b::r ->
          begin
            match a.bv,b.bv with
            | Cte b1, Cte b2 when Bool.equal b1 b2 ->
              cnf_max ({ b with sz = a.sz + b.sz }::r)
            | _, Cte _ -> a::(cnf_max (b::r))
            | _ -> a::b::(cnf_max r)
          end
      in List.map
        (fun (t,vls) ->
           t,cnf_max (List.map to_external_ast (List.hd vls))
        )unif_slic

    (* [solve u v] takes as argument two abstract terms (i.e. concatenation of
       simple terms) [u] and [v] and returns a substitution [subs].

       The substitution [subs] maps all the uninterpreted terms ("other")
       appearing in the abstract terms [u] and [v] to a definition, expressed as
       an abstract term, involving only constants and *fresh* A, B and C
       variables.

       @raises Valid if the two terms are already equal. *)
    let solve u v =
      if equal_abstract X.equal u v then raise Valid
      else begin
        let varsU = get_vars u in
        let varsV = get_vars v in
        if Lists.is_empty varsU && Lists.is_empty varsV
        then raise Util.Unsolvable
        else
          begin
            let st_sys = slice u v in
            let sys_sols = sys_solve st_sys in
            let parts = partition (equal_simple_term X.equal) sys_sols in
            let unif_slic = equations_slice parts in
            let eq_pr = equalities_propagation unif_slic in
            let sol = build_solution unif_slic eq_pr in
            if Options.get_debug_bitv () then
              begin
                Debug.print_sliced_sys st_sys;
                Debug.print_c_solve_res sys_sols;
                Debug.print_partition_res parts;
                Debug.print_partition_res unif_slic;
                Debug.print_final_solution sol;
              end;
            sol
          end
      end

  end

  let compare x y = compare_abstract (embed x) (embed y)

  let equal bv1 bv2 = equal_abstract X.equal bv1 bv2

  let hash_simple_term_aux = function
    | Cte b -> 11 * Hashtbl.hash b
    | Other x -> 17 * hash_signed X.hash x
    | Ext (x, a, b, c) ->
      hash_signed X.hash x + 19 * (a + b + c)

  let hash l =
    List.fold_left
      (fun acc {bv=r; sz=sz} -> acc + 19 * (sz + hash_simple_term_aux r) ) 19 l

  let leaves bitv =
    List.fold_left
      (fun acc x ->
         match x.bv with
         | Cte _  -> acc
         | Other t | Ext(t,_,_,_) -> (X.leaves t.value)@acc
      ) [] bitv

  let is_mine = function
    | [{ bv = Other r; _ }] when not r.negated -> r.value
    | bv -> X.embed bv

  let negate = List.map (fun v ->
      let bv =
        match v.bv with
        | Cte b -> Cte (not b)
        | Other r -> Other { r with negated = not r.negated }
        | Ext (r, sz, i, j) -> Ext ({ r with negated = not r.negated }, sz, i, j)
      in
      { v with bv })

  let print = Debug.print_C_ast

  let nat_of_bv term bv m =
    let mk_2pow n =
      if n > 1 then
        E.int Z.(pow ~$2 n |> to_string)
      else if n = 1 then E.itwo else E.ione
    in
    let mk_ite term n pow =
      let nthbv = E.mk_bvextract n n term in
      let cond = E.mk_eq ~iff:false E.bvone nthbv in
      E.mk_ite cond (mk_2pow pow) E.izero
    in
    let bvr, ctx = Canonizer.make_aux bv [] in
    let r = Canonizer.sigma bvr in
    let _, natl =
      List.fold_left (
        fun (cnt, acc) simple_t ->
          try match simple_t with
            | { bv = Cte false; sz } -> cnt - sz, acc
            | { bv = Cte true; sz } ->
              let l = List.init sz (fun i -> mk_2pow (cnt - i)) in
              cnt - sz, l @ acc
            | { bv = Other { value = r; negated }; sz } ->
              let mk_ite =
                if negated then fun c t e -> mk_ite c e t else mk_ite
              in
              begin match X.term_extract r with
                | Some t, _ ->
                  let l =
                    List.init sz (fun i -> mk_ite t (sz - i - 1) (cnt - i))
                  in
                  cnt - sz, l @ acc
                | None, _ -> raise Exit
              end
            | { bv = Ext ({ value = r; negated }, _, _, ub); sz } ->
              let mk_ite =
                if negated then fun c t e -> mk_ite c e t else mk_ite
              in
              begin match X.term_extract r with
                | Some t, _ ->
                  let l =
                    List.init sz (fun i -> mk_ite t (ub - i) (cnt - i))
                  in
                  cnt - sz, l @ acc
                | None, _ -> raise Exit
              end
          with Exit ->
            let l =
              List.init simple_t.sz (fun i -> mk_ite term (cnt - i) (cnt - i))
            in
            cnt - simple_t.sz, l @ acc
      ) (m - 1, []) r
    in
    E.mk_term (Sy.Op Sy.Plus) natl Ty.Tint, ctx

  let get_bv_ty_sz x =
    match (E.term_view x).ty with
    | Ty.Tbitv n -> n
    | ty ->
      Util.failwith "Expected a bit-vector type, got %a" Ty.print ty

  let make t =
    match E.term_view t with
    | { E.f = Sy.Op BV2Nat; xs = [x] ; ty = Ty.Tint; _ } ->
      let n = get_bv_ty_sz x in
      let x', ctx' = nat_of_bv t x n in
      let r, ctx = X.make x' in
      r, ctx' @ ctx

    | _ ->
      let r, ctx = Canonizer.make_aux t [] in
      is_mine (Canonizer.sigma r), ctx

  let color _ = assert false

  let type_info bv =
    let sz = List.fold_left (fun acc bv -> bv.sz + acc) 0 bv in
    Ty.Tbitv sz

  let extract r ty =
    match X.extract r with
      Some (_::_ as bv) -> Canonizer.to_i_ast bv
    | None -> {bv =  Canonizer.I_Other (pos r); sz = ty}
    | Some [] -> assert false

  let var_or_term x y =
    match x.bv with
    | Other { value = r; negated = false } -> r, is_mine y
    | Other { value = r; negated = true } -> r, is_mine (negate y)
    | _ -> assert false

  let solve_ter u t =
    try
      List.map
        (fun (p,v) -> var_or_term p v)
        (Solver.solve u t)
    with Solver.Valid -> []

  (* ne resout pas quand c'est deja resolu *)
  let solve_bis u t =
    if Options.get_debug_bitv () then
      Printer.print_dbg
        ~module_name:"Bitv" ~function_name:"solve_bis"
        "solve %a = %a" X.print u X.print t;

    match X.extract u , X.extract t with
    | None   , None   -> if X.str_cmp u t > 0 then [u,t] else [t,u]
    | None   , Some t -> solve_ter (embed u) t
    | Some u , None   -> solve_ter u (embed t)
    | Some u , Some t -> solve_ter u t

  let rec subst_rec x subs biv =
    match biv.bv with
    | Canonizer.I_Cte _ -> biv
    | Canonizer.I_Other tt ->
      let tt' =
        if X.equal x tt.value then extract subs biv.sz
        else extract (X.subst x subs tt.value) biv.sz
      in
      if tt.negated then Canonizer.negate tt' else tt'
    | Canonizer.I_Ext (t,i,j) ->
      { biv with bv = Canonizer.I_Ext(subst_rec x subs t,i,j) }
    | Canonizer.I_Comp (u,v) ->
      { biv with
        bv = Canonizer.I_Comp(subst_rec x subs u ,subst_rec x subs v)}

  let subst x subs biv =
    if Options.get_debug_bitv () then
      Printer.print_dbg
        ~module_name:"Bitv" ~function_name:"subst"
        "subst %a |-> %a in %a" X.print x X.print subs print biv;
    if Lists.is_empty biv then is_mine biv
    else
      let r = Canonizer.sigma (subst_rec x subs (Canonizer.to_i_ast biv)) in
      is_mine r

  let fully_interpreted _ = true

  let term_extract _ = None, false

  let abstract_selectors v acc = is_mine v, acc

  let solve r1 r2 pb =
    Sig.{pb with sbt = List.rev_append (solve_bis r1 r2) pb.sbt}

  let assign_value _ _ _ =
    Printer.print_err
      "[Bitv.models] assign_value currently not implemented";
    raise (Util.Not_implemented "Models for bit-vectors")

  let choose_adequate_model _ _ =
    Printer.print_err
      "[Bitv.models] choose_adequate_model currently not implemented";
    raise (Util.Not_implemented "Models for bit-vectors")

end

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

let compare_sort s1 s2 =
  match s1, s2 with
  | A, A | B, B | C, C -> 0
  | A, (B | C) | B, C -> -1
  | C, (A | B) | B, A -> 1

type tvar = { var : int ; sorte : sort_var }

let compare_tvar v1 v2 =
  if v1 == v2 then 0
  else
    let c = compare v1.var v2.var in
    if c <> 0 then c
    else compare_sort v1.sorte v2.sorte

type 'a xterm = Var of tvar | Alien of 'a

type 'a alpha_term = {
  bv : 'a;
  sz : int;
}

type 'a simple_term_aux =
  | Cte of bool
  | Other of 'a xterm
  | Ext of 'a xterm * int * int * int (*// id * size * i * j //*)

type 'a simple_term = ('a simple_term_aux) alpha_term

type 'a abstract =  ('a simple_term) list

(* for the solver *)

type solver_simple_term_aux =
  | S_Cte of bool
  | S_Var of tvar

type solver_simple_term = solver_simple_term_aux alpha_term

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

let compare_alpha_term cmp a1 a2 =
  if a1.sz <> a2.sz then a1.sz - a2.sz else cmp a1.bv a2.bv

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
        | BVneg | BVadd | BVsub | BVmul | BVudiv | BVurem | BVsdiv | BVsrem
        | BVsmod | BVshl | BVlshr
      ) -> true
    | _ -> false

  let embed r =
    match X.extract r with
    | None ->
      begin
        match X.type_info r with
        | Ty.Tbitv n -> [{bv = Other (Alien r) ; sz = n}]
        | _  -> assert false
      end
    | Some b -> b

  let compare_xterm xt1 xt2 = match xt1,xt2 with
    | Var v1, Var v2 ->
      let c1 = compare_sort v1.sorte v2.sorte in
      if c1 <> 0 then c1
      else -(compare v1.var v2.var)
    (* on inverse le signe : les variables les plus fraiches sont
       les plus jeunes (petites)*)

    | Alien t1, Alien t2 -> X.str_cmp t1 t2
    | Var _, Alien _ -> 1
    | Alien _, Var _ -> -1

  let compare_simple_term = compare_alpha_term (fun st1 st2 ->
      match st1, st2 with
      | Cte b1, Cte b2 -> Bool.compare b1 b2
      | Cte false , _ | _ , Cte true -> -1
      | _ , Cte false | Cte true,_ -> 1

      | Other t1 , Other t2 -> compare_xterm t1 t2
      | _ , Other _ -> -1
      | Other _ , _ -> 1

      | Ext(t1,s1,i1,_) , Ext(t2,s2,i2,_) ->
        let c1 = compare s1 s2 in
        if c1<>0 then c1
        else let c2 = compare i1 i2 in
          if c2 <> 0 then c2 else compare_xterm t1 t2
    )

  let compare_abstract = Lists.compare compare_simple_term

  let compare_solver_simple_term = compare_alpha_term (fun st1 st2 ->
      match st1, st2 with
      | S_Cte b1, S_Cte b2 -> Bool.compare b1 b2
      | S_Cte false, _ | _, S_Cte true -> -1
      | _ , S_Cte false | S_Cte true,_ -> 1
      | S_Var v1, S_Var v2 ->
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
      | I_Other of X.r xterm
      | I_Ext of term * int * int
      | I_Comp of term * term

    and term = term_aux alpha_term

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

      | I_Other xterm1, I_Other xterm2 -> compare_xterm xterm1 xterm2

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
      let nctx = ref[] in
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
      let ctx = List.rev_append !nctx ctx in
      bitv_to_icomp (List.hd res) (List.tl res), ctx

    let bit_of_expr t =
      match E.term_view t with
      | { f = Sy.Int s; _ } ->
        begin match Hstring.view s with
          | "1" -> Some true
          | "0" -> Some false
          | _ ->
            failwith (
              Format.asprintf "Expeceted \"1\" or \"0\", but got \"%a\""
                E.print t
            )
        end
      | _ -> None

    let bit_e_neg neg t =
      if neg
      then E.mk_ite (E.mk_eq ~iff:false t E.izero) E.bvone E.bvzero
      else E.mk_ite (E.mk_eq ~iff:false t E.izero) E.bvzero E.bvone

    let bv_of_bool ?(neg = false) b =
      if (if neg then not b else b) then E.bvone else E.bvzero

    let mk_nthbv_eq bv_t n e =
      E.mk_eq ~iff:false (E.mk_bitv_extract n n bv_t 1) e

    let get_nth_eq_b bv_t cnt t_b =
      mk_nthbv_eq bv_t cnt (bv_of_bool t_b)

    let bitv_of_nat ?(neg = false) bv_t nat_t size ctx =
      let bitf = if neg then (fun b -> not b) else (fun b -> b) in
      let pow n =
        E.mk_term (Sy.Op Sy.Pow) [E.itwo; E.int (Int.to_string n)] Ty.Tint
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
              let t1 = { bv = I_Other (Alien r); sz = 1 } in
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
                  { bv = I_Other (Alien r); sz = 1}
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
              let t1 = { bv = I_Other (Alien r); sz = 1} in
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

    let bvor_ctes ~is_and b1 sz1 b2 sz2 =
      let bres = if is_and then b1 && b2 else b1 || b2 in
      if sz1 > sz2 then
        {bv = Cte bres; sz = sz2}, [{ bv = Cte b1; sz = sz1 - sz2 }], []
      else if sz1 < sz2 then
        {bv = Cte bres; sz = sz1}, [], [{ bv = Cte b1; sz = sz2 - sz1 }]
      else {bv = Cte bres; sz = sz1}, [], []

    let bvor_cte_other ~is_and b sz1 o sz2 =
      let bres = if is_and then not b else b in
      if sz1 > sz2 then
        let l1 = [{ bv = Cte b; sz = sz1 - sz2 }] in
        if bres then { bv = Cte b; sz = sz2 }, l1, []
        else { bv = Other o; sz = sz2 }, l1, []
      else if sz1 < sz2 then
        let l2 = [{ bv = Ext (o, sz2, 0, sz2 - sz1 - 1); sz = sz2 - sz1 }] in
        if bres then { bv = Cte b; sz = sz1 }, [], l2
        else { bv = Ext (o, sz2, sz2 - sz1, sz2 - 1); sz = sz1 }, [], l2
      else
      if bres then { bv = Cte b; sz = sz1 }, [], []
      else { bv = Other o; sz = sz1 }, [], []

    let bvor_cte_ext ~is_and b sz1 o sz2' sz2 lb ub =
      let bres = if is_and then not b else b in
      if sz1 > sz2 then
        let l1 = [{ bv = Cte b; sz = sz1 - sz2 }] in
        if bres
        then { bv = Cte b; sz = sz2 }, l1, []
        else { bv = Ext (o, sz2', lb, ub); sz = sz2 }, l1, []
      else if sz1 < sz2 then
        let l2 =
          [{ bv = Ext (o, sz2', lb, lb + sz2 - sz1 - 1); sz = sz2 - sz1 }]
        in
        if bres
        then { bv = Cte b; sz = sz1 }, [], l2
        else { bv = Ext (o, sz2', lb + sz2 - sz1, ub); sz = sz1 }, [], l2
      else
      if bres
      then { bv = Cte b; sz = sz1 }, [], []
      else { bv = Ext (o, sz2', lb, ub); sz = sz1 }, [], []

    (** [mk_bvget_or_eq t cnt t1 cnt1 t2 cnt2]:
        t[cnt] = if t1[cnt1] = 0 then t2[cnt2] else 1 *)
    let mk_bvget_or_eq nt cnt t1 cnt1 t2 cnt2 =
      E.mk_eq ~iff:false (E.mk_bitv_extract cnt cnt nt 1) (
        E.mk_ite
          (E.mk_eq ~iff:false (E.mk_bitv_extract cnt1 cnt1 t1 1) E.bvzero)
          (E.mk_bitv_extract cnt2 cnt2 t2 1)
          E.bvone)

    (** [mk_bvget_and_eq t cnt t1 cnt1 t2 cnt2]:
        t[cnt] = if t1[cnt1] = 1 then t2[cnt2] else 0 *)
    let mk_bvget_and_eq nt cnt t1 cnt1 t2 cnt2 =
      E.mk_eq ~iff:false (E.mk_bitv_extract cnt cnt nt 1) (
        E.mk_ite
          (E.mk_eq ~iff:false (E.mk_bitv_extract cnt1 cnt1 t1 1) E.bvone)
          (E.mk_bitv_extract cnt2 cnt2 t2 1)
          E.bvzero
      )

    (** turn into a dispatcher function  *)
    let mk_o_eqs =
      fun ctx t ~is_and nt t1 i1 t2 i2 n ->
      let rec aux1 ctx cnt =
        if cnt >= n then ctx else
          let eq = mk_bvget_and_eq t cnt t1 (cnt + i1) t2 (cnt + i2) in
          aux1 (eq :: ctx) (cnt + 1)
      in
      let rec aux2 ctx cnt =
        if cnt >= n then ctx else
          let eq = mk_bvget_or_eq t cnt t1 (cnt + i1) t2 (cnt + i2) in
          aux2 (eq :: ctx) (cnt + 1)
      in
      E.mk_eq ~iff:false t nt :: if is_and then aux1 ctx 0 else aux2 ctx 0

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
          E.mk_bitv_concat
            (E.mk_bitv_extract 0 (n - 2) t (n - 1))
            (E.mk_bitv_extract (n - 1) (n - 1) t 1)
            n
        )

    let rec mk_rotate_right n i t =
      if i = 0 then t else
        mk_rotate_right n (i - 1) (
          E.mk_bitv_concat
            (E.mk_bitv_extract 0 0 t 1)
            (E.mk_bitv_extract 1 (n - 1) t (n - 1))
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
             (E.mk_bitv_extract (n-1) (n-1) t1 1)
             (E.mk_bitv_extract (n-1) (n-1) t2 1))
          (mk_bitv_comp (n-1)
             (E.mk_bitv_extract 0 (n-2) t1 (n-1))
             (E.mk_bitv_extract 0 (n-2) t2 (n-1)))

    let mk_bvshl n x y =
      let x' = E.mk_term (Sy.Op Sy.BV2Nat) [x] Ty.Tint in
      let y' = E.mk_term (Sy.Op Sy.BV2Nat) [y] Ty.Tint in
      let y'' = E.mk_term (Sy.Op Sy.Pow) [E.itwo; y'] Ty.Tint in
      let natres = E.mk_term (Sy.Op Sy.Mult) [x'; y''] Ty.Tint in
      E.mk_term (Sy.Op (Sy.Nat2BV n)) [natres] (Ty.Tbitv n)

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
        let bv, nctx = mk_bvor ~is_and:neg r1' r2' t' x y ctx'' in
        to_i_ast bv, nctx (* not great! *)

      | { E.f = Sy.Op BVExtend (b, k); xs = [ x ]; ty = Ty.Tbitv n; _ } ->
        let r1, ctx' = make_aux ~neg x ctx in
        extend_term b ~neg r1 k n,
        ctx'

      | { E.f = Sy.Op BV_repeat k; xs = [ x ]; ty = Ty.Tbitv _; _ } ->
        let r1, ctx' = make_aux ~neg x ctx in
        repeat_term k r1, ctx'

      | { E.f = Sy.Op BV_rotate (k, true); xs = [ x ]; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (mk_rotate_right n k x) ctx

      | { E.f = Sy.Op BV_rotate (k, false); xs = [ x ]; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (mk_rotate_left n k x) ctx

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

      | { E.f = Sy.Op BVudiv; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (E.mk_bvudiv n x y) ctx

      | { E.f = Sy.Op BVurem; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (E.mk_bvurem n x y) ctx

      | { E.f = Sy.Op BVsdiv; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (E.mk_bvsdiv n x y) ctx

      | { E.f = Sy.Op BVsrem; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (E.mk_bvsrem n x y) ctx

      | { E.f = Sy.Op BVsmod; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (E.mk_bvsmod n x y) ctx

      | { E.f = Sy.Op BVshl; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        make_aux ~neg (mk_bvshl n x y) ctx

      | { E.f = Sy.Op BVlshr; xs = [x; y] ; ty = Ty.Tbitv n; _ } ->
        let z = E.mk_term (Sy.Op Sy.Pow) [E.itwo; E.mk_bv2nat y] Ty.Tint in
        make_aux ~neg (
          E.mk_nat2bv n (E.mk_term (Sy.Op Sy.Div) [E.mk_bv2nat x; z] Ty.Tint)
        ) ctx

      | { E.ty = Ty.Tbitv n; _ } ->
        if neg then
          let tv = E.fresh_name (Ty.Tbitv n) in
          let t'' = E.mk_bvnot n t' in
          let rv = X.term_embed tv in
          let eq = E.mk_eq ~iff:false tv t'' in
          {bv = I_Other (Alien rv); sz = n}, eq :: ctx
        else
          let r', ctx' = X.make t' in
          {bv = I_Other (Alien r'); sz = n}, ctx' @ ctx

      | _ ->
        failwith
          (Format.asprintf "[Bitv] make: Unexpected term %a@." E.print t')

    and mk_bvor ?(is_and = false) r1 r2 t t1 t2 ctx =
      let rec aux r1 r2 ctx =
        match r1, r2 with
        | hd1 :: tl1, hd2 :: tl2 when compare_simple_term hd1 hd2 = 0 ->
          let l, ctx' = aux tl1 tl2 ctx in
          hd1 :: l, ctx'

        | { bv = Cte b1; sz = sz1 } :: tl1, { bv = Cte b2; sz = sz2 } :: tl2 ->
          let n, nl1, nl2 = bvor_ctes ~is_and b1 sz1 b2 sz2 in
          let l, ctx' = aux (nl1 @ tl1) (nl2 @ tl2) ctx in
          n :: l, ctx'

        | { bv = Cte b; sz = sz1; } :: tl1,
          { bv = Other o; sz = sz2; } :: tl2 ->
          let n, nl1, nl2 = bvor_cte_other ~is_and b sz1 o sz2 in
          let l, ctx' = aux (nl1 @ tl1) (nl2 @ tl2) ctx in
          n :: l, ctx'

        | { bv = Other o; sz = sz1; } :: tl2,
          { bv = Cte b; sz = sz2; } :: tl1 ->
          let n, nl1, nl2 = bvor_cte_other ~is_and b sz2 o sz1 in
          let l, ctx' = aux (nl1 @ tl1) (nl2 @ tl2) ctx in
          n :: l, ctx'

        | { bv = Cte b; sz = sz1; } :: tl1,
          { bv = Ext (o, sz2', lb, ub); sz = sz2; } :: tl2 ->
          let n, nl1, nl2 = bvor_cte_ext ~is_and b sz1 o sz2' sz2 lb ub in
          let l, ctx' = aux (nl1 @ tl1) (nl2 @ tl2) ctx in
          n :: l, ctx'

        | { bv = Ext (o, sz2', lb, ub); sz = sz2; } :: tl2,
          { bv = Cte b; sz = sz1; } :: tl1 ->
          let n, nl1, nl2 = bvor_cte_ext ~is_and b sz1 o sz2' sz2 lb ub in
          let l, ctx' = aux (nl1 @ tl1) (nl2 @ tl2) ctx in
          n :: l, ctx'

        | { bv = Other o1; sz = sz1; } :: tl1,
          { bv = Other o2; sz = sz2; } :: tl2 ->
          if sz1 > sz2 then
            let nsz = sz1 - sz2 in
            let nr, nctx = bvor_os t ~is_and t1 0 t2 0 sz2 ctx in
            let nl1 = {bv = Ext (o1, sz1, sz2, sz1 - 1); sz = nsz } :: tl1 in
            let l, ctx' = aux nl1 tl2 nctx in
            nr @ l, ctx'
          else if sz2 > sz1 then
            let nsz = sz2 - sz1 in
            let nr, nctx = bvor_os t ~is_and t1 0 t2 0 sz1 ctx in
            let nl2 = {bv = Ext (o2, sz2, sz1, sz2 - 1); sz = nsz } :: tl2 in
            let l, ctx' = aux tl1 nl2 nctx in
            nr @ l, ctx'
          else
            let nr, nctx = bvor_os t ~is_and t1 0 t2 0 sz1 ctx in
            let l, ctx' = aux tl1 tl2 nctx in
            nr @ l, ctx'

        | { bv = Ext (o1, sz1', lb1, ub1); sz = sz1; } :: tl1,
          { bv = Ext (o2, sz2', lb2, ub2); sz = sz2; } :: tl2 ->
          if sz1 > sz2 then
            let nsz = sz1 - sz2 in
            let nr, nctx =
              bvor_os t ~is_and t1 lb1 t2 lb2 sz2 ctx
            in
            let nl1 = {bv = Ext (o1, sz1', lb1 + sz2, ub1); sz = nsz } :: tl1 in
            let l, ctx' = aux nl1 tl2 nctx in
            nr @ l, ctx'
          else if sz2 > sz1 then
            let nsz = sz2 - sz1 in
            let nr, nctx =
              bvor_os t ~is_and t1 lb1 t2 lb2 sz1 ctx
            in
            let nl2 = {bv = Ext (o2, sz2', lb2 + sz1, ub2); sz = nsz } :: tl2 in
            let l, ctx' = aux tl1 nl2 nctx in
            nr @ l, ctx'
          else
            let nr, nctx =
              bvor_os t ~is_and t1 lb1 t2 lb2 sz1 ctx
            in
            let l, ctx' = aux tl1 tl2 nctx in
            nr @ l, ctx'

        | { bv = Other o1; sz = sz1; } :: tl1,
          { bv = Ext (o2, sz2', lb2, ub2); sz = sz2; } :: tl2 ->
          if sz1 > sz2 then
            let nsz = sz1 - sz2 in
            let nr, nctx = bvor_os t ~is_and t1 0 t2 lb2 sz2 ctx in
            let nl1 = {bv = Ext (o1, sz1, sz2, sz1 - 1); sz = nsz } :: tl1 in
            let l, ctx' = aux nl1 tl2 nctx in
            nr @ l, ctx'
          else if sz2 > sz1 then
            let nsz = sz2 - sz1 in
            let nr, nctx = bvor_os t ~is_and t1 0 t2 lb2 sz1 ctx in
            let nl2 = {bv = Ext (o2, sz2', lb2 + sz1, ub2); sz = nsz } :: tl2 in
            let l, ctx' = aux tl1 nl2 nctx in
            nr @ l, ctx'
          else
            let nr, nctx = bvor_os t ~is_and t1 0 t2 lb2 sz1 ctx in
            let l, ctx' = aux tl1 tl2 nctx in
            nr @ l, ctx'

        | { bv = Ext (o1, sz1', lb1, ub1); sz = sz1; } :: tl1,
          { bv = Other o2; sz = sz2; } :: tl2 ->
          if sz1 > sz2 then
            let nsz = sz1 - sz2 in
            let nr, nctx = bvor_os t ~is_and t1 lb1 t2 0 sz2 ctx in
            let nl1 = {bv = Ext (o1, sz1', lb1 + sz2, ub1); sz = nsz } :: tl1 in
            let l, ctx' = aux nl1 tl2 nctx in
            nr @ l, ctx'
          else if sz2 > sz1 then
            let nsz = sz2 - sz1 in
            let nr, nctx = bvor_os t ~is_and t1 lb1 t2 0 sz1 ctx in
            let nl2 = {bv = Ext (o2, sz2, sz1, sz2 - 1); sz = nsz } :: tl2 in
            let l, ctx' = aux tl1 nl2 nctx in
            nr @ l, ctx'
          else
            let nr, nctx = bvor_os t ~is_and t1 lb1 t2 0 sz1 ctx in
            let l, ctx' = aux tl1 tl2 nctx in
            nr @ l, ctx'

        | [], [] -> [], ctx
        | _ -> assert false (* should be unreachable *)
      in
      aux r1 r2 ctx

    and bvor_os t ~is_and t1 cnt1 t2 cnt2 sz ctx =
      let nt = E.fresh_name (Ty.Tbitv sz) in
      let rterm, nctx = make_aux nt ctx in
      let nctx = mk_o_eqs nctx t ~is_and nt t1 cnt1 t2 cnt2 sz in
      let nr = sigma rterm in
      nr, nctx
  end

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer

    let print_tvar fmt ({var=v;sorte=s},sz) =
      Format.fprintf fmt "%s_%d[%d]@?"
        (match s with | A -> "a" | B -> "b" | C -> "c")
        v sz

    (* unused
       open Canonizer
       let rec print_I_ast fmt ast = match ast.bv with
       | I_Cte b -> fprintf fmt "%d[%d]@?" (if b then 1 else 0) ast.sz
       | I_Other (Alien t) -> fprintf fmt "%a[%d]@?" X.print t ast.sz
       | I_Other (Var tv) -> fprintf fmt "%a@?" print_tvar (tv,ast.sz)
       | I_Ext (u,i,j) -> fprintf fmt "%a<%d,%d>@?" print_I_ast u i j
       | I_Comp(u,v) -> fprintf fmt "@[(%a * %a)@]" print_I_ast u print_I_ast v
    *)

    let print fmt ast =
      let open Format in
      match ast.bv with
      | Cte b -> fprintf fmt "%d[%d]@?" (if b then 1 else 0) ast.sz
      | Other (Alien t) -> fprintf fmt "%a@?" X.print t
      | Other (Var tv) -> fprintf fmt "%a@?" print_tvar (tv,ast.sz)
      | Ext (Alien t,_,i,j) ->
        fprintf fmt "%a@?" X.print t;
        fprintf fmt "<%d,%d>@?" i j
      | Ext (Var tv,_,i,j) ->
        fprintf fmt "%a@?" print_tvar (tv,ast.sz);
        fprintf fmt "<%d,%d>@?" i j

    let print_C_ast fmt = function
        [] -> assert false
      | x::l -> print fmt x; List.iter (Format.fprintf fmt " @@ %a" print) l

    let print_s fmt ast = match ast.bv with
      | S_Cte b -> Format.fprintf fmt "%d[%d]@?" (if b then 1 else 0) ast.sz
      | S_Var tv -> Format.fprintf fmt "%a@?" print_tvar (tv,ast.sz)

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

    let slice t u  =
      let f_add (s1,s2) acc =
        let b =
          compare_simple_term s1 s2 = 0
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
      else [ { bv = S_Var (fresh_var genre) ; sz = size } ]

    let cte_vs_other bol st = st , [{bv = S_Cte bol ; sz = st.sz}]

    let cte_vs_ext bol xt s_xt i j =
      let a1  = fresh_bitv A i in
      let a2  = fresh_bitv A (s_xt - 1 - j) in
      let cte = [ {bv = S_Cte bol ; sz =j - i + 1 } ] in
      let var = { bv = Other xt ; sz = s_xt }
      in var, a2@cte@a1

    let other_vs_other st1 st2 =
      let c = fresh_bitv C st1.sz in [ (st1,c) ; (st2,c) ]

    let other_vs_ext st xt s_xt i j =
      let c  = fresh_bitv C st.sz in
      let a1 = fresh_bitv A i in
      let a2 = fresh_bitv A (s_xt - 1 - j) in
      let extr = { bv = Other xt ; sz = s_xt }
      in [ (st,c) ; (extr,a2 @ c @ a1) ]

    let ext1_vs_ext2 (id,s,i,j) (id',s',i',j') = (* id != id' *)
      let c   = fresh_bitv (C) (j - i + 1) in
      let a1  = fresh_bitv A i  in
      let a1' = fresh_bitv A i' in
      let a2  = fresh_bitv A (s - 1 - j)   in
      let a2' = fresh_bitv A (s' - 1 - j') in
      let x_v = { sz = s  ; bv = Other id  } in
      let y_v = { sz = s' ; bv = Other id' } in
      [ (x_v , a2 @ c @ a1) ; (y_v , a2' @ c @ a1') ]

    let ext_vs_ext xt siz (i1,i2) tai =
      let overl = i1 + tai -i2 in
      if overl <= 0 then begin
        let a1 = fresh_bitv A i1     in
        let a2 = fresh_bitv A (-overl) in
        let a3 = fresh_bitv A (siz - tai - i2) in
        let b  = fresh_bitv  B tai
        in ({ bv = Other xt ; sz = siz } , a3 @ b @ a2 @ b @ a1)
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
        while !cpt <= b_box do
          acc := b1 @ b2 @(!acc);
          cpt := !cpt + nn_overl
        done;
        ({ bv = Other xt ; sz = siz } , a3 @ (!acc) @ a1)
      end

    let sys_solve sys =
      let c_solve (st1,st2) = match st1.bv,st2.bv with
        |Cte _, Cte _ -> raise Util.Unsolvable (* forcement un 1 et un 0 *)

        |Cte b, Other (Var _) -> [cte_vs_other b st2]
        |Other (Var _), Cte b -> [cte_vs_other b st1]

        |Cte b, Other (Alien _) -> [cte_vs_other b st2]
        |Other (Alien _), Cte b -> [cte_vs_other b st1]

        |Cte b, Ext(xt,s_xt,i,j) -> [cte_vs_ext b xt s_xt i j]
        |Ext(xt,s_xt,i,j), Cte b -> [cte_vs_ext b xt s_xt i j]
        |Other _, Other _ -> other_vs_other st1 st2

        |Other _, Ext(xt,s_xt,i,j) ->
          other_vs_ext st1 xt s_xt i j

        |Ext(xt,s_xt,i,j), Other _ -> other_vs_ext st2 xt s_xt i j
        |Ext(id,s,i,j), Ext(id',s',i',j') ->
          if compare_xterm id id' <> 0
          then ext1_vs_ext2 (id,s,i,j) (id',s',i',j')
          else [ext_vs_ext id s (if i<i' then (i,i') else (i',i)) (j - i + 1)]

      in List.flatten (List.map c_solve sys)


    let partition cmp l =
      let rec add acc (t,cnf) = match acc with
        |[] -> [(t,[cnf])]
        |(t',cnf')::r -> if cmp t t' = 0 then (t',cnf::cnf')::r
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

    let slice_var var s1 =
      let s2 = var.sz - s1 in
      match var.bv with
      |S_Cte _ -> {var with sz = s1},{var with sz = s2},None
      |S_Var v ->
        let (fs,sn,tr) = match v.sorte with
          |A -> (fresh_var A), (fresh_var A), A
          |B -> (fresh_var B), (fresh_var B), B
          |C -> (fresh_var C), (fresh_var C), C
        in {bv = S_Var fs; sz = s1},{bv = S_Var sn; sz = s2},Some tr

    let rec slice_composition eq pat (ac_eq,c_sub) = match (eq,pat) with
      |[],[] -> (ac_eq,c_sub)
      |st::_,n::_  when st.sz < n -> assert false
      |st::comp,n::pt ->
        if st.sz = n then slice_composition comp pt (st::ac_eq , c_sub)
        else let (st_n,res,flag) = slice_var st n
          in begin
            match flag with
            |Some B ->
              let comp' = List.fold_right (fun s_t acc ->
                  if compare_solver_simple_term s_t st <> 0
                  then s_t::acc
                  else st_n::res::acc
                ) comp []
              in slice_composition (res::comp') pt (st_n::ac_eq,c_sub)

            |Some C -> let ac' = (st_n::ac_eq,(st,(st_n,res))::c_sub)
              in slice_composition (res::comp) pt ac'

            | _ -> slice_composition (res::comp) pt (st_n::ac_eq,c_sub)
          end
      | _ -> assert false

    let uniforme_slice vls =
      let pat = slicing_pattern(List.map (List.map(fun bv ->bv.sz))vls) in
      let rec f_aux acc subs l_vs = match l_vs with
        |[] -> acc,subs
        |eq::eqs -> let (eq',c_subs) = slice_composition eq pat ([],[])
          in f_aux (List.rev eq'::acc) (c_subs@subs) eqs
      in f_aux [] [] vls

    let apply_subs subs sys =
      let rec f_aux = function
        |[] -> assert false
        |v::r -> try let (v1,v2) = List.assoc v subs in v1::v2::(f_aux r)
          with _ -> v::(f_aux r)
      in List.map (fun (t,vls) ->(t,List.map f_aux vls))sys

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
              let cmp (a, l1) (b, l2) =
                let c = compare_simple_term a b in
                if c <> 0 then c
                else
                  Lists.compare (Lists.compare compare_solver_simple_term) l1 l2
              in
              if Lists.compare cmp _bw bw = 0
              then slice_rec ((t,vls')::bw) _fw
              else slice_rec [] (bw@((t,vls'):: _fw))
            end
      in slice_rec [] parts

    let rec union_sets sets =
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

    let init_sets vals =
      let acc = List.map (fun at -> ST_Set.singleton at) (List.hd vals) in
      let tl = (List.tl vals) in
      let f_aux = List.map2 (fun ac_e e -> ST_Set.add e ac_e)
      in List.fold_left f_aux acc tl

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

    let build_solution unif_slic sets =
      let get_rep var =
        fst(List.find ( fun(_,set)->ST_Set.mem var set ) sets) in
      let to_external_ast v =
        {sz = v.sz;
         bv = match v.bv with
           |S_Cte b -> Cte b
           |S_Var _ ->
             begin
               match (get_rep v).bv with
               |S_Cte b -> Cte b
               |S_Var tv -> Other (Var tv)
             end
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

    let solve u v =
      if Lists.compare compare_simple_term u v = 0 then raise Valid
      else begin
        let varsU = get_vars u in
        let varsV = get_vars v in
        if Lists.is_empty varsU && Lists.is_empty varsV
        then raise Util.Unsolvable
        else
          begin
            let st_sys = slice u v in
            let sys_sols = sys_solve st_sys in
            let parts = partition compare_simple_term sys_sols in
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

  (* should use hashed compare to be faster, not structural comparison *)
  let equal bv1 bv2 = compare_abstract bv1 bv2 = 0

  let hash_xterm = function
    | Var {var = i; sorte = A} -> 11 * i
    | Var {var = i; sorte = B} -> 17 * i
    | Var {var = i; sorte = C} -> 19 * i
    | Alien r -> 23 * X.hash r

  let hash_simple_term_aux = function
    | Cte b -> 11 * Hashtbl.hash b
    | Other x -> 17 * hash_xterm x
    | Ext (x, a, b, c) ->
      hash_xterm x + 19 * (a + b + c)

  let hash l =
    List.fold_left
      (fun acc {bv=r; sz=sz} -> acc + 19 * (sz + hash_simple_term_aux r) ) 19 l

  let leaves bitv =
    List.fold_left
      (fun acc x ->
         match x.bv with
         | Cte _  -> acc
         | Ext( Var v,sz,_,_) ->
           (X.embed [{bv=Other (Var v) ; sz = sz }])::acc
         | Other (Var _)  -> (X.embed [x])::acc
         | Other (Alien t) | Ext(Alien t,_,_,_) -> (X.leaves t)@acc
      ) [] bitv

  let is_mine = function [{ bv = Other (Alien r); _ }] -> r | bv -> X.embed bv

  let print = Debug.print_C_ast

  let nat_of_bv term bv m =
    let mk_2pow n =
      if n > 1 then
        E.mk_term (Sy.Op Sy.Pow) [E.itwo; E.int (Int.to_string n)] Ty.Tint
      else if n = 1 then E.itwo else E.ione
    in
    let mk_ite term n pow =
      let nthbv = E.mk_bitv_extract n n term 1 in
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
            | { bv = Other (Alien r); sz } ->
              begin match X.term_extract r with
                | Some t, _ ->
                  let l =
                    List.init sz (fun i -> mk_ite t (sz - i - 1) (cnt - i))
                  in
                  cnt - sz, l @ acc
                | None, _ -> raise Exit
              end
            | { bv = Ext (Alien r, _, _, ub); sz } ->
              begin match X.term_extract r with
                | Some t, _ ->
                  let l =
                    List.init sz (fun i -> mk_ite t (ub - i) (cnt - i))
                  in
                  cnt - sz, l @ acc
                | None, _ -> raise Exit
              end
            | _ -> raise Exit
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
      failwith
        (Format.asprintf "Expected a bit-vector type, got %a" Ty.print ty)

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
    | Some (_::_ as bv) -> Canonizer.to_i_ast bv
    | None -> {bv =  Canonizer.I_Other (Alien r); sz = ty}
    | Some _ -> assert false

  let extract_xterm r =
    match X.extract r with
    | Some [{ bv = Other (Var _ as x); _ }] -> x
    | None -> Alien r
    | _ -> assert false

  let var_or_term x =
    match x.bv with
    | Other Alien r -> r
    | Other Var _ as xt -> X.embed [{bv = xt; sz = x.sz}]
    | _ -> assert false

  (* ne resout pas quand c'est deja resolu *)
  let solve_bis u t =
    if Options.get_debug_bitv () then
      Printer.print_dbg
        ~module_name:"Bitv" ~function_name:"solve_bis"
        "solve %a = %a" X.print u X.print t;

    match X.extract u , X.extract t with
    | None   , None   -> if X.str_cmp u t > 0 then [u,t] else [t,u]
    | None   , Some _ -> [u , t]
    | Some _ , None   -> [t , u]
    | Some u , Some t ->
      try
        List.map
          (fun (p,v) -> var_or_term p,is_mine v)
          (Solver.solve u t)
      with Solver.Valid -> []



  let rec subst_rec x subs biv =
    match biv.bv , extract_xterm x with
    | Canonizer.I_Cte _ , _ -> biv
    | Canonizer.I_Other (Var y), Var z when compare_tvar y z = 0 ->
      extract subs biv.sz
    | Canonizer.I_Other (Var _) , _ -> biv
    | Canonizer.I_Other (Alien tt) , _ ->
      if X.equal x tt then
        extract subs biv.sz
      else extract (X.subst x subs tt) biv.sz
    | Canonizer.I_Ext (t,i,j) , _ ->
      { biv with bv = Canonizer.I_Ext(subst_rec x subs t,i,j) }
    | Canonizer.I_Comp (u,v) , _ ->
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

  let term_extract r =
    match X.extract r with
    | None -> X.term_extract r
    | Some l ->
      try
        let mk_bv b sz =
          let c = if b then '1' else '0' in
          E.bitv (String.init sz (fun _ -> c)) (Ty.Tbitv sz)
        in
        match l with
        | { bv = Cte b; sz; } :: tl ->
          let _, t =
            List.fold_left (
              fun (n, acc) r ->
                match r with
                | { bv = Cte b; sz; } ->
                  let nsz =  n + sz in
                  nsz,
                  E.mk_bitv_concat acc (mk_bv b sz) nsz
                | _ -> raise Exit
            ) (sz, mk_bv b sz) tl
          in
          Some t, false
        | _ -> None, false
      with Exit -> None, false

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

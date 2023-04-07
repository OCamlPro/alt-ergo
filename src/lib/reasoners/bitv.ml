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

module Sy = Symbols
module E = Expr

type sort_var = A | B | C

type tvar = { var : int ; sorte : sort_var }

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

type 'a abstract =
  | BV of ('a simple_term) list
  | BVAccess of (('a simple_term) list * int)
  | Bit of 'a

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

module Shostak(X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name = "bitv"

  let is_mine_symb sy _ =
    match sy with
    | Sy.Bitv _ | Sy.Op (
        Sy.Concat | Sy.Extract _ | Sy.BVGet _ | Sy.Nat2BV _
      ) -> true
    | _ -> false

  let embed r =
    match X.extract r with
    | None ->
      begin
        match X.type_info r with
        | Ty.Tbitv n -> BV [{bv = Other (Alien r) ; sz = n}]
        | _  -> assert false
      end
    | Some b -> b

  let compare_xterm xt1 xt2 = match xt1,xt2 with
    | Var v1, Var v2 ->
      let c1 = compare v1.sorte v2.sorte in
      if c1 <> 0 then c1
      else -(compare v1.var v2.var)
    (* on inverse le signe : les variables les plus fraiches sont
       les plus jeunes (petites)*)

    | Alien t1, Alien t2 -> X.str_cmp t1 t2
    | Var _, Alien _ -> 1
    | Alien _, Var _ -> -1

  let compare_simple_term st1 st2 =
    if st1.sz <> st2.sz then st1.sz - st2.sz
    else
      begin
        match st1.bv,st2.bv with
        | Cte b,Cte b' -> compare b b'
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
      end

  module ST_Set = Set.Make (
    struct
      type t = solver_simple_term
      let compare st1 st2 =
        if st1.sz <> st2.sz then st1.sz - st2.sz
        else
          begin
            match st1.bv,st2.bv with
            | S_Cte b, S_Cte b' -> compare b b'
            | S_Cte false, _ | _, S_Cte true -> -1
            | _ , S_Cte false | S_Cte true,_ -> 1
            | S_Var v1, S_Var v2 ->
              let c1 = compare v1.sorte v2.sorte
              in if c1 <> 0 then c1 else compare v1.var v2.var
          end
    end)

  module Canonizer = struct

    type term_aux  =
      | I_Cte of bool
      | I_Other of X.r xterm
      | I_Ext of term * int * int
      | I_Comp of term * term

    and term = term_aux alpha_term

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
          match s.bv , t.bv with
          |I_Cte b1,I_Cte b2 when b1=b2 ->beta({s with sz=s.sz+t.sz}::tl')
          |I_Ext(d1,i,j),I_Ext(d2,k,l) when d1=d2 && l=i-1 ->
            let tmp = {sz = s.sz + t.sz ; bv = I_Ext(d1,k,j)}
            in if k=0 then (simple_t tmp)::(beta tl') else beta (tmp::tl')
          |_ -> (simple_t s)::(beta (t::tl'))
        end

    (** **)
    let sigma term = beta (alpha term)

    let bitv_to_icomp =
      List.fold_left (fun ac bt ->{ bv = I_Comp (ac,bt) ; sz = bt.sz + ac.sz })

    let rec nth_bit r i =
      if i >= r.sz then None else
        match r.bv with
        | I_Cte b -> Some b
        | I_Other _ -> None
        | I_Ext (t, ei, ej) ->
          let i' = ei + i in
          if i' > ej then None else nth_bit t i'
        | I_Comp (t2, t1) ->
          if i < t1.sz then nth_bit t1 i else nth_bit t2 (i - t1.sz)

    let string_to_bitv ?(update_ctx = false) ?bounds s t cnt ctx =
      let size = String.length s in
      let mk_eq b pos =
        E.mk_eq ~iff:false
          (E.mk_term (Symbols.Op (Symbols.BVGet pos)) [t] Ty.Tint)
          (if b then E.int "1" else E.int "0")
      in
      let tmp = ref[] in
      let nctx = ref[] in
      if update_ctx && Options.get_use_bv () then
        String.iteri (
          fun i car ->
            let pos = size - i - 1 in
            let b = car<>'0' in
            nctx :=
              begin match bounds with
                | None -> mk_eq b (cnt + pos) :: !nctx
                | Some (lb, ub) ->
                  if pos >= lb && pos <= ub
                  then mk_eq b (cnt + pos - lb) :: !nctx
                  else !nctx
              end;
            tmp := (b,1)::(!tmp)
        ) s
      else String.iter(fun car -> tmp := (car<>'0',1)::(!tmp)) s;
      let rec f_aux l acc = match l with
        | [] -> assert false
        | [(b,n)] -> { sz = n ; bv = I_Cte b }::acc
        | (b1,n)::(b2,m)::r when b1 = b2 -> f_aux ((b1,n+m)::r) acc
        | (b1,n)::(b2,m)::r ->
          (f_aux ((b2,m)::r)) ({ sz = n ; bv = I_Cte b1 }::acc)
      in
      let res = f_aux (!tmp) [] in
      let ctx = List.rev_append !nctx ctx in
      bitv_to_icomp (List.hd res) (List.tl res), ctx

    let bitv_of_nat bv_t nat_t size ctx =
      let two = E.int "2" in
      let pow n =
        E.mk_term (Sy.Op Sy.Pow) [two; E.int (Int.to_string n)] Ty.Tint
      in
      let mdiv n =
        E.mk_term (Sy.Op Sy.Modulo)
          [E.mk_term (Sy.Op Sy.Div) [nat_t; pow n] Ty.Tint; two] Ty.Tint
      in
      let get_eq n e =
        let bvgi =
          E.mk_term (Symbols.Op (Symbols.BVGet n)) [bv_t] Ty.Tint
        in
        E.mk_eq ~iff:false bvgi e
      in
      let get_eq_b n b =
        get_eq n (if b then E.int "1" else E.int "0")
      in
      let rec aux ?prec cnt acc sz ctx =
        if cnt >= size
        then (
          let nacc =
            match prec with
            | Some b ->
              { bv = Cte b; sz } :: acc
            | None -> acc
          in
          nacc, ctx)
        else
          let v_t = mdiv cnt in
          let r, ctx' = X.make v_t in
          let nctx = ctx' @ ctx in
          match X.term_extract r with
          | None, _ ->
            let nctx = get_eq cnt v_t :: nctx in
            begin match prec with
              | Some b ->
                let nacc =
                  {bv = Cte b; sz } ::
                  {bv = Other (Alien r); sz = 1} ::
                  acc
                in
                aux (cnt + 1) nacc 0 nctx
              | None ->
                let nacc = {bv =  Other (Alien r); sz = 1 } :: acc in
                aux (cnt + 1) nacc 0 nctx
            end
          | Some t, _ ->
            match E.term_view t with
            | E.{ f = Sy.Int s; _ } ->
              begin match Hstring.view s with
                | "1" ->
                  let nctx = get_eq_b cnt true :: nctx in
                  begin match prec with
                    | Some true -> aux ?prec (cnt + 1) acc (sz + 1) nctx
                    | Some false ->
                      let nacc = {bv = Cte false; sz } :: acc in
                      aux ~prec:true (cnt + 1) nacc 1 nctx
                    | None -> aux ~prec:true (cnt + 1) acc 1 nctx
                  end
                | "0" ->
                  let nctx = get_eq_b cnt false :: nctx in
                  begin match prec with
                    | Some true ->
                      let nacc = {bv = Cte true; sz } :: acc in
                      aux ~prec:false (cnt + 1) nacc 1 nctx
                    | Some false -> aux ?prec (cnt + 1) acc (sz + 1) nctx
                    | None -> aux ~prec:false (cnt + 1) acc 1 nctx
                  end
                | str ->
                  failwith (
                    Format.sprintf
                      "Expeceted \"1\" or \"0\", but got \"%s\"" str
                  )
              end
            | _ ->
              let nctx = get_eq cnt t :: nctx in
              let nacc = {bv =  Other (Alien r); sz = 1 } :: acc in
              aux (cnt + 1) nacc 0 nctx
      in
      aux 0 [] 0 ctx

    let make t =
      let rec make_rec cnt ?(update_ctx = false) ?bounds t' ctx =
        match E.term_view t' with
        | { E.f = Sy.Bitv s; _ } ->
          string_to_bitv ~update_ctx ?bounds s t cnt ctx

        | { E.f = Sy.Op Sy.Concat ;
            xs = [t2;t1] ; ty = Ty.Tbitv n; _ } ->
          let sz', (bounds2, uc2), (bounds1, uc1) =
            let { E.ty = ty2; _ }, { E.ty = ty1; _ } =
              E.term_view t2, E.term_view t1
            in
            match ty2, ty1 with
            | Ty.Tbitv _, Ty.Tbitv sz ->
              begin match bounds with
                | None ->
                  (if update_ctx then sz else 0),
                  (None, update_ctx),
                  (None, update_ctx)
                | Some (lb, ub) ->
                  if lb >= sz then
                    0,
                    (Some (lb - sz, ub - sz), update_ctx),
                    (None, false)
                  else if ub < sz then
                    (if update_ctx then sz - lb else 0),
                    (None, false),
                    (Some (lb, ub), update_ctx)
                  else
                    (if update_ctx then sz - lb else 0),
                    (Some (0, ub - sz), update_ctx),
                    (Some (lb, sz - 1), update_ctx)
              end
            | _ ->
              failwith (
                Format.asprintf
                  "Concat: expected two bitvectors, got %a and %a"
                  Ty.print ty1 Ty.print ty2)
          in
          let uc1, uc2 = uc1 && update_ctx, uc2 && update_ctx in
          let r1, ctx =
            make_rec cnt ~update_ctx:uc1 ?bounds:bounds1 t1 ctx
          in
          let r2, ctx =
            make_rec (cnt + sz') ~update_ctx:uc2 ?bounds:bounds2 t2 ctx
          in
          { bv = I_Comp (r2, r1) ; sz = n }, ctx

        | { E.f = Sy.Op Sy.Extract (i, j); xs = [t] ; ty = Ty.Tbitv sz; _ } ->
          let bounds =
            match bounds with
            | None -> (i, j)
            | Some (lb, ub) ->
              let nlb = i + lb in
              let nub = i + ub in
              (nlb, nub)
          in
          let r, ctx = make_rec cnt ~update_ctx ~bounds t ctx in
          { sz ; bv = I_Ext (r, i, j)}, ctx

        | { E.ty = Ty.Tbitv n; _ } ->
          let r', ctx' = X.make t' in
          let ctx = ctx' @ ctx in
          {bv = I_Other (Alien r') ; sz = n}, ctx

        | _ -> assert false
      in
      let r, ctx =
        match E.term_view t with
        | { E.f = Sy.Op (Sy.BVGet i); xs = [x] ; ty = Ty.Tint; _ } ->
          (* TODO:
             Should it the "x" bitv be memoized? (what about all the others?)
             Can bitv.ml only make the sub-bitv on which the access is done? *)
          let r, ctx = make_rec 0 ~update_ctx:false x [] in
          begin match nth_bit r i with
            | None -> BVAccess ((sigma r), i), ctx
            | Some b ->
              let t' = if b then E.int "1" else E.int "0" in
              let r', ctx' = X.make t' in
              Bit r', ctx' @ ctx
          end

        | { E.f = Sy.Op (Sy.Nat2BV m); xs = [x] ; ty = Ty.Tbitv n; _ } ->
          assert (m = n);
          let bvl, nctx = bitv_of_nat t x n [] in
          BV bvl, List.rev nctx

        | _ ->
          let r, ctx = make_rec ~update_ctx:true 0 t [] in
          BV (sigma r), ctx
      in
      r, ctx
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
        if (s1 = s2 || List.mem (s1,s2) acc || List.mem (s2,s1) acc) then acc
        else (s1,s2)::acc
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
          if id <> id' then ext1_vs_ext2 (id,s,i,j) (id',s',i',j')
          else[ext_vs_ext id s (if i<i' then (i,i') else (i',i)) (j - i + 1)]

      in List.flatten (List.map c_solve sys)


    let partition l =
      let rec add acc (t,cnf) = match acc with
        |[] -> [(t,[cnf])]
        |(t',cnf')::r -> if t = t' then (t',cnf::cnf')::r
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
            |Some B -> let comp' = List.fold_right
                           (fun s_t acc -> if s_t <> st then s_t::acc
                             else st_n::res::acc
                           )comp  []
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
          in if subs =[] then slice_rec ((t,vls')::bw) r
          else
            begin
              let _bw = apply_subs subs bw in
              let _fw = apply_subs subs r in
              if _bw = bw then slice_rec ((t,vls')::bw) _fw
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
        if ok = [] then st::union_sets tl
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
            |Cte bol,Cte bol' when bol = bol' ->
              cnf_max ({ b with sz = a.sz + b.sz }::r)
            | _,Cte _ -> a::(cnf_max (b::r))
            | _ -> a::b::(cnf_max r)
          end
      in List.map
        (fun (t,vls) ->
           t,cnf_max (List.map to_external_ast (List.hd vls))
        )unif_slic


    let solve u v =
      if u = v then raise Valid
      else begin
        let varsU = get_vars u in
        let varsV = get_vars v in
        if varsU = [] && varsV = [] then raise Util.Unsolvable
        else
          begin
            let st_sys = slice u v in
            let sys_sols = sys_solve st_sys in
            let parts = partition sys_sols in
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

  let compare_mine b1 b2 =
    let rec comp l1 l2 = match l1,l2 with
        [] , [] -> 0
      | [] , _ -> -1
      | _ , [] -> 1
      | st1::l1 , st2::l2 ->
        let c = compare_simple_term st1 st2 in
        if c<>0 then c else comp l1 l2
    in comp b1 b2

  let compare x y = compare (embed x) (embed y)

  (* should use hashed compare to be faster, not structural comparison *)
  let equal r1 r2 =
    let rec aux l n i =
      match l with
      | [] -> None
      | {bv = _; sz} as h :: t ->
        if n < i
        then aux t (n+sz) i
        else
        if n = i
        then Some h
        else None
    in
    match r1, r2 with
    | BV bv1, BV bv2 -> compare_mine bv1 bv2 = 0
    | BVAccess (ra1, i1), BVAccess (ra2, i2) ->
      begin match aux ra1 0 i1, aux ra2 0 i2 with
        | Some f1, Some f2 ->
          if f1.sz = 1 && f2.sz = 1 then
            compare_simple_term f1 f2 = 0
          else
            compare_simple_term f1 f2 = 0 && i1 = i2 (* ? *)
        | _ -> false
      end
    | Bit r1, Bit r2 -> X.equal r1 r2
    | _ -> false

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

  let hash r =
    let hash_l l =
      List.fold_left
        (fun acc {bv=r; sz=sz} -> acc + 19 * (sz + hash_simple_term_aux r)) 19 l
    in
    match r with
    | BV l -> hash_l l
    | BVAccess (l, _i) -> hash_l l (* TODO: fix *)
    | Bit r -> X.hash r

  let leaves bitv =
    match bitv with
    | BV bv
    | BVAccess (bv, _) ->
      List.fold_left
        (fun acc x ->
           match x.bv with
           | Cte _  -> acc
           | Ext( Var v,sz,_,_) ->
             (X.embed (BV [{bv=Other (Var v) ; sz = sz }]))::acc
           | Other (Var _)  -> (X.embed (BV [x]))::acc
           | Other (Alien t) | Ext(Alien t,_,_,_) -> (X.leaves t)@acc
        ) [] bv
    | Bit r -> X.leaves r

  let is_mine r =
    match r with
    | BV [{ bv = Other (Alien r); _ }] -> r
    | Bit r -> r
    | _ -> X.embed r

  let print fmt r =
    match r with
    | BV bv -> Debug.print_C_ast fmt bv
    | BVAccess (r, i) ->
      Format.fprintf fmt "(%a)^{%d}" Debug.print_C_ast r i
    | Bit r -> X.print fmt r

  let make t =
    let r, ctx = Canonizer.make t in
    is_mine r, ctx

  let color _ = assert false

  let type_info bv =
    match bv with
    | BV bv ->
      let sz = List.fold_left (fun acc bv -> bv.sz + acc) 0 bv in
      Ty.Tbitv sz
    | BVAccess _ | Bit _ -> Ty.Tint

  let to_i_ast biv =
    let f_aux st =
      {sz = st.sz;
       bv = match st.bv with
         | Cte b -> Canonizer.I_Cte b
         | Other tt -> Canonizer.I_Other tt
         | Ext(tt,siz,i,j)  ->
           let tt' = { sz = siz ; bv = Canonizer.I_Other tt }
           in Canonizer.I_Ext(tt',i,j)
      } in
    List.fold_left
      (fun acc st ->
         let tmp = f_aux st
         in { bv = Canonizer.I_Comp(acc,tmp) ; sz = acc.sz + tmp.sz }
      ) (f_aux (List.hd biv)) (List.tl biv)

  let extract r ty =
    match X.extract r with
      Some (BV (_::_ as bv)) -> to_i_ast bv
    | None -> {bv =  Canonizer.I_Other (Alien r); sz = ty}
    | Some _ -> assert false

  let extract_xterm r =
    match X.extract r with
      Some (BV [{ bv = Other (Var _ as x); _ }]) -> x
    | None -> Alien r
    | _ -> assert false

  let var_or_term x =
    match x.bv with
      Other (Var _) -> X.embed (BV [x])
    | Other (Alien r) -> r
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
    | Some (BV u) , Some (BV t) ->
      begin
        try
          let l = Solver.solve u t in
          List.map
            (fun (p,v) -> var_or_term p,is_mine (BV v))
            l
        with Solver.Valid -> []
      end
    | _ -> assert false


  let rec subst_rec x subs biv =
    match biv.bv , extract_xterm x with
    | Canonizer.I_Cte _ , _ -> biv
    | Canonizer.I_Other (Var y) , Var z when y=z -> extract subs biv.sz
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
    match biv with
    | BV bv ->
      if bv = []
      then is_mine (BV bv)
      else
        let r = Canonizer.sigma (subst_rec x subs (to_i_ast bv)) in
        is_mine (BV r)
    | BVAccess (bv, i) ->
      if bv = []
      then is_mine (BVAccess (bv, i)) (* ? *)
      else
        let r = Canonizer.sigma (subst_rec x subs (to_i_ast bv)) in
        is_mine (BVAccess (r, i))
    | Bit r -> is_mine (Bit (X.subst x subs r))
(*
  module M =  Map.Make
    (struct
      type t = X.r
      let compare = X.compare
     end)


  module Map = Map.Make
    (struct
      type t = (X.r simple_term) list
      let compare = compare_mine
     end)

  module Set = Set.Make (
    struct
      type t = (X.r simple_term) list
      let compare = compare_mine
    end)
*)
  let fully_interpreted _ = true

  let term_extract r =
    let res =
      match X.extract r with
      | None -> X.term_extract r
      | Some v ->
        begin match v with
          | BV l ->
            begin try
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
                          E.mk_term
                            (Sy.Op Sy.Concat) [acc; mk_bv b sz] (Ty.Tbitv nsz)
                        | _ -> raise Exit
                    ) (sz ,mk_bv b sz) tl
                  in
                  Some t, false
                | _ ->
                  None, false
              with Exit ->
                None, false
            end
          | BVAccess (l, i) ->
            begin match X.term_extract (is_mine (BV l)) with
              | None, _ -> None, false
              | Some t, _ ->
                let E.{ ty; _ } = E.term_view t in
                let rt = E.mk_term (Symbols.Op (Symbols.BVGet i)) [t] ty in
                Some (rt), false
            end
          | Bit r -> X.term_extract r
        end
    in
    res

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

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
module A = Xliteral

module Sy = Symbols
module E = Expr

module Z = Numbers.Z
module Q = Numbers.Q

let is_mult h = Sy.equal (Sy.Op Sy.Mult) h
let mod_symb = Sy.name "@mod"

let calc_power (c : Q.t) (d : Q.t) (ty : Ty.t) =
  (* d must be integral and if we work on integer exponentation,
     d must be positive*)
  if not (Q.is_int d) then raise Exit;
  if Ty.Tint == ty && Q.sign d < 0 then raise Exit;
  let n = match Z.to_machine_int (Q.to_z d) with
    | Some n -> n
    | None -> raise Exit
  in
  (* This lines prevent overflow from computation *)
  let sz = Z.numbits (Q.num c) + Z.numbits (Q.den c) in
  if sz <> 0 && Stdlib.abs n > 100_000 / sz then raise Exit;
  let res = Q.power c n in
  assert (ty != Ty.Tint || Q.is_int c);
  res

let calc_power_opt (c : Q.t) (d : Q.t) (ty : Ty.t) =
  try Some (calc_power c d ty)
  with Exit -> None

module Type (X:Sig.X) : Polynome.T with type r = X.r = struct
  include
    Polynome.Make(struct
      include X
      module Ac = Ac.Make(X)
      let mult v1 v2 =
        X.ac_embed
          {
            distribute = true;
            h = Sy.Op Sy.Mult;
            t = X.type_info v1;
            l = let l2 = match X.ac_extract v1 with
                | Some { h; l; _ } when Sy.equal h (Sy.Op Sy.Mult) -> l
                | _ -> [v1, 1]
              in Ac.add (Sy.Op Sy.Mult) (v2,1) l2
          }
    end)
end

module Shostak
    (X : Sig.X)
    (P : Polynome.EXTENDED_Polynome with type r = X.r) = struct

  type t = P.t

  type r = P.r

  let name = "arith"

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let solve_aux r1 r2 =
      if get_debug_arith () then
        Printer.print_dbg
          ~module_name:"Arith" ~function_name:"solve_aux"
          "we solve %a=%a" X.print r1 X.print r2

    let solve_one r1 r2 sbs =
      let c = ref 0 in
      let print fmt (p,v) =
        incr c;
        fprintf fmt  "%d) %a |-> %a@." !c X.print p X.print v
      in
      if get_debug_arith () then
        Printer.print_dbg
          ~module_name:"Arith" ~function_name:"solve_one"
          "solving %a = %a yields:@,%a"
          X.print r1 X.print r2
          (Printer.pp_list_no_space print) sbs
  end
  (*BISECT-IGNORE-END*)

  let is_mine_symb sy _ty =
    let open Sy in
    match sy with
    | Int _ | Real _ -> true
    | Op (Plus | Minus | Mult | Div | Modulo
         | Float | Fixed | Abs_int | Abs_real | Sqrt_real
         | Sqrt_real_default | Sqrt_real_excess
         | Real_of_int | Int_floor | Int_ceil
         | Max_int | Max_real | Min_int | Min_real
         | Pow | Integer_log2
         | Integer_round) -> true
    | _ -> false

  let empty_polynome ty = P.create [] Q.zero ty

  let is_mine p = match P.is_monomial p with
    | Some (a,x,b) when Q.equal a Q.one && Q.sign b = 0 -> x
    | _ -> P.embed p

  let embed r = match P.extract r with
    | Some p -> p
    | _ -> P.create [Q.one, r] Q.zero (X.type_info r)

  (* t1 % t2 = md  <->
     c1. 0 <= md ;
     c2. md < t2 ;
     c3. exists k. t1 = t2 * k + t ;
     c4. t2 <> 0 (already checked) *)
  let mk_modulo md t1 t2 p2 ctx =
    let zero = E.int "0" in
    let c1 = E.mk_builtin ~is_pos:true A.LE [zero; md] in
    let c2 =
      match P.is_const p2 with
      | Some n2 ->
        let an2 = Q.abs n2 in
        assert (Q.is_int an2);
        let t2 = E.int (Q.to_string an2) in
        E.mk_builtin ~is_pos:true A.LT [md; t2]
      | None ->
        E.mk_builtin ~is_pos:true A.LT [md; t2]
    in
    let k  = E.fresh_name Ty.Tint in
    let t3 = E.mk_term (Sy.Op Sy.Mult) [t2;k] Ty.Tint in
    let t3 = E.mk_term (Sy.Op Sy.Plus) [t3;md] Ty.Tint in
    let c3 = E.mk_eq ~iff:false t1 t3 in
    c3 :: c2 :: c1 :: ctx

  let mk_euc_division p p2 t1 t2 ctx =
    match P.to_list p2 with
    | [], coef_p2 ->
      let md = E.mk_term (Sy.Op Sy.Modulo) [t1;t2] Ty.Tint in
      let r, ctx' = X.make md in
      let rp =
        P.mult_const (Q.div Q.one coef_p2) (embed r) in
      P.sub p rp, ctx' @ ctx
    | _ -> assert false


  let exact_sqrt_or_Exit q =
    (* this function is probably not accurate because it
       works on Z.t to compute eventual exact sqrt *)
    let c = Q.sign q in
    if c < 0 then raise Exit;
    let n = Q.num q in
    let d = Q.den q in
    let s_n, _ = Z.sqrt_rem n in
    assert (Z.sign s_n >= 0);
    if not (Z.equal (Z.mult s_n s_n) n) then raise Exit;
    let s_d, _ = Z.sqrt_rem d in
    assert (Z.sign s_d >= 0);
    if not (Z.equal (Z.mult s_d s_d) d) then raise Exit;
    let res = Q.from_zz s_n s_d in
    assert (Q.equal (Q.mult res res) q);
    res

  let default_sqrt_or_Exit q =
    let c = Q.sign q in
    if c < 0 then raise Exit;
    match Q.sqrt_default q with
    | None -> raise Exit
    | Some res -> assert (Q.compare (Q.mult res res) q <= 0); res

  let excess_sqrt_or_Exit q =
    let c = Q.sign q in
    if c < 0 then raise Exit;
    match Q.sqrt_excess q with
    | None -> raise Exit
    | Some res -> assert (Q.compare (Q.mult res res) q >= 0); res

  let mk_partial_interpretation_1 aux_func coef p_acc ty t x =
    let r_x, _ = X.make x in
    try
      match P.to_list (embed r_x) with
      | [], d ->
        let d = aux_func d in (* may raise Exit *)
        P.add_const (Q.mult coef d) p_acc
      | _ -> raise Exit
    with Exit ->
      let a = X.term_embed t in
      P.add (P.create [coef, a] Q.zero ty) p_acc

  let mk_partial_interpretation_2 aux_func coef p_acc ty t x y =
    let px = embed (fst (X.make x)) in
    let py = embed (fst (X.make y)) in
    try
      match P.is_const px, P.is_const py with
      | Some c_x, Some c_y ->
        P.add_const (Q.mult coef (aux_func c_x c_y)) p_acc
      | _ ->
        P.add (P.create [coef, (X.term_embed t)] Q.zero ty) p_acc
    with Exit ->
      P.add (P.create [coef, (X.term_embed t)] Q.zero ty) p_acc

  let rec mke coef p t ctx =
    let { E.f = sb ; xs; ty; _ } =
      match E.term_view t with
      | E.Not_a_term _ -> assert false
      | E.Term tt -> tt
    in
    match sb, xs with
    | (Sy.Int n | Sy.Real n) , _  ->
      let c = Q.mult coef (Q.from_string (Hstring.view n)) in
      P.add_const c p, ctx

    | Sy.Op Sy.Mult, [t1;t2] ->
      let p1, ctx = mke coef (empty_polynome ty) t1 ctx in
      let p2, ctx = mke Q.one (empty_polynome ty) t2 ctx in
      if get_no_nla() && P.is_const p1 == None && P.is_const p2 == None
      then
        (* becomes uninterpreted *)
        let tau = E.mk_term (Sy.name ~kind:Sy.Ac "@*") [t1; t2] ty in
        let xtau, ctx' = X.make tau in
        P.add p (P.create [coef, xtau] Q.zero ty), List.rev_append ctx' ctx
      else
        P.add p (P.mult p1 p2), ctx

    | Sy.Op Sy.Div, [t1;t2] ->
      let p1, ctx = mke Q.one (empty_polynome ty) t1 ctx in
      let p2, ctx = mke Q.one (empty_polynome ty) t2 ctx in
      if get_no_nla() &&
         (P.is_const p2 == None ||
          (ty == Ty.Tint && P.is_const p1 == None)) then
        (* becomes uninterpreted *)
        let tau = E.mk_term (Sy.name "@/") [t1; t2] ty in
        let xtau, ctx' = X.make tau in
        P.add p (P.create [coef, xtau] Q.zero ty), List.rev_append ctx' ctx
      else
        let p3, ctx =
          try
            let p, approx = P.div p1 p2 in
            if approx then mk_euc_division p p2 t1 t2 ctx
            else p, ctx
          with Division_by_zero | Polynome.Maybe_zero ->
            P.create [Q.one, X.term_embed t] Q.zero ty, ctx
        in
        P.add p (P.mult_const coef p3), ctx

    | Sy.Op Sy.Plus , l ->
      List.fold_left (fun (p, ctx) u -> mke coef p u ctx )(p, ctx) l

    | Sy.Op Sy.Minus , [t1;t2] ->
      let p2, ctx = mke (Q.minus coef) p t2 ctx in
      mke coef p2 t1 ctx

    | Sy.Op Sy.Modulo , [t1;t2] ->
      let p1, ctx = mke Q.one (empty_polynome ty) t1 ctx in
      let p2, ctx = mke Q.one (empty_polynome ty) t2 ctx in
      if get_no_nla() &&
         (P.is_const p1 == None || P.is_const p2 == None)
      then
        (* becomes uninterpreted *)
        let tau = E.mk_term (Sy.name "@%") [t1; t2] ty in
        let xtau, ctx' = X.make tau in
        P.add p (P.create [coef, xtau] Q.zero ty), List.rev_append ctx' ctx
      else
        let p3, ctx =
          try P.modulo p1 p2, ctx
          with e ->
            let t = E.mk_term mod_symb [t1; t2] Ty.Tint in
            let ctx = match e with
              | Division_by_zero | Polynome.Maybe_zero -> ctx
              | Polynome.Not_a_num -> mk_modulo t t1 t2 p2 ctx
              | _ -> assert false
            in
            P.create [Q.one, X.term_embed t] Q.zero ty, ctx
        in
        P.add p (P.mult_const coef p3), ctx

    (*** <begin>: partial handling of some arith/FPA operators **)
    | Sy.Op Sy.Float, [prec; exp; mode; x] ->
      let aux_func e =
        let res, _, _ = Fpa_rounding.float_of_rational prec exp mode e in
        res
      in
      mk_partial_interpretation_1 aux_func coef p ty t x, ctx

    | Sy.Op Sy.Integer_round, [mode; x] ->
      let aux_func = Fpa_rounding.round_to_integer mode in
      mk_partial_interpretation_1 aux_func coef p ty t x, ctx

    | Sy.Op (Sy.Abs_int | Sy.Abs_real) , [x] ->
      mk_partial_interpretation_1 Q.abs coef p ty t x, ctx

    | Sy.Op Sy.Sqrt_real, [x] ->
      mk_partial_interpretation_1 exact_sqrt_or_Exit coef p ty t x, ctx

    | Sy.Op Sy.Sqrt_real_default, [x] ->
      mk_partial_interpretation_1 default_sqrt_or_Exit coef p ty t x, ctx

    | Sy.Op Sy.Sqrt_real_excess, [x] ->
      mk_partial_interpretation_1 excess_sqrt_or_Exit coef p ty t x, ctx

    | Sy.Op Sy.Real_of_int, [x] ->
      mk_partial_interpretation_1 (fun d -> d) coef p ty t x, ctx

    | Sy.Op Sy.Int_floor, [x] ->
      mk_partial_interpretation_1 Q.floor coef p ty t x, ctx

    | Sy.Op Sy.Int_ceil, [x] ->
      mk_partial_interpretation_1 Q.ceiling coef p ty t x, ctx

    | Sy.Op (Sy.Max_int | Sy.Max_real), [x;y] ->
      let aux_func c d = if Q.compare c d >= 0 then c else d in
      mk_partial_interpretation_2 aux_func coef p ty t x y, ctx

    | Sy.Op (Sy.Min_int | Sy.Min_real), [x;y] ->
      let aux_func c d = if Q.compare c d <= 0 then c else d in
      mk_partial_interpretation_2 aux_func coef p ty t x y, ctx

    | Sy.Op Sy.Integer_log2, [x] ->
      let aux_func q =
        if Q.compare_to_0 q <= 0 then raise Exit;
        Q.from_int (Fpa_rounding.integer_log_2 q)
      in
      mk_partial_interpretation_1 aux_func coef p ty t x, ctx

    | Sy.Op Sy.Pow, [x; y] ->
      mk_partial_interpretation_2
        (fun x y -> calc_power x y ty) coef p ty t x y, ctx

    | Sy.Op Sy.Fixed, _ ->
      (* Fixed-Point arithmetic currently not implemented *)
      assert false

    (*** <end>: partial handling of some arith/FPA operators **)

    | _ ->
      let a, ctx' = X.make t in
      let ctx = ctx' @ ctx in
      match P.extract a with
      | Some p' -> P.add p (P.mult_const coef p'), ctx
      | _ -> P.add p (P.create [coef, a] Q.zero ty), ctx

  let make t =
    tool_req 4 "TR-Arith-Make";
    let ty = E.type_info t in
    let p, ctx = mke Q.one (empty_polynome ty) t [] in
    is_mine p, ctx

  let rec expand p n acc =
    assert (n >=0);
    if n = 0 then acc else expand p (n-1) (p::acc)

  let unsafe_ac_to_arith { l = rl; t = ty; _ } =
    let mlt = List.fold_left (fun l (r,n) -> expand (embed r)n l) [] rl in
    List.fold_left P.mult (P.create [] Q.one ty) mlt


  let rec number_of_vars l =
    List.fold_left (fun acc (r, n) -> acc + n * nb_vars_in_alien r) 0 l

  and nb_vars_in_alien r =
    match P.extract r with
    | Some p ->
      let l, _ = P.to_list p in
      List.fold_left (fun acc (_, x) -> max acc (nb_vars_in_alien x)) 0 l
    | None ->
      begin
        match X.ac_extract r with
        | Some ac when is_mult ac.h ->
          number_of_vars ac.l
        | _ -> 1
      end

  let max_list_ = function
    | [] -> 0
    | [ _, x ] -> nb_vars_in_alien x
    | (_, x) :: l ->
      let acc = nb_vars_in_alien x in
      List.fold_left (fun acc (_, x) -> max acc (nb_vars_in_alien x)) acc l

  let contains_a_fresh_alien xp =
    List.exists
      (fun x ->
         match X.term_extract x with
         | Some t, _ -> E.is_fresh t
         | _ -> false
      ) (X.leaves xp)

  let has_ac p kind =
    List.exists
      (fun (_, x) ->
         match X.ac_extract x with Some ac -> kind ac | _ -> false)
      (fst (P.to_list p))

  let color ac =
    match ac.l with
    | [(_, 1)] -> assert false
    | _ ->
      let p = unsafe_ac_to_arith ac in
      if not ac.distribute then
        if has_ac p (fun ac -> is_mult ac.h) then X.ac_embed ac
        else is_mine p
      else
        let xp = is_mine p in
        if contains_a_fresh_alien xp then
          let l, _ = P.to_list p in
          let mx = max_list_ l in
          if mx = 0 || mx = 1 || number_of_vars ac.l > mx then is_mine p
          else X.ac_embed ac
        else xp

  let type_info p = P.type_info p

  module SX = Set.Make(struct type t = r let compare = X.hash_cmp end)

  let leaves p = P.leaves p

  let subst x t p =
    let p = P.subst x (embed t) p in
    let ty = P.type_info p in
    let l, c = P.to_list p in
    let p  =
      List.fold_left
        (fun p (ai, xi) ->
           let xi' = X.subst x t xi in
           let p' = match P.extract xi' with
             | Some p' -> P.mult_const ai p'
             | _ -> P.create [ai, xi'] Q.zero ty
           in
           P.add p p')
        (P.create [] c ty) l
    in
    is_mine p


  let compare x y = P.compare (embed x) (embed y)

  let equal p1 p2 = P.equal p1 p2

  let hash = P.hash

  (* symmetric modulo p 131 *)
  let mod_sym a b =
    let m = Q.modulo a b in
    let m =
      if Q.sign m < 0 then
        if Q.compare m (Q.minus b) >= 0 then Q.add m b else assert false
      else
      if Q.compare m b <= 0 then m else assert false

    in
    if Q.compare m (Q.div b (Q.from_int 2)) < 0 then m else Q.sub m b

  let map_monomes f l ax =
    List.fold_left
      (fun acc (a,x) ->
         let a = f a in if Q.sign a = 0 then acc else (a, x) :: acc)
      [ax] l

  let apply_subst sb v =
    is_mine (List.fold_left (fun v (x, p) -> embed (subst x p v)) v sb)

  (* substituer toutes variables plus grandes que x *)
  let subst_bigger x l =
    List.fold_left
      (fun (l, sb) (b, y) ->
         if X.ac_extract y != None && X.str_cmp y x > 0 then
           let k = X.term_embed (E.fresh_name Ty.Tint) in
           (b, k) :: l, (y, embed k)::sb
         else (b, y) :: l, sb)
      ([], []) l

  let is_mine_p = List.map (fun (x,p) -> x, is_mine p)

  let extract_min = function
    | [] -> assert false
    | [c] -> c, []
    | (a, x) :: s ->
      List.fold_left
        (fun ((a, x), l) (b, y) ->
           if Q.compare (Q.abs a) (Q.abs b) <= 0 then
             (a, x), ((b, y) :: l)
           else (b, y), ((a, x):: l)) ((a, x),[]) s


  (* Decision Procedures. Page 131 *)
  let rec omega l b =

    (* 1. choix d'une variable donc le |coef| est minimal *)
    let (a, x), l = extract_min l in

    (* 2. substituer les aliens plus grand que x pour
       assurer l'invariant sur l'ordre AC *)
    let l, sbs = subst_bigger x l in
    let p = P.create l b Ty.Tint in
    assert (Q.sign a <> 0);
    if Q.equal a Q.one then
      (* 3.1. si a = 1 alors on a une substitution entiere pour x *)
      let p = P.mult_const Q.m_one p in
      (x, is_mine p) :: (is_mine_p sbs)
    else if Q.equal a Q.m_one then
      (* 3.2. si a = -1 alors on a une subst entiere pour x*)
      (x,is_mine p) :: (is_mine_p sbs)
    else
      (* 4. sinon, (|a| <> 1) et a <> 0 *)
      (* 4.1. on rend le coef a positif s'il ne l'est pas deja *)
      let a, l, b =
        if Q.sign a < 0  then
          (Q.minus a,
           List.map (fun (a,x) -> Q.minus a,x) l, (Q.minus b))
        else (a, l, b)
      in
      (* 4.2. on reduit le systeme *)
      omega_sigma sbs a x l b

  and omega_sigma sbs a x l b =

    (* 1. on definie m qui vaut a + 1 *)
    let m = Q.add a Q.one in

    (* 2. on introduit une variable fraiche *)
    let sigma = X.term_embed (E.fresh_name Ty.Tint) in

    (* 3. l'application de la formule (5.63) nous donne la valeur du pivot x*)
    let mm_sigma = (Q.minus m, sigma) in
    let l_mod = map_monomes (fun a -> mod_sym a m) l mm_sigma in

    (* 3.1. Attention au signe de b :
       on le passe a droite avant de faire mod_sym, d'ou Q.minus *)
    let b_mod = Q.minus (mod_sym (Q.minus b) m) in
    let p = P.create l_mod b_mod Ty.Tint in

    let sbs = (x, p) :: sbs in

    (* 4. on substitue x par sa valeur dans l'equation de depart.
       Voir la formule (5.64) *)
    let p' = P.add (P.mult_const a p) (P.create l b Ty.Tint) in

    (* 5. on resoud sur l'equation simplifiee *)
    let sbs2 = solve_int p' in

    (* 6. on normalise sbs par sbs2 *)
    let sbs =  List.map (fun (x, v) -> x, apply_subst sbs2 v) sbs in

    (* 7. on supprime les liaisons inutiles de sbs2 et on merge avec sbs *)
    let sbs2 = List.filter (fun (y, _) -> not (X.equal y sigma)) sbs2 in
    List.rev_append sbs sbs2

  and solve_int p =
    Steps.incr (Steps.Omega);
    if P.is_empty p then raise Not_found;
    let pgcd = P.pgcd_numerators p in
    let ppmc = P.ppmc_denominators p in
    let p = P.mult_const (Q.div ppmc pgcd) p in
    let l, b = P.to_list p in
    if not (Q.is_int b) then raise Util.Unsolvable;
    omega l b

  let is_null p =
    if Q.sign (snd (P.separate_constant p)) <> 0 then
      raise Util.Unsolvable;
    []

  let solve_int p =
    try solve_int p with Not_found -> is_null p

  let solve_real p =
    Steps.incr (Steps.Omega);
    try
      let a, x = P.choose p in
      let p = P.mult_const (Q.div Q.m_one a) (P.remove x p) in
      [x, is_mine p]
    with Not_found -> is_null p


  let unsafe_ac_to_arith { l = rl; t = ty; _ } =
    let mlt = List.fold_left (fun l (r, n) -> expand (embed r) n l) [] rl in
    List.fold_left P.mult (P.create [] Q.one ty) mlt

  let polynome_distribution p unsafe_mode =
    let l, c = P.to_list p in
    let ty = P.type_info p in
    let pp =
      List.fold_left
        (fun p (coef, x) ->
           match X.ac_extract x with
           | Some ac when is_mult ac.h ->
             P.add p (P.mult_const coef (unsafe_ac_to_arith ac))
           | _ ->
             P.add p (P.create [coef,x] Q.zero ty)
        ) (P.create [] c ty) l
    in
    if not unsafe_mode && has_ac pp (fun ac -> is_mult ac.h) then p
    else pp

  let solve_aux r1 r2 unsafe_mode =
    tool_req 4 "TR-Arith-Solve";
    Debug.solve_aux r1 r2;
    let p = P.sub (embed r1) (embed r2) in
    let pp = polynome_distribution p unsafe_mode in
    let ty = P.type_info p in
    let sbs = if ty == Ty.Treal then solve_real pp else solve_int pp in
    let sbs = List.fast_sort (fun (a,_) (x,_) -> X.str_cmp x a)sbs in
    sbs

  let apply_subst r l = List.fold_left (fun r (p,v) -> X.subst p v r) r l

  exception Unsafe

  let check_pivot_safety p nsbs unsafe_mode =
    let q = apply_subst p nsbs in
    if X.equal p q then p
    else
      match X.ac_extract p with
      | Some _ when unsafe_mode -> raise Unsafe
      | Some ac -> X.ac_embed {ac with distribute = false}
      | None -> assert false (* p is a leaf and not interpreted *)

  let triangular_down sbs unsafe_mode =
    List.fold_right
      (fun (p,v) nsbs ->
         (check_pivot_safety p nsbs unsafe_mode, apply_subst v nsbs) :: nsbs)
      sbs []

  let is_non_lin pv = match X.ac_extract pv with
    | Some { Sig.h; _ } -> is_mult h
    | _ -> false

  let make_idemp _ _ sbs lvs unsafe_mode =
    let sbs = triangular_down sbs unsafe_mode in
    let sbs = triangular_down (List.rev sbs) unsafe_mode in (*triangular up*)
    let sbs = List.filter (fun (p,_) -> SX.mem p lvs || is_non_lin p) sbs in
      (*
        This assert is not TRUE because of AC and distributivity of '*'
        assert (not (get_enable_assertions ()) ||
        X.equal (apply_subst a sbs) (apply_subst b sbs));
      *)
    List.iter
      (fun (p, _) ->
         if not (SX.mem p lvs) then (assert (is_non_lin p); raise Unsafe)
      )sbs;
    sbs

  let solve_one pb r1 r2 lvs unsafe_mode =
    let sbt = solve_aux r1 r2 unsafe_mode in
    let sbt = make_idemp r1 r2 sbt lvs unsafe_mode in (*may raise Unsafe*)
    Debug.solve_one r1 r2 sbt;
    {pb with sbt = List.rev_append sbt pb.sbt}

  let solve r1 r2 pb =
    let lvs = List.fold_right SX.add (X.leaves r1) SX.empty in
    let lvs = List.fold_right SX.add (X.leaves r2) lvs in
    try
      if get_debug_arith () then
        Printer.print_dbg
          ~module_name:"Arith" ~function_name:"solve"
          "Try solving with unsafe mode.";
      solve_one pb r1 r2 lvs true (* true == unsafe mode *)
    with Unsafe ->
    try
      if get_debug_arith () then
        Printer.print_dbg
          ~module_name:"Arith" ~function_name:"solve"
          "Cancel unsafe solving mode. Try safe mode";
      solve_one pb r1 r2 lvs false (* false == safe mode *)
    with Unsafe ->
      assert false

  let make t =
    if get_timers() then
      try
        Timers.exec_timer_start Timers.M_Arith Timers.F_make;
        let res = make t in
        Timers.exec_timer_pause Timers.M_Arith Timers.F_make;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Arith Timers.F_make;
        raise e
    else make t

  let solve r1 r2 pb =
    if get_timers() then
      try
        Timers.exec_timer_start Timers.M_Arith Timers.F_solve;
        let res = solve r1 r2 pb in
        Timers.exec_timer_pause Timers.M_Arith Timers.F_solve;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Arith Timers.F_solve;
        raise e
    else solve r1 r2 pb

  let print = P.print

  let fully_interpreted sb =
    match sb with
    | Sy.Op (Sy.Plus | Sy.Minus) -> true
    | _ -> false

  let term_extract _ = None, false

  let abstract_selectors p acc =
    let p, acc = P.abstract_selectors p acc in
    is_mine p, acc


  (* this function is only called when some arithmetic values do not yet
     appear in IntervalCalculus. Otherwise, the simplex with try to
     assign a value
  *)
  let assign_value =
    let cpt_int = ref Q.m_one in
    let cpt_real = ref Q.m_one in
    let max_constant distincts acc =
      List.fold_left
        (fun acc x ->
           match P.is_const (embed x) with None -> acc | Some c -> Q.max c acc)
        acc distincts
    in
    fun r distincts eq ->
      if P.is_const (embed r) != None then None
      else
      if List.exists
          (fun (t,x) ->
             let symb, ty = match E.term_view t with
               | E.Not_a_term _ -> assert false
               | E.Term tt -> tt.E.f, tt.E.ty
             in
             is_mine_symb symb ty && X.leaves x == []
          ) eq
      then None
      else
        let term_of_cst, cpt = match X.type_info r with
          | Ty.Tint  -> E.int, cpt_int
          | Ty.Treal -> E.real, cpt_real
          | _ -> assert false
        in
        cpt := Q.add Q.one (max_constant distincts !cpt);
        Some (term_of_cst (Q.to_string !cpt), true)



  let pprint_const_for_model =
    let pprint_positive_const c =
      let num = Q.num c in
      let den = Q.den c in
      if Z.is_one den then Z.to_string num
      else Format.sprintf "(/ %s %s)" (Z.to_string num) (Z.to_string den)
    in
    fun r ->
      match P.is_const (embed r) with
      | None -> assert false
      | Some c ->
        let sg = Q.sign c in
        if sg = 0 then "0"
        else if sg > 0 then pprint_positive_const c
        else Format.sprintf "(- %s)" (pprint_positive_const (Q.abs c))

  let choose_adequate_model t r l =
    if get_debug_interpretation () then
      Printer.print_dbg
        ~module_name:"Arith" ~function_name:"choose_adequate_model"
        "choose_adequate_model for %a" E.print t;
    let l = List.filter (fun (_, r) -> P.is_const (embed r) != None) l in
    let r =
      match l with
      | [] ->
        (* We do this, because terms of some semantic values created
           by CS are not created and added to UF *)
        assert (P.is_const (embed r) != None);
        r

      | (_,r)::l ->
        List.iter (fun (_,x) -> assert (X.equal x r)) l;
        r
    in
    r, pprint_const_for_model r

end

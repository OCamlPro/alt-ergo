(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
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
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

open Format
open Options
open Sig
open Matching_types

module Z = Numbers.Z
module Q = Numbers.Q

module L = Xliteral

module Sy = Symbols
module I = Intervals.Legacy

open Inequalities

module X = Shostak.Combine

module P = Shostak.Polynome

module MP0 = Map.Make(P)
module SP = Set.Make(P)
module SX = Shostak.SXH
module MX0 = Shostak.MXH
module MPL = Expr.Map

let src = Logs.Src.create ~doc:"IntervalCalculus" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

let oracle =
  lazy (
    let module OracleContainer = (val Inequalities.get_current ()) in
    let module Oracle = OracleContainer.Make(P) in
    (module Oracle : Inequalities.S with type p = P.t))

let get_oracle () = Lazy.force oracle

module SE = Expr.Set
module ME = Expr.Map
module Ex = Explanation
module E = Expr
module EM = Matching.Make
    (struct
      include Uf
      (* unused -- let add_term2 env t ~add_to_cs:_ = fst (Uf.add env t) *)
      let are_equal env s t ~init_terms:_ =
        Uf.are_equal env s t ~added_terms:false
      (* unused -- let class_of2 = Uf.class_of *)
      let term_repr env t ~init_term:_ = Uf.term_repr env t
    end)

module LR = Uf.LX

let alien_of p = Shostak.Arith.is_mine p

let poly_of r = Shostak.Arith.embed r

(* should be provided by the shostak part or CX directly *)
let is_alien x =
  match P.is_monomial @@ poly_of x with
  | Some(a, _, c) -> Q.equal a Q.one && Q.equal c Q.zero
  | _ -> false


module SimVar = struct
  type t = X.r
  let compare = X.hash_cmp
  let is_int r = X.type_info r == Ty.Tint
  let print fmt x =
    if is_alien x then fprintf fmt "%a" X.print x
    else fprintf fmt "s!%d" (X.hash x) (* slake vars *)
end


module Sim = OcplibSimplex.Basic.Make(SimVar)(Numbers.Q)(Explanation)

let timer = Timers.M_Arith

type t = {
  inequations : P.t Inequalities.t MPL.t;
  monomes: (I.t * SX.t) MX0.t;
  polynomes : I.t MP0.t;
  delayed : Rel_utils.Delayed.t;
  known_eqs : SX.t;
  improved_p : SP.t;
  improved_x : SX.t;
  classes : SE.t list;
  (* State of the union-find represented by all its equivalence classes.
     This state is kept for debugging purposes only. It is updated after
     assuming literals of the theory and returned by queries in case of
     inconsistency. *)

  size_splits : Q.t;
  int_sim : Sim.Core.t;
  rat_sim : Sim.Core.t;
  new_uf : Uf.t;
  th_axioms : (Expr.th_elt * Explanation.t) ME.t;
  linear_dep : SE.t ME.t;
  syntactic_matching :
    (Matching_types.trigger_info * Matching_types.gsubst list) list list;
}

module Sim_Wrap = struct

  let check_unsat_result simplex env =
    match Sim.Result.get None simplex with
    | Sim.Core.Unknown -> assert false
    | Sim.Core.Unbounded _ -> assert false
    | Sim.Core.Max _ -> assert false
    | Sim.Core.Sat _ -> ()
    | Sim.Core.Unsat ex ->
      let ex = Lazy.force ex in
      if get_debug_fm () then
        Printer.print_dbg
          ~module_name:"IntervalCalculus" ~function_name:"check_unsat_result"
          "simplex derived unsat: %a" Explanation.print ex;
      raise (Ex.Inconsistent (ex, env.classes))

  let solve env _i =
    let int_sim = Sim.Solve.solve env.int_sim in
    check_unsat_result int_sim env;
    let rat_sim = Sim.Solve.solve env.rat_sim in
    check_unsat_result rat_sim env;
    {env with int_sim; rat_sim}


  let solve env i =
    Timers.with_timer Timers.M_Simplex Timers.F_solve @@ fun () ->
    solve env i

  let extract_bound i get_lb =
    let func, q =
      if get_lb
      then I.borne_inf, Sim.Core.R2.lower
      else I.borne_sup, Sim.Core.R2.upper
    in
    try
      let bnd, explanation, large = func i in
      let bvalue =
        if large
        then Sim.Core.R2.of_r bnd
        else q bnd
      in
      Some Sim.Core.{bvalue; explanation}
    with I.No_finite_bound -> None

  let same_bnds _old _new =
    match _old, _new with
    | None, None -> true
    | None, Some _ | Some _, None -> false
    | Some Sim.Core.{bvalue = r1; _}, Some Sim.Core.{bvalue = r2; _} ->
      Sim.Core.R2.equal r1 r2

  let add_if_better p _old _new simplex =
    (* p is in normal form pos *)
    let old_mn = extract_bound _old true in
    let old_mx = extract_bound _old false in
    let new_mn = extract_bound _new true in
    let new_mx = extract_bound _new false in
    if same_bnds old_mn new_mn && same_bnds old_mx new_mx then simplex
    else
      let l, z = P.to_list p in
      assert (Q.sign z = 0);
      let simplex, _changed =
        match l with
          [] -> assert false
        | [c, x] ->
          assert (Q.is_one c);
          Sim.(Assert.var
                 simplex x
                 ?min:new_mn
                 ?max:new_mx
              )
        | _ ->
          let l = List.rev_map (fun (c, x) -> x, c) l in
          Sim.(Assert.poly simplex (Core.P.from_list l) (alien_of p)
                 ?min:new_mn
                 ?max:new_mx
              )
      in
      (* we don't solve immediately. It may be expensive *)
      simplex


  let finite_non_point_dom info =
    match info.Sim.Core.mini, info.Sim.Core.maxi with
    | None, _ | _, None -> None
    | Some {bvalue = a; _}, Some {bvalue = x; _} ->
      assert (Sim.Core.R2.is_pure_rational a);
      assert (Sim.Core.R2.is_pure_rational x);
      let c = Sim.Core.R2.compare a x in
      assert (c <= 0); (* because simplex says sat *)
      if c = 0 then None else Some (Q.sub x.v a.v)

  let case_split =
    let gen_cs x n s orig =
      if get_debug_fm () then
        Printer.print_dbg
          ~module_name:"IntervalCalculus" ~function_name:"case_split"
          "[Sim_CS-%d] %a = %a of size %a"
          orig X.print x Q.print n  Q.print s;
      let ty = X.type_info x in
      let r1 = x in
      let r2 = alien_of (P.create [] n  ty) in
      [LR.mkv_eq r1 r2, true, Th_util.CS (Th_util.Th_arith, s)]
    in
    let aux_1 uf x (info,_) acc =
      assert (X.type_info x == Ty.Tint);
      match finite_non_point_dom info with
      | Some s when
          (Sim.Core.equals_optimum info.Sim.Core.value info.Sim.Core.mini ||
           Sim.Core.equals_optimum info.Sim.Core.value info.Sim.Core.maxi)
          && Uf.is_normalized uf x ->
        let v = info.Sim.Core.value in
        assert (Q.is_int v.v);
        begin
          match acc with
          | Some (_,_,s') when Q.compare s' s <= 0 -> acc
          | _ -> Some (x,v, s)
        end
      | _ -> acc
    in
    let aux_2 env uf x (info,_) acc =
      let v = info.Sim.Core.value in
      assert (X.type_info x == Ty.Tint);
      match finite_non_point_dom info with
      | Some s when Q.is_int v.v && Uf.is_normalized uf x ->
        let fnd1, cont1 =
          try true, I.contains (fst (MX0.find x env.monomes)) v.v
          with Not_found -> false, true
        in
        let fnd2, cont2 =
          try true, I.contains (MP0.find (poly_of x) env.polynomes) v.v
          with Not_found -> false, true
        in
        if (fnd1 || fnd2) && cont1 && cont2 then
          match acc with
          | Some (_,_,s') when Q.compare s' s <= 0 -> acc
          | _ -> Some (x,v, s)
        else
          acc
      | _ -> acc
    in
    fun env uf ->
      let int_sim = env.int_sim in
      assert (int_sim.Sim.Core.status == Sim.Core.SAT);
      let acc =
        Sim.Core.MX.fold (aux_1 uf) int_sim.Sim.Core.non_basic None
      in
      let acc =
        Sim.Core.MX.fold (aux_1 uf) int_sim.Sim.Core.basic acc
      in
      match acc with
      | Some (x, n, s) -> gen_cs x n.v s 1
      (*!!!disable case-split that separates and interval into two parts*)
      | None ->
        let acc =
          Sim.Core.MX.fold (aux_2 env uf) int_sim.Sim.Core.non_basic None
        in
        let acc =
          Sim.Core.MX.fold (aux_2 env uf) int_sim.Sim.Core.basic acc
        in
        match acc with
        | Some (x, n, s) -> gen_cs x n.v s 2
        | None -> []


  let infer_best_bounds env p =
    let best_bnd lp ~upper sim i set_new_bound =
      let q = if upper then Q.one else Q.m_one in
      let lp = List.rev_map (fun (c, x) -> x, Q.mult q c) lp in
      let sim, mx_res = Sim.Solve.maximize sim (Sim.Core.P.from_list lp) in
      match Sim.Result.get mx_res sim with
      | Sim.Core.Unknown -> assert false
      | Sim.Core.Sat _   -> assert false (* because we maximized *)
      | Sim.Core.Unsat _ -> assert false (* we know sim is SAT *)
      | Sim.Core.Unbounded _ -> i
      | Sim.Core.Max(mx,_sol) ->
        let {Sim.Core.max_v; is_le} = Lazy.force mx in
        set_new_bound max_v.explanation (Q.mult q max_v.bvalue.v) ~is_le:is_le i
    in
    if get_debug_fpa () >= 2 then
      Printer.print_dbg
        ~module_name:"IntervalCalculus" ~function_name:"infer_best_bounds"
        "#infer bounds for %a" P.print p;
    let ty = P.type_info p in
    let sim = if ty == Ty.Tint then env.int_sim else env.rat_sim in
    let i = I.undefined ty in
    let lp, c = P.to_list p in
    assert (Q.is_zero c);
    assert (sim.Sim.Core.status == Sim.Core.SAT);
    let i = best_bnd lp ~upper:true sim i I.new_borne_sup in
    let i = best_bnd lp ~upper:false sim i I.new_borne_inf in
    if get_debug_fpa () >= 2 then
      Printer.print_dbg
        ~module_name:"IntervalCalculus" ~function_name:"infer_best_bounds"
        "## inferred bounds for %a: %a" P.print p I.print i;
    i

end

module MP = struct
  include MP0

  let assert_normalized_poly p =
    assert
      (let _p0, c0, d0 = P.normal_form_pos p in
       let b = Q.is_zero c0 && Q.is_one d0 in
       Printer.print_err ~error:(not b)
         "[IC.assert_normalized_poly] %a is not normalized"
         P.print p;
       b)

  let n_add p i old ({ polynomes; _ } as env) =
    (*NB: adding a new entry into the map is considered as an improvement*)
    assert_normalized_poly p;
    if I.is_strict_smaller i old || not (MP0.mem p polynomes) then
      let ty = P.type_info p in
      let polynomes = MP0.add p i polynomes in
      let improved_p = SP.add p env.improved_p in
      if ty == Ty.Tint then
        {env with
         polynomes; improved_p;
         int_sim = Sim_Wrap.add_if_better p old i env.int_sim}
      else
        {env with
         polynomes; improved_p;
         rat_sim = Sim_Wrap.add_if_better p old i env.rat_sim}
    else
      let () = assert (I.equal i old) in
      env

  (* find with normalized polys *)
  let n_find p mp =
    assert_normalized_poly p;
    MP0.find p mp

  (* shadow the functions find and add of MP with the ones below
     to force the use of n_find and n_add for normalized polys *)
  [@@@ocaml.warning "-32"]
  let find (_ : unit) (_ : unit) = assert false
  let add (_ : unit) (_ : unit) (_ : unit) = assert false
  [@@@ocaml.warning "+32"]

end

module MX = struct
  include MX0

  let assert_is_alien x =
    assert (
      let b = is_alien x in
      Printer.print_err ~error:(not b)
        "[IC.assert_is_alien] %a is not an alien" X.print x;
      b
    )

  let n_add x ((i,_) as e) old ({ monomes; _ } as env) =
    (*NB: adding a new entry into the map is considered as an improvement*)
    assert_is_alien x;
    if I.is_strict_smaller i old || not (MX0.mem x monomes) then
      let ty = X.type_info x in
      let monomes = MX0.add x e monomes in
      let improved_x = SX.add x env.improved_x in
      if ty == Ty.Tint then
        {env with
         monomes; improved_x;
         int_sim = Sim_Wrap.add_if_better (poly_of x) old i env.int_sim}
      else
        {env with
         monomes; improved_x;
         rat_sim = Sim_Wrap.add_if_better (poly_of x) old i env.rat_sim}
    else
      let () = assert (I.equal i old) in
      (* because use_x may be updated*)
      {env with monomes = MX0.add x e monomes}


  (* find with real aliens *)
  let n_find x mp =
    assert_is_alien x;
    MX0.find x mp


  (* shadow the functions find and add of MX with the ones below
     to force the use of n_find and n_add for true aliens *)
  [@@@ocaml.warning "-32"]
  let find (_ : unit) (_ : unit) = assert false
  let add (_ : unit) (_ : unit) (_ : unit) = assert false
  [@@@ocaml.warning "+32"]
end

(* generic find for values that may be non-alien or non
   normalized polys *)
let generic_find ?(only_inf=false) xp env =
  let is_mon = is_alien xp in
  if get_debug_fm () then
    Printer.print_dbg ~flushed:false
      ~module_name:"IntervalCalculus" ~function_name:"generic_find"
      "Searching %s for: %a ... "
      (if only_inf then "a lower bound" else "an interval") X.print xp;
  try
    if not is_mon then raise Not_found;
    let i, use = MX.n_find xp env.monomes in
    if get_debug_fm () then
      Printer.print_dbg ~header:false "found";
    i, use, is_mon
  with Not_found ->
    (* according to this implem, it means that we can find aliens in polys
       but not in monomes. FIX THIS => an interval of x in monomes and in
       polys may be differents !!! *)
    if get_debug_fm () then
      Printer.print_dbg ~flushed:false ~header:false
        "not_found@ ";
    let p0 = poly_of xp in
    let p, c = P.separate_constant p0 in
    let p, c0, d = P.normal_form_pos p in
    if get_debug_fm () then
      Printer.print_dbg ~flushed:false ~header:false
        "normalized into %a + %a * ( %a )@ "
        Q.print c Q.print d P.print p;
    assert (Q.sign d <> 0 && Q.sign c0 = 0);
    let ty = P.type_info p0 in
    let ip =
      try MP.n_find p env.polynomes with Not_found -> I.undefined ty
    in
    (* In some cases when this function is called, the caller only care about
       the lower bound of the given polynome. However, the affine scaling logic
       we apply later can detect empty intervals, and if it reaches an empty
       interval, the function will raise, in order to let its caller know the
       interval is not consistent/reachable/satisfiable.
       This interacts badly with callers who only care about the lower bound,
       as these callers do not catch the inconsistent exception, and this can
       lead to the solver returning Unsat/Valid even when it is incorrect to
       do so. (see issues #460 #340, and PRs #342 and #465). *)
    let ip =
      if only_inf then
        if Q.sign d >= 0 then
          I.only_borne_inf ip
        else
          I.only_borne_sup ip
      else
        ip
    in
    if get_debug_fm () then
      Printer.print_dbg ~header:false
        "@[<v>found interval: %a for %a,@ scaling interval by * %a, then + %a@]"
        I.print ip P.print p Q.print d Q.print c;
    let new_ip = I.affine_scale ~const:c ~coef:d ip in
    if get_debug_fm () then
      Printer.print_dbg ~header:false
        "scaled %a into %a" I.print ip I.print new_ip;
    new_ip, SX.empty, is_mon


(* generic add for values that may be non-alien or non
   normalized polys *)
let generic_add x j use is_mon env =
  (* NB: adding an entry into the map is considered as an improvement *)
  let ty = X.type_info x in
  if is_mon then
    try MX.n_add x (j,use) (fst (MX.n_find x env.monomes)) env
    with Not_found -> MX.n_add x (j, use) (I.undefined ty) env
  else
    let p0 = poly_of x in
    let p, c = P.separate_constant p0 in
    let p, c0, d = P.normal_form_pos p in
    assert (Q.sign d <> 0 && Q.sign c0 = 0);
    (* x = (p + c0) * d <-> p = x * 1/d - c0 / d *)
    let j = I.affine_scale ~coef:(Q.inv d) ~const:(Q.div (Q.minus c) d) j in
    try MP.n_add p j (MP.n_find p env.polynomes) env
    with Not_found -> MP.n_add p j (I.undefined ty) env


(*BISECT-IGNORE-BEGIN*)
module Debug = struct
  open Printer

  let add p =
    if get_debug_fm () then
      print_dbg
        ~module_name:"IntervalCalculus" ~function_name:"add"
        "@[<v 2>New polynome added: %a]" P.print p

  let assume ~query a expl =
    if get_debug_fm () then
      print_dbg
        ~module_name:"IntervalCalculus" ~function_name:"assume"
        "@[<v 2>%s We assume: %a@,explanations: %a@]"
        (if query then "[query]" else "")
        LR.print (LR.make a)
        Explanation.print expl

  let print_use fmt use =
    SX.iter (fprintf fmt "%a, " X.print) use

  let env env =
    if get_debug_fm () then begin
      print_dbg
        ~module_name:"IntervalCalculus" ~function_name:"env"
        "@ ------------ FM: inequations-------------------------@ ";
      MPL.iter
        (fun a { ple0 = p; is_le = is_le; _ } ->
           print_dbg ~flushed:false ~header:false "%a%s0  |  %a@ "
             P.print p (if is_le then "<=" else "<") E.print a
        )env.inequations;
      print_dbg ~flushed:false ~header:false
        "------------ FM: monomes ----------------------------@ ";
      MX.iter
        (fun x (i, use) ->
           print_dbg ~flushed:false ~header:false
             "%a : %a |-use-> {%a}@ "
             X.print x I.print i print_use use)
        env.monomes;
      print_dbg ~flushed:false ~header:false
        "------------ FM: polynomes---------------------------@ ";
      MP.iter
        (fun p i ->
           print_dbg ~flushed:false ~header:false
             "%a : %a@ " P.print p I.print i)
        env.polynomes;
      print_dbg ~header:false
        "-----------------------------------------------------"
    end

  let implied_equalities l =
    if get_debug_fm () then
      let pp_literal ppf = function
        | Literal.LTerm e -> Expr.print ppf e
        | LSem ra -> LR.print ppf (LR.make ra)
      in
      let print fmt (ra, ex, _) =
        fprintf fmt "@,%a %a"
          pp_literal ra
          Explanation.print ex
      in
      print_dbg
        ~module_name:"IntervalCalculus" ~function_name:"implied_equalities"
        "@[<v 2> %d implied equalities %a@]"
        (List.length l)
        (pp_list_no_space print) l

  let case_split r1 r2 =
    if get_debug_fm () then
      print_dbg
        ~module_name:"IntervalCalculus" ~function_name:"case-split"
        "%a = %a" X.print r1 X.print r2

  let no_case_split s =
    if get_debug_fm () then
      print_dbg
        ~module_name:"IntervalCalculus" ~function_name:"case-split"
        "%s : nothing" s

  let inconsistent_interval expl =
    if get_debug_fm () then
      print_dbg
        ~module_name:"IntervalCalculus"
        ~function_name:"inconsistent_interval"
        "interval inconsistent %a" Explanation.print expl

  let added_inequation kind ineq =
    if get_debug_fm () then begin
      print_dbg
        ~module_name:"IntervalCalculus" ~function_name:"added_inequation"
        "I derived the (%s) inequality: %a %s 0@ "
        kind P.print ineq.ple0
        (if ineq.is_le then "<=" else "<");
      print_dbg ~flushed:false ~header:false
        "from the following combination:@ ";
      Util.MI.iter
        (fun _a (coef, ple0, is_le) ->
           print_dbg ~flushed:false ~header:false
             "\t%a * (%a %s 0) +"
             Q.print coef P.print ple0 (if is_le then "<=" else "<")
        )ineq.dep;
      print_dbg ~header:false "\t0"
    end

  let tighten_interval_modulo_eq_begin p1 p2 =
    if get_debug_fm () then
      print_dbg
        ~module_name:"IntervalCalculus"
        ~function_name:"tighten_interval_modulo_eq_begin"
        "tighten intervals modulo eq: %a = %a"
        P.print p1 P.print p2

  let tighten_interval_modulo_eq_middle p1 p2 i1 i2 j =
    if get_debug_fm () then
      print_dbg
        ~module_name:"IntervalCalculus"
        ~function_name:"tighten_interval_modulo_eq_middle"
        "%a has interval %a@ \
         %a has interval %a@ \
         intersection is %a"
        P.print p1 I.print i1
        P.print p2 I.print i2
        I.print j

  let tighten_interval_modulo_eq_end p1 p2 b1 b2 =
    if get_debug_fm () then begin
      if b1 then
        print_dbg
          ~module_name:"IntervalCalculus"
          ~function_name:"tighten_interval_modulo_eq_end"
          "> improve interval of %a" P.print p1;
      if b2 then
        print_dbg
          ~module_name:"IntervalCalculus"
          ~function_name:"tighten_interval_modulo_eq_end"
          "> improve interval of %a" P.print p2;
      if not b1 && not b2 then
        print_dbg
          ~module_name:"IntervalCalculus"
          ~function_name:"tighten_interval_modulo_eq_end"
          "> no improvement"
    end

end
(*BISECT-IGNORE-END*)

let calc_pow a b ty uf =
  let ra, expl_a = Uf.find uf a in
  let rb, expl_b = Uf.find uf b in
  let pa = poly_of ra in
  let pb = poly_of rb in
  try
    match P.is_const pb with
    | Some c_y ->
      let res =
        (* x ** 1 -> x *)
        if Q.equal c_y Q.one then
          ra
          (* x ** 0 -> 1 *)
        else if Q.equal c_y Q.zero then
          alien_of (P.create [] Q.one ty)
        else
          match P.is_const pa with
          | Some c_x ->
            (* x ** y *)
            let res = Arith.calc_power c_x c_y ty  in
            alien_of (P.create [] res ty)
          | None -> raise Exit
      in
      Some (res,Ex.union expl_a expl_b)
    | None -> None
  with Exit -> None

let delayed_pow uf _op = function
  | [ a; b ] -> calc_pow a b (E.type_info a) uf
  | _ -> assert false

(* These are the partially interpreted functions that we know how to compute.
   They will be computed immediately if possible, or as soon as we learn the
   value of their arguments. *)
let dispatch = function
  | Symbols.Pow -> Some delayed_pow
  | _ -> None

let empty uf = {
  inequations = MPL.empty;
  monomes = MX.empty ;
  polynomes = MP.empty ;
  delayed = Rel_utils.Delayed.create ~is_ready:X.is_constant dispatch;
  known_eqs = SX.empty ;
  improved_p = SP.empty ;
  improved_x = SX.empty ;
  classes = Uf.cl_extract uf;
  size_splits = Q.one;
  new_uf = Uf.empty;

  rat_sim =
    Sim.Solve.solve
      (Sim.Core.empty ~is_int:false ~check_invs:false);
  int_sim =
    Sim.Solve.solve
      (Sim.Core.empty ~is_int:true ~check_invs:false);

  th_axioms = ME.empty;
  linear_dep = ME.empty;
  syntactic_matching = [];
}, Uf.domains uf

(*let up_improved env p oldi newi =
  if I.is_strict_smaller newi oldi then
  { env with improved = SP.add p env.improved }
  else env*)


(** computes an interval for vars = x_1^n_1 * ..... * x_i^n_i
    (1) if some var is not in monomes, then return undefined
    (2) check that all vars are in monomes before doing interval ops **)
let mult_bornes_vars vars env ty =
  try
    let l =
      List.rev_map (fun (y,n) ->
          let i, _, _ = generic_find y env in i, n
        ) vars
    in
    List.fold_left
      (fun ui (yi,n) -> I.mult ui (I.power n yi))
      (I.point Q.one ty Explanation.empty) l
  with Not_found -> I.undefined ty

(** computes the interval of a polynome from those of its monomes.
    The monomes are supposed to be already added in env **)
let intervals_from_monomes ?(monomes_inited=true) env p =
  let pl, v = P.to_list p in
  (* in the case of integer polynomes, ensure that we only round once
     at the end, and not at every add/scale operation on intervals. *)
  let rational_interval =
    List.fold_left
      (fun i (a, x) ->
         let i_x, _  =
           try MX.n_find x env.monomes
           with Not_found ->
             assert (not monomes_inited);
             I.undefined (X.type_info x), SX.empty
         in
         I.add (I.scale a (I.coerce Ty.Treal i_x)) i
      ) (I.point v Ty.Treal Explanation.empty) pl
  in
  I.coerce (P.type_info p) rational_interval

(* because, it's not sufficient to look in the interval that corresponds to
   the normalized form of p ... *)
let cannot_be_equal_to_zero env p ip =
  try
    let z = alien_of (P.create [] Q.zero (P.type_info p)) in
    match X.solve (alien_of p) z with
    | [] -> None (* p is equal to zero *)
    | _ -> I.doesnt_contain_0 ip
  with Util.Unsolvable -> Some (Explanation.empty, env.classes)


let rec init_monomes_of_poly are_eq env p use_p expl =
  List.fold_left
    (fun env (_, x) ->
       try
         let u, old_use_x = MX.n_find x env.monomes in
         MX.n_add x (u, SX.union old_use_x use_p) u env
       with Not_found ->
         update_monome are_eq expl use_p env x
    ) env (fst (P.to_list p))

and init_alien are_eq expl p (normal_p, c, d) use_x env =
  let env = init_monomes_of_poly are_eq env p use_x expl in
  let i = intervals_from_monomes env p in
  let i =
    try
      (* p = (normal_p + c) * d *)
      let old_i = MP.n_find normal_p env.polynomes in
      let old_i = I.affine_scale ~const:(Q.mult c d) ~coef:d old_i in
      I.intersect i old_i
    with Not_found -> i
  in
  env, i

and update_monome are_eq expl use_x env x =
  let ty = X.type_info x in
  let ui, env = match  X.ac_extract x with
    | Some { h; l; _ }
      when Symbols.equal h (Symbols.Op Symbols.Mult) ->
      let use_x = SX.singleton x in
      let env =
        List.fold_left
          (fun env (r,_) ->
             let rp, _, _ = poly_of r |> P.normal_form_pos in
             match P.is_monomial rp with
             | Some (a,y,b) when Q.equal a Q.one && Q.sign b = 0 ->
               update_monome are_eq expl use_x env y
             | _ -> env (* should update polys ? *)
          ) env l in
      let m = mult_bornes_vars l env ty in
      m, env
    | _ ->
      match X.term_extract x with
      | Some t, _ ->
        let use_x = SX.singleton x in
        begin
          match E.term_view t with
          | { E.f = (Sy.Op Sy.Div); xs = [a; b]; _ } ->
            let ra, ea =
              let (ra, _) as e = Uf.find env.new_uf a in
              if List.filter (X.equal x) (X.leaves ra) == [] then e
              else fst (X.make a), Explanation.empty (*otherwise, we loop*)
            in
            let rb, eb =
              let (rb, _) as e = Uf.find env.new_uf b in
              if List.filter (X.equal x) (X.leaves rb) == [] then e
              else fst (X.make b), Explanation.empty (*otherwise, we loop*)
            in
            let expl = Explanation.union expl (Explanation.union ea eb) in
            let pa = poly_of ra in
            let pb = poly_of rb in
            let (pa', ca, da) as npa = P.normal_form_pos pa in
            let (pb', cb, db) as npb = P.normal_form_pos pb in
            let env, ia =
              init_alien are_eq expl pa npa use_x env in
            let ia = I.add_explanation ia ea in (* take repr into account*)
            let env, ib =
              init_alien are_eq expl pb npb use_x env in
            let ib = I.add_explanation ib eb in (* take repr into account*)
            let ia, ib = match cannot_be_equal_to_zero env pb ib with
              | Some (ex, _) when Q.equal ca cb
                               && P.compare pa' pb' = 0 ->
                let expl = Explanation.union ex expl in
                I.point da ty expl, I.point db ty expl
              | Some (ex, _) ->
                begin
                  match are_eq a b with
                  | Some (ex_eq, _) ->
                    let expl = Explanation.union ex expl in
                    let expl = Explanation.union ex_eq expl in
                    I.point Q.one ty expl,
                    I.point Q.one ty expl
                  | None -> ia, ib
                end
              | None -> ia, ib
            in
            I.div ia ib, env
          | _ -> I.undefined ty, env
        end
      | _ -> I.undefined ty, env
  in
  let u, use_x' =
    try MX.n_find x env.monomes
    with Not_found -> I.undefined (X.type_info x), use_x in
  let ui = I.intersect ui u in
  MX.n_add x (ui, (SX.union use_x use_x')) u env

let rec tighten_ac are_eq x env expl =
  let ty = X.type_info x in
  let u, _use_x =
    try MX.n_find x env.monomes
    with Not_found -> I.undefined ty, SX.empty in
  try
    match X.ac_extract x with
    | Some { h; l = [x,n]; _ }
      when Symbols.equal h (Symbols.Op Symbols.Mult) && n mod 2 = 0  ->
      let env =
        if is_alien x then
          (* identity *)
          let u = I.coerce ty (I.root n (I.coerce Treal u)) in
          let (pu, use_px) =
            try MX.n_find x env.monomes (* we know that x is a monome *)
            with Not_found -> I.undefined ty, SX.empty
          in
          let u = I.intersect u pu in
          let env = MX.n_add x (u, use_px) pu env in
          tighten_non_lin are_eq x use_px env expl
        else
          (* Do something else for polys and non normalized-monomes ? *)
          env
      in
      env
    | Some { h; l = [x,n]; _ } when
        Symbols.equal h (Symbols.Op Symbols.Mult) && n > 2 ->
      let env =
        if is_alien x then
          let u = I.coerce ty (I.root n (I.coerce Treal u)) in
          let pu, use_px =
            try MX.n_find x env.monomes (* we know that x is a monome *)
            with Not_found -> I.undefined ty, SX.empty
          in
          let u = I.intersect u pu in
          let env = MX.n_add x (u, use_px) pu env in
          tighten_non_lin are_eq x use_px env expl
        else
          (* Do something else for polys and non normalized-monomes ? *)
          env
      in
      env
    | _ -> env
  with Q.Not_a_float -> env


and tighten_div _ env _ =
  env

and tighten_non_lin are_eq x use_x env expl =
  let env' = tighten_ac are_eq x env expl in
  let env' = tighten_div x env' expl in
  (*let use_x = SX.union use1_x use2_x in*)
  (* let i, _ = MX.find x env.monomes in *)
  (*let env' = update_monome are_eq expl use_x env' x in too expensive*)
  SX.fold
    (fun x acc ->
       let _, use = MX.n_find x acc.monomes in (* this is non-lin mult *)
       (*if I.is_strict_smaller new_i i then*)
       update_monome are_eq expl use acc x
       (*else acc*))
    use_x env'

let update_monomes_from_poly p i env =
  let lp, _ = P.to_list p in
  List.fold_left (fun env (a,x) ->
      let np = P.remove x p in
      let (np,c,d) = P.normal_form_pos np in
      (* a * x + (np + c) * d = 0 -> a * x = -d * np - d * c *)
      try
        let inp = MP.n_find np env.polynomes in
        let new_ix =
          I.scale
            (Q.inv a)
            (I.add i
               (I.affine_scale
                  ~coef:(Q.minus d) ~const:(Q.mult (Q.minus d) c) inp))
        in
        let old_ix, ux = MX.n_find x env.monomes in
        let ix = I.intersect old_ix new_ix in
        MX.n_add x (ix, ux) old_ix env
      with Not_found -> env
    ) env lp

let update_polynomes_intervals env =
  MP.fold
    (fun p ip env ->
       let new_i = intervals_from_monomes env p in
       let i = I.intersect new_i ip in
       if I.is_strict_smaller i ip then
         update_monomes_from_poly p i (MP.n_add p i ip env)
       else env
    ) env.polynomes env

let update_non_lin_monomes_intervals are_eq env =
  MX.fold
    (fun x (_, use_x) env ->
       tighten_non_lin are_eq x use_x env Explanation.empty
    ) env.monomes env

let find_one_eq x u =
  match I.is_point u with
  | Some (v, ex) when X.type_info x != Ty.Tint || Q.is_int v ->
    let eq =
      LR.mkv_eq x (alien_of (P.create [] v (X.type_info x))) in
    Some (eq, None, ex, Th_util.Other)
  | _ -> None

let find_eq eqs x u env =
  match find_one_eq x u with
  | None -> eqs
  | Some eq1 ->
    begin
      match X.ac_extract x with
      | Some { h; l = [y,_]; _ }
        when Symbols.equal h (Symbols.Op Symbols.Mult) ->
        let neweqs = try
            let u, _, _ = generic_find y env in
            match find_one_eq y u with
            | None -> eq1::eqs
            | Some eq2 -> eq1::eq2::eqs
          with Not_found -> eq1::eqs
        in neweqs
      | _ -> eq1::eqs
    end

type ineq_status =
  | Trivial_eq
  | Trivial_ineq of Q.t
  | Bottom
  | Monome of Q.t * P.r * Q.t
  | Other

let ineq_status { ple0 = p ; is_le; _ } =
  match P.is_monomial p with
    Some (a, x, v) -> Monome (a, x, v)
  | None ->
    if P.is_empty p then
      let _, v = P.separate_constant p in
      let c = Q.sign v (* equiv. to compare v Q.zero *) in
      if c > 0 || (c >=0 && not is_le) then Bottom
      else
      if c = 0 && is_le then Trivial_eq
      else Trivial_ineq v
    else Other

(*let ineqs_from_dep dep borne_inf is_le =
  List.map
  (fun {poly_orig = p; coef = c} ->
  let (m,v,ty) = P.mult_const minusone p in
  (* quelle valeur pour le ?????? *)
  { ple0 = {poly = (m, v +/ (Q.div borne_inf c), ty); le = is_le} ;
  dep = []}
  )dep*)

let mk_equality p =
  let r1 = alien_of p in
  let r2 = alien_of (P.create [] Q.zero (P.type_info p)) in
  LR.mkv_eq r1 r2

let fm_equalities eqs { dep; expl = ex; _ } =
  Util.MI.fold
    (fun _ (_, p, _) eqs ->
       (mk_equality p, None, ex, Th_util.Other) :: eqs
    ) dep eqs


let update_intervals are_eq env eqs expl (a, x, v) is_le =
  let (u0, use_x0) as ixx = MX.n_find x env.monomes in
  let uints, use_x =
    match X.ac_extract x with
    | Some { h; l; _ } when Symbols.equal h (Symbols.Op Symbols.Mult) ->
      let m = mult_bornes_vars l env (X.type_info x) in
      I.intersect m u0, use_x0
    | _ -> ixx
  in
  let b = Q.div (Q.mult Q.m_one v) a in
  let u =
    if Q.sign a > 0 then
      I.new_borne_sup expl b ~is_le uints
    else
      I.new_borne_inf expl b ~is_le uints in
  let env = MX.n_add x (u, use_x) u0 env in
  let env =  tighten_non_lin are_eq x use_x env expl in
  env, (find_eq eqs x u env)

let update_ple0 are_eq env p0 is_le expl =
  if P.is_empty p0 then env
  else
    let ty = P.type_info p0 in
    let a, _ = P.choose p0 in
    let p, change =
      if Q.sign a < 0 then
        P.mult_const Q.m_one p0, true
      else p0, false in
    let p, c, _ = P.normal_form p in
    let c = Q.minus c in
    let u =
      if change then
        I.new_borne_inf expl c ~is_le (I.undefined ty)
      else
        I.new_borne_sup expl c ~is_le (I.undefined ty) in
    let u, pu =
      try
        (* p is in normal_form_pos because of the ite above *)
        let pu = MP.n_find p env.polynomes in
        let i = I.intersect u pu in
        i, pu
      with Not_found -> u, I.undefined ty
    in
    let env =
      if I.is_strict_smaller u pu then
        update_monomes_from_poly p u (MP.n_add p u pu env)
      else env
    in
    match P.to_list p0 with
    | [a,x], v ->
      fst(update_intervals are_eq env [] expl (a, x, v) is_le)
    | _ -> env

let register_relationship c x pi expl (x_rels, p_rels) =
  let x_rels =
    let a = Q.minus c, expl in
    let s = Q.sign c in
    assert (s <> 0);
    let low, up =
      try MX0.find x x_rels with Not_found -> MP0.empty, MP0.empty in
    let v =
      if s < 0 then
        MP0.add pi a low, up  (* low_bnd(pi) / (-c) is a low_bnd of x *)
      else
        low, MP0.add pi a up  (* low_bnd(pi) / (-c) is an up_bnd of x *)
    in
    MX0.add x v x_rels
  in
  let p_rels =
    let p0, c0, d0 = P.normal_form_pos pi in
    let b = c, Q.minus c0, Q.minus d0, expl in
    let s = Q.sign d0 in
    assert (s <> 0);
    let low,up =
      try MP0.find p0 p_rels with Not_found -> MX0.empty, MX0.empty in
    let w =
      if s < 0 then
        (*low_bnd(c*x)/(-d0) + (-c0) is a low_bnd of p0*)
        MX0.add x b low, up
      else
        (*low_bnd(c*x)/(-d0) + (-c0) is an up_bnd of p0*)
        low, MX0.add x b up
    in
    MP0.add p0 w p_rels
  in
  x_rels, p_rels


let add_inequations are_eq acc x_opt lin =
  List.fold_left
    (fun ((env, eqs, rels) as acc) ineq ->
       let expl = ineq.expl in
       match ineq_status ineq with
       | Bottom           ->
         Debug.added_inequation "Bottom" ineq;
         raise (Ex.Inconsistent (expl, env.classes))

       | Trivial_eq       ->
         Debug.added_inequation "Trivial_eq" ineq;
         env, fm_equalities eqs ineq, rels

       | Trivial_ineq  c  ->
         Debug.added_inequation "Trivial_ineq"  ineq;
         let n, pp =
           Util.MI.fold
             (fun _ (_, p, is_le) ((n, pp) as acc) ->
                if is_le then acc else
                  match pp with
                  | Some _ -> n+1, None
                  | None when n=0 -> 1, Some p
                  | _ -> n+1, None) ineq.dep (0,None)
         in
         let env =
           Util.MI.fold
             (fun _ (coef, p, is_le) env ->
                let ty = P.type_info p in
                let is_le =
                  match pp with
                    Some x -> P.compare x p = 0 | _ -> is_le && n=0
                in
                let p' = P.sub (P.create [] (Q.div c coef) ty) p in
                update_ple0 are_eq env p' is_le expl
             ) ineq.dep env
         in
         env, eqs, rels

       | Monome (a, x, v) ->
         Debug.added_inequation "Monome" ineq;
         let env, eqs =
           update_intervals
             are_eq env eqs expl (a, x, v) ineq.is_le
         in
         env, eqs, rels

       | Other            ->
         match x_opt with
         | None -> acc
         | Some x ->
           let ple0 = ineq.ple0 in
           let c = try P.find x ple0 with Not_found -> assert false in
           let ple0 = P.remove x ple0 in
           env, eqs, register_relationship c x ple0 ineq.expl rels
    ) acc lin

let split_problem current_age env ineqs aliens =
  let l, all_lvs =
    List.fold_left
      (fun (acc, all_lvs) ({ ple0 = p; _ } as ineq) ->


         match ineq_status ineq with
         | Trivial_eq | Trivial_ineq _ -> (acc, all_lvs)
         | Bottom ->
           raise (Ex.Inconsistent (ineq.expl, env.classes))
         | _ ->
           let lvs =
             List.fold_left (fun acc e -> SX.add e acc) SX.empty (aliens p)
           in
           ([ineq], lvs) :: acc , SX.union lvs all_lvs
      )([], SX.empty) ineqs
  in
  let ll =
    SX.fold
      (fun x l ->
         let lx, l_nx = List.partition (fun (_,s) -> SX.mem x s) l in
         match lx with
         | [] -> assert false
         | e:: lx ->
           let elx =
             List.fold_left
               (fun (l, lvs) (l', lvs') ->
                  List.rev_append l l', SX.union lvs lvs') e lx in
           elx :: l_nx
      ) all_lvs l
  in
  let ll =
    List.filter
      (fun (ineqs, _) ->
         List.exists
           (fun ineq -> Z.equal current_age ineq.age) ineqs
      )ll
  in
  List.fast_sort (fun (a,_) (b,_) -> List.length a - List.length b) ll

let is_normalized_poly uf p =
  let p = alien_of p in
  let rp, _  = Uf.find_r uf p in
  if X.equal p rp then true
  else begin
    Printer.print_err
      "%a <= 0 NOT normalized@,It is equal to %a"
      X.print p X.print rp;
    false
  end

let better_upper_bound_from_intervals env p =
  let p0, c0, d0 = P.normal_form_pos p in
  assert (Q.is_zero c0);
  try
    let i = MP.n_find p0 env.polynomes in
    if Q.is_one d0 then I.borne_sup i
    else
    if Q.is_m_one d0 then
      let bi, ex, is_large = I.borne_inf i in
      Q.minus bi, ex, is_large
    else assert false
  with I.No_finite_bound | Not_found ->
    assert false (*env.polynomes is up to date w.r.t. ineqs *)

let better_bound_from_intervals env ({ ple0; is_le; dep; _ } as v) =
  let p, c = P.separate_constant ple0 in
  assert (not (P.is_empty p));
  let cur_up_bnd = Q.minus c in
  let i_up_bnd, expl, is_large = better_upper_bound_from_intervals env p in
  let new_p = P.add_const (Q.minus i_up_bnd) p in
  let a = match Util.MI.bindings dep with [a,_] -> a | _ -> assert false in
  let cmp = Q.compare i_up_bnd cur_up_bnd in
  assert (cmp <= 0);
  if cmp = 0 then
    match is_le, is_large with
    | false, true -> assert false (* intervals are normalized wrt ineqs *)
    | false, false | true, true -> v (* no change *)
    | true , false -> (* better bound, Large ineq becomes Strict *)
      {v with
       ple0 = new_p;
       expl = expl;
       is_le = false;
       dep = Util.MI.singleton a (Q.one, new_p, false)}
  else (* new bound is better. i.e. i_up_bnd < cur_up_bnd *)
    {v with
     ple0 = new_p;
     expl = expl;
     is_le = is_large;
     dep = Util.MI.singleton a (Q.one, new_p, is_large)}

let args_of p = List.rev_map snd (fst (P.to_list p))

let update_linear_dep env rclass_of ineqs =
  let terms =
    List.fold_left
      (fun st { ple0; _ } ->
         List.fold_left
           (fun st (_, x) -> SE.union st (rclass_of x))
           st (fst (P.to_list ple0))
      )SE.empty ineqs
  in
  let linear_dep =
    SE.fold
      (fun t linear_dep -> ME.add t terms linear_dep) terms env.linear_dep
  in
  {env with linear_dep}

let refine_x_bounds ix env rels is_low =
  MP.fold
    (fun p (m_cx, ineq_ex) ix ->
       try
         (* recall (construction of x_rels):
            -> is_low     : low_bnd(pi) / (-c) is a low_bnd of x
            -> not is_low : low_bnd(pi) / (-c) is an up_bnd of x
         *)
         assert (is_low == (Q.sign m_cx > 0));
         let ip, _, _ = generic_find ~only_inf:true (alien_of p) env in
         let b, ex_b, is_le = I.borne_inf ip in (* invariant, see above *)
         let b = Q.div b m_cx in
         let func = if is_low then I.new_borne_inf else I.new_borne_sup in
         func (Explanation.union ineq_ex ex_b) b ~is_le ix
       with I.No_finite_bound -> ix
    )rels ix

let monomes_relational_deductions env x_rels =
  MX.fold
    (fun x (low, up) env ->
       let ix0, use_x =
         try MX.n_find x env.monomes with Not_found -> assert false in
       let ix = refine_x_bounds ix0 env low true in
       let ix = refine_x_bounds ix  env up  false in
       if I.is_strict_smaller ix ix0 then MX.n_add x (ix, use_x) ix0 env
       else env
    )x_rels env

let refine_p_bounds ip _p env rels is_low =
  MX.fold
    (fun x (cx, mc0, md0, ineq_ex) ip ->
       try
         (* recall (construction of p_rels):
            -> is_low     : low_bnd(c*x) / (-d0) + (-c0) is a low_bnd of p0
            -> not is_low : low_bnd(c*x) / (-d0) + (-c0) is an up_bnd of p0
            where p = (p0 + c0) * d0 and c*x + p <= 0
         *)
         assert (is_low == (Q.sign md0 > 0));
         let ix,_ =
           try MX.n_find x env.monomes with Not_found -> raise Exit in
         let bx, ex_b, is_le =
           (if Q.sign cx > 0 then I.borne_inf else I.borne_sup) ix in
         (* this this the low_bnd of c*x, see above *)
         let b = Q.mult cx bx in
         let b = Q.add (Q.div b md0) mc0 in (* final bnd of p0 *)
         let func = if is_low then I.new_borne_inf else I.new_borne_sup in
         func (Explanation.union ineq_ex ex_b) b ~is_le ip
       with Exit | I.No_finite_bound -> ip
    )rels ip

let polynomes_relational_deductions env p_rels =
  MP.fold
    (fun p0 (low, up) env ->
       (* p0 is in normal_form pos *)
       let xp = alien_of p0 in
       if not (MP.mem p0 env.polynomes || MX.mem xp env.monomes) then env
       else
         let ip0, use, is_mon = generic_find xp env in
         let ip = refine_p_bounds ip0 p0 env low true in
         let ip = refine_p_bounds ip  p0 env up  false in
         if I.is_strict_smaller ip ip0 then
           if is_mon then MX.n_add xp (ip, use) ip0 env
           else MP.n_add p0 ip ip0 env
         else
           env
    )p_rels env


let fm (module Oracle : S with type p = P.t) uf are_eq rclass_of env eqs =
  if get_debug_fm () then
    Printer.print_dbg
      ~module_name:"IntervalCalculus"
      ~function_name:"fm"
      "in fm/fm-simplex";
  Options.tool_req 4 "TR-Arith-Fm";
  let ineqs =
    MPL.fold (fun _ v acc ->
        Options.heavy_assert (fun () -> is_normalized_poly uf v.ple0);
        (better_bound_from_intervals env v) :: acc
      ) env.inequations []
  in
  let current_age = Oracle.current_age () in
  let pbs = split_problem current_age env ineqs args_of in
  let res = List.fold_left
      (fun (env, eqs) (ineqs, _) ->
         let env = update_linear_dep env rclass_of ineqs in
         let mp = Oracle.MINEQS.add_to_map Oracle.MINEQS.empty ineqs in
         let env, eqs, (x_rels, p_rels) =
           Oracle.available add_inequations are_eq
             (env, eqs, (MX.empty, MP.empty)) mp
         in
         let env = monomes_relational_deductions env x_rels in
         let env = polynomes_relational_deductions env p_rels in
         env, eqs
      )(env, eqs) pbs
  in
  if get_debug_fm () then
    Printer.print_dbg
      ~module_name:"IntervalCalculus"
      ~function_name:"fm"
      "out fm/fm-simplex";
  res

let is_num r =
  let ty = X.type_info r in ty == Ty.Tint || ty == Ty.Treal

let add_disequality are_eq env eqs p expl =
  let ty = P.type_info p in
  match P.to_list p with
  | ([], v) ->
    if Q.sign v = 0 then
      raise (Ex.Inconsistent (expl, env.classes));
    env, eqs
  | ([a, x], v) ->
    let b = Q.div (Q.minus v) a in
    let i2, use2 =
      try
        MX.n_find x env.monomes
      with Not_found -> I.undefined ty, SX.empty
    in
    let i = I.exclude ~ex:expl b i2 in
    let env = MX.n_add x (i,use2) i2 env in
    let env = tighten_non_lin are_eq x use2 env expl in
    env, find_eq eqs x i env
  | _ ->
    let p, c, _ = P.normal_form_pos p in
    let i2 =
      try
        MP.n_find p env.polynomes
      with Not_found -> I.undefined ty
    in
    let i = I.exclude ~ex:expl (Q.minus c) i2 in
    let env =
      if I.is_strict_smaller i i2 then
        update_monomes_from_poly p i (MP.n_add p i i2 env)
      else env
    in
    env, eqs

let add_equality are_eq env eqs p expl =
  let ty = P.type_info p in
  match P.to_list p with
  | ([], v) ->
    if Q.sign v <> 0 then
      raise (Ex.Inconsistent (expl, env.classes));
    env, eqs

  | ([a, x], v) ->
    let b = Q.div (Q.minus v) a in
    let i = I.point b ty expl in
    let i2, use =
      try MX.n_find x env.monomes
      with Not_found -> I.undefined ty, SX.empty
    in
    let i = I.intersect i i2 in
    let env = MX.n_add x (i, use) i2 env in
    let env = tighten_non_lin are_eq x use env expl in
    env, find_eq eqs x i env
  | _ ->
    let p, c, _ = P.normal_form_pos p in
    let i = I.point (Q.minus c) ty expl in
    let i, ip =
      try
        let ip =  MP.n_find p env.polynomes in
        I.intersect i ip, ip
      with Not_found -> i, I.undefined ty
    in
    let env =
      if I.is_strict_smaller i ip then
        update_monomes_from_poly p i (MP.n_add p i ip env)
      else env
    in
    let env =
      { env with
        known_eqs = SX.add (alien_of p) env.known_eqs
      } in
    env, eqs

let normal_form a = match a with
  | L.Builtin (false, L.LE, [r1; r2])
    when X.type_info r1 == Ty.Tint ->
    let pred_r1 = P.sub (poly_of r1) (P.create [] Q.one Ty.Tint) in
    LR.mkv_builtin true L.LE [r2; alien_of pred_r1]

  | L.Builtin (true, L.LT, [r1; r2]) when
      X.type_info r1 == Ty.Tint ->
    let pred_r2 = P.sub (poly_of r2) (P.create [] Q.one Ty.Tint) in
    LR.mkv_builtin true L.LE [r1; alien_of pred_r2]

  | L.Builtin (false, L.LE, [r1; r2]) ->
    LR.mkv_builtin true L.LT [r2; r1]

  | L.Builtin (false, L.LT, [r1; r2]) ->
    LR.mkv_builtin true L.LE [r2; r1]

  | _ -> a

let equalities_from_polynomes env eqs =
  let known, eqs =
    MP.fold
      (fun p i (knw, eqs) ->
         let xp = alien_of p in
         if SX.mem xp knw then knw, eqs
         else
           match I.is_point i with
           | Some (num, ex) ->
             let r2 = alien_of (P.create [] num (P.type_info p)) in
             SX.add xp knw, (LR.mkv_eq xp r2, None, ex, Th_util.Other) :: eqs
           | None -> knw, eqs
      ) env.polynomes  (env.known_eqs, eqs)
  in {env with known_eqs= known}, eqs



let equalities_from_monomes env eqs =
  let known, eqs =
    MX.fold
      (fun x (i,_) (knw, eqs) ->
         if SX.mem x knw then knw, eqs
         else
           match I.is_point i with
           | Some (num, ex) ->
             let r2 = alien_of (P.create [] num (X.type_info x)) in
             SX.add x knw, (LR.mkv_eq x r2, None, ex, Th_util.Other) :: eqs
           | None -> knw, eqs
      ) env.monomes  (env.known_eqs, eqs)
  in {env with known_eqs= known}, eqs

let equalities_from_intervals env eqs =
  let env, eqs = equalities_from_polynomes env eqs in
  equalities_from_monomes env eqs

let count_splits env la =
  let nb =
    List.fold_left
      (fun nb (_,_,_,i) ->
         match i with
         | Th_util.CS (Th_util.Th_arith, n) -> Numbers.Q.mult nb n
         | _ -> nb
      )env.size_splits la
  in
  {env with size_splits = nb}

let remove_ineq a ineqs =
  match a with None -> ineqs | Some a -> MPL.remove a ineqs

let add_ineq a v ineqs =
  match a with None -> ineqs | Some a -> MPL.add a v ineqs


(*** functions to improve intervals modulo equality ***)
let tighten_eq_bounds env r1 r2 p1 p2 origin_eq expl =
  if P.is_const p1 != None || P.is_const p2 != None then env
  else
    match origin_eq with
    | Th_util.CS _ | Th_util.NCS _ -> env
    | Th_util.Subst | Th_util.Other ->
      (* Subst is needed, but is Other needed ?? or is it subsumed ? *)
      Debug.tighten_interval_modulo_eq_begin p1 p2;
      let i1, us1, is_mon_1 = generic_find r1 env in
      let i2, us2, is_mon_2 = generic_find r2 env in
      (* We are assuming [origin_eq] with explanation [expl], where [origin_eq]
       * is an equality between terms [r1] and [r2] with respective intervals
       * [i1] and [i2].
       *
       * The shared interval for both [r1] and [r2] after the assumption
       * becomes the intersection of [i1] and [i2], and must account for the
       * additional explanation [expl] (since [origin_eq] is only valid under
       * [expl]).
       *
       * [I.intersect] raises a "not consistent" exception if the two intervals
       * are disjoint, but it does so *before* the additional explanation is
       * added to the intervals' bounds, so we must add it explicitly in that
       * case.
      *)
      let intersect i1 i2 =
        try I.intersect i1 i2
        with I.NotConsistent ex -> raise (I.NotConsistent (Ex.union ex expl))
      in
      let j = I.add_explanation (intersect i1 i2) expl in
      Debug.tighten_interval_modulo_eq_middle p1 p2 i1 i2 j;
      let impr_i1 = I.is_strict_smaller j i1 in
      let impr_i2 = I.is_strict_smaller j i2 in
      Debug.tighten_interval_modulo_eq_end p1 p2 impr_i1 impr_i2;
      let env =
        if impr_i1 then generic_add r1 j us1 is_mon_1 env else env
      in
      if impr_i2 then generic_add r2 j us2 is_mon_2 env else env

let rec loop_update_intervals are_eq env cpt =
  let cpt = cpt + 1 in
  let env = {env with improved_p=SP.empty; improved_x=SX.empty} in
  let env = update_non_lin_monomes_intervals are_eq env in
  let env = Sim_Wrap.solve env 1 in
  let env = update_polynomes_intervals env in
  let env = Sim_Wrap.solve env 1 in
  if env.improved_p == SP.empty && env.improved_x == SX.empty || cpt > 10
  then env
  else loop_update_intervals are_eq env cpt

let assume ~query env uf la =
  let module Oracle = (val get_oracle ()) in
  Oracle.incr_age ();
  let env = count_splits env la in
  let are_eq = Uf.are_equal uf ~added_terms:true in
  let classes = Uf.cl_extract uf in
  let rclass_of = Uf.rclass_of uf in
  let env =
    {env with
     improved_p=SP.empty; improved_x=SX.empty; classes; new_uf = uf}
  in
  Debug.env env;
  let nb_num = ref 0 in
  let env, eqs, new_ineqs, to_remove =
    List.fold_left
      (fun ((env, eqs, new_ineqs, rm) as acc) (a, root, expl, orig) ->
         let a = normal_form a in
         Debug.assume ~query a expl;
         Steps.incr (Interval_Calculus);
         try
           match a with
           | L.Builtin(_, ((L.LE | L.LT) as n), [r1;r2]) ->
             incr nb_num;
             let p1 = poly_of r1 in
             let p2 = poly_of r2 in
             let ineq =
               Oracle.create_ineq p1 p2 (n == L.LE) root expl in
             begin
               match ineq_status ineq with
               | Bottom -> raise (Ex.Inconsistent (expl, env.classes))
               | Trivial_eq | Trivial_ineq _ ->
                 {env with inequations=remove_ineq root env.inequations},
                 eqs, new_ineqs,
                 (match root with None -> rm | Some a -> a:: rm)

               | Monome _
               | Other ->
                 let env =
                   init_monomes_of_poly
                     are_eq env ineq.ple0 SX.empty
                     Explanation.empty
                 in
                 let env =
                   update_ple0
                     are_eq env ineq.ple0 (n == L.LE) expl
                 in
                 {env with inequations=add_ineq root ineq env.inequations},
                 eqs, true, rm
             end

           | L.Distinct (false, [r1; r2]) when is_num r1 && is_num r2 ->
             incr nb_num;
             let p = P.sub (poly_of r1) (poly_of r2) in
             begin
               match P.is_const p with
               | Some c ->
                 if Q.is_zero c then (* bottom *)
                   raise (Ex.Inconsistent (expl, env.classes))
                 else (* trivial *)
                   let rm = match root with Some a -> a::rm | None -> rm in
                   env, eqs, new_ineqs, rm
               | None ->
                 let env = init_monomes_of_poly are_eq env p SX.empty
                     Explanation.empty
                 in
                 let env, eqs = add_disequality are_eq env eqs p expl in
                 env, eqs, new_ineqs, rm
             end

           | L.Eq(r1, r2) when is_num r1 && is_num r2 ->
             incr nb_num;
             let p1 = poly_of r1 in
             let p2 = poly_of r2 in
             let p = P.sub p1 p2 in
             let env = init_monomes_of_poly are_eq env p SX.empty
                 Explanation.empty
             in
             let env, eqs = add_equality are_eq env eqs p expl in
             let env = tighten_eq_bounds env r1 r2 p1 p2 orig expl in
             let eqs =
               Rel_utils.Delayed.update env.delayed env.new_uf r1 r2 orig eqs
             in
             env, eqs, new_ineqs, rm

           | _ -> acc

         with I.NotConsistent expl ->
           Debug.inconsistent_interval expl ;
           raise (Ex.Inconsistent (expl, env.classes))
      )
      (env, [], false, []) la

  in
  try
    let env = if query then env else Sim_Wrap.solve env 1 in
    if !nb_num = 0 || query then env, {Sig_rel.assume=[]; remove = to_remove}
    else
      (* we only call fm when new ineqs are assumed *)
      let env, eqs =
        if new_ineqs && not (Options.get_no_fm ()) then
          fm (module Oracle) uf are_eq rclass_of env eqs
        else env, eqs
      in
      let env = Sim_Wrap.solve env 1 in
      let env = loop_update_intervals are_eq env 0 in
      let env, eqs = equalities_from_intervals env eqs in

      Debug.env env;
      let to_assume = Rel_utils.assume_nontrivial_eqs eqs la in
      Debug.implied_equalities to_assume;
      env, {Sig_rel.assume = to_assume; remove = to_remove}
  with I.NotConsistent expl ->
    Debug.inconsistent_interval expl ;
    raise (Ex.Inconsistent (expl, env.classes))


let assume ~query env uf la =
  let env, res = assume ~query env uf la in
  let polys =
    MP.fold
      (fun p _ mp ->
         if Uf.is_normalized uf (alien_of p) then mp else MP.remove p mp)
      env.polynomes env.polynomes
  in
  {env with polynomes = polys}, Uf.domains uf, res

let query env uf a_ex =
  try
    ignore(assume ~query:true env uf [a_ex]);
    None
  with Ex.Inconsistent (expl, classes) -> Some (expl, classes)

let case_split_polynomes env =
  let o = MP.fold
      (fun p i o ->
         match I.finite_size i with
         | Some s when Q.compare s Q.one > 0 ->
           begin
             match o with
             | Some (s', _, _) when Q.compare s' s < 0 -> o
             | _ ->
               let n, _, is_large = I.borne_inf i in
               assert (is_large);
               Some (s, p, n)
           end
         | _ -> o
      ) env.polynomes None in
  match o with
  | Some (s, p, n) ->
    let r1 = alien_of p in
    let r2 = alien_of (P.create [] n  (P.type_info p)) in
    Debug.case_split r1 r2;
    [LR.mkv_eq r1 r2, true, Th_util.CS (Th_util.Th_arith, s)], s
  | None ->
    Debug.no_case_split "polynomes";
    [], Q.zero

let case_split_monomes env =
  let o = MX.fold
      (fun x (i,_) o ->
         match I.finite_size i with
         | Some s when Q.compare s Q.one > 0 ->
           begin
             match o with
             | Some (s', _, _) when Q.compare s' s < 0 -> o
             | _ ->
               let n, _, is_large = I.borne_inf i in
               assert (is_large);
               Some (s, x, n)
           end
         | _ -> o
      ) env.monomes None in
  match o with
  | Some (s,x,n) ->
    let ty = X.type_info x in
    let r1 = x in
    let r2 = alien_of (P.create [] n  ty) in
    Debug.case_split r1 r2;
    [LR.mkv_eq r1 r2, true, Th_util.CS (Th_util.Th_arith, s)], s
  | None ->
    Debug.no_case_split "monomes";
    [], Q.zero

let check_size for_model env res =
  if for_model then res
  else
    match res with
    | [] -> res
    | [_, _, Th_util.CS (Th_util.Th_arith, s)] ->
      if Numbers.Q.compare (Q.mult s env.size_splits) (get_max_split ()) <= 0 ||
         Numbers.Q.sign  (get_max_split ()) < 0 then res
      else []
    | _ -> assert false

let default_case_split env uf ~for_model =
  Options.tool_req 4 "TR-Arith-CaseSplit";
  match check_size for_model  env (Sim_Wrap.case_split env uf) with
    [] ->
    begin
      let cs1, sz1 = case_split_polynomes env in
      let cs2, sz2 =  case_split_monomes env in
      match check_size for_model env cs1, check_size for_model env cs2
      with
      | [], cs | cs, []  -> cs
      | cs1, cs2 -> if Q.compare sz1 sz2 < 0 then cs1 else cs2
    end
  | res -> res

let add =
  let are_eq t1 t2 =
    if E.equal t1 t2 then Some (Explanation.empty, []) else None
  in
  fun env new_uf r t ->
    Debug.env env;
    try
      let env = {env with new_uf} in
      let p = poly_of r in
      Debug.add p;
      if is_num r then
        let env =
          init_monomes_of_poly are_eq env p SX.empty Explanation.empty
        in
        let delayed, eqs =
          Rel_utils.Delayed.add env.delayed env.new_uf r t
        in
        { env with delayed }, Uf.domains new_uf, eqs
      else env, Uf.domains new_uf, []
    with I.NotConsistent expl ->
      Debug.inconsistent_interval expl;
      raise (Ex.Inconsistent (expl, env.classes))

(*
    let extract_improved env =
      SP.fold
        (fun p acc ->
        MP.add p (MP.find p env.polynomes) acc)
        env.improved MP.empty
*)

let new_terms _ = SE.empty

let case_split_union_of_intervals =
  let aux acc uf i z =
    if Uf.is_normalized uf z then (
      ignore @@
      I.fold (fun prev { lb = _ ; ub } ->
          match prev, ub with
          | None, Open ub -> Some (L.LT, ub)
          | None, Closed ub -> Some (L.LE, ub)
          | Some bnd, _ -> acc := Some (z, bnd); raise Exit
          | None, _ -> None
        ) None i
    )
  in fun env uf ->
    let cs = ref None in
    try
      MP.iter (fun p i -> aux cs uf i (alien_of p)) env.polynomes;
      MX.iter (fun x (i,_) -> aux cs uf i x) env.monomes;
      []
    with Exit ->
    match !cs with
    | None -> assert false
    | Some (r1, (pred, n)) ->
      let ty = X.type_info r1 in
      let r2 = alien_of (P.create [] n ty) in
      [LR.mkv_builtin true pred [r1; r2], true,
       Th_util.CS (Th_util.Th_arith, Q.one)]


(*****)

let int_constraints_from_map_intervals =
  let aux p xp i uf acc =
    if Uf.is_normalized uf xp && I.is_point i == None
       && P.type_info p == Ty.Tint
    then (p, I.integer_hull i) :: acc
    else acc
  in
  fun env uf ->
    let acc =
      MP.fold (fun p i acc -> aux p (alien_of p) i uf acc) env.polynomes []
    in
    MX.fold (fun x (i,_) acc -> aux (poly_of x) x i uf acc) env.monomes acc

let bnd_to_simplex_bnd (bnd, ex) =
  Sim.Core.{ bvalue = R2.of_r (Q.from_z bnd) ; explanation = ex }

let fm_simplex_unbounded_integers_encoding env uf =
  let simplex = Sim.Core.empty ~is_int:true ~check_invs:true in
  let int_ctx = int_constraints_from_map_intervals env uf in
  List.fold_left
    (fun simplex (p, (lb, ub)) ->
       let l, c = P.to_list p in
       assert (Q.is_zero c);
       let min = Option.map bnd_to_simplex_bnd lb in
       let max = Option.map bnd_to_simplex_bnd ub in
       match l with
       | [] -> assert false
       | [c, x] ->
         assert (Q.is_one c);
         Sim.Assert.var simplex x ?min ?max |> fst
       | _ ->
         let l = List.rev_map (fun (c, x) -> x, c) (List.rev l) in
         let xp = alien_of p in
         let sim_p =
           match Sim.Core.poly_of_slake simplex xp with
           | Some res -> res
           | None -> Sim.Core.P.from_list l
         in
         Sim.Assert.poly simplex sim_p xp ?min ?max |> fst

    ) simplex int_ctx


let round_to_integers list =
  List.rev_map (fun (x, q1) ->
      let f = Q.floor q1 in
      let c = Q.ceiling q1 in
      x, if Q.compare (Q.sub q1 f) (Q.sub c q1) > 0 then f else c
    ) (List.rev list)


(* cannot replace directly with env.int_sim because of encoding *)
let model_from_simplex sim is_int env uf =
  match Sim.Result.get None sim with
  | Sim.Core.Unknown | Sim.Core.Unbounded _ | Sim.Core.Max _ -> assert false

  | Sim.Core.Unsat ex ->
    (* when splitting on union of intervals, FM does not include
       related ineqs when crossing. So, we may miss some bounds/deductions,
       and FM-Simplex may fail to find a model *)
    raise (Ex.Inconsistent(Lazy.force ex, env.classes))

  | Sim.Core.Sat sol ->
    let {Sim.Core.main_vars; slake_vars; int_sol; epsilon=_} = Lazy.force sol in
    let main_vars, _slake_vars =
      if int_sol || not is_int then main_vars, slake_vars
      else round_to_integers main_vars, round_to_integers slake_vars
    in
    let fct = if is_int then E.int else E.real in
    List.fold_left
      (fun acc (v, q) ->
         assert (not is_int || Q.is_int q);
         if SX.mem v env.known_eqs || not (Uf.is_normalized uf v) then
           (* may happen because of incremental simplex on rationals *)
           acc
         else
           let t = fct (Q.to_string q) in
           let r, _ = X.make t in
           if get_debug_interpretation () then
             Printer.print_dbg
               ~module_name:"IntervalCalculus"
               ~function_name:"model_from_simplex"
               "[%s simplex] %a = %a"
               (if is_int then "integer" else "rational")
               X.print v X.print r;
           (v, r, Explanation.empty) :: acc
      )[] (List.rev main_vars)


let model_from_infinite_domains =
  let mk_cs acc (x, v, _ex) =
    ((LR.view (LR.mk_eq x v)), true,
     Th_util.CS (Th_util.Th_arith, Q.from_int 2)) :: acc
  in
  fun env uf ->
    assert (env.int_sim.Sim.Core.status == Sim.Core.SAT);
    assert (env.rat_sim.Sim.Core.status == Sim.Core.SAT);
    let rat_sim = env.rat_sim in (* reuse existing rat_sim *)
    let int_sim = (* create a new int_sim with FM-Simplex encoding *)
      let sim = fm_simplex_unbounded_integers_encoding env uf in
      Sim.Solve.solve sim
    in
    let l1 = model_from_simplex rat_sim false env uf in
    let l2 = model_from_simplex int_sim true  env uf in
    List.fold_left mk_cs (List.fold_left mk_cs [] l1) l2

let mk_const_term c ty =
  match ty with
  | Ty.Tint -> E.Ints.of_Z (Q.to_z c)
  | Ty.Treal -> E.Reals.of_Q c
  | _ -> assert false

let case_split env uf ~for_model =
  let res = default_case_split env uf ~for_model in
  match res with
  | [] ->
    if not for_model then []
    else
      begin
        match case_split_union_of_intervals env uf with
        | [] -> model_from_infinite_domains env uf
        | l -> l
      end
  | _ -> res

(* Helper function used in [optimizing_objective] to pick a value
   for the polynomial [p] in its interval. We use this function to split the
   search space and bias it towards the optimum in the case the value produced
   by the optimization procedure doesn't satisfy some constraints that involve
   strict inequalities or the problem is unbounded. *)
let middle_value env ~is_max ty p bound =
  let interval =
    match MP0.find_opt p env.polynomes, bound with
    | Some i, Some bound ->
      begin
        try
          if is_max then
            I.new_borne_sup Ex.empty bound ~is_le:false i
          else
            I.new_borne_inf Ex.empty bound ~is_le:false i
        with I.NotConsistent _ -> assert false
      end
    | Some i, None -> i
    | None, _ -> I.point Q.zero ty Ex.empty
  in
  let q = I.pick ~is_max interval in
  alien_of (P.create [] q ty)

let optimizing_objective_for_ty ~is_max ty env uf e =
  (* soundness: if there are expressions to optmize, this should be
     done without waiting for ~for_model flag to be true *)
  let repr, _ = Uf.find uf e in
  let r1 = Uf.make uf e in (* instead of repr, which may be a constant *)
  let p = poly_of repr in
  match P.is_const p with
  | Some optim ->
    if Options.get_debug_optimize () then
      Printer.print_dbg "%a has the value %a@."
        E.print e
        Q.print optim;

    let r2 = alien_of (P.create [] optim  ty) in
    Debug.case_split r1 r2;
    let t2 = mk_const_term optim ty in
    let value = Objective.Value.Value t2 in
    let case_split =
      LR.mkv_eq r1 r2, true, Th_util.CS (Th_util.Th_arith, Q.one)
    in
    Th_util.{ value; case_split }

  | None ->
    begin
      let sim = if ty == Ty.Tint then env.int_sim else env.rat_sim in
      let p = if is_max then p else P.mult_const Q.m_one p in
      let l, c = P.to_list p in
      let l = List.rev_map (fun (x, y) -> y, x) (List.rev l) in
      let sim, mx_res = Sim.Solve.maximize sim (Sim.Core.P.from_list l) in
      match Sim.Result.get mx_res sim with
      | Sim.Core.Unknown ->
        (* The decision procedure is complete. *)
        assert false

      | Sim.Core.Sat _   ->
        (* This answer is only returned by OcplibSimplex if we only want to
           check the satisfability of the linear program. *)
        assert false

      | Sim.Core.Unsat _ ->
        (* We know that the linear program is satisfisable as we check it
           before. *)
        assert false

      | Sim.Core.Unbounded _ ->
        let value =
          if is_max then
            Objective.Value.Pinfinity
          else
            Objective.Value.Minfinity
        in
        (* As the problem is unbounded, we need to produce a value for the
           objective function. Rather than picking a value directly, we add a
           constraint to let the case split mechanism pick a "large" (or
           "small") value in the interval (otherwise, later objectives are
           computed while assuming that the middle value is forced, which is
           incorrect). *)
        let case_split =
          LR.mkv_builtin false LT
            [r1; middle_value env ~is_max ty p None],
          true,
          Th_util.CS (Th_util.Th_arith, Q.one)
        in
        Th_util.{ value; case_split }

      | Sim.Core.Max (lazy Sim.Core.{ max_v; is_le }, _sol) ->
        let max_p = Q.add max_v.bvalue.v c in
        let optim = if is_max then max_p else Q.mult Q.m_one max_p in
        if Options.get_debug_optimize () then
          begin
            if is_le then
              Printer.print_dbg "%a has a %s: %a@." Expr.print e
                (if is_max then "maximum" else "minimum") Q.print optim
            else
              Printer.print_dbg "%a is a %s bound of %a" Q.print optim
                (if is_max then "upper" else "lower") Expr.print e
          end;
        let r2 = alien_of (P.create [] optim ty) in
        Debug.case_split r1 r2;
        let t2 = mk_const_term optim ty in
        let value =
          if is_le then
            Objective.Value.Value t2
          else
            begin
              if is_max then Objective.Value.Limit (Below, t2)
              else Objective.Value.Limit (Above, t2)
            end
        in
        let r2 =
          if is_le then
            r2
          else
            (* As some bounds are strict, the value [r2] does not satisfy the
               constraints of the problem. In this case, we pick a value
               in the domain of the polynomial [p]. But we propagate the new
               value [value] for this objective. Indeed, we want to be able
               to print it while using the statement [get-objective]. *)
            let q =
              match P.is_const (poly_of r2) with
              | Some q -> q
              | None -> assert false
            in
            middle_value env ~is_max ty p (Some q)
        in
        let case_split =
          LR.mkv_eq r1 r2, true, Th_util.CS (Th_util.Th_arith, Q.one)
        in
        { value; case_split }
    end

let optimizing_objective env uf Objective.Function.{ e; is_max; _ } =
  match E.type_info e with
  | Tint | Treal as ty ->
    Some (optimizing_objective_for_ty ~is_max ty env uf e)
  | _ -> None

(*** part dedicated to FPA reasoning ************************************)

let best_interval_of optimized env p =
  (* p is supposed to be in normal_form_pos *)
  match P.is_const p with
  | Some c -> env, I.point c (P.type_info p) Explanation.empty
  | None ->
    let i =
      try let i, _, _ = generic_find (alien_of p) env in i
      with Not_found -> I.undefined (P.type_info p)
    in
    if SP.mem p !optimized then env, i
    else
      try
        let j = Sim_Wrap.infer_best_bounds env p in
        optimized := SP.add p !optimized;
        let k = I.intersect i j in
        if not (I.is_strict_smaller k i) then env, i
        else
          let env = MP.n_add p k i env in
          Sim_Wrap.solve env 1, k
      with I.NotConsistent expl ->
        if true (*get_debug_fpa() >= 2*) then begin
          [@ocaml.ppwarning "TODO: find an example triggering this case!"]
          Printer.print_wrn
            "TODO: should check that this is correct !!!";
          Errors.warning_as_error ()
        end;
        raise (Ex.Inconsistent (expl, env.classes))

let mk_const_term ty s =
  match ty with
  | Ty.Tint -> E.int (Q.to_string s)
  | Ty.Treal -> E.real (Q.to_string s)
  | _ -> assert false

let integrate_mapsTo_bindings sbs maps_to =
  try
    let sbs =
      List.fold_left
        (fun ((sbt, sty) as sbs) (x, tx) ->
           assert (not (Var.Map.mem x sbt));
           let t = E.apply_subst sbs tx in
           let mk, _ = X.make t in
           match P.is_const (poly_of mk) with
           | None ->
             if get_debug_fpa () >= 2 then
               Printer.print_dbg
                 ~module_name:"IntervalCalculus"
                 ~function_name:"integrate_maps_to_bindings"
                 "bad semantic trigger %a |-> %a@,\
                  left-hand side is not a constant!"
                 Var.print x E.print tx;
             raise Exit
           | Some c ->
             let tc = mk_const_term (E.type_info t) c in
             Var.Map.add x tc sbt, sty
        )sbs maps_to
    in
    Some sbs
  with Exit -> None

let extend_with_domain_substitution =
  (* TODO : add the ability to modify the value of epsilon ? *)
  let eps = Q.div_2exp Q.one 1076 in
  let aux idoms sbt =
    Var.Map.fold
      (fun v_hs (lv, uv, ty) sbt ->
         if Var.is_local v_hs then sbt
         else
           let lb_var = v_hs in
           let lb_val = match lv, uv with
             | None, None -> raise Exit
             | Some (q1, false), Some (q2, false) when Q.equal q1 q2 ->
               mk_const_term ty q1

             | Some (q1,_), Some (q2,_) ->
               Printer.print_err
                 "[Error] %a <= %a <= %a@,\
                  Which value should we choose?"
                 Q.print q1
                 Var.print lb_var
                 Q.print q2;
               assert (Q.compare q2 q1 >= 0);
               assert false

             | Some (q, is_strict), None -> (* hs > q or hs >= q *)
               mk_const_term ty (if is_strict then Q.add q eps else q)

             | None, Some (q, is_strict) -> (* hs < q or hs <= q *)
               mk_const_term ty (if is_strict then Q.sub q eps else q)
           in
           Var.Map.add lb_var lb_val sbt
      ) idoms sbt
  in
  fun (sbt, sbty) idoms ->
    try Some (aux idoms sbt, sbty)
    with Exit ->
      if get_debug_fpa() >=2 then
        Printer.print_dbg
          "extend_with_domain_substitution failed!";
      None

let terms_linear_dep { linear_dep ; _ } lt =
  match lt with
  | [] | [_] -> true
  | e::l ->
    try
      let st = ME.find e linear_dep in
      List.for_all (fun t -> SE.mem t st) l
    with Not_found -> false

exception Sem_match_fails of t

let domain_matching _lem_name tr sbt env uf optimized =
  try
    let idoms, maps_to, env, _uf =
      List.fold_left
        (fun (idoms, maps_to, env, uf) s ->
           match s with
           | E.MapsTo (x, t) ->
             (* this will be done in the latest phase *)
             idoms, (x, t) :: maps_to, env, uf

           | E.Interval (t, lb, ub) ->
             let tt = E.apply_subst sbt t in
             assert (E.is_ground tt);
             let uf, _ = Uf.add uf tt in
             let rr, _ex = Uf.find uf tt in
             let p = poly_of rr in
             let p', c', d = P.normal_form_pos p in
             let env, i' = best_interval_of optimized env p' in
             let i = I.affine_scale ~coef:d ~const:(Q.mult d c') i' in
             begin match I.match_interval lb ub i idoms with
               | None -> raise (Sem_match_fails env)
               | Some idoms -> idoms, maps_to, env, uf
             end

           | E.NotTheoryConst t ->
             let tt = E.apply_subst sbt t in
             let uf, _ = Uf.add uf tt in
             if X.leaves (fst (Uf.find uf tt)) == [] ||
                X.leaves (fst (X.make tt)) == [] then
               raise (Sem_match_fails env);
             idoms, maps_to, env, uf

           | E.IsTheoryConst t ->
             let tt = E.apply_subst sbt t in
             let uf, _ = Uf.add uf tt in
             let r, _ = X.make tt in
             if X.leaves r != [] then raise (Sem_match_fails env);
             idoms, maps_to, env, uf

           | E.LinearDependency (x, y) ->
             let x = E.apply_subst sbt x in
             let y = E.apply_subst sbt y in
             if not (terms_linear_dep env [x;y]) then
               raise (Sem_match_fails env);
             let uf, _ = Uf.add uf x in
             let uf, _ = Uf.add uf y in
             idoms, maps_to, env, uf
        )(Var.Map.empty, [], env, uf) tr.E.semantic
    in
    env, Some (idoms, maps_to)
  with Sem_match_fails env -> env, None


let semantic_matching lem_name tr sbt env uf optimized =
  match domain_matching lem_name tr sbt env uf optimized with
  | env, None -> env, None
  | env, Some(idom, mapsTo) ->
    begin match extend_with_domain_substitution sbt idom with
      | None -> env, None
      | Some sbs -> env, integrate_mapsTo_bindings sbs mapsTo
    end

let record_this_instance f accepted lorig =
  if Options.get_profiling() then
    match E.form_view lorig with
    | E.Lemma { E.name; loc; _ } ->
      Profiling.new_instance_of name f loc accepted
    | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
    | E.Let _ | E.Iff _ | E.Xor _ -> assert false

let profile_produced_terms menv lorig nf s trs =
  if Options.get_profiling() then
    let st0 =
      List.fold_left (fun st t -> E.sub_terms st (E.apply_subst s t))
        SE.empty trs
    in
    let name, loc, _ = match E.form_view lorig with
      | E.Lemma { E.name; main; loc; _ } -> name, loc, main
      | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
      | E.Let _ | E.Iff _ | E.Xor _ -> assert false
    in
    let st1 = E.max_ground_terms_rec_of_form nf in
    let diff = SE.diff st1 st0 in
    let info, _ = EM.terms_info menv in
    let _new = SE.filter (fun t -> not (ME.mem t info)) diff in
    Profiling.register_produced_terms name loc st0 st1 diff _new

let new_facts_for_axiom
    ~do_syntactic_matching menv uf selector optimized substs accu =
  List.fold_left
    (fun acc ({trigger_formula=f; trigger_age=age; trigger_dep=dep;
               trigger_orig=orig; trigger = tr; trigger_increm_guard},
              subst_list) ->
      List.fold_left
        (fun (env, acc)
          {sbs = sbs;
           sty = sty;
           gen = g;
           goal = b;
           s_term_orig = torig;
           s_lem_orig = lorig} ->
                (*
                  Here, we'll try to extends subst 's' to conver variables
                  appearing in semantic triggers
                *)
          let lem_name = E.name_of_lemma orig in
          let s = sbs, sty in
          if get_debug_fpa () >= 2 then
            Printer.print_dbg ~flushed:false
              ~module_name:"IntervalCalculus"
              ~function_name:"new_facts_for_axiom"
              "try to extend synt sbt %a of ax %a@ "
              (Var.Map.pp E.print) sbs E.print orig;
          if tr.E.semantic == [] && not do_syntactic_matching then
            (* pure syntactic insts already generated *)
            env, acc

          else if not (terms_linear_dep env torig) then (
            if get_debug_fpa () >= 2 then
              Printer.print_dbg
                ~header:false
                "semantic matching failed(1)";
            env, acc

          ) else
            match semantic_matching lem_name tr s env uf optimized with
            | env, None ->
              if get_debug_fpa () >= 2 then
                Printer.print_dbg
                  ~header:false
                  "semantic matching failed(2)";
              env, acc
            | env, Some sbs ->
              if get_debug_fpa () >= 2 then
                Printer.print_dbg
                  ~header:false
                  "semantic matching succeeded:@ %a"
                  (Var.Map.pp E.print) (fst sbs);
              let nf = E.apply_subst sbs f in
              (* incrementality/push. Although it's not supported for
                 theories *)
              let nf = E.mk_imp trigger_increm_guard nf in
              let accepted = selector nf orig in
              record_this_instance nf accepted lorig;
              if accepted then begin
                let hyp =
                  List.map (fun f -> E.apply_subst sbs f) tr.E.hyp
                in
                let p =
                  { E.ff = nf;
                    origin_name = E.name_of_lemma lorig;
                    trigger_depth = tr.E.t_depth;
                    gdist = -1;
                    hdist = -1;
                    nb_reductions = 0;
                    age = 1+(max g age);
                    mf = true;
                    gf = b;
                    lem = Some lorig;
                    from_terms = torig;
                    (* does'nt work if a 'gf' with theory_elim = true
                       was already assumed in the SAT !!! *)
                    theory_elim = false;
                  }
                in
                profile_produced_terms menv lorig nf s tr.E.content;
                let dep =
                  if not (Options.get_unsat_core() || Options.get_profiling())
                  then
                    dep
                  else Ex.union dep (Ex.singleton (Ex.Dep lorig))
                in
                env, (hyp, p, dep) :: acc
              end
              else (* instance not 'accepted' *)
                env, acc
        ) acc subst_list
    ) accu substs


let syntactic_matching menv env uf _selector =
  let mconf =
    {Util.nb_triggers = get_nb_triggers ();
     no_ematching = get_no_ematching();
     triggers_var = get_triggers_var ();
     use_cs = false;
     backward = Util.Normal;
     greedy = get_greedy ();
    }
  in
  let synt_match =
    ME.fold
      (fun f (_th_ax, dep) accu ->
         (* currently, No diff between propagators and case-split axs *)
         let forms = ME.singleton f (E.vrai, 0 (*0 = age *), dep) in
         let menv = EM.add_triggers mconf menv forms in
         let res = EM.query mconf menv uf in
         if get_debug_fpa () >= 2 then begin
           let cpt = ref 0 in
           List.iter (fun (_, l) -> List.iter (fun _ -> incr cpt) l) res;
           Printer.print_dbg
             ~module_name:"IntervalCalculus"
             ~function_name:"syntactic_matching"
             "syntactic matching of Ax %s: got %d substs"
             (E.name_of_lemma f) !cpt
         end;
         res:: accu
      )env.th_axioms []
  in
  {env with syntactic_matching = synt_match}

let instantiate ~do_syntactic_matching match_terms env uf selector =
  if get_debug_fpa () >= 2 then
    Printer.print_dbg
      ~module_name:"IntervalCalculus" ~function_name:"instanciate"
      "entering IC.instantiate";
  let optimized = ref (SP.empty) in
  let t_infos, t_subterms = match_terms in
  let menv = EM.make ~max_t_depth:100 t_infos t_subterms [] in
  let env =
    if not do_syntactic_matching then env
    else syntactic_matching menv env uf selector
  in
  let env, insts =
    List.fold_left
      (fun accu substs ->
         new_facts_for_axiom
           ~do_syntactic_matching menv uf selector optimized substs accu
      )(env, []) env.syntactic_matching
  in
  if get_debug_fpa () >= 2 then
    Printer.print_dbg
      ~module_name:"IntervalCalculus" ~function_name:"instanciate"
      "IC.instantiate: %d insts generated" (List.length insts);
  env, insts


let assume_th_elt t th_elt dep =
  let { Expr.axiom_kind; ax_form; th_name; extends; _ } = th_elt in
  let kd_str =
    if axiom_kind == Util.Propagator then "Th propagator" else "Th CS"
  in
  match extends with
  | Util.NIA | Util.NRA | Util.FPA | Util.RIA ->
    if get_debug_fpa () >= 2 then
      Printer.print_dbg
        ~module_name:"IntervalCalculus" ~function_name:"assume_th_elt"
        "[Theory %s][%s] %a"
        th_name kd_str E.print ax_form;
    assert (not (ME.mem ax_form t.th_axioms));
    {t with th_axioms = ME.add ax_form (th_elt, dep) t.th_axioms}

  | _ -> t

let assume = assume ~query:false

let instantiate ~do_syntactic_matching env uf selector =
  Timers.with_timer timer Timers.F_instantiate @@ fun () ->
  instantiate ~do_syntactic_matching env uf selector

let reinit_cache () =
  let module Oracle = (val get_oracle ()) in
  Oracle.reset_age_cpt ();
  EM.reinit_caches ()

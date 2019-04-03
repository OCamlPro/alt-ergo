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

module Z = Numbers.Z
module Q = Numbers.Q

module X = Shostak.Combine

module P = Shostak.Polynome
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
    if is_alien x then Format.fprintf fmt "%a" X.print x
    else Format.fprintf fmt "s!%d" (X.hash x) (* slake vars *)
end

module Sim = OcplibSimplex.Basic.Make(SimVar)(Q)(Explanation)

module M =
struct
  include Map.Make(P)
  let find_opt v m = (* For 4.4 compatibility *)
    try Some (find v m) with Not_found -> None
end

let r : X.r = X.term_embed (Expr.fresh_name Ty.Tint)

type solution = ((P.r * Z.t) list)

let cubetest (p : P.t) : P.t * Q.t =
  let coef_list, cst = P.to_list p in
  (* p(X) <= 0
     => p(X) - cst <= -cst
     => q(X) <= -cst  *)

  let k = (* k = - cst - 1/2 * Sum (|coef|) *)
    let sum =
      List.fold_left
        (fun acc (c,_) -> Q.add acc @@ Q.abs c)
        Q.zero
        coef_list
    in
    (Q.div sum @@ Q.from_int 2)
  in
  let q = (* q = (real) q *)
    P.create ((k, r) :: coef_list) Q.zero Ty.Treal in
  q,(Q.minus cst)


  (*
  let coef_list, cst = P.to_list p in
  (* p(X) <= 0
     => p(X) - cst <= -cst
     => q(X) <= -cst  *)

  let k = (* k = - cst - 1/2 * Sum (|coef|) *)
    let sum =
      List.fold_left
        (fun acc (c,_) -> Q.add acc @@ Q.abs c)
        Q.zero
        coef_list
    in
    Q.sub
      (Q.minus cst)
      (Q.div sum @@ Q.from_int 2)
  in
  let q = (* q = (real) q *)
    P.create coef_list Q.zero Ty.Treal in
  q,k*)
(*
  let q' = (* q' = q + k *)
      q
    |> P.add (P.create [] k Ty.Treal)
  in
  q'
*)
type bound = Q.t * Q.t (* The second val sets *)

let cubetest_sort (p_list : P.t list)
  : (bound option * bound option) M.t =

  let add_to_map
      (acc : (bound option * bound option) M.t)
      (p : P.t) =
    let q,k = cubetest p in (* q(X) <= 0 *)
    match M.find_opt q acc with
      Some (lower, None) ->
      M.add q (lower, Some (k, Q.zero)) acc

    | Some (lower, Some (upper,_)) ->
      M.add q (lower, Some (Q.min k upper, Q.zero)) acc

    | None (* Maybe -q is already inside ? *) ->
      let q',k' = P.mult_const Q.m_one q, Q.minus k in
      match M.find_opt q' acc with
        Some (None, upper) -> (* A new lower bound is added *)
        M.add q' ((Some (k', Q.zero)), upper) acc

      | Some (Some (lower,_), upper) ->
        M.add q' ((Some (Q.max lower k', Q.zero)),upper) acc

      | None -> (* q has never been seen *)
        M.add q (None, Some (k, Q.zero)) acc
  in
  List.fold_left
    add_to_map
    M.empty
    p_list

let cube_center_simplex (p_list : P.t list) : Sim.Core.t =
  let simp =
    Sim.Solve.solve
      (Sim.Core.empty ~is_int:false ~check_invs:false ~debug:0) in
  let poly_bounds = cubetest_sort p_list in
  let add_and_test p (new_mn, new_mx) (s : Sim.Core.t) =
    (* assert P.normal_form_pos p = p; *)
    let l, z = P.to_list p in
    assert (Q.sign z = 0);
    let new_simplex, _ =
      match l with
        [] -> assert false
      | [c, x] ->
        assert (Q.is_one @@ Q.abs c);
        if Q.sign c > 0
        then
          Sim.Assert.var s x new_mn Explanation.empty new_mx Explanation.empty
        else
          let op_bound (bound : bound option) =
            match bound with
              None -> None
            | Some (b,c) -> Some (Q.minus b, c) in
          Sim.Assert.var
            s
            x
            (op_bound new_mx)
            Explanation.empty
            (op_bound new_mn)
            Explanation.empty
      | _ ->
        let l = List.rev_map (fun (c, x) -> x, c) l in
        Sim.Assert.poly s (Sim.Core.P.from_list l) (alien_of p)
          new_mn Explanation.empty new_mx Explanation.empty
    in new_simplex
  in
  M.fold
    add_and_test
    poly_bounds
    simp

(** Returns the closest integer vector (considering norm_1) from the input
    rational vector.
    Doesn't round the radius variable r if used. *)
let get_closest  (z : (X.r * Q.t) list) : solution =
  let apprx =
    fun ((r,v) : ('a * Q.t)) : ('a * Z.t) ->
      let v' = (if Q.sign v < 0 then Q.ceiling else Q.floor) v in
      if Q.compare (Q.abs @@ Q.sub v v') (Q.from_float 0.5) < 0
      then r, (Q.to_z v')
      else r, Q.to_z ((if Q.sign v < 0 then Q.sub else Q.add) v' Q.one)
  in
  List.fold_left
    (fun acc ((x,_) as mon) ->
       if X.equal x r
       then acc
       else if is_alien x then  (apprx mon) :: acc else acc
    )
    []
    z

let integer_sol_if_exists (result : Sim.Core.result)
  : solution option =
  match result with
    Unknown
  | Unbounded _
  | Max (_, _) -> assert false
  | Unsat _ -> None

  | Sat sol ->
    let q_sol =
      (Lazy.force sol).main_vars @ (Lazy.force sol).slake_vars in
    Some (get_closest q_sol)

let integer_sol_if_max
    s
    (result : Sim.Core.result)
  : (solution * bool) option =
  match result with
    Unknown
  | Sat _ -> assert false
  | Unsat _ -> None

  | Unbounded _sols -> (* Check if the radius is unbounded *)
    let s, _ =
      Sim.Assert.var s r
        (Some (Q.one, Q.zero))
        Explanation.empty
        None
        Explanation.empty
    in
    let s, t =
      Sim.Solve.maximize s @@ Sim.Core.P.from_list [r,Q.one] in
    begin match Sim.Result.get t s with
      | Unbounded sol ->
        let q_sol =
          (Lazy.force sol).main_vars @
          (Lazy.force sol).slake_vars in
        Some (get_closest q_sol, true)
      | _ -> assert false
    end
  | Max (max, sol) ->
    let q_sol =
      (Lazy.force sol).main_vars @ (Lazy.force sol).slake_vars in
    let closest = get_closest q_sol in
    let max = (Lazy.force max).max_v in
    Some (closest, (Q.compare max Q.one >= 0))

let cubefast (p_list : P.t list) : solution option =
  cube_center_simplex p_list
  |> Sim.Solve.solve
  |> Sim.Result.get None
  |> integer_sol_if_exists

let apply_subst r l =
  List.fold_left (fun r (p,v) -> P.subst p v r) r l

(* Checks if the integer solution is inside the polyhedron *)
let check_sol (p_list : P.t list) (sol : solution) : bool =
  let res_poly =
    List.map (fun (x,v) -> (x,P.create [] (Q.from_z v) Ty.Tint)) sol in
  List.for_all
    (fun p ->
       let poly_const =
         apply_subst p res_poly in
       match P.to_list poly_const with
         [], c -> Q.sign c <= 0
       | _ -> (* Every variable should have been replaced *)
         assert false
    )
    p_list

let cubefast_k (p_list : P.t list) : (solution * bool) option =
  cube_center_simplex p_list
  |> (fun s -> Sim.Solve.maximize s @@ Sim.Core.P.from_list [r,Q.one])
  |> (fun (s,t) -> Sim.Result.get t s, s)
  |> (fun (sol,s) -> integer_sol_if_max s sol)
  |> (fun sol ->
      match sol with
        None -> None
      | Some (_, true) -> sol
      | Some (s, false) ->
        Some (s, check_sol p_list s)
    )

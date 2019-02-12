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

module Q = Numbers.Q

module Ex = Explanation

type borne =
  | Strict of (Q.t * Ex.t)
  | Large of (Q.t * Ex.t)
  | Pinfty | Minfty

type t = {
  ints : (borne * borne) list;
  is_int : bool;
  expl: Ex.t
}

exception NotConsistent of Ex.t
exception No_finite_bound

(*BISECT-IGNORE-BEGIN*)
module Debug = struct

  let print_borne fmt = function
    | Minfty -> fprintf fmt "-inf"
    | Pinfty -> fprintf fmt "+inf"
    | Strict (v, e) | Large (v, e) ->
      fprintf fmt "%s" (Q.to_string v);
      if verbose () || unsat_core () then fprintf fmt " %a" Ex.print e

  let print_interval fmt (b1,b2) =
    let c1, c2 = match b1, b2 with
      | Large _, Large _ -> '[', ']'
      | Large _, _ -> '[', '['
      | _, Large _ -> ']', ']'
      | _, _ -> ']', '['
    in
    fprintf fmt "%c%a;%a%c" c1 print_borne b1 print_borne b2 c2

  let print_list fmt = function
    | [] -> fprintf fmt "[empty]"
    | e::l ->
      print_interval fmt e;
      List.iter (fprintf fmt " U %a" print_interval) l

  let print fmt { ints; expl = e; _ } =
    print_list fmt ints;
    if verbose () || unsat_core () then fprintf fmt " %a" Ex.print e

end
(*BISECT-IGNORE-END*)

let print = Debug.print
let pretty_print = Debug.print


let large_borne_of  n e = Large  (n, e)
let strict_borne_of n e = Strict (n, e)

let undefined_int  = {ints = [Minfty, Pinfty]; is_int = true ; expl = Ex.empty}
let undefined_real = {ints = [Minfty, Pinfty]; is_int = false; expl = Ex.empty}

let undefined ty = match ty with
  | Ty.Tint  -> undefined_int
  | Ty.Treal -> undefined_real
  | _ -> assert false

let is_undefined t = match t.ints with
  | [Minfty, Pinfty] -> true
  | _ -> false

let point b ty e = {
  ints = [Large (b, e), Large (b, e)];
  is_int = ty == Ty.Tint;
  expl = e
}

let is_point { ints = l; expl = e; _ } =
  match l with
  | [Large (v1, e1) , Large (v2, e2)] when Q.equal v1 v2 ->
    Some (v1, Ex.union e (Ex.union e1 e2))
  | _ -> None

let finite_size { ints = l; is_int = is_int; _ } =
  if not is_int then None
  else
    try
      let acc = ref [] in
      List.iter
        (fun (b1, b2) ->
           match b1, b2 with
           | Minfty, _ | _, Pinfty -> raise Exit
           | Large (v1, _) , Large (v2, _) -> acc := (v1, v2) :: !acc
           | _, _ -> assert false
        )l;
      let res =
        List.fold_left
          (fun n (v1, v2) -> Q.add n (Q.add (Q.sub v2 v1) Q.one)) Q.zero !acc
      in
      Some res
    with Exit -> None

let borne_inf = function
  | { ints = (Large (v, ex), _) :: _; _ } -> v, ex, true
  | { ints = (Strict (v, ex), _) :: _; _ } -> v, ex, false
  | _ -> raise No_finite_bound

let borne_sup { ints; _ } =
  match List.rev ints with
  | (_, Large (v, ex))::_ -> v, ex, true
  | (_, Strict (v, ex))::_ -> v, ex, false
  | _ -> raise No_finite_bound

let explain_borne = function
  | Large (_, e) | Strict (_, e) -> e
  | _ -> Ex.empty

let add_expl_to_borne b e =
  if Ex.is_empty e then b
  else
    match b with
    | Large (n, e') -> Large (n, Ex.union e e')
    | Strict (n, e') -> Strict (n, Ex.union e e')
    | Pinfty | Minfty -> b

let add_expl_zero i expl =
  if Ex.is_empty expl then i
  else
    let res =
      List.rev_map (fun x ->
          match x with
          | Large (c1,e1), Large (c2,e2) when Q.sign c1 = 0 && Q.sign c2 = 0 ->
            Large (Q.zero, Ex.union e1 expl), Large (Q.zero, Ex.union e2 expl)
          | _ -> x
        ) i.ints
    in
    { i with ints = List.rev res }

let int_of_borne_inf b =
  match b with
  | Minfty | Pinfty -> b
  | Large (v, e) -> Large ((if Q.is_int v then v else Q.ceiling v), e)
  | Strict (v, e) ->
    if Q.is_int v then Large (Q.add v Q.one, e)
    else
      let v' = Q.ceiling v in
      assert (Q.compare v' v > 0);
      Large (v', e)

let int_of_borne_sup b =
  match b with
  | Minfty | Pinfty -> b
  | Large (v, e) -> Large ((if Q.is_int v then v else Q.floor v), e)
  | Strict (v, e) ->
    if Q.is_int v then Large (Q.sub v Q.one, e)
    else
      let v' = Q.floor v in
      assert (Q.compare v' v < 0);
      Large (v', e)

let int_bornes (l, u) = int_of_borne_inf l, int_of_borne_sup u

let compare_bounds b1 ~is_low1 b2 ~is_low2 =
  match b1, b2 with
  | Minfty, Minfty | Pinfty, Pinfty -> 0
  | Minfty, _ | _, Pinfty -> -1
  | _, Minfty | Pinfty, _ -> 1

  | Large (v1, _), Large (v2, _) -> Q.compare v1 v2

  | Strict (v1, _), Strict (v2, _) ->
    let c = Q.compare v1 v2 in
    if c <> 0 then c
    else if is_low1 == is_low2 then 0  (* bl_bl or bu_bu *)
    else if is_low1 then 1  (* implies not is_low2 *)
    else -1  (* implies not is_low1 and is_low2 *)

  | Strict (v1, _), Large (v2, _) ->
    let c = Q.compare v1 v2 in
    if c <> 0 then c else if is_low1 then 1 else -1

  | Large (v1, _), Strict (v2, _) ->
    let c = Q.compare v1 v2 in
    if c <> 0 then c else if is_low2 then -1 else 1

let zero_endpoint b =
  match b with
  | Large (v, _) -> Q.is_zero v
  | _ -> false

let min_of_lower_bounds b1 b2 =
  if compare_bounds b1 ~is_low1:true b2 ~is_low2:true <= 0 then b1 else b2

let max_of_upper_bounds b1 b2 =
  if compare_bounds b1 ~is_low1:false b2 ~is_low2:false >= 0 then b1 else b2

let zero_large = Large (Q.zero, Ex.empty)

let low_borne_pos_strict b =
  compare_bounds b ~is_low1:true zero_large ~is_low2:true > 0

let up_borne_pos_strict b =
  compare_bounds b ~is_low1:false zero_large ~is_low2:false > 0

let low_borne_neg_strict b =
  compare_bounds b ~is_low1:true zero_large ~is_low2:true < 0

let up_borne_neg_strict b =
  compare_bounds b ~is_low1:false zero_large ~is_low2:false < 0


(* should be removed: probably buggy when mixing lower and upper bounds *)
let pos_borne b = match b with
  | Pinfty -> true
  | Minfty -> false
  | Strict (v, _) | Large (v, _) -> Q.sign v >= 0

(* should be removed: probably buggy when mixing lower and upper bounds *)
let neg_borne b = match b with
  | Pinfty -> false
  | Minfty -> true
  | Strict (v, _) | Large (v, _) -> Q.sign v <= 0

(* TODO: generalize the use of this type and the function joint below
   to other operations on intervals *)
type kind =
  | Empty of Explanation.t
  | Int of (borne * borne)

let join l glob_ex = (* l should not be empty *)
  let rec j_aux _todo _done =
    match _todo, _done with
    | [], [] -> assert false
    | [], _  -> List.rev _done, None
    | [Empty ex], []  -> [], Some ex
    | (Int b) :: l, _ -> j_aux l (b :: _done)
    | (Empty ex) :: l, _ ->
      let _done = match _done with
        | [] -> []
        | (low, up) :: r -> (low, add_expl_to_borne up ex) :: r
      in
      let _todo = match l with
        | [] -> []
        | (Empty ex') :: r -> (Empty (Ex.union ex ex')) :: r
        | (Int (low, up)) :: r -> (Int (add_expl_to_borne low ex, up)) :: r
      in
      j_aux _todo _done
  in
  match j_aux l [] with
  | [], None    -> assert false
  | l , None    -> l
  | [], Some ex -> raise (NotConsistent (Ex.union ex glob_ex));
  | _ , Some _  -> assert false


let intersect =
  let rec step is_int l1 l2 acc =
    match l1, l2 with
    | [], _ | _, [] ->  List.rev acc

    | (_, up1) :: r1, (lo2, _) :: _ when
        compare_bounds up1 ~is_low1:false lo2 ~is_low2:true < 0 ->
      (* No overlap. (lo1, up1) is smaller *)
      let nexpl  = Ex.union (explain_borne up1) (explain_borne lo2) in
      step is_int r1 l2 ((Empty nexpl) :: acc)

    | (lo1, _) :: _, (_, up2) :: r2 when
        compare_bounds lo1 ~is_low1:true up2 ~is_low2:false > 0 ->
      (* No overlap. (lo2, up2) is smaller *)
      let nexpl  = Ex.union (explain_borne up2) (explain_borne lo1) in
      step is_int l1 r2 ((Empty nexpl) :: acc)

    | (lo1, up1)::r1, (lo2, up2)::r2 ->
      let cll = compare_bounds lo1 ~is_low1:true lo2 ~is_low2:true in
      let cuu = compare_bounds up1 ~is_low1:false up2 ~is_low2:false in
      if cll <= 0 && cuu >= 0 then (* (lo1, up1) subsumes (lo2, up2) *)
        step is_int l1 r2 ((Int (lo2,up2))::acc) (* ex of lo1 and up1 ? *)
      else
      if cll >= 0 && cuu <= 0 then (* (lo2, up2) subsumes (lo1, up1) *)
        step is_int r1 l2 ((Int(lo1,up1))::acc) (* ex of lo2 and up2 ? *)
      else
      if cll <= 0 && cuu <= 0 then (* lo1 <= lo2 <=  up1 <= up2 *)
        step is_int r1 l2 ((Int(lo2,up1))::acc) (* ex of lo1 and up2 ? *)
      else
      if cll >= 0 && cuu >= 0 then (* lo2 <= lo1 <=  up2 <= up1 *)
        step is_int l1 r2 (Int((lo1,up2))::acc) (* ex of lo2 and up1 ? *)
      else assert false
  in
  fun
    ({ints=l1; expl=e1; is_int=is_int} as uints1)
    { ints = l2; expl = e2; _ } ->
    (*l1 and l2 are supposed to be normalized *)
    let expl = Ex.union e1 e2 in
    let l = step is_int l1 l2 []  in
    let res = { uints1 with ints = join l expl; expl } in
    assert (res.ints != []);
    res

let new_borne_sup expl b ~is_le uints =
  let aux b expl =
    let b = (if is_le then large_borne_of else strict_borne_of) b expl in
    if uints.is_int then int_of_borne_sup b else b
  in
  intersect
    { ints = [Minfty, aux b expl];
      is_int = uints.is_int;
      expl = Ex.empty } uints

let new_borne_inf expl b ~is_le uints =
  let aux b expl =
    let b = (if is_le then large_borne_of else strict_borne_of) b expl in
    if uints.is_int then int_of_borne_inf b else b
  in
  intersect
    { ints = [aux b expl, Pinfty];
      is_int = uints.is_int;
      expl = Ex.empty } uints

type interval_class =
  | P
  | M
  | N
  | Z

let class_of l u =
  if zero_endpoint l && zero_endpoint u then Z
  else if pos_borne l && pos_borne u then begin
    assert (up_borne_pos_strict u);
    P
  end
  else if neg_borne l && neg_borne u then begin
    assert (low_borne_neg_strict l);
    N
  end
  else begin
    assert (low_borne_neg_strict l);
    assert (up_borne_pos_strict u);
    M
  end

let union_bornes is_int l =
  let rec aux is_int l acc =
    match l with
    | [] -> acc
    | [e] -> e::acc
    | (l1, u1)::((l2, u2)::r as r2) ->
      if compare_bounds u1 ~is_low1:false l2 ~is_low2:true < 0 then
        match is_int, u1, l2 with
        | true, Large(x,_), Large (y, _) when Q.equal (Q.sub y x) Q.one ->
          aux is_int ((l1, u2)::r) acc
        | _ ->
          (* the only case where we put things in acc *)
          aux is_int r2 ((l1, u1)::acc)
      else
      if compare_bounds u1 ~is_low1:false u2 ~is_low2:false > 0 then
        aux is_int ((l1, u1)::r) acc
      else
        aux is_int ((l1, u2)::r) acc
  in
  List.rev (aux is_int l [])

let union_intervals uints =
  let l = List.fast_sort (fun (l1, _) (l2, _) ->
      compare_bounds l1 ~is_low1:true l2 ~is_low2:true) uints.ints in
  {uints with ints = union_bornes uints.is_int l}

let minus_borne = function
  | Minfty -> Pinfty
  | Pinfty -> Minfty
  | Large (v, e) -> Large (Q.minus v, e)
  | Strict (v, e) -> Strict (Q.minus v, e)

let rev_normalize_int_bounds rl ex n =
  let l =
    List.rev_map
      (fun b ->
         let b = int_bornes b in
         match b with
         | Large (v, ex1), Large (w, ex2) when Q.compare w v < 0 ->
           Empty (Ex.union ex1 ex2)
         | Strict (v, ex1), Large (w, ex2)
         | Large (v, ex1) , Strict (w, ex2)
         | Strict (v, ex1), Strict (w, ex2) when Q.compare w v <= 0 ->
           Empty (Ex.union ex1 ex2)
         | _ -> Int b
      ) rl
  in
  if Q.compare n Q.zero > 0 (* !!! this test should be checked *) then join l ex
  else List.rev (join (List.rev l) ex)


let exclude =
  let rec complement l prev acc =
    match l with
    | (b1,b2)::r ->
      let bu = match b1 with
        | Strict v -> Large v
        | Large v -> Strict v
        | _ -> b1
      in
      let bl = match b2 with
        | Strict v -> Large v
        | Large v -> Strict v
        | _ -> b2
      in
      if bu == Minfty then complement r bl acc
      else complement r bl ((prev, bu)::acc)
    | [] ->
      List.rev (if prev == Pinfty then acc else (prev, Pinfty)::acc)
  in
  fun uints1 uints2 ->
    let l_c = complement uints1.ints Minfty [] in
    let l_c =
      if uints2.is_int then List.rev (List.rev_map int_bornes l_c) else l_c
    in
    let uints1_c = union_intervals {uints1 with ints = l_c} in
    intersect uints1_c uints2

let scale_interval_zero n (b1, b2) =
  assert (Q.sign n = 0);
  Large (Q.zero, explain_borne b1), Large (Q.zero, explain_borne b2)

let scale_borne_non_zero n b =
  assert (Q.sign n > 0);
  match b with
  | Pinfty | Minfty -> b
  | Large (v, e) -> Large (Q.mult n v, e)
  | Strict (v, e) -> Strict (Q.mult n v, e)

let scale_interval_pos n (b1, b2) =
  scale_borne_non_zero n b1, scale_borne_non_zero n b2

let scale_interval_neg n (b1, b2) =
  minus_borne (scale_borne_non_zero (Q.minus n) b2),
  minus_borne (scale_borne_non_zero (Q.minus n) b1)

let scale n uints =
  Options.tool_req 4 "TR-Arith-Axiomes scale";
  if Q.equal n Q.one then uints
  else
    let sgn = Q.sign n in
    let aux =
      if sgn = 0 then scale_interval_zero
      else if sgn > 0 then scale_interval_pos
      else scale_interval_neg
    in
    let rl = List.rev_map (aux n) uints.ints in
    let l =
      if uints.is_int then rev_normalize_int_bounds rl uints.expl n
      else List.rev rl
    in
    let res = union_intervals { uints with ints = l } in
    assert (res.ints != []);
    res

let add_borne b1 b2 =
  match b1,b2 with
  | Minfty, Pinfty | Pinfty, Minfty -> assert false
  | Minfty, _ | _, Minfty -> Minfty
  | Pinfty, _ | _, Pinfty -> Pinfty
  | Large (v1, e1), Large (v2, e2) ->
    Large (Q.add v1 v2, Ex.union e1 e2)
  | (Large (v1, e1) | Strict (v1, e1)), (Large (v2, e2) | Strict (v2, e2)) ->
    Strict (Q.add v1 v2, Ex.union e1 e2)

let add_interval is_int l (b1,b2) =
  List.fold_right
    (fun (b1', b2') l ->
       let l1 = ((add_borne b1 b1'),(add_borne b2 b2'))::l in
       union_bornes is_int (l1)
    ) l []

let add {ints = l1; is_int = is_int; expl = e1} { ints = l2; expl = e2; _ } =
  let l =
    List.fold_left
      (fun l bs -> let i = add_interval is_int l1 bs in i@l) [] l2
  in
  let res = union_intervals { ints = l ; is_int; expl = Ex.union e1 e2 } in
  assert (res.ints != []);
  res

let sub i1 i2 = add i1 (scale Q.m_one i2)

let merge i1 i2 =
  union_intervals
    {ints = List.rev_append i1.ints i2.ints; is_int = i1.is_int;
     expl = Explanation.union i1.expl i2.expl}

let contains i q =
  List.exists
    (fun (b1, b2) ->
       begin
         match b1 with
         | Minfty -> true
         | Pinfty -> assert false
         | Large(v, _) -> Q.compare v q <= 0
         | Strict(v, _) -> Q.compare v q < 0
       end
       && begin
         match b2 with
         | Pinfty -> true
         | Minfty -> assert false
         | Large(v, _) -> Q.compare v q >= 0
         | Strict(v, _) -> Q.compare v q > 0
       end
    ) i.ints

let doesnt_contain_0 =
  let rec explain_no_zero l =
    match l with
    | [] -> assert false
    | (b1, b2) :: l ->
      let pos_strict_b1 = low_borne_pos_strict b1 in
      let pos_strict_b2 = up_borne_pos_strict b2 in
      if pos_strict_b1 && pos_strict_b2 then
        (* there is no negative values at all *)
        Some (Ex.union (explain_borne b1) (explain_borne b2), [])
      else
        begin
          (* we know l does not contain 0. So, these asserts should hold *)
          assert (not pos_strict_b1);
          assert (not pos_strict_b2);
          assert (low_borne_neg_strict b1);
          assert (up_borne_neg_strict b2);
          match l with
          | [] ->
            (* there is no positive values at all *)
            Some (Ex.union (explain_borne b1) (explain_borne b2), [])
          | (c1,_)::_ ->
            if low_borne_pos_strict c1 then
              Some (Ex.union (explain_borne b2) (explain_borne c1), [])
            else explain_no_zero l
        end
  in
  fun int ->
    if contains int Q.zero then None
    else explain_no_zero int.ints


let is_positive { ints; expl; _ } =
  match ints with
  | [] -> assert false
  | (lb,_)::_ -> if pos_borne lb then Some (expl, []) else None

let root_default_num v n =
  if n = 2 then Q.sqrt_default v else Q.root_default v n

let root_exces_num v n =
  if n = 2 then Q.sqrt_excess v else Q.root_excess v n

(* should be removed and replaced with compare_bounds, with makes distinction
   between lower and upper bounds *)
let compare_bornes b1 b2 =
  match b1, b2 with
  | Minfty, Minfty | Pinfty, Pinfty -> 0
  | Minfty, _ | _, Pinfty -> -1
  | Pinfty, _ | _, Minfty -> 1
  | Strict (v1, _), Strict (v2, _) | Large (v1, _), Large (v2, _)
  | Strict (v1, _), Large (v2, _) | Large (v1, _), Strict (v2, _) ->
    Q.compare v1 v2


let is_strict_smaller =
  let rec aux l1 l2 nb_eq sz_l1 sz_l2 =
    match l1, l2 with
      [], _ -> true, nb_eq, sz_l1, (sz_l2 + List.length l2)
    | _, [] -> false, nb_eq, (sz_l1 + List.length l1), sz_l2
    | b1::r1, b2::r2 ->
      let lo1, up1 = b1 in
      let lo2, up2 = b2 in
      let c_l1_l2 = compare_bounds lo1 ~is_low1:true lo2 ~is_low2:true in
      let c_u1_u2 = compare_bounds up1 ~is_low1:false up2 ~is_low2:false in
      let c_l1_u2 = compare_bounds lo1 ~is_low1:true up2 ~is_low2:false in
      let c_u1_l2 = compare_bounds up1 ~is_low1:false lo2 ~is_low2:true in
      if c_l1_l2 = 0 && c_u1_u2 = 0 then
        aux r1 r2 (nb_eq + 1) (sz_l1 + 1) (sz_l2 + 1)
      else
      if c_l1_l2 >= 0 && c_u1_u2 <= 0 then (* without being equal *)
        (* b1 \subset b2! look for inclusion of r1 in l2 *)
        aux r1 l2 nb_eq (sz_l1 + 1) sz_l2
      else
      if c_l1_u2 >= 0 then
        (*ignore b2, and look for inclusion of l1 in r2*)
        aux l1 r2 nb_eq sz_l1 (sz_l2 + 1)
      else
      if c_u1_l2 < 0 then
        raise Exit(* b1 is not included in any part of l2*)
      else
      if c_l1_l2 <= 0 && c_u1_u2 >= 0 then (* without being equal *)
        raise Exit (*no inclusion, we have b2 \subset b1 !! *)
      else
      if c_l1_l2 < 0 && c_u1_u2 < 0 ||
         c_l1_l2 > 0 && c_u1_u2 > 0 then
        raise Exit (* intersection and differences are not empty *)
      else
        assert false
  in
  fun i1 i2 ->
    try
      let res, nb_eq, sz_l1, sz_l2 = aux i1.ints i2.ints 0 0 0 in
      (* if res is true, we should check that i1 and i2 are not equal *)
      res && (sz_l1 <> sz_l2 || nb_eq <> sz_l1)
    with Exit -> false


let mult_borne b1 b2 =
  match b1,b2 with
  | Minfty, Pinfty | Pinfty, Minfty -> assert false
  | Minfty, b | b, Minfty ->
    if compare_bornes b (large_borne_of Q.zero Ex.empty) = 0
    then b
    else if pos_borne b then Minfty
    else Pinfty
  | Pinfty, b | b, Pinfty ->
    if compare_bornes b (large_borne_of Q.zero Ex.empty) = 0
    then b
    else if pos_borne b then Pinfty
    else Minfty
  | Strict (_, e1), Large (v, e2)
  | Large (v, e1), Strict (_, e2) when Q.is_zero v ->
    Large (Q.zero, Ex.union e1 e2)

  | Strict (v1, e1), Strict (v2, e2) | Strict (v1, e1), Large (v2, e2)
  | Large (v1, e1), Strict (v2, e2) ->
    Strict (Q.mult v1 v2, Ex.union e1 e2)
  | Large (v1, e1), Large (v2, e2) ->
    Large (Q.mult v1 v2, Ex.union e1 e2)

let mult_borne_inf b1 b2 =
  match b1,b2 with
  | Minfty, Pinfty | Pinfty, Minfty -> Minfty
  | _, _ -> mult_borne b1 b2

let mult_borne_sup b1 b2 =
  match b1,b2 with
  | Minfty, Pinfty | Pinfty, Minfty -> Pinfty
  | _, _ -> mult_borne b1 b2


let mult_bornes (a,b) (c,d) =
  (* see ../extra/intervals_mult.png *)
  (* put the explanation of both bounds for multiplication. Putting
     just one of them is probably incorrect. When a bound is [0,0], put
     the explanation of that bound instead of empty.
     TODO: make a deeper study!!!*)
  let ex_a_b = Ex.union (explain_borne a) (explain_borne b) in
  let ex_c_d = Ex.union (explain_borne c) (explain_borne d) in
  let all_ex = Ex.union ex_a_b ex_c_d in
  match class_of a b, class_of c d with
  | P, P ->
    mult_borne_inf a c, mult_borne_sup b d, all_ex
  | P, M ->
    mult_borne_inf b c, mult_borne_sup b d, all_ex
  | P, N ->
    mult_borne_inf b c, mult_borne_sup a d, all_ex
  | M, P ->
    mult_borne_inf a d, mult_borne_sup b d, all_ex
  | M, M ->
    min_of_lower_bounds (mult_borne_inf a d) (mult_borne_inf b c),
    max_of_upper_bounds (mult_borne_sup a c) (mult_borne_sup b d),
    all_ex
  | M, N ->
    mult_borne_inf b c, mult_borne_sup a c, all_ex
  | N, P ->
    mult_borne_inf a d, mult_borne_sup b c, all_ex
  | N, M ->
    mult_borne_inf a d, mult_borne_sup a c, all_ex
  | N, N ->
    mult_borne_inf b d, mult_borne_sup a c, all_ex
  | Z, (P | M | N | Z) -> (a, b, ex_a_b)
  | (P | M | N ), Z -> (c, d, ex_c_d)

let rec power_borne_inf p b =
  match p with
  | 1 -> b
  | p -> mult_borne_inf b (power_borne_inf (p-1) b)

let rec power_borne_sup p b =
  match p with
  | 1 -> b
  | p -> mult_borne_sup b (power_borne_sup (p-1) b)

let max_merge b1 b2 =
  let ex = Ex.union (explain_borne b1) (explain_borne b2) in
  let max = max_of_upper_bounds b1 b2 in
  match max with
  | Minfty | Pinfty -> max
  | Large (v, _) -> Large (v, ex)
  | Strict (v, _) -> Strict (v, ex)

let power_bornes p (b1,b2) =
  if neg_borne b1 && pos_borne b2 then
    match p with
    | 0 -> assert false
    | p when p mod 2 = 0 ->
      (* max_merge to have explanations !!! *)
      let m = max_merge (power_borne_sup p b1) (power_borne_sup p b2) in
      (Large (Q.zero, Ex.empty), m)
    | _ -> (power_borne_inf p b1, power_borne_sup p b2)
  else if pos_borne b1 && pos_borne b2 then
    (power_borne_inf p b1, power_borne_sup p b2)
  else if neg_borne b1 && neg_borne b2 then
    match p with
    | 0 -> assert false
    | p when p mod 2 = 0 -> (power_borne_inf p b2, power_borne_sup p b1)
    | _ -> (power_borne_inf p b1, power_borne_sup p b2)
  else assert false

let int_div_of_borne_inf min_f b =
  match b with
  | Minfty | Pinfty -> b
  | Large (v, e) ->
    Large ((if Q.is_int v then v else (*Q.floor*) min_f v), e)

  | Strict (v, e) ->
    (* this case really happens ?? *)
    if Q.is_int v then Large (Q.add v Q.one, e)
    else
      let v' = (*Q.floor*) min_f v in (* correct ? *)
      assert (Q.compare v' v > 0);
      Large (v', e)

let int_div_of_borne_sup max_f b =
  match b with
  | Minfty | Pinfty -> b
  | Large (v, e) ->
    Large ((if Q.is_int v then v else (*Q.floor*) max_f v), e)

  | Strict (v, e) ->
    (* this case really happens ?? *)
    if Q.is_int v then Large (Q.sub v Q.one, e)
    else
      let v' = (*Q.floor*) max_f v in (* correct ? *)
      assert (Q.compare v' v < 0);
      Large (v', e)

(* we use int_div_bornes for division of integer intervals instead of
   int_bornes because the div op is Euclidean division  is this case *)
let int_div_bornes min_f max_f l u =
  int_div_of_borne_inf min_f l, int_div_of_borne_sup max_f u

let mult u1 u2 =
  Options.tool_req 4 "TR-Arith-Axiomes mult";
  let resl, expl =
    List.fold_left
      (fun (l', expl) b1 ->
         List.fold_left
           (fun (l, ex) b2 ->
              let bl, bu, ex' = mult_bornes b1 b2 in
              let bl = add_expl_to_borne bl ex' in
              let bu = add_expl_to_borne bu ex' in
              (bl, bu)::l, Ex.union ex ex') (l', expl) u2.ints)
      ([], Ex.empty) u1.ints
  in
  let res =
    union_intervals
      { ints= resl; is_int = u1.is_int;
        expl = Ex.union expl (Ex.union u1.expl u2.expl) } in
  assert (res.ints != []);
  res


let power n u =
  Options.tool_req 4 "TR-Arith-Axiomes power";
  let l = List.map (power_bornes n) u.ints in
  union_intervals { u with ints = l }

let root_default_borne is_int x n =
  match x with
  | Pinfty -> Pinfty
  | Minfty -> Minfty
  | Large (v, e) | Strict (v, e) ->
    let sign, s =
      if Q.sign v >= 0 then (fun q -> q), root_default_num v n
      else Q.minus, root_exces_num (Q.minus v) n
    in
    match s with
    | None -> Minfty
    | Some s ->
      let s = sign s in
      if is_int then
        let cs = Q.ceiling s in
        let cs2 = Q.power cs n in
        if Q.compare v cs2 <= 0 then Large (cs, e)
        else Large (Q.add cs Q.one, e)
      else Large (s, e)

let root_exces_borne is_int x n =
  match x with
  | Pinfty -> Pinfty
  | Minfty -> Minfty
  | Large (v, e) | Strict (v, e) ->
    let sign, s =
      if Q.sign v >= 0 then (fun d -> d), root_exces_num v n
      else Q.minus, root_default_num (Q.minus v) n
    in
    match s with
    | None -> Pinfty
    | Some s ->
      let s = sign s in
      if is_int then
        let cs = Q.floor s in
        let cs2 = Q.power cs n in
        if Q.compare v cs2 >= 0 then Large (cs, e)
        else Large (Q.sub cs Q.one, e)
      else Large (s, e)

let sqrt_interval is_int (l, ex) (b1,b2) =
  let l1 = minus_borne (root_exces_borne is_int b2 2) in
  let u1 = minus_borne (root_default_borne is_int b1 2) in
  let l2 = root_default_borne is_int b1 2 in
  let u2 = root_exces_borne is_int b2 2 in
  let c1 = compare_bornes l1 u1 in
  let c2 = compare_bornes l2 u2 in
  if c1 > 0 then
    if c2 > 0 then
      l, Ex.union ex (Ex.union (explain_borne b1) (explain_borne b2))
    else (l2,u2)::l, ex
  else
  if c2 > 0 then (l1, u1)::l, ex
  else (union_bornes is_int [(l1,u1); (l2, u2)]) @ l, ex

let sqrt {ints = l; is_int = is_int; expl} =
  Options.tool_req 4 "TR-Arith-Axiomes sqrt";
  let l, expl = List.fold_left (sqrt_interval is_int) ([], expl) l in
  if l == [] then raise (NotConsistent expl);
  let res = union_intervals { ints = l; is_int; expl} in
  assert (res.ints != []);
  res

let root_interval is_int (b1,b2) n =
  let u,l = (root_default_borne is_int b1 n, root_exces_borne is_int b2 n) in
  if compare_bornes u l <= 0 then Int(u,l)
  else Empty (Ex.union (explain_borne b1) (explain_borne b2))

let rec root n ({ints = l; is_int = is_int; expl } as u) =
  Options.tool_req 4"TR-Arith-Axiomes root";
  if n mod 2 = 0 then root (n/2) (sqrt u)
  else
    let l = List.rev_map (fun bs -> root_interval is_int bs n) l in
    let l = join (List.rev l) expl in
    let res = union_intervals {u with ints = l; is_int = is_int} in
    assert (res.ints != []);
    res

let inv_borne_inf b is_int ~other =
  match b with
  | Pinfty -> assert false
  | Minfty ->
    if is_int then Large (Q.zero,  explain_borne other)
    else Strict (Q.zero, explain_borne other)
  | Strict (c, _) | Large (c, _) when Q.sign c = 0 -> Pinfty
  | Strict (v, e) -> Strict (Q.div Q.one v, e)
  | Large (v, e) -> Large (Q.div Q.one v, e)

let inv_borne_sup b is_int ~other =
  match b with
  | Minfty -> assert false
  | Pinfty ->
    if is_int then Large (Q.zero, explain_borne other)
    else Strict (Q.zero, explain_borne other)
  | Strict (c, _) | Large (c, _) when Q.sign c = 0 -> Minfty
  | Strict (v, e) -> Strict (Q.div Q.one v, e)
  | Large (v, e) -> Large (Q.div Q.one v, e)

let inv_bornes (l, u) is_int =
  inv_borne_sup u is_int ~other:l, inv_borne_inf l is_int ~other:u


let inv ({ ints = l; is_int; _ } as u) =
  match doesnt_contain_0 u with
  | None -> { u with ints = [Minfty, Pinfty] }
  | Some (ex, _) ->
    let l' =
      List.fold_left
        (fun acc (l,u) ->
           let l = add_expl_to_borne l ex in
           let u = add_expl_to_borne u ex in
           (inv_bornes (l, u) is_int) :: acc
        ) [] l
    in
    assert (l' != []);
    (* ! SHOULD NOT try to simplify here if is_int is true *)
    union_intervals { u with ints = l' }


type sign_of_interval = Zero | Pos | Neg | Mixed

let sign_of_interval { ints; _ } =
  match ints, List.rev ints with
  | [], _ | _, [] -> assert false
  | (inf, _)::_, (_,sup)::_ ->
    match inf, sup with
    | Pinfty, _  | _, Minfty -> assert false
    | Minfty, Pinfty -> Mixed
    | Large(v,_), Large(v',_)  ->
      if Q.compare v Q.zero > 0 then Pos
      else if Q.compare v' Q.zero < 0 then Neg
      else if Q.is_zero v && Q.is_zero v' then Zero
      else Mixed

    | (Strict(v,_) | Large(v,_)), (Strict(v',_) | Large(v',_))  ->
      if Q.compare v Q.zero >= 0 then Pos
      else if Q.compare v' Q.zero <= 0 then Neg
      else Mixed

    | (Strict(v,_) | Large(v,_)), Pinfty  ->
      if Q.compare v Q.zero >= 0 then Pos
      else Mixed

    | Minfty, (Strict(v',_) | Large(v',_))  ->
      if Q.compare v' Q.zero <= 0 then Neg
      else Mixed


let div i1 i2 =
  Options.tool_req 4 "TR-Arith-Axiomes div";
  let inv_i2 = inv i2 in
  if is_undefined inv_i2 then inv_i2
  else
    let i1 = match doesnt_contain_0 i2 with
      | Some (ex, _) -> add_expl_zero i1 ex
      | None -> i1
    in
    let ({ ints = l; is_int = is_int; _ } as i) = mult i1 inv_i2 in
    assert (l != []);
    if is_int then
      (* not just int_bornes because it's Euclidean division *)
      let min_f, max_f =
        match sign_of_interval i2 with
        | Zero -> assert false (* inv_i2 is not undefined *)
        | Pos -> Q.floor, Q.floor
        | Neg -> Q.ceiling, Q.ceiling
        | Mixed -> Q.floor, Q.ceiling
      in
      let rl = List.rev_map (fun (l,u) -> int_div_bornes min_f max_f l u) l in
      union_intervals { i with ints = List.rev rl }
    else { i with ints = l }

let abs =
  let zero_inf_r =
    new_borne_inf Ex.empty Q.zero ~is_le:true (undefined Ty.Treal)
  in
  let zero_inf_i =
    new_borne_inf Ex.empty Q.zero ~is_le:true (undefined Ty.Tint)
  in
  fun i ->
    let xx = if i.is_int then zero_inf_i else zero_inf_r in
    intersect (merge i (scale Q.m_one i)) xx

let mk_closed l u llarge ularge lexp uexp ty =
  let lb = if llarge then Large(l, lexp) else Strict (l, lexp) in
  let ub = if ularge then Large(u, uexp) else Strict (u, uexp) in
  { ints = [lb, ub]; is_int = ty == Ty.Tint; expl = Ex.union lexp uexp }

type bnd = (Numbers.Q.t * Numbers.Q.t) option * Explanation.t

let bnd_of_borne b ex0 low =
  match b with
  | Pinfty when not low -> None, ex0
  | Minfty when low -> None, ex0
  | Pinfty | Minfty -> assert false
  | Large (c, ex)   -> Some (c, Q.zero), Ex.union ex0 ex
  | Strict (c, ex)  -> Some (c, if low then Q.one else Q.m_one), Ex.union ex0 ex

let bounds_of env =
  let ex = env.expl in
  match env.ints with
  | [] -> [(None, ex), (None, ex)]
  | l ->
    List.rev
      (List.rev_map
         (fun (b1, b2) -> bnd_of_borne b1 ex true, bnd_of_borne b2 ex false) l)

let add_explanation i ex =
  if Ex.is_empty ex then i
  else
    let rl =
      List.rev_map (fun (l, u) ->
          add_expl_to_borne l ex, add_expl_to_borne u ex) i.ints
    in
    {i with ints = List.rev rl; expl = Ex.union i.expl ex}

let equal i1 i2 =
  try
    List.iter2
      (fun (b1,c1) (b2,c2) ->
         if compare_bounds b1 ~is_low1:true b2 ~is_low2:true <> 0 ||
            compare_bounds c1 ~is_low1:false c2 ~is_low2:false <> 0 then
           raise Exit
      )i1.ints i2.ints;
    true
  with Exit | Invalid_argument _ -> false

let min_bound { ints; _ } =
  match ints with
  | [] -> assert false
  | (b, _) :: _ -> b

let max_bound { ints; _} =
  match List.rev ints with
  | [] -> assert false
  | (_, b) :: _ -> b

type interval_matching =
  ((Q.t * bool) option * (Q.t * bool) option * Ty.t) Var.Map.t

module MV = Var.Map
module Sy = Symbols

let is_question_mark =
  let qm = Hstring.make "?" in
  fun s -> Hstring.equal qm (Var.view s).Var.hs

let consistent_bnds low up =
  match low, up with
  | Some (q_low, str_low), Some (q_up, str_up) ->
    let c = Q.compare q_up q_low in
    c > 0 || (c = 0 && not str_low && not str_up)
  | _ -> true

let new_up_bound idoms s ty q is_strict =
  let old_low, old_up, ty =
    try MV.find s idoms
    with Not_found -> None,None,ty
  in
  let new_up =
    match old_up with
    | None -> Some (q, is_strict)
    | Some (r, str)  ->
      let c = Q.compare r q in
      if c < 0 then old_up
      else if c > 0 then Some (q, is_strict)
      else
      if is_strict == str || is_strict then old_up
      else Some (q, is_strict)
  in
  if new_up == old_up then idoms
  else
  if consistent_bnds old_low new_up then MV.add s (old_low, new_up, ty) idoms
  else raise Exit

let new_low_bound idoms s ty q is_strict =
  let old_low, old_up, ty =
    try MV.find s idoms
    with Not_found -> None,None,ty
  in
  let new_low =
    match old_low with
    | None -> Some (q, is_strict)
    | Some (r, str)  ->
      let c = Q.compare r q in
      if c > 0 then old_low
      else if c < 0 then Some (q, is_strict)
      else
      if is_strict == str || is_strict then old_low
      else Some (q, is_strict)
  in
  if new_low == old_low then idoms
  else
  if consistent_bnds new_low old_up then MV.add s (new_low, old_up, ty) idoms
  else raise Exit

let new_var idoms s ty =
  if MV.mem s idoms then idoms
  else MV.add s (None, None, ty) idoms

let match_interval_upper {Sy.sort; is_open; kind; is_lower} i imatch =
  assert (not is_lower);
  match kind, max_bound i with
  | Sy.VarBnd s, _ when is_question_mark s -> imatch (* ? var *)
  | Sy.VarBnd _, Minfty -> assert false
  | Sy.VarBnd s, Pinfty -> new_var imatch s sort
  | Sy.VarBnd s, Strict (v, _) -> new_low_bound imatch s sort v false
  | Sy.VarBnd s, Large  (v, _) -> new_low_bound imatch s sort v is_open

  | Sy.ValBnd _, Minfty -> assert false
  | Sy.ValBnd _, Pinfty -> raise Exit
  | Sy.ValBnd vl, Strict (v, _) ->
    let c = Q.compare v vl in
    if c > 0 then raise Exit;
    imatch

  | Sy.ValBnd vl, Large  (v, _) ->
    let c = Q.compare v vl in
    if c > 0 || c = 0 && is_open then raise Exit;
    imatch


let match_interval_lower {Sy.sort; is_open; kind; is_lower} i imatch =
  assert (is_lower);
  match kind, min_bound i with
  | Sy.VarBnd s, _ when is_question_mark s -> imatch (* ? var *)
  | Sy.VarBnd _, Pinfty -> assert false
  | Sy.VarBnd s,  Minfty -> new_var imatch s sort
  | Sy.VarBnd s, Strict (v, _) -> new_up_bound imatch s sort v false
  | Sy.VarBnd s, Large  (v, _) -> new_up_bound imatch s sort v is_open

  | Sy.ValBnd _, Minfty -> raise Exit
  | Sy.ValBnd _, Pinfty -> assert false
  | Sy.ValBnd vl, Strict (v, _) ->
    let c = Q.compare v vl in
    if c < 0 then raise Exit;
    imatch

  | Sy.ValBnd vl, Large  (v, _) ->
    let c = Q.compare v vl in
    if c < 0 || c = 0 && is_open then raise Exit;
    imatch

let match_interval lb ub i accu =
  try Some (match_interval_upper ub i (match_interval_lower lb i accu))
  with Exit -> None


(*****************)

(* Some debug code for Intervals: commented by default

   let no_inclusion =
   let not_included (b1, c1) (b2, c2) =
    not (
      compare_bounds b1 ~is_low1:true b2 ~is_low2:true >= 0 &&
        compare_bounds c1 ~is_low1:false c2 ~is_low2:false <= 0
    )
   in
   let b_inc_list d l =
    List.iter (fun e ->
      assert (not_included d e);
      assert (not_included e d)
    ) l
   in
   let rec aux todo =
    match todo with
    | [] -> assert false
    | [e] -> ()
    | d::l -> b_inc_list d l; aux l
   in
   fun i ->
    (*fprintf fmt "[no_inclusion] i = %a@." print i;*)
    aux i.ints

   let not_mergeable =
   let rec aux is_int l =
    match l with
    | [] -> assert false
    | [e] -> ()
    | (_,a)::(((b,_)::_) as l) ->
      begin
        match a, b with
        | Minfty, _ | _, Pinfty -> assert false (*should not happen*)
        | Pinfty, _ | _, Minfty -> assert false
                                       (*should not happen or not norm*)
        | Large(q1,_) , Large(q2,_) ->
          assert (Q.compare q1 q2 < 0); (* otherwise, we can merge *)
          if is_int then
            (* the gap between q1 and q2 should be > 1. Otherwise,
               we can merge *)
            assert (Q.compare (Q.sub q2 q1) Q.one > 0)

        | Strict(q1,_), Large(q2,_) ->
          assert (not is_int);
          assert (Q.compare q1 q2 < 0) (* otherwise, we can merge *)

        | Large(q1,_) , Strict(q2,_) ->
          assert (not is_int);
          assert (Q.compare q1 q2 < 0) (* otherwise, we can merge *)

        | Strict(q1,_) , Strict(q2,_) ->
          assert (not is_int);
          assert (Q.compare q1 q2 <= 0) (* otherwise, we can merge *)
      end;
      aux is_int l;
   in
   fun i ->
    (*fprintf fmt "[no_mergeable] i = %a@." print i;*)
    aux i.is_int i.ints

   let assert_is_normalized i =
   not_mergeable i;
   no_inclusion i;
   i

   let exclude i j =
   try
    let k = exclude i j in
    k |> assert_is_normalized
   with Assert_failure _ -> assert false

   let intersect i j =
   try
    let k = intersect i j in
    k |> assert_is_normalized
   with Assert_failure _ -> assert false

   let mult i j =
   try mult i j |> assert_is_normalized
   with Assert_failure _ -> assert false

   let power i j =
   try power i j |> assert_is_normalized
   with Assert_failure _ -> assert false

   let sqrt i =
   try sqrt i |> assert_is_normalized
   with Assert_failure _ -> assert false

   let root n i =
   try root n i |> assert_is_normalized
   with Assert_failure _ -> assert false

   let add i j =
   try
    (*fprintf fmt "@.i   = %a@." print i;
    fprintf fmt "j   = %a@." print j;*)
    let k = add i j in
    (*fprintf fmt "res = %a@." print k;*)
    k |> assert_is_normalized
   with Assert_failure _ -> assert false

   let scale q i =
   try scale q i |> assert_is_normalized
   with Assert_failure _ -> assert false

   let sub i j =
   try sub i j |> assert_is_normalized
   with Assert_failure _ -> assert false

   let merge i j =
   try merge i j |> assert_is_normalized
   with Assert_failure _ -> assert false

   let abs i =
   try abs i |> assert_is_normalized
   with Assert_failure _ -> assert false

   let div i j =
   try div i j |> assert_is_normalized
   with Assert_failure _ -> assert false
*)

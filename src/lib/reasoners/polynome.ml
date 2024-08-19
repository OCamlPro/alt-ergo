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

module Z = Numbers.Z
module Q = Numbers.Q

exception Not_a_num
exception Maybe_zero

module type S = sig
  include Sig.X
  val mult : r -> r -> r
end

module type T = sig

  type r
  type t

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val create : (Q.t * r) list -> Q.t -> Ty.t-> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mult : t -> t -> t
  val mult_const : Q.t -> t -> t
  val add_const : Q.t -> t -> t
  val div : t -> t -> t * bool
  val modulo : t -> t -> t

  val is_const : t -> Q.t option
  val is_empty : t -> bool
  val find : r -> t -> Q.t
  val choose : t -> Q.t * r
  val subst : r -> t -> t -> t
  val remove : r -> t -> t
  val to_list : t -> (Q.t * r) list * Q.t
  val leaves : t -> r list

  val print : Format.formatter -> t -> unit
  val type_info : t -> Ty.t
  val is_monomial : t -> (Q.t * r * Q.t) option

  val ppmc_denominators : t -> Q.t
  val pgcd_numerators : t -> Q.t
  val normal_form : t -> t * Q.t * Q.t
  val normal_form_pos : t -> t * Q.t * Q.t
  val abstract_selectors : t -> (r * r) list -> t * (r * r) list

  val separate_constant : t -> t * Numbers.Q.t

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t

  module Ints : sig
    val of_bigint : Z.t -> t
    val zero : t
    val (~-) : t -> t
    val (+) : t -> t -> t
    val (-) : t -> t -> t
    val (~$$) : Z.t -> t
    val (+$$) : t -> Z.t -> t
    val ( *$$ ) : t -> Z.t -> t
  end
end

module type EXTENDED_Polynome = sig
  include T
  val extract : r -> t option
  val embed : t -> r
end

module Make (X : S) = struct

  type r = X.r

  module M : Map.S with type key = r =
    Map.Make(
    struct
      type t = r

      (*sorted in decreasing order to comply with AC(X) order requirements*)
      let compare x y = X.str_cmp y x
    end)

  type t = { m : Q.t M.t; c : Q.t; ty : Ty.t }

  let map_to_list m = List.rev (M.fold (fun x a aliens -> (a, x)::aliens) m [])

  exception Out of int

  let compare_maps l1 l2 =
    try
      List.iter2
        (fun (a,x) (b,y) ->
           let c = X.str_cmp x y   in if c <> 0 then raise (Out c);
           let c = Q.compare a b in if c <> 0 then raise (Out c) )l1 l2;
      0
    with
    | Out c -> c
    | Invalid_argument s ->
      assert (String.compare s "List.iter2" = 0);
      List.length l1 - List.length l2

  let compare p1 p2 =
    let c = Ty.compare p1.ty p2.ty in
    if c <> 0 then c
    else match M.is_empty p1.m, M.is_empty p2.m with
      | true , false -> -1
      | false, true  -> 1
      | true , true  -> Q.compare p1.c p2.c
      | false, false ->
        let c =  compare_maps (map_to_list p1.m) (map_to_list p2.m) in
        if c = 0 then Q.compare p1.c p2.c else c

  let equal { m = m1; c = c1; _ } { m = m2; c = c2; _ } =
    Q.equal c1 c2 && M.equal Q.equal m1 m2

  let hash p =
    let h =
      M.fold
        (fun k v acc ->
           23 * acc + (X.hash k) * Q.hash v
        )p.m (19 * Q.hash p.c + 17 * Ty.hash p.ty)
    in
    abs h

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    let pprint fmt p =
      let zero = ref true in
      M.iter
        (fun x n ->
           let s, n, op =
             if Q.equal n Q.one then (if !zero then "" else "+"), "", ""
             else if Q.equal n Q.m_one then "-", "", ""
             else
             if Q.sign n > 0 then
               (if !zero then "" else "+"), Q.to_string n, "*"
             else "-", Q.to_string (Q.minus n), "*"
           in
           zero := false;
           Format.fprintf fmt "%s%s%s%a" s n op X.print x
        ) p.m;
      let s, n =
        if Q.sign p.c > 0 then (if !zero then "" else "+"), Q.to_string p.c
        else if Q.sign p.c < 0 then "-", Q.to_string (Q.minus p.c)
        else (if !zero then "","0" else "","") in
      Format.fprintf fmt "%s%s" s n

    let print fmt p =
      if Options.get_term_like_pp () then pprint fmt p
      else begin
        M.iter (fun t n ->
            Format.fprintf fmt "%s*%a " (Q.to_string n) X.print t
          ) p.m;
        Format.fprintf fmt "%s%s"
          (if Q.compare_to_0 p.c >= 0 then "+ " else "")
          (Q.to_string p.c);
        Format.fprintf fmt " [%a]" Ty.print p.ty
      end
  end
  (*BISECT-IGNORE-END*)

  let print = Debug.print

  let is_const p = if M.is_empty p.m then Some p.c else None

  let find x m = try M.find x m with Not_found -> Q.zero

  let create l c ty =
    let m =
      List.fold_left
        (fun m (n, x) ->
           let n' = Q.add n (find x m) in
           if Q.sign n' = 0 then M.remove x m else M.add x n' m) M.empty l
    in
    { m = m; c = c; ty = ty }

  let add p1 p2 =
    Options.tool_req 4 "TR-Arith-Poly plus";
    let m =
      M.fold
        (fun x a m ->
           let a' = Q.add (find x m) a in
           if Q.sign a' = 0 then M.remove x m  else M.add x a' m)
        p2.m p1.m
    in
    { m = m; c = Q.add p1.c p2.c; ty = p1.ty }

  let mult_const n p =
    if Q.sign n = 0 then { m = M.empty; c = Q.zero; ty = p.ty }
    else { p with m = M.map (Q.mult n) p.m; c =  Q.mult n p.c }

  let add_const n p = {p with c = Q.add p.c n}

  let mult_monome a x p  =
    let ax = { m = M.add x a M.empty; c = Q.zero; ty = p.ty} in
    let acx = mult_const p.c ax in
    let m =
      M.fold
        (fun xi ai m -> M.add (X.mult x xi) (Q.mult a ai) m) p.m acx.m
    in
    { acx with m = m}

  let mult p1 p2 =
    Options.tool_req 4 "TR-Arith-Poly mult";
    let p = mult_const p1.c p2 in
    M.fold (fun x a p -> add (mult_monome a x p2) p) p1.m p

  let sub p1 p2 =
    Options.tool_req 4 "TR-Arith-Poly moins";
    let m =
      M.fold
        (fun x a m ->
           let a' = Q.sub (find x m) a in
           if Q.sign a' = 0 then M.remove x m  else M.add x a' m)
        p2.m p1.m
    in
    { m = m; c = Q.sub p1.c p2.c; ty = p1.ty }


  let euc_mod_num c1 c2 =
    let c = Q.modulo c1 c2 in
    if Q.sign c < 0 then Q.add c (Q.abs c2) else c

  let euc_div_num c1 c2 = Q.div (Q.sub c1 (euc_mod_num c1 c2))  c2

  let div p1 p2 =
    Options.tool_req 4 "TR-Arith-Poly div";
    if not (M.is_empty p2.m) then raise Maybe_zero;
    if Q.sign p2.c = 0 then raise Division_by_zero;
    let p = mult_const (Q.div Q.one p2.c) p1 in
    match M.is_empty p.m, p.ty with
    | _ , Ty.Treal  ->  p, false
    | true, Ty.Tint  -> {p with c = euc_div_num p1.c p2.c}, false
    | false, Ty.Tint ->  p, true (* XXX *)
    | _ -> assert false

  let modulo p1 p2 =
    Options.tool_req 4 "TR-Arith-Poly mod";
    if not (M.is_empty p2.m) then raise Maybe_zero;
    if Q.sign p2.c = 0 then raise Division_by_zero;
    if not (M.is_empty p1.m) then raise Not_a_num;
    { p1 with c = euc_mod_num p1.c p2.c }

  let find x p = M.find x p.m

  let is_empty p = M.is_empty p.m

  let choose p =
    let tn= ref None in
    (*version I : prend le premier element de la table*)
    (try M.iter
           (fun x a -> tn := Some (a, x); raise Exit) p.m with Exit -> ());
    (*version II : prend le dernier element de la table i.e. le plus grand
      M.iter (fun x a -> tn := Some (a, x)) p.m;*)
    match !tn with Some p -> p | _ -> raise Not_found

  let subst x p1 p2 =
    try
      let a = M.find x p2.m in
      add (mult_const a p1) { p2 with m = M.remove x p2.m}
    with Not_found -> p2

  let remove x p = { p with m = M.remove x p.m }

  let to_list p = map_to_list p.m , p.c

  module SX = Set.Make(struct type t = r let compare = X.hash_cmp end)

  let xs_of_list sx l = List.fold_left (fun s x -> SX.add x s) sx l

  let leaves p =
    let s =
      M.fold (fun a _ s -> xs_of_list s (X.leaves a)) p.m SX.empty
    in
    SX.elements s

  let type_info p = p.ty

  let is_monomial p  =
    try
      M.fold
        (fun x a r ->
           match r with
           | None -> Some (a, x, p.c)
           | _ -> raise Exit)
        p.m None
    with Exit -> None

  let ppmc_denominators { m; _ } =
    let res =
      M.fold
        (fun _ c acc -> Z.my_lcm (Q.den c) acc)
        m Z.one in
    Q.abs (Q.from_z res)

  let pgcd_numerators { m; _ } =
    let res =
      M.fold
        (fun _ c acc -> Z.my_gcd (Q.num c) acc)
        m Z.zero
    in
    Q.abs (Q.from_z res)

  let normal_form ({ m; _ } as p) =
    if M.is_empty m then
      { p with c = Q.zero }, p.c, Q.one
    else
      let ppcm = ppmc_denominators p in
      let pgcd = pgcd_numerators p in
      let p = mult_const (Q.div ppcm pgcd) p in
      { p with c = Q.zero }, p.c, (Q.div pgcd ppcm)

  let normal_form_pos p =
    let p, c, d = normal_form p in
    try
      let a, _ = choose p in
      if Q.sign a > 0 then p, c, d
      else mult_const Q.m_one p, Q.minus c, Q.minus d
    with Not_found -> p, c, d

  let abstract_selectors p acc =
    let mp, acc =
      M.fold
        (fun r i (mp, acc) ->
           let r, acc = X.abstract_selectors r acc in
           let mp =
             try
               let j = M.find r mp in
               let k = Q.add i j in
               if Q.sign k = 0 then M.remove r mp else M.add r k mp
             with Not_found -> M.add r i mp
           in
           mp, acc
        )p.m (M.empty, acc)
    in
    {p with m=mp}, acc

  let separate_constant t = { t with c = Q.zero}, t.c

  (* Operators and helpers for readability *)

  module Set = Set.Make(struct type nonrec t = t let compare = compare end)
  module Map = Map.Make(struct type nonrec t = t let compare = compare end)

  module Ints = struct
    let of_bigint n = create [] (Q.from_z n) Tint
    let (~$$) = of_bigint
    let zero = ~$$Z.zero
    let (~-) = mult_const Q.m_one
    let (+) = add
    let (-) = sub
    let (+$$) p n = add_const (Q.from_z n) p
    let ( *$$ ) p n = mult_const (Q.from_z n) p
  end
end

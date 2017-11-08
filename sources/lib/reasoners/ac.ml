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

open Options
open Format

module HS = Hstring
module Sy = Symbols

module type S = sig

  (* embeded AC semantic values *)
  type r

  (* extracted AC semantic values *)
  type t = r Sig.ac

  (* builds an embeded semantic value from an AC term *)
  val make : Term.t -> r * Literal.LT.t list

  (* tells whether the given term is AC*)
  val is_mine_symb : Sy.t -> bool

  (* compares two AC semantic values *)
  val compare : t -> t -> int

  (* tests if two values are equal (using tags) *)
  val equal : t -> t -> bool

  (* hash function for ac values *)
  val hash : t -> int

  (* returns the type infos of the given term *)
  val type_info : t -> Ty.t

  (* prints the AC semantic value *)
  val print : formatter -> t -> unit

  (* returns the leaves of the given AC semantic value *)
  val leaves : t -> r list

  (* replaces the first argument by the second one in the given AC value *)
  val subst : r -> r -> t -> r

  (* add flatten the 2nd arg w.r.t HS.t, add it to the given list
     and compact the result *)
  val add : Symbols.t -> r * int -> (r * int) list -> (r * int) list

  val fully_interpreted : Symbols.t -> bool

  val abstract_selectors : t -> (r * r) list -> r * (r * r) list

  val compact : (r * int) list -> (r * int) list
end

module Make (X : Sig.X) = struct

  open Sig

  type r = X.r

  type t = X.r Sig.ac

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct


    let print_x fmt v =
      match X.leaves v with
      | [w] when X.equal v w -> fprintf fmt "%a" X.print v
      | _ -> fprintf fmt "(%a)" X.print v


    let rec pr_elt sep fmt (e,n) =
      assert (n >=0);
      if n = 0 then ()
      else fprintf fmt "%s%a%a" sep print_x e (pr_elt sep) (e,n-1)

    let pr_xs sep fmt = function
      | [] -> assert false
      | (p,n)::l  ->
        fprintf fmt "%a" print_x p;
        List.iter (fprintf fmt "%a" (pr_elt sep))((p,n-1)::l)

    let print fmt {h=h ; l=l} =
      if Sy.equal h (Sy.Op Sy.Mult) then
        fprintf fmt "%a" (pr_xs "'*'") l
      else
        fprintf fmt "%a(%a)" Sy.print h (pr_xs ",") l

    let assert_compare a b c1 c2 =
      assert (
        if not (c1 = 0 && c2 = 0 ||
            c1 < 0 && c2 > 0 ||
            c1 > 0 && c2 < 0) then begin
          fprintf fmt "Ac.compare:@.%a vs @.%a@. = %d@.@." print a print b c1;
          fprintf fmt "But@.";
          fprintf fmt "Ac.compare:@.%a vs @.%a@. = %d@.@." print b print a c2;
          false
        end
        else true
      )

    let subst p v tm =
      if debug_ac () then
        fprintf fmt "[ac] subst %a by %a in %a@."
	  X.print p X.print v X.print (X.ac_embed tm)

  end
  (*BISECT-IGNORE-END*)

  let print = Debug.print

  let flatten h (r,m) acc =
    match X.ac_extract r with
      | Some ac when Sy.equal ac.h h ->
	List.fold_left (fun z (e,n) -> (e,m * n) :: z) acc ac.l
      | _ -> (r,m) :: acc

  let sort = List.fast_sort (fun (x,n) (y,m) -> X.str_cmp x y)

  let rev_sort l = List.rev (sort l)

  let compact xs =
    let rec f acc = function
      | [] -> acc
      | [(x,n)] -> (x,n) :: acc
      | (x,n) :: (y,m) :: r ->
	if X.equal x y then f acc ((x,n+m) :: r)
	else f ((x,n)::acc) ((y,m) :: r)
    in
    f [] (sort xs) (* increasing order - f's result in a decreasing order*)

  let fold_flatten sy f =
    List.fold_left (fun z (rt,n) -> flatten sy ((f rt),n) z) []

  let expand =
    List.fold_left
      (fun l (x,n) -> let l= ref l in for i=1 to n do l:=x::!l done; !l) []

  let abstract2 sy t r acc =
    match X.ac_extract r with
      | Some ac when Sy.equal sy ac.h -> r, acc
      | None -> r, acc
      | Some _ -> match Term.view t with
          | {Term.f=Sy.Name(hs,Sy.Ac) ;xs=xs;ty=ty} ->
            let aro_sy = Sy.name ("@" ^ (HS.view hs)) in
            let aro_t = Term.make aro_sy xs ty  in
            let eq = Literal.LT.mk_eq aro_t t in
            X.term_embed aro_t, eq::acc
          | {Term.f=Sy.Op Sy.Mult ;xs=xs;ty=ty} ->
            let aro_sy = Sy.name "@*" in
            let aro_t = Term.make aro_sy xs ty  in
            let eq = Literal.LT.mk_eq aro_t t in
            X.term_embed aro_t, eq::acc
          | {Term.ty=ty} ->
            let k = Term.fresh_name ty in
            let eq = Literal.LT.mk_eq k t in
            X.term_embed k, eq::acc

  let make t =
    Timers.exec_timer_start Timers.M_AC Timers.F_make;
    let x = match Term.view t with
      | {Term.f= sy; xs=[a;b]; ty=ty} when Sy.is_ac sy ->
        let ra, ctx1 = X.make a in
        let rb, ctx2 = X.make b in
        let ra, ctx = abstract2 sy a ra (ctx1 @ ctx2) in
        let rb, ctx = abstract2 sy b rb ctx in
        let rxs = [ ra,1 ; rb,1 ] in
	X.ac_embed {h=sy; l=compact (fold_flatten sy (fun x -> x) rxs); t=ty;
                    distribute = true},
        ctx
      | _ -> assert false
    in
    Timers.exec_timer_pause Timers.M_AC Timers.F_make;
    x

  let is_mine_symb sy = Options.no_ac() == false && Sy.is_ac sy

  let type_info {t=ty} = ty

  let leaves { l=l } = List.fold_left (fun z (a,_) -> (X.leaves a) @ z)[] l

  let rec mset_cmp = function
    |  []   ,  []   ->  0
    |  []   , _::_  -> -1
    | _::_  ,  []   ->  1
    | (a,m)::r  , (b,n)::s  ->
      let c = X.str_cmp a b in
      if c <> 0 then c
      else
	let c = m - n in
	if c <> 0 then c
	else mset_cmp(r,s)

  let size = List.fold_left (fun z (rx,n) -> z + n) 0


  module SX = Set.Make(struct type t=r let compare = X.str_cmp end)

  let leaves_list l =
    let l =
      List.fold_left
        (fun acc (x,n) ->
          let sx = List.fold_right SX.add (X.leaves x) SX.empty in
          SX.fold (fun lv acc -> (lv, n) :: acc)  sx acc
        ) []l
    in
    compact l


  (* x et y are sorted in a decreasing order *)
  let compare {h=f ; l=x} {h=g ; l=y} =
    let c = Sy.compare f g in
    if c <> 0 then c
    else
      let llx = leaves_list x in
      let lly = leaves_list y in
      let c = size llx - size lly in
      if c <> 0 then c
      else
        let c = mset_cmp (leaves_list x , leaves_list y) in
        if c <> 0 then c
        else mset_cmp (x , y)


  let compare a b =
    let c1 = compare a b in
    let c2 = compare b a in
    Debug.assert_compare a b c1 c2;
    c1

  (*
    let mset_compare ord {h=f ; l=x} {h=g ; l=y} =
    let c = Sy.compare f g in
    if c <> 0 then c
    else assert false
  *)

  let equal {h=f ; l=lx} {h=g ; l=ly} =
    Sy.equal f g &&
      try List.for_all2 (fun (x, m) (y, n) -> m = n && X.equal x y) lx ly
      with Invalid_argument _ -> false

  let hash {h = f ; l = l; t = t} =
    let acc = Sy.hash f + 19 * Ty.hash t in
    abs (List.fold_left (fun acc (x, y) -> acc + 19 * (X.hash x + y)) acc l)


  let subst p v ({h=h;l=l;t=t} as tm)  =
    Options.exec_thread_yield ();
    Timers.exec_timer_start Timers.M_AC Timers.F_subst;
    Debug.subst p v tm;
    let t = X.color {tm with l=compact (fold_flatten h (X.subst p v) l)} in
    Timers.exec_timer_pause Timers.M_AC Timers.F_subst;
    t


  let add h arg arg_l =
    Timers.exec_timer_start Timers.M_AC Timers.F_add;
    let r = compact (flatten h arg arg_l) in
    Timers.exec_timer_pause Timers.M_AC Timers.F_add;
    r

  let fully_interpreted sb = true

  let abstract_selectors ({l=args} as ac) acc =
    let args, acc =
      List.fold_left
        (fun (args, acc) (r, i) ->
          let r, acc = X.abstract_selectors r acc in
          (r, i) :: args, acc
        )([],acc) args
    in
    let xac = X.ac_embed {ac with l = compact args} in
    xac, acc

(* Ne suffit pas. Il faut aussi prevoir le collapse ? *)
(*try List.assoc xac acc, acc
  with Not_found ->
  let v = X.term_embed (Term.fresh_name ac.t) in
  v, (xac, v) :: acc*)

end


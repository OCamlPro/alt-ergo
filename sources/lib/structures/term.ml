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

open Format
open Hconsing
open Options

module Sy = Symbols

type view =
  {
    f: Sy.t;
    xs: t list;
    ty: Ty.t;
    tag: int;
    vars : Ty.t Sy.Map.t Lazy.t;
    vty : Ty.Svty.t Lazy.t;
    depth: int;
    nb_nodes : int;
  }

and t = view

module Subst = struct
  include Symbols.Map

  let print pr_elt fmt sbt =
    iter (fun k v -> fprintf fmt "%a -> %a  " Sy.print k pr_elt v) sbt
end

type subst = t Subst.t * Ty.subst

module H = struct
  type elt = view
  type t = elt
  let eq t1 t2 = try
                      Sy.equal t1.f t2.f
                      && List.for_all2 (==) t1.xs t2.xs
                      && Ty.equal t1.ty t2.ty
    with Invalid_argument _ -> false

  let equal = eq

  let hash t =
    abs (List.fold_left
	   (fun acc x-> acc*19 +x.tag) (Sy.hash t.f + Ty.hash t.ty)
	   t.xs)

  let set_id tag x = {x with tag = tag}

  let initial_size = 4096

  let disable_weaks () = Options.disable_weaks ()
end

module T = Make(H)

let view t = t

let rec print_silent fmt t =
  let {f=x;xs=l;ty=ty} = view t in
  match x, l with
    | Sy.Op Sy.Get, [e1; e2] ->
      fprintf fmt "%a[%a]" print e1 print e2

    | Sy.Op Sy.Set, [e1; e2; e3] ->
      fprintf fmt "%a[%a<-%a]" print e1 print e2 print e3

    | Sy.Op Sy.Concat, [e1; e2] ->
      fprintf fmt "%a@@%a" print e1 print e2

    | Sy.Op Sy.Extract, [e1; e2; e3] ->
      fprintf fmt "%a^{%a,%a}" print e1 print e2 print e3

    | Sy.Op (Sy.Access field), [e] ->
      fprintf fmt "%a.%s" print e (Hstring.view field)

    | Sy.Op (Sy.Record), _ ->
      begin match ty with
	| Ty.Trecord {Ty.lbs=lbs} ->
	  assert (List.length l = List.length lbs);
	  fprintf fmt "{";
	  ignore (List.fold_left2 (fun first (field,_) e ->
	    fprintf fmt "%s%s = %a"  (if first then "" else "; ")
	      (Hstring.view field) print e;
	    false
	  ) true lbs l);
	  fprintf fmt "}";
	| _ -> assert false
      end

    (* TODO: introduce PrefixOp in the future to simplify this ? *)
    | Sy.Op op, [e1; e2] when op == Sy.Pow_real_int || op == Sy.Max_real ||
        op == Sy.Max_int || op == Sy.Min_real || op == Sy.Min_int ||
        op == Sy.Pow_real_real || op == Sy.Integer_round ->
      fprintf fmt "%a(%a,%a)" Sy.print x print e1 print e2

    | Sy.Op op, [e1; e2] ->
      fprintf fmt "(%a %a %a)" print e1 Sy.print x print e2

    | Sy.In(lb, rb), [t] ->
      fprintf fmt "(%a in %a, %a)" print t Sy.print_bound lb Sy.print_bound rb
    | _, [] ->
      fprintf fmt "%a" Sy.print x

    | _, _ ->
      fprintf fmt "%a(%a)" Sy.print x print_list l

and print_verbose fmt t =
  fprintf fmt "(%a : %a)" print_silent t Ty.print (view t).ty

and print fmt t =
  if Options.debug () then print_verbose fmt t
  else print_silent fmt t

and print_list_sep sep fmt = function
  | [] -> ()
  | [t] -> print fmt t
  | t::l -> Format.fprintf fmt "%a%s%a" print t sep (print_list_sep sep) l

and print_list fmt = print_list_sep "," fmt


(*
   * We keep true and false as repr
   * ordering is influenced by depth
   * otherwise, we compare tag2 - tag1 so that fresh vars will be smaller
*)
let compare t1 t2 =
  if t1 == t2 then 0
  else
    let c = t1.depth - t2.depth in
    if c <> 0 then c
    else
      match (view t1).f, (view t2).f with
      | (Sy.True | Sy.False ), (Sy.True | Sy.False) -> t2.tag - t1.tag
      | (Sy.True | Sy.False ), _ -> -1
      | _, (Sy.True | Sy.False ) -> 1
      | _ -> t2.tag - t1.tag

let sort = List.sort compare

let merge_maps acc b =
  Sy.Map.merge (fun sy a b ->
    match a, b with
    | None, None -> assert false
    | Some _, None -> a
    | _ -> b
  ) acc b

let vars_of_make s l ty =
  lazy (
    match s, l with
    | Sy.Var _, [] -> Sy.Map.singleton s ty
    | Sy.Var _, _ -> assert false
    | _, [] -> Sy.Map.empty
    | _, e::r ->
      List.fold_left
        (fun s t -> merge_maps s (Lazy.force t.vars))
        (Lazy.force e.vars) r
  )

let vty_of_make l ty =
  lazy (
    List.fold_left
      (fun acc t -> Ty.Svty.union acc (Lazy.force t.vty))
      (Ty.vty_of ty) l
  )

let make s l ty =
  let d = 1 + List.fold_left (fun z t -> max z t.depth) 0 l in
  let nb_nodes = List.fold_left (fun z t -> z + t.nb_nodes) 1 l in
  let vars = vars_of_make s l ty in
  let vty = vty_of_make l ty in
  T.make {f=s; xs=l; ty=ty; depth=d; tag= -42; vars; vty; nb_nodes}

let fresh_name ty = make (Sy.name (Hstring.fresh_string())) [] ty

let is_fresh t =
  match view t with
    | {f=Sy.Name(hs,_);xs=[]} -> Hstring.is_fresh_string (Hstring.view hs)
    | _ -> false

let is_fresh_skolem t =
  match view t with
  | {f=Sy.Name(hs,_)} -> Hstring.is_fresh_skolem (Hstring.view hs)
  | _ -> false

let shorten t =
  let {f=f;xs=xs;ty=ty} = view t in
  make f xs (Ty.shorten ty)

let vrai = make (Sy.True) [] Ty.Tbool
let faux = make (Sy.False) [] Ty.Tbool
let void = make (Sy.Void) [] Ty.Tunit

let positive_int i = make (Sy.int i) [] Ty.Tint

let int i =
  let len = String.length i in
  assert (len >= 1);
  match i.[0] with
    | '-' ->
      assert (len >= 2);
      let pi = String.sub i 1 (len - 1) in
      make (Sy.Op Sy.Minus) [ positive_int "0"; positive_int pi ] Ty.Tint
    | _ -> positive_int i

let positive_real i = make (Sy.real i) [] Ty.Treal

let real r =
  let len = String.length r in
  assert (len >= 1);
  match r.[0] with
    | '-' ->
      assert (len >= 2);
      let pi = String.sub r 1 (len - 1) in
      make (Sy.Op Sy.Minus) [ positive_real "0"; positive_real pi ] Ty.Treal
    | _ -> positive_real r

let bitv bt ty = make (Sy.Bitv bt) [] ty

let is_int t = (view t).ty == Ty.Tint

let is_real t = (view t).ty == Ty.Treal

let equal t1 t2 =  t1 == t2

let hash t = t.tag

let pred t = make (Sy.Op Sy.Minus) [t;int "1"] Ty.Tint

module Set =
  Set.Make(struct type t' = t type t=t' let compare=compare end)

module Map =
  Map.Make(struct type t' = t type t=t' let compare=compare end)

let vars_of t acc = merge_maps acc (Lazy.force t.vars)

let vty_of t = Lazy.force t.vty

module Hsko = Hashtbl.Make(H)
let gen_sko ty = make (Sy.fresh "@sko") [] ty

let is_skolem_cst v =
  try
    Pervasives.(=) (String.sub (Sy.to_string v.f) 0 4) "_sko"
  with Invalid_argument _ -> false

let find_skolem =
  let hsko = Hsko.create 17 in
  fun v ty ->
    if is_skolem_cst v then
      try Hsko.find hsko v
      with Not_found ->
	let c = gen_sko ty in Hsko.add hsko v c; c
    else v

let is_ground t =
  Symbols.Map.is_empty (vars_of t Sy.Map.empty) && Ty.Svty.is_empty (vty_of t)

let rec apply_subst (s_t,s_ty) t =
  let {f=f;xs=xs;ty=ty; vars; vty} = view t in
  if is_ground t then t
  else
    let vars = Lazy.force vars in
    let vty = Lazy.force vty in
    let s_t = Sy.Map.filter (fun sy _ -> Sy.Map.mem sy vars) s_t in
    let s_ty = Ty.M.filter (fun id _ -> Ty.Svty.mem id vty) s_ty in
    if s_t == Sy.Map.empty && s_ty == Ty.M.empty then t
    else
      try
        let v = Sy.Map.find f s_t in
        find_skolem v ty
      with Not_found ->
        let s = s_t, s_ty in
        let xs', same = Lists.apply (apply_subst s) xs in
        let ty' = Ty.apply_subst s_ty ty in
        if same && ty == ty' then t
        else make f xs' ty'

let compare_subst (s_t1, s_ty1) (s_t2, s_ty2) =
  let c = Ty.compare_subst s_ty1 s_ty2 in
  if c<>0 then c else Sy.Map.compare compare s_t1 s_t2

let equal_subst (s_t1, s_ty1) (s_t2, s_ty2) =
  Ty.equal_subst s_ty1 s_ty2 || Sy.Map.equal equal s_t1 s_t2

let fold_subst_term f (s,_) acc = Sy.Map.fold f s acc

let union_subst (s_t1, s_ty1) ((s_t2, s_ty2) as subst) =
  let s_t =
    Sy.Map.fold
      (fun k x s2 -> Sy.Map.add k x s2)
      (Sy.Map.map (apply_subst subst) s_t1) s_t2
  in
  let s_ty = Ty.union_subst s_ty1 s_ty2 in
  s_t, s_ty

let rec subterms acc t =
  let {xs=xs} = view t in List.fold_left subterms (Set.add t acc) xs


module Labels = Hashtbl.Make(H)

let labels = Labels.create 100007

let add_label lbl t =
  Labels.replace labels t lbl

let label t = try Labels.find labels t with Not_found -> Hstring.empty


let label_model h =
  try Pervasives.(=) (String.sub (Hstring.view h) 0 6) "model:"
  with Invalid_argument _ -> false

let rec is_in_model_rec depth { f = f; xs = xs } =
  let lb = Symbols.label f in
  (label_model lb
   &&
     (try
	let md = Scanf.sscanf (Hstring.view lb) "model:%d" (fun x -> x) in
	depth <= md
      with Scanf.Scan_failure _ | End_of_file-> true))
  ||
    List.exists (is_in_model_rec (depth +1)) xs

let is_in_model t =
  label_model (label t) || is_in_model_rec 0 t


let is_labeled t = not (Hstring.equal (label t) Hstring.empty)

let print_tagged_classes fmt =
  List.iter (fun cl ->
    let cl = List.filter is_labeled (Set.elements cl) in
    if cl != [] then
      fprintf fmt "\n{ %a }" (print_list_sep " , ") cl)

let type_info t = t.ty
let top () = vrai
let bot () = faux


let apply_subst s t =
  if Options.timers() then
    try
      Timers.exec_timer_start Timers.M_Term Timers.F_apply_subst;
      let res = apply_subst s t in
      Timers.exec_timer_pause Timers.M_Term Timers.F_apply_subst;
      res
    with e ->
      Timers.exec_timer_pause Timers.M_Term Timers.F_apply_subst;
      raise e
  else apply_subst s t

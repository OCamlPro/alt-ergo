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
open Hconsing
open Options

module Sy = Symbols
module SMap = Sy.Map
module SSet = Sy.Set

(** Data structures *)

type binders = (Ty.t * int) SMap.t (*int tag in globally unique *)

type t = view

and view = {
  f: Sy.t;
  xs: t list;
  ty: Ty.t;
  bind : bind_kind;
  tag: int;
  vars : (Ty.t * int) SMap.t; (* vars to types and nb of occurences *)
  vty : Ty.Svty.t;
  depth: int;
  nb_nodes : int;
  pure : bool;
  mutable neg : t option
}

and decl_kind =
  | Dtheory
  | Daxiom
  | Dgoal
  | Dpredicate of t
  | Dfunction of t

and bind_kind =
  | B_none
  | B_lemma of quantified
  | B_skolem of quantified
  | B_let of letin

and quantified = {
  name : string;
  main : t;
  toplevel : bool;
  user_trs : trigger list;
  binders : binders;
  (* These fields should be (ordered) lists ! important for skolemization *)
  sko_v : t list;
  sko_vty : Ty.t list;
  loc : Loc.t; (* location of the "GLOBAL" axiom containing this quantified
                  formula. It forms with name a unique id *)
  kind : decl_kind;
}

and letin = {
  let_v: Sy.t;
  let_e : t;
  in_e : t;
  let_sko : t; (* fresh symb. with free vars *)
  is_bool : bool;
}

and semantic_trigger =
  | Interval of t * Sy.bound * Sy.bound
  | MapsTo of Var.t * t
  | NotTheoryConst of t
  | IsTheoryConst of t
  | LinearDependency of t * t

and trigger = {
  content : t list;
  (* this field is filled (with a part of 'content' field) by theories
     when assume_th_elt is called *)
  semantic : semantic_trigger list;
  hyp : t list;
  t_depth : int;
  from_user : bool;
  guard : t option
}

type expr = t

type subst = expr SMap.t * Ty.subst

type term_view =
  | Term of view
  | Not_a_term of {is_lit : bool}

type lit_view =
  | Eq of t * t
  | Eql of t list
  | Distinct of t list
  | Builtin of bool * Sy.builtin * t list
  | Pred of t * bool
  | Not_a_lit of { is_form : bool }

type form_view =
  | Unit of t*t  (* unit clauses *)
  | Clause of t*t*bool      (* a clause (t1 or t2) bool <-> is implication *)
  | Iff of t * t
  | Xor of t * t
  | Literal of t   (* an atom *)
  | Lemma of quantified   (* a lemma *)
  | Skolem of quantified  (* lazy skolemization *)
  | Let of letin (* a binding of an expr *)
  | Not_a_form


(** Comparison and hashing functions *)

(* We keep true and false as repr * ordering is influenced by
   depth. Constants are smaller. Otherwise, we compare tag1 - tag2 so
   that fresh vars will be smaller *)
(* XXX Uf.term_repr sensitive to the way this function is coded *)
let compare t1 t2 =
  if t1 == t2 then 0
  else
    let c = t1.depth - t2.depth in
    if c <> 0 then c
    else t1.tag - t2.tag

let equal t1 t2 =  t1 == t2

let hash t = t.tag

let uid t = t.tag

let compare_subst (s_t1, s_ty1) (s_t2, s_ty2) =
  let c = Ty.compare_subst s_ty1 s_ty2 in
  if c<>0 then c else SMap.compare compare s_t1 s_t2

let equal_subst (s_t1, s_ty1) (s_t2, s_ty2) =
  Ty.equal_subst s_ty1 s_ty2 || SMap.equal equal s_t1 s_t2

let compare_let let1 let2 =
  let c = Sy.compare let1.let_v let2.let_v in
  if c <> 0 then c
  else
    let c = compare let1.let_e let2.let_e in
    if c <> 0 then c
    else compare let1.in_e let2.in_e

let compare_binders b1 b2 =
  SMap.compare (fun (ty1,i) (ty2,j) ->
      let c = i - j in if c <> 0 then c else Ty.compare ty1 ty2)
    b1 b2

let [@inline always] compare_sko_xxx sk1 sk2 cmp_xxx =
  try
    List.iter2
      (fun s t ->
         let c = cmp_xxx s t in
         if c <> 0 then raise (Util.Cmp c)
      )sk1 sk2;
    0
  with
  | Util.Cmp c -> c
  | Invalid_argument _ -> List.length sk1 - List.length sk2

let compare_sko_vars sk1 sk2 = compare_sko_xxx sk1 sk2 compare

let compare_sko_vty sk1 sk2 = compare_sko_xxx sk1 sk2 Ty.compare

let compare_lists l1 l2 cmp_elts =
  let res = Util.cmp_lists l1 l2 cmp_elts in
  if res <> 0 then raise (Util.Cmp res)

let compare_triggers _f1 _f2 trs1 trs2 =
  try
    List.iter2
      (fun tr1 tr2 ->
         compare_lists tr1.content tr2.content compare;
         compare_lists tr1.hyp tr2.hyp compare;
         compare_lists tr1.semantic tr2.semantic
           (fun a b ->
              Util.compare_algebraic a b
                (function
                  | Interval (s, b1, b2), Interval (t, c1, c2) ->
                    let c = compare s t in
                    if c <> 0 then c
                    else
                      let c = Sy.compare_bounds b1 c1 in
                      if c <> 0 then c else Sy.compare_bounds b2 c2

                  | MapsTo (h1, t1), MapsTo (h2, t2) ->
                    let c = compare t1 t2 in
                    if c <> 0 then c else Var.compare h1 h2

                  | NotTheoryConst a, NotTheoryConst b
                  | IsTheoryConst a , IsTheoryConst b  -> compare a b

                  | LinearDependency (s1, t1), LinearDependency (s2, t2) ->
                    let c = compare s1 s2 in
                    if c <> 0 then c else compare t1 t2

                  | _, (Interval _ | MapsTo _ | NotTheoryConst _
                       | IsTheoryConst _ | LinearDependency _) ->
                    assert false
                )
           )
      ) trs1 trs2;
    0
  with
  | Util.Cmp c -> c
  | Invalid_argument _ -> List.length trs1 - List.length trs2

let compare_quant
    {main=f1; binders=b1; sko_v=sko_v1; sko_vty=free_vty1; user_trs=trs1; _}
    {main=f2; binders=b2; sko_v=sko_v2; sko_vty=free_vty2; user_trs=trs2; _}
  =
  let c = compare f1 f2 in
  if c <> 0 then c
  else
    let c = compare_binders b1 b2 in
    if c <> 0 then c
    else
      let c = compare_sko_vars sko_v1 sko_v2 in
      if c <> 0 then c
      else
        let c = compare_sko_vty free_vty1 free_vty2 in
        if c <> 0 then c
        else compare_triggers f1 f2 trs1 trs2

module Msbt : Map.S with type key = expr SMap.t =
  Map.Make
    (struct
      type t = expr SMap.t
      let compare a b = SMap.compare compare a b
    end)

module Msbty : Map.S with type key = Ty.t Ty.M.t =
  Map.Make
    (struct
      type t = Ty.t Ty.M.t
      let compare a b = Ty.M.compare Ty.compare a b
    end)

module TSet : Set.S with type elt = expr =
  Set.Make (struct type t = expr let compare = compare end)

module TMap : Map.S with type key = expr =
  Map.Make (struct type t = expr let compare = compare end)

module H = struct
  type elt = t
  type t = elt

  let eq t1 t2 = try
      Sy.equal t1.f t2.f
      && List.for_all2 (==) t1.xs t2.xs
      && Ty.equal t1.ty t2.ty
      &&
      Util.compare_algebraic t1.bind t2.bind
        (function
          | B_lemma q1, B_lemma q2
          | B_skolem q1, B_skolem q2 -> compare_quant q1 q2
          | B_let a, B_let b -> compare_let a b
          | _, (B_none | B_lemma _ | B_skolem _ | B_let _) -> assert false
        ) = 0
    with Invalid_argument _ -> false

  let equal = eq

  let hash t =
    abs @@
    List.fold_left
      (fun acc x-> acc * 23 + x.tag)
      (7 * Hashtbl.hash t.bind + 5 * Sy.hash t.f + Ty.hash t.ty)
      t.xs

  let set_id tag x = {x with tag = tag}

  let initial_size = 9001

  let disable_weaks () = Options.get_disable_weaks ()
end

module Labels = Hashtbl.Make(H)
module HC = Make(H)
module Hsko = Hashtbl.Make(H)

module F_Htbl : Hashtbl.S with type key = t =
  Hashtbl.Make(struct
    type t'=t
    type t = t'
    let hash = hash
    let equal = equal
  end)

(** different views of an expression *)

let lit_view t =
  let { f; xs; ty; _ } = t in
  if ty != Ty.Tbool then Not_a_lit {is_form = false}
  else
    match f with
    | Sy.Form _  -> Not_a_lit {is_form = true}
    | Sy.Lit lit ->
      begin match lit, xs with
        | (Sy.L_eq | Sy.L_neg_eq), ([] | [_]) -> assert false
        | Sy.L_eq, [a;b] -> Eq (a, b)
        | Sy.L_eq, l     -> Eql l
        | Sy.L_neg_eq, l -> Distinct l
        | Sy.L_built x, l -> Builtin(true, x, l)
        | Sy.L_neg_built x, l -> Builtin(false, x, l)
        | Sy.L_neg_pred, [a] -> Pred(a, true)
        | Sy.L_neg_pred, _ -> assert false
      end
    | _ -> Pred(t, false)

let form_view t =
  let { f; xs; bind; _ } = t in
  if t.ty != Ty.Tbool then Not_a_form
  else
    match f, xs, bind with
    | Sy.Form (Sy.F_Unit _), [a;b], _ -> Unit (a, b)
    | Sy.Form (Sy.F_Clause i), [a;b], _ -> Clause (a, b, i)
    | Sy.Form Sy.F_Iff, [a;b], _ -> Iff(a, b)
    | Sy.Form Sy.F_Xor, [a;b], _ -> Xor(a, b)
    | Sy.Form Sy.F_Lemma, [], B_lemma lem -> Lemma lem
    | Sy.Form Sy.F_Skolem, [], B_skolem sko -> Skolem sko
    | Sy.Lit (Sy.L_eq | Sy.L_neg_eq | Sy.L_neg_pred |
              Sy.L_built _ | Sy.L_neg_built _), _, _ ->
      Literal t
    | Sy.Let, [], B_let ({ is_bool = true; _ } as x) -> Let x

    | _ -> Literal t

let term_view t =
  let { f; ty; _ } = t in
  if ty != Ty.Tbool then Term t
  else match f with
    | Sy.Form _ -> Not_a_term {is_lit = false}
    | Sy.Lit _  -> Not_a_term {is_lit = true}
    | _ -> Term t (* bool term *)

(** pretty printing *)

let print_binders =
  let print_one fmt (sy, (ty, _)) =
    fprintf fmt "%a:%a" Sy.print sy Ty.print ty
  in fun fmt b ->
    match SMap.bindings b with
    | [] ->
      (* can happen when quantifying only on type variables *)
      fprintf fmt "(no term variables)"
    | e::l ->
      print_one fmt e;
      List.iter (fun e -> fprintf fmt ", %a" print_one e) l

let rec print_silent fmt t =
  let { f ; xs ; ty; bind; _ } = t in
  match f, xs with
  (* Formulas *)
  | Sy.Form form, xs ->
    begin
      match form, xs, bind with
      | Sy.F_Unit _, [f1; f2], _ ->
        fprintf fmt "@[(%a /\\@ %a)@]" print_silent f1 print_silent f2

      | Sy.F_Iff, [f1; f2], _ ->
        fprintf fmt "@[(%a <->@ %a)@]" print_silent f1 print_silent f2

      | Sy.F_Xor, [f1; f2], _ ->
        fprintf fmt "@[(%a xor@ %a)@]" print_silent f1 print_silent f2

      | Sy.F_Clause _, [f1; f2], _ ->
        fprintf fmt "@[(%a \\/@ %a)@]" print_silent f1 print_silent f2

      | Sy.F_Lemma, [], B_lemma { user_trs ; main ; name ; binders; _ } ->
        if get_verbose () then
          fprintf fmt "(lemma: %s forall %a[%a].@  %a)"
            name
            print_binders binders
            print_triggers user_trs
            print_silent main
        else
          fprintf fmt "(lem %s)" name

      | Sy.F_Skolem, [], B_skolem { main; binders; _ } ->
        fprintf fmt "(<sko exists %a.> %a)"
          print_binders binders print_silent main

      | _ -> assert false
    end

  | Sy.Let, [] ->
    let x = match bind with B_let x -> x | _ -> assert false in
    fprintf fmt
      "(let%a %a =@ %a in@ %a)"
      (fun fmt x -> if Options.get_verbose () then
          fprintf fmt
            " [sko = %a]" print x.let_sko) x
      Sy.print x.let_v print x.let_e print_silent x.in_e

  (* Literals *)
  | Sy.Lit lit, xs ->
    begin
      match lit, xs with
      | Sy.L_eq, a::l ->
        fprintf fmt "(%a%a)"
          print a (fun fmt -> List.iter (fprintf fmt " = %a" print)) l

      | Sy.L_neg_eq, [a; b] ->
        fprintf fmt "(%a <> %a)" print a print b

      | Sy.L_neg_eq, a::l ->
        fprintf fmt "distinct(%a%a)"
          print a (fun fmt -> List.iter (fprintf fmt ", %a" print)) l

      | Sy.L_built Sy.LE, [a;b] ->
        fprintf fmt "(%a <= %a)" print a print b

      | Sy.L_built Sy.LT, [a;b] ->
        fprintf fmt "(%a < %a)" print a print b

      | Sy.L_neg_built Sy.LE, [a; b] ->
        fprintf fmt "(%a > %a)" print a print b

      | Sy.L_neg_built Sy.LT, [a; b] ->
        fprintf fmt "(%a >= %a)" print a print b

      | Sy.L_neg_pred, [a] ->
        fprintf fmt "(not %a)" print a

      | Sy.L_built (Sy.IsConstr hs), [e] ->
        fprintf fmt "(%a ? %a)" print e Hstring.print hs

      | Sy.L_neg_built (Sy.IsConstr hs), [e] ->
        fprintf fmt "not (%a ? %a)" print e Hstring.print hs

      | (Sy.L_built (Sy.LT | Sy.LE) | Sy.L_neg_built (Sy.LT | Sy.LE)
        | Sy.L_neg_pred | Sy.L_eq | Sy.L_neg_eq
        | Sy.L_built (Sy.IsConstr _)
        | Sy.L_neg_built (Sy.IsConstr _)) , _ ->
        assert false

    end

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
      | Ty.Trecord { Ty.lbs = lbs; _ } ->
        assert (List.length xs = List.length lbs);
        fprintf fmt "{";
        ignore (List.fold_left2 (fun first (field,_) e ->
            fprintf fmt "%s%s = %a"  (if first then "" else "; ")
              (Hstring.view field) print e;
            false
          ) true lbs xs);
        fprintf fmt "}";
      | _ -> assert false
    end

  (* TODO: introduce PrefixOp in the future to simplify this ? *)
  | Sy.Op op, [e1; e2] when op == Sy.Pow || op == Sy.Integer_round ||
                            op == Sy.Max_real || op == Sy.Max_int ||
                            op == Sy.Min_real || op == Sy.Min_int ->
    fprintf fmt "%a(%a,%a)" Sy.print f print e1 print e2

  (* TODO: introduce PrefixOp in the future to simplify this ? *)
  | Sy.Op (Sy.Constr hs), ((_::_) as l) ->
    fprintf fmt "%a(%a)" Hstring.print hs print_list l

  | Sy.Op _, [e1; e2] ->
    fprintf fmt "(%a %a %a)" print e1 Sy.print f print e2

  | Sy.Op Sy.Destruct (hs, grded), [e] ->
    fprintf fmt "%a#%s%a"
      print e (if grded then "" else "!") Hstring.print hs


  | Sy.In(lb, rb), [t] ->
    fprintf fmt "(%a in %a, %a)" print t Sy.print_bound lb Sy.print_bound rb


  | _, [] ->
    fprintf fmt "%a" Sy.print f

  | _, _ ->
    fprintf fmt "%a(%a)" Sy.print f print_list xs

and print_verbose fmt t =
  fprintf fmt "(%a : %a)" print_silent t Ty.print t.ty

and print fmt t =
  if Options.get_debug () then print_verbose fmt t
  else print_silent fmt t

and print_list_sep sep fmt = function
  | [] -> ()
  | [t] -> print fmt t
  | t::l -> Format.fprintf fmt "%a%s%a" print t sep (print_list_sep sep) l

and print_list fmt = print_list_sep "," fmt

and print_triggers fmt trs =
  List.iter (fun { content = l; _ } ->
      fprintf fmt "| %a@," print_list l;
    ) trs


(** Some auxiliary functions *)

let type_info t = t.ty

(* unused
   let is_term e = match e.f with
   | Sy.Form _ | Sy.Lit _  -> false
   | _ -> true (* bool vars are terms *)
*)

let mk_binders =
  let cpt = ref 0 in
  fun st ->
    TSet.fold
      (fun t sym ->
         incr cpt;
         match t with
         | { f = (Sy.Var _) as v; ty; _ } -> SMap.add v (ty, !cpt) sym
         | _ -> assert false
      )st SMap.empty


let merge_vars acc b =
  SMap.merge (fun sy a b ->
      match a, b with
      | None, None -> assert false
      | Some _, None -> a
      | None, Some _ -> b
      | Some (ty, x), Some (ty', y) ->
        assert (Ty.equal ty ty' || Sy.equal sy Sy.underscore);
        Some (ty, x + y)
    ) acc b

let free_vars t acc = merge_vars acc t.vars

let free_type_vars t = t.vty

let is_ground t =
  SMap.is_empty (free_vars t SMap.empty) &&
  Ty.Svty.is_empty (free_type_vars t)

let id _ = 0

let size t = t.nb_nodes

let depth t = t.depth

let rec is_positive e =
  let { f; bind; _ } = e in
  match f, bind with
  | Sy.Lit (Sy.L_neg_pred | Sy.L_neg_eq | Sy.L_neg_built _), _ -> false
  | Sy.Form (Sy.F_Clause _ | Sy.F_Skolem | Sy.F_Xor), _ -> false
  | Sy.Let, B_let { in_e; is_bool = true; _ } -> is_positive in_e
  | _ -> true

let neg t =
  match t with
  | { ty = Ty.Tbool; neg = Some n; _ } -> n
  | { f = _; _ } -> assert false

let is_int t = t.ty == Ty.Tint
let is_real t = t.ty == Ty.Treal

let is_fresh t =
  match t with
  | { f = Sy.Name (hs,_); xs = []; _ } ->
    Hstring.is_fresh_string (Hstring.view hs)
  | _ -> false

let is_fresh_skolem t =
  match t with
  | { f = Sy.Name (hs,_); _ } -> Hstring.is_fresh_skolem (Hstring.view hs)
  | _ -> false

let name_of_lemma f =
  match form_view f with
  | Lemma { name; _ } -> name
  | _ -> assert false

let name_of_lemma_opt opt =
  match opt with
  | None -> "(Lemma=None)"
  | Some f -> name_of_lemma f


(** Labeling and models *)

let labels = Labels.create 107

let add_label =
  let add_aux lbl t = Labels.replace labels t lbl in
  fun lbl e ->
    match e with
    | { f = Sy.Form _; _ } -> ()
    | { f = Sy.Lit _; _ } | { ty = Ty.Tbool; _ } ->
      add_aux lbl e;
      add_aux lbl (neg e)
    | _ ->
      add_aux lbl e

let label t =
  try Labels.find labels t
  with Not_found ->
    let { f = f; _ } = t in
    Sy.label f

let is_model_label =
  let model = "model:" in
  fun h ->
    try String.equal (String.sub (Hstring.view h) 0 6) model
    with Invalid_argument _ -> false

let rec is_in_model_rec depth { f = f; xs = xs ; _ } =
  let lb = Sy.label f in
  (is_model_label lb
   &&
   (try depth <= Scanf.sscanf (Hstring.view lb) "model:%d" (fun x -> x)
    with Scanf.Scan_failure _ | End_of_file-> true))
  ||
  List.exists (is_in_model_rec (depth +1)) xs

let rec is_in_model e =
  is_model_label (label e) ||
  match e with
  | { f = Sy.Form _; _ } -> false
  | { f = Sy.Lit _ ; xs; _ } -> List.exists is_in_model xs
  | _ -> is_in_model_rec 0 e

let print_tagged_classes =
  let is_labeled t = not (Hstring.equal (label t) Hstring.empty) in
  fun fmt l ->
    List.iter (fun cl ->
        let cl = List.filter is_labeled (TSet.elements cl) in
        if cl != [] then
          fprintf fmt "\n{ %a }" (print_list_sep " , ") cl) l


(** smart constructors for terms *)

let free_vars_non_form s l ty =
  match s, l with
  | Sy.Var _, [] -> SMap.singleton s (ty, 1)
  | Sy.Var _, _ -> assert false
  | Sy.Form _, _ -> assert false (* not correct for quantified and Lets *)
  | _, [] -> SMap.empty
  | _, e::r -> List.fold_left (fun s t -> merge_vars s t.vars) e.vars r

let free_type_vars_non_form l ty =
  List.fold_left (fun acc t -> Ty.Svty.union acc t.vty) (Ty.vty_of ty) l

let is_ite s = match s with
  | Sy.Op Sy.Tite -> true
  | _ -> false

let mk_term s l ty =
  assert (match s with Sy.Lit _ | Sy.Form _ -> false | _ -> true);
  let d = match l with
    | [] ->
      1 (*no args ? depth = 1 (ie. current app s, ie constant)*)
    | _ ->
      (* if args, d is 1 + max_depth of args (equals at least to 1 *)
      1 + List.fold_left (fun z t -> max z t.depth) 1 l
  in
  let nb_nodes = List.fold_left (fun z t -> z + t.nb_nodes) 1 l in
  let vars = free_vars_non_form s l ty in
  let vty = free_type_vars_non_form l ty in
  let pure = List.for_all (fun e -> e.pure) l && not (is_ite s) in
  let pos =
    HC.make {f=s; xs=l; ty=ty; depth=d; tag= -42; vars; vty;
             nb_nodes; neg = None; bind = B_none; pure}
  in
  if ty != Ty.Tbool then pos
  else if pos.neg != None then pos
  else
    let neg_s = Sy.Lit Sy.L_neg_pred in
    let neg =
      HC.make {f=neg_s; xs=[pos]; ty=ty; depth=d; tag= -42;
               vars; vty; nb_nodes; neg = None; bind = B_none; pure = false}
    in
    assert (neg.neg == None);
    pos.neg <- Some neg;
    neg.neg <- Some pos;
    pos

let vrai =
  let res =
    let nb_nodes = 0 in
    let vars = SMap.empty in
    let vty = Ty.Svty.empty in
    let faux =
      HC.make
        {f = Sy.False; xs = []; ty = Ty.Tbool; depth = -2; (*smallest depth*)
         tag = -42; vars; vty; nb_nodes; neg = None; bind = B_none;
         pure = true}
    in
    let vrai =
      HC.make
        {f = Sy.True;  xs = []; ty = Ty.Tbool; depth = -1; (*2nd smallest d*)
         tag= -42; vars; vty; nb_nodes; neg = None; bind = B_none;
         pure = true}
    in
    assert (vrai.neg == None);
    assert (faux.neg == None);
    vrai.neg <- Some faux;
    faux.neg <- Some vrai;
    vrai
  in
  res

let faux = neg (vrai)
let void = mk_term (Sy.Void) [] Ty.Tunit

let fresh_name ty = mk_term (Sy.name (Hstring.fresh_string())) [] ty

let positive_int i = mk_term (Sy.int i) [] Ty.Tint

let int i =
  let len = String.length i in
  assert (len >= 1);
  match i.[0] with
  | '-' ->
    assert (len >= 2);
    let pi = String.sub i 1 (len - 1) in
    mk_term (Sy.Op Sy.Minus) [ positive_int "0"; positive_int pi ] Ty.Tint
  | _ -> positive_int i

let positive_real i = mk_term (Sy.real i) [] Ty.Treal

let real r =
  let len = String.length r in
  assert (len >= 1);
  match r.[0] with
  | '-' ->
    assert (len >= 2);
    let pi = String.sub r 1 (len - 1) in
    mk_term (Sy.Op Sy.Minus) [ positive_real "0"; positive_real pi ] Ty.Treal
  | _ -> positive_real r

let bitv bt ty = mk_term (Sy.Bitv bt) [] ty

let pred t = mk_term (Sy.Op Sy.Minus) [t;int "1"] Ty.Tint


(** simple smart constructors for formulas *)

let mk_or f1 f2 is_impl _id =
  if equal f1 (neg f2) then vrai
  else
  if equal f1 f2 then f1
  else if equal f1 (faux) then f2
  else if equal f2 (faux) then f1
  else if (equal f1 (vrai)) || (equal f2 (vrai)) then vrai
  else
    let f1, f2 = if is_impl || compare f1 f2 < 0 then f1, f2 else f2, f1 in
    let d = (max f1.depth f2.depth) in (* the +1 causes regression *)
    let nb_nodes = f1.nb_nodes + f2.nb_nodes + 1 in
    let vars = merge_vars f1.vars f2.vars in
    let vty = Ty.Svty.union f1.vty f2.vty in
    let pos =
      HC.make {f=Sy.Form (Sy.F_Clause is_impl); xs=[f1; f2]; ty=Ty.Tbool;
               depth=d; tag= -42; vars; vty; nb_nodes; neg = None;
               bind = B_none; pure = false}
    in
    if pos.neg != None then pos
    else
      let neg =
        HC.make
          {f=Sy.Form (Sy.F_Unit is_impl); xs=[neg f1; neg f2]; ty=Ty.Tbool;
           depth=d; tag= -42; vars; vty; nb_nodes; neg = None;
           bind = B_none; pure = false}
      in
      assert (neg.neg == None);
      pos.neg <- Some neg;
      neg.neg <- Some pos;
      pos

let mk_iff f1 f2 _id =
  if equal f1 (neg f2) then faux
  else if equal f1 f2 then vrai
  else if equal f1 faux then neg f2
  else if equal f2 faux then neg f1
  else if equal f1 vrai then f2
  else if equal f2 vrai then f1
  else
    let d = (max f1.depth f2.depth) in (* the +1 causes regression *)
    let nb_nodes = f1.nb_nodes + f2.nb_nodes + 1 in
    let vars = merge_vars f1.vars f2.vars in
    let vty = Ty.Svty.union f1.vty f2.vty in
    let pos =
      HC.make {f=Sy.Form Sy.F_Iff; xs=[f1; f2]; ty=Ty.Tbool;
               depth=d; tag= -42; vars; vty; nb_nodes; neg = None;
               bind = B_none; pure = false}
    in
    if pos.neg != None then pos
    else
      let neg =
        HC.make
          {f=Sy.Form Sy.F_Xor; xs=[f1; f2]; ty=Ty.Tbool;
           depth=d; tag= -42; vars; vty; nb_nodes; neg = None;
           bind = B_none; pure = false}
      in
      assert (neg.neg == None);
      pos.neg <- Some neg;
      neg.neg <- Some pos;
      pos

let mk_and f1 f2 is_impl id =
  neg @@ mk_or (neg f1) (neg f2) is_impl id

let mk_imp f1 f2 id = mk_or (neg f1) f2 true id

let mk_xor f1 f2 id =
  neg (mk_iff f1 f2 id)

let mk_if cond f2 f3 id =
  mk_or
    (mk_and cond f2 true id) (mk_and (neg cond) f3 true id) false id

let mk_ite cond th el id =
  let ty = type_info th in
  if ty == Ty.Tbool then mk_if cond th el id
  else mk_term (Sy.Op Sy.Tite) [cond; th; el] ty

let [@inline always] const_term e =
  (* we use this function because depth is currently not correct to
     detect constants (not incremented in some situations due to
     some regression) *)
  match e.f with
  | Sy.Form _ | Sy.Lit _ | Sy.Let  -> false
  | True | False | Void | Name _ | Int _ | Real _ | Bitv _
  | Op _ | Var _ | In _ | MapsTo _ ->
    let res = (e.xs == []) in
    assert (res == (depth e <= 1));
    res

let mk_forall_ter =
  let env = F_Htbl.create 101 in
  fun new_q _id ->
    let { name; main = f; _ } = new_q in
    (* when calling mk_forall_ter, binders should not contains
       ununsed binders. Eventual simplification is done in
       mk_forall_bis, which calls mk_forall_ter *)
    assert (SMap.for_all (fun sy _ -> SMap.mem sy f.vars) new_q.binders);
    if is_ground f then f
    else
      try
        let lem = F_Htbl.find env f in
        let q = match form_view lem with Lemma q -> q | _ -> assert false in
        assert (equal q.main f (* should be true *));
        if compare_quant q new_q <> 0 then raise Exit;
        Printer.print_wrn ~warning:(get_debug_warnings ())
          "(sub) axiom %s replaced with %s" name q.name;
        lem
      with Not_found | Exit ->
        let d = new_q.main.depth in (* + 1 ?? *)
        let nb_nodes = new_q.main.nb_nodes + 1 in
        (* prenex polymorphism. If sko_vty is not empty, then we are at
           toplevel and all free_vtys of lem.main are quantified in this
           lemma. Otherwise (if not toplevel), the free vtys of the lemma
           are those of lem.main *)
        let vty =
          if new_q.toplevel then Ty.Svty.empty
          else free_type_vars new_q.main
        in
        let vars =
          SMap.filter (fun v _ -> not (SMap.mem v new_q.binders))
            (free_vars f SMap.empty)
            (* this assumes that eventual variables in hypotheses are
               binded here *)
        in
        let sko = { new_q with main = neg f} in
        let pos =
          HC.make {f=Sy.Form Sy.F_Lemma; xs=[]; ty=Ty.Tbool;
                   depth=d; tag= -42; vars; vty; nb_nodes; neg = None;
                   bind = B_lemma new_q; pure = false}
        in
        let neg =
          HC.make {f=Sy.Form Sy.F_Skolem; xs=[]; ty=Ty.Tbool;
                   depth=d; tag= -42; vars; vty; nb_nodes; neg = None;
                   bind = B_skolem sko; pure = false}
        in
        pos.neg <- Some neg;
        neg.neg <- Some pos;
        F_Htbl.add env f pos;
        pos

let has_semantic_triggers trs =
  List.exists (fun tr -> tr.semantic != []) trs

let has_hypotheses trs =
  List.exists (fun tr -> tr.hyp != []) trs

let no_occur_check v e =
  not (SMap.mem v e.vars)

let no_vtys l =
  List.for_all (fun e -> Ty.Svty.is_empty e.vty) l

(** smart constructors for literals *)

(* unused
   let is_non_atomic_form e = match e.f with
   | Sy.Form _ -> true
   | _ -> false
*)

(* intended to be used for mk_eq or mk_builtin only *)
let mk_positive_lit s neg_s l =
  let ty = Ty.Tbool in
  assert (
    let open Sy in
    match s with
    | Lit (L_eq | L_built _) -> true
    | Lit (L_neg_eq | L_neg_pred | L_neg_built _) | Form _
    | True | False | Void | Name _ | Int _ | Real _ | Bitv _
    | Op _ | Var _ | In _ | MapsTo _ | Let -> false
  );
  let d = 1 + List.fold_left (fun z t -> max z t.depth) 1 l in
  let nb_nodes = List.fold_left (fun z t -> z + t.nb_nodes) 1 l in
  let vars = free_vars_non_form s l ty in
  let vty = free_type_vars_non_form l ty in
  let pos =
    HC.make {f=s; xs=l; ty=ty; depth=d; tag= -42; vars; vty;
             nb_nodes; neg = None;
             bind = B_none; pure = false}
  in
  if pos.neg != None then pos
  else
    let neg =
      HC.make {f=neg_s; xs=l; ty=ty; depth=d; tag= -42;
               vars; vty; nb_nodes; neg = None;
               bind = B_none; pure = false}
    in
    assert (neg.neg == None);
    pos.neg <- Some neg;
    neg.neg <- Some pos;
    pos

let mk_eq ~iff t1 t2 =
  let c = compare t1 t2 in
  if c = 0 then vrai
  else
    let t1, t2 = if c < 0 then t1, t2 else t2, t1 in
    if type_info t1 == Ty.Tbool then
      if t1 == neg t2 then faux
      else
        (* translate to iff, eventual simplification made in mk_or *)
        let res = mk_iff t1 t2 0 in
        match res.f with
        | Sy.Form _ when not iff ->
          (* in some situation (eg. theories deductions, mk_iff may
             be disabled due to invariants *)
          (* TODO: be able to build IFF even in theories ? *)
          mk_positive_lit (Sy.Lit Sy.L_eq) (Sy.Lit Sy.L_neg_eq) [t1; t2]
        | _ ->
          (*iff has been simplified *)
          res
    else
      mk_positive_lit (Sy.Lit Sy.L_eq) (Sy.Lit Sy.L_neg_eq) [t1; t2]

let mk_nary_eq l =
  try
    let l = List.fast_sort (fun a b -> compare b a) l in (* decreasing *)
    match l with
    | [] | [_] | [_;_] -> assert false
    | e::r ->
      let _ =
        List.fold_left
          (fun last e ->
             if equal last e then raise Exit;
             e
          ) e r
      in
      if type_info e == Ty.Tbool then
        List.fold_left (fun x y -> mk_iff x y 0) e  r
      else
        mk_positive_lit (Sy.Lit Sy.L_eq) (Sy.Lit Sy.L_neg_eq) l
  with Exit ->
    vrai

let mk_distinct ~iff tl =
  match tl with
  | [a; b] -> neg (mk_eq ~iff a b)
  | _ -> neg (mk_nary_eq tl)

let mk_builtin ~is_pos n l =
  let pos =
    mk_positive_lit (Sy.Lit (Sy.L_built n)) (Sy.Lit (Sy.L_neg_built n)) l
  in
  if is_pos then pos else neg pos


(** Substitutions *)

let is_skolem_cst v =
  try String.equal (String.sub (Sy.to_string v.f) 0 4) "_sko"
  with Invalid_argument _ -> false

let get_skolem =
  let hsko = Hsko.create 17 in
  let gen_sko ty = mk_term (Sy.fresh "@sko") [] ty in
  fun v ty ->
    try Hsko.find hsko v
    with Not_found ->
      let c = gen_sko ty in Hsko.add hsko v c; c

let no_capture_issue s_t binders =
  let new_v =
    SMap.fold (fun _ t acc -> merge_vars acc t.vars) s_t SMap.empty
  in
  let capt_bind = SMap.filter (fun sy _ -> SMap.mem sy new_v) binders in
  if SMap.is_empty capt_bind then true
  else
    begin
      Printer.print_wrn
        "captures between@,%aand%a!@,(captured = %a)"
        (SMap.print print) s_t
        print_binders binders
        print_binders capt_bind;
      false
    end

let rec apply_subst_aux (s_t, s_ty) t =
  if is_ground t || (SMap.is_empty s_t && Ty.M.is_empty s_ty) then t
  else
    let { f; xs; ty; vars; vty; bind; _ } = t in
    let s_t = SMap.filter (fun sy _ -> SMap.mem sy vars) s_t in
    let s_ty = Ty.M.filter (fun tvar _ -> Ty.Svty.mem tvar vty) s_ty in
    if SMap.is_empty s_t && Ty.M.is_empty s_ty then t
    else
      let s = s_t, s_ty in
      let xs', same = Lists.apply (apply_subst_aux s) xs in
      let ty' = Ty.apply_subst s_ty ty in
      (*invariant: we are sure that the subst will impact xs or ty
         (or inside a lemma/skolem or let) *)
      assert (xs == [] || not same || not (Ty.equal ty ty'));
      match f, bind with
      | Sy.Var _, _ ->
        assert (xs == []);
        begin
          try
            let v = SMap.find f s_t in
            if is_skolem_cst v then get_skolem v ty else v
          with Not_found ->
            mk_term f [] ty'
        end

      | Sy.Form (Sy.F_Lemma | Sy.F_Skolem), (B_lemma q | B_skolem q) ->
        assert (xs == []);
        let { main; user_trs = trs; binders; sko_v; sko_vty; _ } = q
        in
        (* TODO: implement case where variables capture happens *)
        assert (no_capture_issue s_t binders);
        assert (
          (* invariant: s_t does not contain other free vars than
             those of t, and binders cannot be free vars of t *)
          not (Options.get_enable_assertions ()) ||
          SMap.for_all (fun sy _ -> not (SMap.mem sy s_t)) binders
        );
        let main = apply_subst_aux s main in
        let trs = List.map (apply_subst_trigger s) trs in
        let binders =
          SMap.fold
            (fun sy (ty,i) bders ->
               let ty' = Ty.apply_subst s_ty ty in
               if Ty.equal ty ty' then bders
               else SMap.add sy (ty', i) bders
            )binders binders
        in
        let sko_v = List.map (apply_subst_aux s) sko_v in
        let sko_vty = List.map (Ty.apply_subst s_ty) sko_vty in
        let q = {q with
                 main; user_trs = trs; binders = binders; sko_v;
                 sko_vty}
        in
        begin match f with
          | Sy.Form Sy.F_Lemma  ->
            mk_forall_bis q 0

          | Sy.Form Sy.F_Skolem ->
            neg @@ mk_forall_bis {q with main = neg main} 0
          | _ -> assert false
        end

      | Sy.Let, B_let {let_v; let_e; in_e ; let_sko; is_bool} ->
        assert (xs == []);
        (* TODO: implement case where variables capture happens *)
        assert (no_capture_issue s_t (SMap.singleton let_v (let_e.ty, 0)));
        let let_e2 = apply_subst_aux s let_e in
        let let_sko2 = apply_subst_aux s let_sko in
        (* invariant: s_t only contains vars that are in free in t,
           and let_v cannot be free in t*)
        assert (not (SMap.mem let_v s_t));
        let in_e2 = apply_subst_aux (SMap.remove let_v s_t, s_ty) in_e in
        assert (let_e != let_e2 || in_e != in_e2);
        mk_let_aux {let_v; let_e=let_e2; in_e=in_e2; let_sko=let_sko2; is_bool}

      | Sy.Lit Sy.L_eq, _ ->
        begin match xs' with
          | [] | [_] -> assert false
          | [a; b] ->  mk_eq ~iff:true a b
          | _ -> mk_nary_eq xs'
        end

      | Sy.Lit Sy.L_neg_eq, _ ->
        mk_distinct ~iff:true xs'

      | Sy.Lit Sy.L_neg_pred, _ ->
        neg (match xs' with [e] -> e | _ -> assert false)

      | Sy.Lit (Sy.L_built n), _ ->
        mk_builtin ~is_pos:true n xs'

      | Sy.Lit (Sy.L_neg_built n), _ ->
        mk_builtin ~is_pos:false n xs'

      | Sy.Form (Sy.F_Unit _), _ ->
        begin match xs' with
          | [u; v] -> mk_and u v false (*b*) 0
          | _ -> assert false
        end

      | Sy.Form (Sy.F_Clause b), _ ->
        begin match xs' with
          | [u; v] -> mk_or u v b 0
          | _ -> assert false
        end

      | Sy.Form Sy.F_Iff, _ ->
        begin match xs' with
          | [u; v] -> mk_iff u v 0
          | _ -> assert false
        end

      | Sy.Form Sy.F_Xor, _ ->
        begin match xs' with
          | [u; v] -> mk_xor u v 0
          | _ -> assert false
        end

      | _ ->
        mk_term f xs' ty'

and apply_subst_trigger subst ({ content; guard; _ } as tr) =
  {tr with
   content = List.map (apply_subst_aux subst) content;
   (* semantic_trigger = done on theory side *)
   (* hyp = done on theory side *)
   guard =
     match guard with
     | None -> guard
     | Some g -> Some (apply_subst_aux subst g)
  }

(* *1* We should never subst formulas inside termes. We could allow to
   substitute "let x = form" inside non-pure expressions as long as
   they are not inside terms. But currently, we cannot detect this
   efficiently *)
and mk_let_aux ({ let_v; let_e; in_e; _ } as x) =
  try
    let _, nb_occ = SMap.find let_v in_e.vars in
    if nb_occ = 1 && (let_e.pure (*1*) || Sy.equal let_v in_e.f) ||
       const_term let_e then (* inline in these situations *)
      apply_subst_aux (SMap.singleton let_v let_e, Ty.esubst) in_e
    else
      let ty = type_info in_e in
      let d = max let_e.depth in_e.depth in (* no + 1 ? *)
      let nb_nodes = let_e.nb_nodes + in_e.nb_nodes + 1 (* approx *) in
      (* do not include free vars in let_sko that have been simplified *)
      let vars = merge_vars let_e.vars (SMap.remove let_v in_e.vars) in
      let vty = Ty.Svty.union let_e.vty in_e.vty in
      let pos =
        HC.make {f=Sy.Let; xs=[]; ty;
                 depth=d; tag= -42; vars; vty; nb_nodes; neg = None;
                 bind = B_let x; pure = false}
      in
      if pos.neg != None || not x.is_bool then pos
      else
        let y = {x with in_e = neg in_e} in
        let neg =
          HC.make {f=Sy.Let; xs=[]; ty;
                   depth=d; tag= -42; vars; vty; nb_nodes; neg = None;
                   bind = B_let y; pure = false}
        in
        pos.neg <- Some neg;
        neg.neg <- Some pos;
        pos
  with Not_found -> in_e (* let_v does not appear in in_e *)

and mk_forall_bis (q : quantified) id =
  let binders =  (* ignore binders that are not used in f *)
    SMap.filter (fun sy _ -> SMap.mem sy q.main.vars) q.binders
  in
  if SMap.is_empty binders && Ty.Svty.is_empty q.main.vty then q.main
  else
    let q = {q with binders} in
    match find_particular_subst binders q.user_trs q.main with
    | None -> mk_forall_ter q 0

    | Some sbs ->
      let subst = sbs, Ty.esubst in
      let f = apply_subst_aux subst q.main in
      if is_ground f then f
      else
        let trs = List.map (apply_subst_trigger subst) q.user_trs in
        let sko_v   = List.map (apply_subst_aux subst) q.sko_v in
        let binders = SMap.filter (fun x _ -> not (SMap.mem x sbs)) binders in
        let q = {q with binders; user_trs = trs; sko_v; main = f } in
        mk_forall_bis q id

and find_particular_subst =
  let exception Found of Sy.t * t in
  (* ex: in "forall x, y : int. x <> 1 or f(y) = x+1 or P(x,y)",
     x can be replaced with 1 *)
  let rec find_subst v tv f =
    match form_view f with
    | Not_a_form -> assert false
    | Unit _ | Lemma _ | Skolem _ | Let _ | Iff _ | Xor _ -> ()
    | Clause(f1, f2,_) -> find_subst v tv f1; find_subst v tv f2
    | Literal a ->
      match lit_view a with
      | Distinct [a;b] when
          equal tv a && no_occur_check v b && no_vtys [tv;a] ->
        (* TODO: should unify when type variables are present *)
        raise (Found (v, b))

      | Distinct [a;b] when
          equal tv b && no_occur_check v a && no_vtys [tv; b] ->
        (* TODO: should unify when type variables are present *)
        raise (Found (v, a))

      | Pred (t, is_neg) when equal tv t ->
        raise (Found (v, if is_neg then vrai else faux))

      | _ -> ()
  in
  fun binders trs f ->
    if not (Ty.Svty.is_empty f.vty) || has_hypotheses trs ||
       has_semantic_triggers trs
    then
      None
    else
      begin
        assert (not (SMap.is_empty binders));
        let sbt =
          SMap.fold
            (fun v (ty, _) sbt ->
               try
                 let f = apply_subst_aux (sbt, Ty.esubst) f in
                 find_subst v (mk_term v [] ty) f;
                 sbt
               with Found (x, t) ->
                 assert (not (SMap.mem x sbt));
                 let one_sbt = SMap.singleton x t, Ty.esubst in
                 let sbt = SMap.map (apply_subst_aux one_sbt) sbt in
                 SMap.add x t sbt
            )binders SMap.empty
        in
        if SMap.is_empty sbt then None else Some sbt
      end


let apply_subst =
  let (cache : t Msbty.t Msbt.t TMap.t ref) = ref TMap.empty in
  fun ((sbt, sbty) as s) f ->
    let ch = !cache in
    try TMap.find f ch |> Msbt.find sbt |> Msbty.find sbty
    with Not_found ->
      let nf = apply_subst_aux s f in
      let c_sbt = try TMap.find f ch with Not_found -> Msbt.empty in
      let c_sbty = try Msbt.find sbt c_sbt with Not_found -> Msbty.empty in
      cache := TMap.add f (Msbt.add sbt (Msbty.add sbty nf c_sbty) c_sbt) ch;
      nf

let apply_subst s t =
  if Options.get_timers() then
    try
      Timers.exec_timer_start Timers.M_Expr Timers.F_apply_subst;
      let res = apply_subst s t in
      Timers.exec_timer_pause Timers.M_Expr Timers.F_apply_subst;
      res
    with e ->
      Timers.exec_timer_pause Timers.M_Expr Timers.F_apply_subst;
      raise e
  else apply_subst s t


(** Subterms, and related stuff *)

(* new: first written for term_definition *)
let max_pure_subterms =
  let args_of e =
    match e.bind with
    | B_lemma q | B_skolem q -> [q.main]
    | B_let { let_e; in_e; _ } -> [let_e; in_e]
    | _ -> e.xs
  in
  let rec aux acc e =
    if e.pure then TSet.add e acc
    else List.fold_left aux acc (args_of e)
  in
  fun e -> aux TSet.empty e

let rec sub_terms acc e =
  match e.f with
  | Sy.Form _ | Sy.Lit _ -> acc
  | _ -> List.fold_left sub_terms (TSet.add e acc) e.xs

let args_of_lit e = match e.f with
  | Sy.Form _ -> assert false
  | Sy.Lit _ -> e.xs
  | _ when e.ty == Ty.Tbool -> [e]
  | _ -> assert false

let max_terms_of_lit e =
  TSet.of_list @@ args_of_lit e

let max_ground_terms_of_lit =
  let rec max_sub_ground acc e =
    match e.f with
    | Sy.Form _ | Sy.Lit _ -> assert false
    | _ ->
      if is_ground e then TSet.add e acc
      else List.fold_left max_sub_ground acc e.xs
  in
  fun e -> List.fold_left max_sub_ground TSet.empty (args_of_lit e)

let atoms_rec_of_form =
  let rec atoms only_ground acc f =
    match form_view f with
    | Not_a_form -> assert false
    | Literal a ->
      if not only_ground || is_ground a then TSet.add a acc else acc

    | Lemma { main = f; _ } | Skolem { main = f; _ } ->
      atoms only_ground acc f
    | Unit(f1,f2) | Clause(f1,f2,_) | Iff (f1, f2) | Xor (f1, f2) ->
      atoms only_ground (atoms only_ground acc f1) f2
    | Let { let_e; in_e; _ } ->
      let acc = atoms only_ground acc in_e in
      if let_e.ty == Ty.Tbool then atoms only_ground acc let_e
      else acc [@ocaml.ppwarning "TODO: add some stuff from let_e"]
  in
  fun ~only_ground f acc ->
    atoms only_ground acc f

let max_ground_terms_rec_of_form f =
  TSet.fold
    (fun a acc -> TSet.union acc (max_ground_terms_of_lit a))
    (atoms_rec_of_form ~only_ground:false f TSet.empty) TSet.empty


(** Other smart constructors and skolemization functions **)

let resolution_of_literal a binders free_vty acc =
  match lit_view a with
  | Pred(t, _) ->
    let cond =
      Ty.Svty.subset free_vty (free_type_vars t) &&
      let vars = free_vars t SMap.empty in
      SMap.for_all (fun sy _ -> SMap.mem sy vars) binders
    in
    if cond then TSet.add t acc else acc
  | _ -> acc

let rec resolution_of_disj is_back f binders free_vty acc =
  match form_view f with
  | Literal a -> resolution_of_literal a binders free_vty acc
  | Clause(g,f, true) ->
    if is_back then resolution_of_disj is_back f binders free_vty acc
    else resolution_of_disj is_back g binders free_vty acc
  | Iff(f1, f2) ->
    resolution_of_disj is_back f2 binders free_vty @@
    resolution_of_disj is_back f1 binders free_vty acc

  | _ -> acc

let rec resolution_of_toplevel_conj is_back f binders free_vty acc =
  match form_view f with
  | Unit(f1, f2) ->
    resolution_of_toplevel_conj is_back f2 binders free_vty
      (resolution_of_toplevel_conj is_back f1 binders free_vty acc)
  | _ -> resolution_of_disj is_back f binders free_vty acc

let sub_terms_of_formula f =
  let rec aux f acc =
    match form_view f with
    | Literal a -> List.fold_left sub_terms acc (args_of_lit a)
    | Unit(f1, f2)
    | Iff(f1, f2)
    | Xor(f1, f2)
    | Clause(f1, f2, _) -> aux f2 (aux f1 acc)
    | Skolem q | Lemma q -> aux q.main acc
    | Let xx ->
      let acc = aux xx.in_e acc in
      if type_info xx.let_e == Ty.Tbool then aux xx.let_e acc
      else sub_terms acc xx.let_e
    | Not_a_form -> assert false
  in
  aux f TSet.empty

(* unification/matching like function, to detect when a backward
   triggers is too permessive (general) *)
let cand_is_more_general cand other =
  let rec matches cand other =
    match cand, other with
    | { f = Sy.Var _; _ }, _ -> ()
    | { f = f1; xs=xs1; _}, { f = f2; xs = xs2; _ } when Sy.equal f1 f2 ->
      List.iter2 matches xs1 xs2
    | _ -> raise Exit
  in
  try matches cand other; true
  with Exit -> false

let resolution_triggers ~is_back { kind; main = f; binders; _ } =
  if Options.get_no_backward () then []
  else
    match kind with
    | Dpredicate t | Dfunction t ->
      if type_info t != Ty.Tbool then []
      else
        [ { content = [t];
            hyp = [];
            semantic = [];
            t_depth = t.depth;
            from_user = false;
            guard = None
          } ]
    | Dtheory -> []
    | Daxiom
    | Dgoal ->
      let free_vty = f.vty in
      let cand =
        resolution_of_toplevel_conj is_back f binders free_vty TSet.empty in
      let others =
        TSet.filter (fun t -> not (TSet.mem t cand)) (sub_terms_of_formula f)
      in
      TSet.fold
        (fun t acc ->
           if type_info t != Ty.Tbool ||
              TSet.exists (cand_is_more_general t) others then
             acc
           else
             { content = [t];
               hyp = [];
               semantic = [];
               t_depth = t.depth;
               from_user = false;
               guard = None
             } :: acc
        )cand []

let free_type_vars_as_types e =
  Ty.Svty.fold
    (fun i z -> Ty.Set.add (Ty.Tvar {Ty.v=i; value = None}) z)
    (free_type_vars e) Ty.Set.empty


(* let let_v = let_e in in_e *)
let mk_let let_v let_e in_e _id =
  (* !!! DANGER !!! only keep up vars that are bound with forall or
     exists, not those bound with a let is buggy:
     let up = SMap.filter (fun x _ -> Sy.Set.mem x quant_vars) up in *)
  (* eventual simplification are done in mk_let_aux *)
  let let_e_ty = type_info let_e in
  let free_vars = let_e.vars in (* dep vars are only those appearing in let_e*)
  let free_v_as_terms =
    SMap.fold (fun sy (ty ,_) acc -> (mk_term sy [] ty)::acc) free_vars []
  in
  let let_sko = mk_term (Sy.fresh "_let") free_v_as_terms let_e_ty in
  let is_bool = type_info in_e == Ty.Tbool in
  mk_let_aux {let_v; let_e; in_e; let_sko; is_bool}

let skolemize { main = f; binders; sko_v; sko_vty; _ } =
  let print fmt ty =
    assert (Ty.Svty.is_empty (Ty.vty_of ty));
    fprintf fmt "<%a>" Ty.print ty
  in
  let pp_sep_nospace fmt () = fprintf fmt "" in
  let pp_list fmt l =
    pp_print_list ~pp_sep:pp_sep_nospace print fmt l in
  let tyvars = asprintf "[%a]" pp_list sko_vty in

  let mk_sym cpt s =
    (* garder le suffixe "__" car cela influence l'ordre *)
    Sy.name (Format.sprintf "!?__%s%s!%d" s tyvars cpt)
  in
  let grounding_sbt =
    List.fold_left
      (fun g_sbt sk_t ->
         SMap.fold
           (fun sy (ty, _) g_sbt ->
              if SMap.mem sy g_sbt then g_sbt
              else SMap.add sy (fresh_name ty) g_sbt
           ) (free_vars sk_t SMap.empty) g_sbt
      )SMap.empty sko_v
  in
  let sbt =
    SMap.fold
      (fun x (ty,i) m ->
         let t = mk_term (mk_sym i "_sko") sko_v ty in
         let t = apply_subst (grounding_sbt, Ty.esubst) t in
         SMap.add x t m
      ) binders SMap.empty
  in
  let res = apply_subst_aux (sbt, Ty.esubst) f in
  assert (is_ground res);
  res


let rec mk_ite_eq x c th el =
  if equal th el then mk_eq_aux x th
  else if equal c vrai then mk_eq_aux x th
  else if equal c faux then mk_eq_aux x el
  else
    let e1 = mk_eq_aux x th in
    let e2 = mk_eq_aux x el in
    mk_and (mk_imp c e1 0) (mk_imp (neg c) e2 0) false 0

and mk_eq_aux x e =
  match e.xs with
  | [c;th;el] when is_ite e.f -> mk_ite_eq x c th el
  | _ -> mk_eq ~iff:true  x e

let mk_let_equiv let_sko let_e id  =
  match let_e.xs with
  | [_;_;_] when is_ite let_e.f -> mk_eq_aux let_sko let_e
  | _ ->
    if type_info let_e == Ty.Tbool then mk_iff let_sko let_e id
    else mk_eq ~iff:true let_sko let_e

let rec elim_let =
  let ground_sko sko =
    if is_ground sko then sko
    else
      let sbt =
        SMap.fold
          (fun sy (ty, _) sbt -> SMap.add sy (fresh_name ty) sbt)
          (free_vars sko SMap.empty) SMap.empty
      in
      apply_subst (sbt, Ty.esubst) sko
  in
  fun ~recursive ~conjs subst { let_v; let_e; in_e; let_sko; _ } ->
    assert (SMap.mem let_v (free_vars in_e SMap.empty));
    (* usefull when let_sko still contains variables that are not in
       ie_e due to simplification *)
    let let_sko = apply_subst (subst, Ty.esubst) let_sko in
    let let_sko = ground_sko let_sko in
    assert (is_ground let_sko);
    let let_e = apply_subst (subst, Ty.esubst) let_e in
    if let_sko.nb_nodes >= let_e.nb_nodes && let_e.pure then
      let subst = SMap.add let_v let_e subst in
      elim_let_rec subst in_e ~recursive ~conjs
      [@ocaml.ppwarning "TODO: should also inline form in form. But \
                         not possible to detect if we are not \
                         inlining a form inside a term"]
    else
      let subst = SMap.add let_v let_sko subst in
      let id = id in_e in
      let equiv = mk_let_equiv let_sko let_e id in
      let conjs = (fun f' -> mk_and equiv f' false id) :: conjs in
      elim_let_rec subst in_e ~recursive ~conjs

and elim_let_rec subst in_e ~recursive ~conjs =
  match form_view in_e with
  | Let letin when recursive -> elim_let ~recursive ~conjs subst letin
  | _ ->
    let f = apply_subst (subst, Ty.esubst) in_e in
    List.fold_left (fun acc func -> func acc) f conjs


let elim_let ~recursive letin =
  (* use a list of conjunctions for non inlined lets
     (ie. Let-sko = let-in branche /\ ...)
     to have tail-calls in the mutually recursive functions above *)
  let res = elim_let ~recursive ~conjs:[] SMap.empty letin in
  assert (is_ground res);
  res


let elim_iff f1 f2 id ~with_conj =
  if with_conj then
    mk_and
      (mk_imp f1 f2 id)
      (mk_imp f2 f1 id) false id
  else
    mk_or
      (mk_and f1 f2 false id)
      (mk_and (neg f1) (neg f2) false id) false id

module Triggers = struct

  module Svty = Ty.Svty

  module STRS =
    Set.Make(
    struct
      type t = expr * SSet.t * Svty.t

      let compare (t1,_,_) (t2,_,_) = compare t1 t2
    end)

  let is_prefix v = match v with
    | Sy.Op Sy.Minus -> true
    | _ -> false

  let is_infix v =
    let open Sy in
    match v with
    | Op (Plus | Minus | Mult | Div | Modulo) -> true
    | _ -> false

  let rec score_term (t : expr) =
    let open Sy in
    match t with
    | { f = (True | False | Void | Int _ | Real _ | Bitv _ | Var _); _ } -> 0

    | { f; _ } when is_infix f || is_prefix f ->
      0 (* arithmetic triggers are not suitable *)

    | { f = Op (Get | Set) ; xs = [t1 ; t2]; _ } ->
      max (score_term t1) (score_term t2)

    | { f = Op (Access _ | Destruct _) ; xs = [t]; _ } -> 1 + score_term t
    | { f = Op Record; xs; _ } ->
      1 + (List.fold_left
             (fun acc t -> max (score_term t) acc) 0 xs)
    | { f = Op(Set | Extract) ; xs = [t1; t2; t3]; _ } ->
      max (score_term t1) (max (score_term t2) (score_term t3))

    | { f= (Op _ | Name _) ; xs = tl; _ } ->
      1 + (List.fold_left
             (fun acc t -> max (score_term t) acc) 0 tl)

    | { f = (Sy.MapsTo _ | Sy.In _); xs = [e]; _ } -> score_term e
    | { f = (Lit _ | Form _ | Sy.MapsTo _ | Sy.In _ | Sy.Let); _ } ->
      assert false


  let rec cmp_trig_term (t1 : expr) (t2 : expr) =
    let compare_expr = compare in
    let open Sy in
    match t1, t2 with
    | { f = (True | False | Void | Int _ | Real _ | Bitv _); _ },
      { f = (True | False | Void | Int _ | Real _ | Bitv _); _ } ->
      compare_expr t1 t2

    | { f = (True | False | Void | Int _ | Real _ | Bitv _); _ }, _ -> -1
    | _, { f = (True | False | Void | Int _ | Real _ | Bitv _); _ } ->  1

    | { f = (Var _) as v1; _ }, { f = (Var _) as v2; _ } -> Sy.compare v1 v2
    | { f = Var _; _ }, _ -> -1
    | _, { f = Var _; _ } ->  1
    | { f = s; xs = l1; _ }, { f = s'; xs = l2; _ }
      when is_infix s && is_infix s' ->
      let c = (score_term t1) - (score_term t2) in
      if c <> 0 then c
      else
        let c = Sy.compare s s' in
        if c <> 0 then c else Util.cmp_lists l1 l2 cmp_trig_term

    | { f = s; _ }, _ when is_infix s -> -1
    | _ , { f = s'; _ } when is_infix s' -> 1

    | { f = s1; xs =[t1]; _ }, { f = s2; xs = [t2]; _ }
      when is_prefix s1 && is_prefix s2 ->
      let c = Sy.compare s1 s2 in
      if c<>0 then c else cmp_trig_term t1 t2

    | { f = s1; _ }, _ when is_prefix s1 -> -1

    | _, { f = s2; _ } when is_prefix s2 ->  1

    | { f = (Name _) as s1; xs=tl1; _ }, { f = (Name _) as s2; xs=tl2; _ } ->
      let l1 = List.map score_term tl1 in
      let l2 = List.map score_term tl2 in
      let l1 = List.fast_sort Stdlib.compare l1 in
      let l2 = List.fast_sort Stdlib.compare l2 in
      let c  = Util.cmp_lists l1 l2 Stdlib.compare in
      if c <> 0 then c
      else
        let c = Sy.compare s1 s2 in
        if c <> 0 then c else Util.cmp_lists tl1 tl2 cmp_trig_term

    | { f = Name _; _ }, _ -> -1
    | _, { f = Name _; _ } -> 1

    | { f = Op Get; xs = l1; _ }, { f = Op Get; xs = l2; _ } ->
      Util.cmp_lists l1 l2 cmp_trig_term
    | { f = Op Get; _ }, _ -> -1
    | _, { f = Op Get; _ } -> 1

    | { f = Op Set; xs = l1; _ }, { f = Op Set; xs = l2; _ } ->
      Util.cmp_lists l1 l2 cmp_trig_term
    | { f = Op Set; _ }, _ -> -1
    | _, { f = Op Set; _ } -> 1

    | { f= Op Extract; xs = l1; _ }, { f = Op Extract; xs = l2; _ } ->
      Util.cmp_lists l1 l2 cmp_trig_term
    | { f = Op Extract; _ }, _ -> -1
    | _, { f = Op Extract; _ } -> 1

    | { f = Op Concat; xs = l1; _ }, { f = Op Concat; xs = l2; _} ->
      Util.cmp_lists l1 l2 cmp_trig_term
    | { f = Op Concat; _ }, _ -> -1
    | _, { f = Op Concat; _ } -> 1

    | { f = Op (Access a1) ; xs=[t1]; _ },
      { f = Op (Access a2) ; xs=[t2]; _ } ->
      let c = Stdlib.compare a1 a2 in (* should be Hstring.compare *)
      if c<>0 then c else cmp_trig_term t1 t2

    | { f = Op (Access _); _ }, _ -> -1
    | _, { f = Op (Access _); _ } -> 1

    | { f = Op (Destruct (_,a1)) ; xs = [t1]; _ },
      { f = Op (Destruct (_,a2)) ; xs = [t2]; _ } ->
      let c = Stdlib.compare a1 a2 in (* should be Hstring.compare *)
      if c<>0 then c else cmp_trig_term t1 t2

    | { f = Op (Destruct _); _ }, _ -> -1
    | _, { f =Op (Destruct _); _ } -> 1

    | { f = Op Record ; xs= lbs1; _ }, { f = Op Record ; xs = lbs2; _ } ->
      Util.cmp_lists lbs1 lbs2 cmp_trig_term
    | { f = Op Record; _ }, _ -> -1
    | _, { f = Op Record; _ } -> 1

    | { f = (Op _) as s1; xs=tl1; _ }, { f = (Op _) as s2; xs=tl2; _ } ->
      (* ops that are not infix or prefix *)
      let l1 = List.map score_term tl1 in
      let l2 = List.map score_term tl2 in
      let l1 = List.fast_sort Stdlib.compare l1 in
      let l2 = List.fast_sort Stdlib.compare l2 in
      let c = Util.cmp_lists l1 l2 Stdlib.compare in
      if c <> 0 then c
      else
        let c = Sy.compare s1 s2 in
        if c <> 0 then c else Util.cmp_lists tl1 tl2 cmp_trig_term

    | { f = Op _; _ }, _ -> -1
    | _, { f = Op _; _ } -> 1
    | { f = (Lit _ | Form _ | In _ | MapsTo _ | Let); _ },
      { f = (Lit _ | Form _ | In _ | MapsTo _ | Let); _ } -> assert false

  let cmp_trig_term_list tl2 tl1 =
    let l1 = List.map score_term tl1 in
    let l2 = List.map score_term tl2 in
    let l1 = List.rev (List.fast_sort Stdlib.compare l1) in
    let l2 = List.rev (List.fast_sort Stdlib.compare l2) in
    let c = Util.cmp_lists l1 l2 Stdlib.compare in
    if c <> 0 then c else Util.cmp_lists tl1 tl2 cmp_trig_term

  let unique_stable_sort =
    let rec unique l acc =
      match l with
      | [] -> List.rev acc
      | [e] -> List.rev @@ e :: acc
      | a::((b::_) as l) ->
        if cmp_trig_term_list a b = 0 then unique l acc
        else unique l (a :: acc)
    in
    fun l ->
      unique (List.stable_sort cmp_trig_term_list l) []

  let vty_of_term acc t = Svty.union acc t.vty

  let not_pure t = not t.pure

  let vars_of_term bv acc t =
    SMap.fold
      (fun v _ acc ->
         if SSet.mem v bv then SSet.add v acc else acc
      )t.vars acc

  let filter_good_triggers (bv, vty) trs =
    List.filter
      (fun { content = l; _ } ->
         not (List.exists not_pure l) &&
         let s1 = List.fold_left (vars_of_term bv) SSet.empty l in
         let s2 = List.fold_left vty_of_term Svty.empty l in
         SSet.subset bv s1 && Svty.subset vty s2 )
      trs

  (* unused
     let check_triggers (bv, vty) (trs : trigger list) =
     if trs == [] then
      failwith "There should be a trigger for every quantified formula \
                in a theory.";
     List.iter (fun { content = l; _ } ->
        if List.exists not_pure l then
          failwith "If-Then-Else are not allowed in (theory triggers)";
        let s1 = List.fold_left (vars_of_term bv) SSet.empty l in
        let s2 = List.fold_left vty_of_term Svty.empty l in
        if not (Svty.subset vty s2) || not (SSet.subset bv s1) then
          failwith "Triggers of a theory should contain every quantified \
                    types and variables.")
      trs;
     trs
  *)

  let is_var t = match t.f with
    | Sy.Var _ -> true
    | _ -> false (* constant terms such as "logic nil : 'a list" are
                    allowed in triggers *)

  (***)

  let at_most =
    let rec atmost acc n l =
      match n, l with
      | n, _ when n <= 0 -> acc
      | _ , [] -> acc
      | n, x::l -> atmost (x::acc) (n-1) l
    in
    fun n l ->
      let l = unique_stable_sort l in
      List.rev (atmost [] n l)

  module SLLT =
    Set.Make(
    struct
      type t = expr list * SSet.t * Svty.t
      let compare (a, y1, _) (b, y2, _)  =
        let c = try compare_lists a b compare; 0 with Util.Cmp c -> c in
        if c <> 0 then c else SSet.compare y1 y2
    end)

  let underscore =
    let aux t s =
      let sbt =
        SMap.fold
          (fun v (ty, _occ) sbt ->
             if not (SSet.mem v s) then sbt
             else SMap.add v (mk_term Sy.underscore [] ty) sbt
          )t.vars SMap.empty
      in
      if SMap.is_empty sbt then t, true
      else
        apply_subst (sbt, Ty.esubst) t, false
    in
    fun bv ((t,vt,vty) as e) ->
      let s = SSet.diff vt bv in
      if SSet.is_empty s then e
      else
        let t,_ = aux t s in
        let vt = SSet.add Sy.underscore (SSet.inter vt bv) in
        t,vt,vty

  let parties mconf bv vty l escaped_vars =
    let l =
      if mconf.Util.triggers_var then l
      else List.filter (fun (t,_,_) -> not (is_var t)) l
    in
    let rec parties_rec (llt, llt_ok)  l =
      match l with
      | [] -> llt_ok
      | (t, bv1, vty1)::l ->
        let llt, llt_ok =
          SLLT.fold
            (fun (l, bv2, vty2) (llt, llt_ok) ->
               if SSet.subset bv1 bv2 && Svty.subset vty1 vty2 then
                 (* t doesn't bring new vars *)
                 llt, llt_ok
               else
                 let bv3 = SSet.union bv2 bv1 in
                 let vty3 = Svty.union vty2 vty1 in
                 let e = t::l, bv3, vty3 in
                 if SSet.subset bv bv3 && Svty.subset vty vty3 then
                   llt, SLLT.add e llt_ok
                 else
                   SLLT.add e llt, llt_ok
            )
            llt (llt, llt_ok)
        in
        parties_rec (SLLT.add ([t], bv1, vty1) llt, llt_ok) l
    in
    let l = if escaped_vars  then List.rev_map (underscore bv) l else l in
    let s = List.fold_left (fun z e -> STRS.add e z) STRS.empty l in
    let l = STRS.elements s in (* remove redundancies in old l *)
    SLLT.elements (parties_rec (SLLT.empty, SLLT.empty) l)

  let simplification =
    let strict_subset bv vty =
      List.exists
        (fun (_, bv',vty') ->
           (SSet.subset bv bv' && not(SSet.equal bv bv')
            && Svty.subset vty vty')
           || (Svty.subset vty vty' && not(Svty.equal vty vty')
               && SSet.subset bv bv') )
    in
    let rec simpl_rec bv_a vty_a acc = function
      | [] -> acc
      | ((_, bv, vty) as e)::l ->
        if strict_subset bv vty l || strict_subset bv vty acc ||
           (SSet.subset bv_a bv && Svty.subset vty_a vty) ||
           (SSet.equal (SSet.inter bv_a bv) SSet.empty &&
            Svty.equal (Svty.inter vty_a vty) Svty.empty)
        then simpl_rec bv_a vty_a acc l
        else  simpl_rec bv_a vty_a (e::acc) l
    in fun bv_a vty_a l ->
      simpl_rec bv_a vty_a [] l

  let multi_triggers menv bv vty trs escaped_vars =
    let terms = simplification bv vty trs in
    let l_parties = parties menv bv vty terms escaped_vars in
    let lm = List.map (fun (lt, _, _) -> lt) l_parties in
    let mv , mt = List.partition (List.exists is_var) lm in
    let mv = List.sort (fun l1 l2 -> List.length l1 - List.length l2) mv in
    let mt = List.sort (fun l1 l2 -> List.length l1 - List.length l2) mt in
    let lm = if menv.Util.triggers_var then mt@mv else mt in
    let m = at_most menv.Util.nb_triggers lm in
    at_most menv.Util.nb_triggers m

  let mono_triggers menv vterm vtype trs =
    let mono = List.filter
        (fun (_, bv_t, vty_t) ->
           SSet.subset vterm bv_t && Svty.subset vtype vty_t) trs
    in
    let trs_v, trs_nv = List.partition (fun (t, _, _) -> is_var t) mono in
    let base = if menv.Util.triggers_var then trs_nv @ trs_v else trs_nv in
    at_most menv.Util.nb_triggers (List.map (fun (t, _, _) -> [t]) base)

  let filter_interpreted_arith mono =
    let m =
      List.filter
        (fun t ->
           match t with
           | [{ f = Sy.Op Sy.Plus; _ }] -> false
           | [{ f = Sy.Op Sy.Minus; _ }] -> false
           | _ -> true
        )mono
    in
    (* no triggers whose head is '+' or '-' if alternative triggers
       are computed *)
    match m with
    | [] -> mono
    | _ -> m

  let make_triggers menv vterm vtype (trs : STRS.t) ~escaped_vars =
    let trs = STRS.elements trs in
    let mono = mono_triggers menv vterm vtype trs in
    let mono = filter_interpreted_arith mono in
    if menv.Util.greedy then
      (* merge directly multi in mono if greedy is set *)
      mono @ multi_triggers menv vterm vtype trs escaped_vars, []
    else
      mono,
      if mono != [] then []
      else multi_triggers menv vterm vtype trs escaped_vars

  (***)

  let free_vars_as_set e =
    SMap.fold (fun sy _ s -> SSet.add sy s) e.vars SSet.empty

  let potential_triggers =
    let has_bvar bv_lf bv =
      SMap.exists (fun e _ -> SSet.mem e bv) bv_lf
    in
    let has_tyvar vty vty_lf =
      Svty.exists (fun e -> Svty.mem e vty) vty_lf
    in
    let args_of e lets =
      match e.bind with
      | B_lemma q | B_skolem q -> lets, [q.main]
      | B_let ({ let_v; let_e; in_e; _ } as x) ->
        SMap.add let_v x lets, [let_e; in_e]
      | _ -> lets, e.xs
    in
    let rec aux ((vterm, vtype) as vars) ((strs, lets) as acc) e =
      let strs, lets =
        if e.pure && (has_bvar e.vars vterm || has_tyvar e.vty vtype) &&
           not (is_prefix e.f)
        then
          let vrs = free_vars_as_set e in
          STRS.add (e, vrs, e.vty) strs, lets
        else
          acc
      in
      let lets, args = args_of e lets in
      List.fold_left (aux vars) (strs, lets) args
    in
    fun vars e ->
      aux vars (STRS.empty, SMap.empty) e

  let triggers_of_list l =
    List.map
      (fun content ->
         { content;
           semantic = [];
           hyp = [];
           from_user = false;
           guard = None;
           t_depth = List.fold_left (fun z t -> max z (depth t)) 0 content
         }
      ) l

  let is_literal e =
    match lit_view e with
    | Not_a_lit _ -> false
    | _ -> true

  let trs_in_scope full_trs f =
    STRS.filter
      (fun (e, _, _) ->
         SMap.for_all
           (fun sy (ty, _) ->
              try
                let ty', _ = Sy.Map.find sy f.vars
                in Ty.equal ty ty'
              with Not_found -> false
           )e.vars
      )full_trs

  let max_terms f ~exclude =
    let eq = equal in
    let rec max_terms acc (e : t) =
      let open Sy in
      match e with
      | { f = Sy.Form (
          Sy.F_Unit _ | Sy.F_Clause _ | Sy.F_Xor | Sy.F_Iff); _ } ->
        List.fold_left max_terms acc e.xs

      | { f = Sy.Form (Sy.F_Lemma | Sy.F_Skolem) | Sy.Let; _ } -> raise Exit
      | { f; _ } when is_infix f -> raise Exit
      (*| {f = Op _} -> raise Exit*)
      | { f = Op _; _ } ->
        if eq exclude e then acc else e :: acc

      | { f = Name (_, _); _ } ->
        if eq exclude e then acc else e :: acc

      | { f = ( True | False | Void | Int _ | Real _
              | Bitv _ | In (_, _) | MapsTo _ ); _ } -> acc
      | { f = Var _; _ } -> raise Exit
      | { f = Lit L_neg_pred; _ } -> List.fold_left max_terms acc e.xs
      | { f = Lit _; _ } -> (*List.fold_left max_terms acc e.xs*)raise Exit
    in
    try max_terms [] f with Exit -> []

  let expand_lets terms lets =
    let sbt =
      SMap.fold
        (fun sy { let_e; _ } sbt ->
           let let_e = apply_subst (sbt, Ty.esubst) let_e in
           if let_e.pure then SMap.add sy let_e sbt
           else sbt
                [@ocaml.ppwarning "TODO: once 'let x = term in term' \
                                   added, check that the resulting sbt \
                                   is well normalized (may be not true \
                                   depending on the ordering of vars in lets"]
        )lets SMap.empty
    in
    let sbs = sbt, Ty.esubst in
    STRS.fold
      (fun (e, _, _) strs ->
         let e = apply_subst sbs e in
         STRS.add (e, free_vars_as_set e, e.vty) strs
      )terms terms

  let check_user_triggers f toplevel binders trs0 ~decl_kind =
    if SMap.is_empty binders && Ty.Svty.is_empty f.vty then trs0
    else
      let vtype = if toplevel then f.vty else Ty.Svty.empty in
      let vterm = SMap.fold (fun sy _ s -> SSet.add sy s) binders SSet.empty in
      if decl_kind == Dtheory then
        trs0
        [@ocaml.ppwarning "TODO: filter_good_triggers for this \
                           case once free-vars issues of theories \
                           axioms with hypotheses fixed"]
        (*check_triggers (vterm, vtype) trs0*)
        [@ocaml.ppwarning "TODO: do it for this case once \
                           free-vars issues of theories axioms \
                           with hypotheses fixed"]
      else
        filter_good_triggers (vterm, vtype) trs0

  let make f binders decl_kind mconf =
    if SMap.is_empty binders && Ty.Svty.is_empty f.vty then []
    else
      let vtype = f.vty in
      let vterm = SMap.fold (fun sy _ s -> SSet.add sy s) binders SSet.empty in
      match decl_kind, f with
      | Dtheory, _ -> assert false
      | (Dpredicate e | Dfunction e), _ ->
        let defn = match f with
          | { f = (Sy.Form Sy.F_Iff | Sy.Lit Sy.L_eq) ; xs = [e1; e2]; _ } ->
            if equal e e1 then e2 else if equal e e2 then e1 else f
          | _ -> f
        in
        let tt = max_terms defn ~exclude:e in
        let tt = List.fast_sort (fun a b -> depth b - depth a) tt in
        filter_good_triggers (vterm, vtype) @@ triggers_of_list [[e]; tt]

      | _, { f = (Sy.Form Sy.F_Iff) ; xs = [e1; e2]; _ } when is_literal e1 ->
        let f_trs1, lets = potential_triggers (vterm, vtype) e1 in
        let f_trs1 = expand_lets f_trs1 lets in
        let trs1 = trs_in_scope f_trs1 e1 in
        let f_trs2, lets = potential_triggers (vterm, vtype) e2 in
        let f_trs2 = expand_lets f_trs2 lets in
        let trs2 = trs_in_scope f_trs2 e2 in
        let mono_1, multi_1 =
          make_triggers mconf vterm vtype trs1 ~escaped_vars:false
        in
        let mono_2, multi_2 =
          make_triggers mconf vterm vtype trs2 ~escaped_vars:false
        in
        let mono = List.rev_append mono_1 mono_2 in
        let multi = List.rev_append multi_1 multi_2 in
        let res =
          match mono with
          | _::_ -> mono (* try to take nb_triggers ? *)
          | [] ->
            let mono_11, multi_12 =
              make_triggers mconf vterm vtype f_trs1 ~escaped_vars:true
            in
            let mono_21, multi_22 =
              make_triggers mconf vterm vtype f_trs2 ~escaped_vars:true
            in
            let mono' = List.rev_append mono_11 mono_21 in
            let multi' = List.rev_append multi_12 multi_22 in
            if mono' != [] then mono'
            else if multi != [] then multi
            else multi'
        in
        triggers_of_list res

      | _ ->
        let f_trs, lets = potential_triggers (vterm, vtype) f in
        let f_trs = expand_lets f_trs lets in
        let trs = trs_in_scope f_trs f in
        let mono, multi =
          make_triggers mconf vterm vtype trs ~escaped_vars:false
        in
        triggers_of_list @@
        match mono with
        | _::_ -> mono (* try to take nb_triggers ? *)
        | [] ->
          let mono', multi' =
            make_triggers mconf vterm vtype f_trs ~escaped_vars:true
          in
          if mono' != [] then mono'
          else if multi != [] then multi
          else multi'

end

(*****)

let make_triggers = Triggers.make

let mk_forall name loc binders trs f id ~toplevel ~decl_kind =
  let decl_kind =
    if toplevel then decl_kind
    else match decl_kind with
      | Dpredicate  _ | Dfunction _ -> Daxiom (* pred and func only toplevel*)
      | _ -> decl_kind
  in
  let binders =
    (* ignore binders that are not used in f ! already done in mk_forall_bis
       but maybe usefull for triggers inference *)
    SMap.filter (fun sy _ -> SMap.mem sy f.vars) binders
  in
  let sko_v =
    SMap.fold (fun sy (ty, _) acc ->
        if SMap.mem sy binders then acc else (mk_term sy [] ty) :: acc)
      (free_vars f SMap.empty) []
  in
  let free_vty = free_type_vars_as_types f in
  let sko_vty = if toplevel then [] else Ty.Set.elements free_vty in
  let trs = Triggers.check_user_triggers f toplevel binders trs ~decl_kind in
  mk_forall_bis
    {name; loc; binders; toplevel;
     user_trs = trs; main = f; sko_v; sko_vty; kind = decl_kind} id

let mk_exists name loc binders trs f id ~toplevel ~decl_kind =
  if not toplevel || Ty.Svty.is_empty f.vty then
    neg (mk_forall name loc binders trs (neg f) id ~toplevel ~decl_kind)
  else
    (* If there are type variables in a toplevel exists: 1 - we add
       a forall quantification without term variables (ie. only with
       type variables). 2 - we keep the triggers of 'exists' to try
       to instantiate these type variables *)
    let nm = sprintf "#%s#sub-%d" name 0 in
    let tmp =
      neg (mk_forall nm loc binders trs (neg f) id ~toplevel:false ~decl_kind)
    in
    mk_forall name loc SMap.empty trs tmp id ~toplevel ~decl_kind


let rec compile_match mk_destr mker e cases accu =
  match cases with
  | [] -> accu

  | (Typed.Var x, p) :: _ ->
    apply_subst ((SMap.singleton (Symbols.var x) e), Ty.esubst) p

  | (Typed.Constr {name; args}, p) :: l ->
    let _then =
      List.fold_left
        (fun acc (var, destr, ty) ->
           let destr = mk_destr destr in
           let d = mk_term destr [e] ty in
           mk_let (Sy.var var) d acc 0
        )p args
    in
    match l with
      [] -> _then
    | _ ->
      let _else = compile_match mk_destr mker e l accu in
      let cond = mker e name in
      mk_ite cond _then _else 0

(* TO BE REMOVED *)
let debug_compile_match e cases res =
  if get_debug_adt () then begin
    Printer.print_dbg  ~flushed:false ~module_name:"Expr"
      "compilation of: match %a with@ " print e;
    let p_list_vars fmt l =
      match l with
        [] -> ()
      | [e,_,_] -> Var.print fmt e
      | (e,_,_) :: l ->
        fprintf fmt "(%a" Var.print e;
        List.iter (fun (e,_,_) -> fprintf fmt ", %a" Var.print e) l;
        fprintf fmt ")"
    in
    List.iter
      (fun (p, v) ->
         match p with
         | Typed.Constr {name; args} ->
           Printer.print_dbg  ~flushed:false ~header:false
             "| %a %a -> %a@ "
             Hstring.print name
             p_list_vars args
             print v;
         | Typed.Var x ->
           Printer.print_dbg  ~flushed:false ~header:false
             "| %a -> %a@ " Var.print x print v;
      )cases;
    Printer.print_dbg ~header:false
      "end@ result is: %a" print res;
  end

let mk_match e cases =
  let ty = type_info e in
  let mk_destr =
    match ty with
    | Ty.Tadt _ -> (fun hs -> Sy.destruct ~guarded:true (Hstring.view hs))
    | Ty.Trecord _ -> (fun hs -> Sy.Op (Sy.Access hs))
    | Ty.Tsum _ -> (fun _hs -> assert false) (* no destructors for Tsum *)
    | _ -> assert false
  in
  let mker =
    match ty with
    | Ty.Tadt _ ->
      (fun e name -> mk_builtin ~is_pos:true (Sy.IsConstr name) [e])

    | Ty.Trecord _ ->
      (fun _e _name -> assert false) (* no need to test for records *)

    | Ty.Tsum _ ->
      (fun e n -> (* testers are equalities for Tsum *)
         let constr = mk_term (Sy.constr (Hstring.view n)) [] (type_info e) in
         mk_eq ~iff:false e constr)

    | _ -> assert false
  in
  let res = compile_match mk_destr mker e cases e in
  debug_compile_match e cases res;
  res
  [@ocaml.ppwarning "TODO: introduce a let if e is a big expr"]
  [@ocaml.ppwarning "TODO: add other elim schemes"]
  [@ocaml.ppwarning "TODO: add a match construct in expr"]


let is_pure e = e.pure

module Purification = struct

  (* lets_counter is used to order 'let' constructs before they are added to the
     'lets' map. This way, we keep their order in the original expression, and
     reconstruct them correctly in mk_lifted. *)
  let lets_counter = ref 0

  let add_let sy e lets =
    incr lets_counter;
    SMap.add sy (e, !lets_counter) lets

  let rec purify_term t lets =
    if t.pure then t, lets
    else
      match t.f, t.bind with
      | Sy.Let, B_let { let_v; let_e; in_e; _ } ->
        (* let_e is purified when processing the lets map *)
        let in_e , lets = purify_term in_e  lets in
        in_e, add_let let_v let_e lets

      | (Sy.Lit _ | Sy.Form _), _ ->
        let fresh_sy = Sy.fresh ~is_var:true "Pur-F" in
        mk_term fresh_sy [] t.ty , add_let fresh_sy t lets

      | _ -> (* detect ITEs *)
        match term_view t with
        | Not_a_term _ -> assert false (* should not happen ? *)
        | Term t ->
          match t.xs with
          | [_;_;_] when is_ite t.f ->
            let fresh_sy = Sy.fresh ~is_var:true "Pur-Ite" in
            mk_term fresh_sy [] t.ty , add_let fresh_sy t lets

          | _ ->
            let xs, lets =
              List.fold_left (fun (acc, lets) t ->
                  let t', lets' = purify_term t lets in
                  t' :: acc, lets'
                ) ([], lets) (List.rev t.xs)
            in
            mk_term t.f xs t.ty, lets

  and purify_generic mk l =
    let l, lets =
      List.fold_left (fun (acc, lets) t ->
          let t', lets' = purify_term t lets in
          t' :: acc, lets'
        )([], SMap.empty) (List.rev l)
    in
    mk_lifted (mk l) lets

  and purify_eq l =
    purify_generic (fun l ->
        match l with
        | [] | [_] -> assert false
        | [a; b ] -> mk_eq ~iff:true a b
        | l -> mk_nary_eq l
      ) l

  and purify_distinct l =
    purify_generic (fun l -> mk_distinct ~iff:true l) l

  and purify_builtin neg pred l =
    purify_generic (fun l -> mk_builtin ~is_pos:neg pred l) l

  and purify_predicate p is_neg =
    purify_generic (fun l ->
        match l with
        | [e] -> if is_neg then neg e else e
        | _ -> assert false
      ) [p]

  and purify_literal e =
    if List.for_all is_pure e.xs then e (* this is OK for lits and terms *)
    else match lit_view e with
      | Not_a_lit _ -> assert false
      | Eq (a, b)  ->
        assert (a.ty != Ty.Tbool);
        (* TODO: translate to iff *)
        purify_eq [a; b]
      | Eql l      -> purify_eq l
      | Distinct l -> purify_distinct l
      | Builtin (neg,prd,l) -> purify_builtin neg prd l
      | Pred (p, is_neg) -> purify_predicate p is_neg

  and purify_form e =
    assert (e.ty == Ty.Tbool);
    if is_pure e then e (* non negated predicates *)
    else
      match e.f with
      | Sy.True | Sy.False | Sy.Var _ | Sy.In _ ->
        e
      | Sy.Name _ -> (* non negated predicates with impure parts *)
        let e, lets = purify_term e SMap.empty in
        mk_lifted e lets

      | Sy.Let -> (* let on forms *)
        begin match e.xs, e.bind with
          | [], B_let ({ let_e; in_e; _ } as letin) ->
            if let_e.pure && in_e.pure then e
            else
              let let_e', lets = purify_non_toplevel_ite let_e SMap.empty in
              let in_e' = purify_form in_e in
              if let_e == let_e' && in_e == in_e' then e
              else
                mk_lifted
                  (mk_let_aux {letin with let_e = let_e'; in_e = in_e'})
                  lets
          | _, (B_lemma _ | B_skolem _ | B_none | B_let _) -> assert false
        end

      | Sy.Void | Sy.Int _ | Sy.Real _ | Sy.Bitv _ | Sy.Op _ | Sy.MapsTo _ ->
        assert false (* not formulas *)

      | Sy.Lit _ -> purify_literal e
      | Sy.Form x ->
        begin match x, e.xs, e.bind with
          | Sy.F_Unit imp, [a;b], _ ->
            let a' = purify_form a in
            let b' = purify_form b in
            if a == a' && b == b' then e else mk_and a' b' imp 0

          | Sy.F_Clause imp, [a;b], _ ->
            let a' = purify_form a in
            let b' = purify_form b in
            if a == a' && b == b' then e else mk_or a' b' imp 0

          | Sy.F_Iff, [a;b], _ ->
            let a' = purify_form a in
            let b' = purify_form b in
            if a == a' && b == b' then e else mk_iff a' b' 0

          | Sy.F_Xor, [a;b], _ ->
            let a' = purify_form a in
            let b' = purify_form b in
            if a == a' && b == b' then e else mk_xor a' b' 0

          | Sy.F_Lemma, [], B_lemma q ->
            let m = purify_form q.main in
            if m == q.main then e
            else mk_forall_ter {q with main = m} 0

          | Sy.F_Skolem, [], B_skolem q ->
            let m = purify_form q.main in
            if m == q.main then e
            else neg (mk_forall_ter {q with main = (neg m)} 0)

          | (Sy.F_Unit _ | Sy.F_Clause _ | Sy.F_Iff
            | Sy.F_Xor | Sy.F_Skolem | Sy.F_Lemma),
            _, _ ->
            assert false
        end

  and mk_lifted e lets =
    let ord_lets =  (*beware of ordering: to be checked *)
      List.fast_sort
        (fun (_, (_,cpt1)) (_,(_,cpt2)) -> cpt1 - cpt2) (SMap.bindings lets)
    in
    List.fold_left
      (fun acc (let_v, (let_e, _cpt)) ->
         let let_e, lets = purify_non_toplevel_ite let_e SMap.empty in
         assert (let_e.ty != Ty.Tbool || SMap.is_empty lets);
         mk_lifted (mk_let let_v let_e acc 0) lets
      )e ord_lets

  and purify_non_toplevel_ite e lets =
    match e.f, e.xs with
    | _, [c; th; el] when is_ite e.f ->
      let c = purify_form c in
      let th, lets = purify_non_toplevel_ite th lets in
      let el, lets = purify_non_toplevel_ite el lets in
      mk_term e.f [c; th; el] e.ty, lets

    | (Sy.Form _ | Sy.Lit _), _ -> purify_form e, lets
    | _ -> purify_term e lets

end

(*
let purify_literal a =
  Purification.lets_counter := 0;
  Purification.purify_literal a
*)

let purify_form f =
  Purification.lets_counter := 0;
  Purification.purify_form f

module Set = TSet
module Map = TMap

(******)


type gformula = {
  ff: expr;
  nb_reductions : int;
  trigger_depth : int;
  age: int;
  lem: expr option;
  origin_name : string;
  from_terms : expr list;
  mf: bool;
  gf: bool;
  gdist : int; (* dist to goal *)
  hdist : int; (* dist to hypotheses *)
  theory_elim : bool;
}

type th_elt =
  {
    th_name : string;
    ax_name : string;
    ax_form : t;
    extends : Util.theories_extensions;
    axiom_kind : Util.axiom_kind;
  }

let print_th_elt fmt t =
  Format.fprintf fmt "%s/%s: @[<hov>%a@]" t.th_name t.ax_name print t.ax_form

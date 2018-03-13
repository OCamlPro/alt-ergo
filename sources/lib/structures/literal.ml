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

open Hconsing
open Options
type 'a view =
  | Eq of 'a * 'a
  | Distinct of bool * 'a list
  | Builtin of bool * Hstring.t * 'a list
  | Pred of 'a * bool

type 'a atom_view =
  | EQ of 'a * 'a
  | BT of Hstring.t * 'a list
  | PR of 'a
  | EQ_LIST of 'a list

module type OrderedType = sig
  type t
  val compare : t -> t -> int
  val hash :  t -> int
  val print : Format.formatter -> t -> unit
  val top : unit -> t
  val bot : unit -> t
  val type_info : t -> Ty.t
end

module type S = sig
  type elt
  type t

  val make : elt view -> t
  val view : t -> elt view
  val atom_view : t -> elt atom_view * bool (* is_negated ? *)

  val mk_eq : elt -> elt -> t
  val mk_distinct : bool -> elt list -> t
  val mk_builtin : bool -> Hstring.t -> elt list -> t
  val mk_pred : elt -> bool -> t

  val mkv_eq : elt -> elt -> elt view
  val mkv_distinct : bool -> elt list -> elt view
  val mkv_builtin : bool -> Hstring.t -> elt list -> elt view
  val mkv_pred : elt -> bool -> elt view

  val neg : t -> t

  val add_label : Hstring.t -> t -> unit
  val label : t -> Hstring.t

  val print : Format.formatter -> t -> unit

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val uid : t -> int

  module Map : Map.S with type key = t
  module Set : Set.S with type elt = t

end

module Make (X : OrderedType) : S with type elt = X.t = struct

  type elt = X.t

  type atom =
    {value : elt atom_view;
     uid : int }

  type t = { at : atom; neg : bool; tpos : int; tneg : int }

  let compare a1 a2 = Pervasives.compare a1.tpos a2.tpos
  let equal a1 a2 = a1.tpos = a2.tpos (* XXX == *)
  let hash a1 = a1.tpos
  let uid a1 = a1.tpos
  let neg t = {t with neg = not t.neg; tpos = t.tneg; tneg = t.tpos}

  let atom_view t = t.at.value, t.neg

  let view t = match t.neg, t.at.value with
    | false, EQ(s,t) -> Eq(s,t)
    | true , EQ(s,t) -> Distinct(false, [s;t]) (* b false <-> not negated *)
    | false, EQ_LIST l -> Distinct (true,l)
    | true,  EQ_LIST l -> Distinct (false,l)
    | b    , PR p    -> Pred(p,b)
    | b    , BT(n,l) -> Builtin(not b, n, l) (* b true <-> not negated *)

  module T = struct
    type t' = t
    type t = t'
    let compare=compare
    let equal = equal
    let hash = hash
  end

  module Set = Set.Make(T)
  module Map = Map.Make(T)

  module Labels = Hashtbl.Make(T)

  let labels = Labels.create 100007

  let add_label lbl t = Labels.replace labels t lbl

  let label t = try Labels.find labels t with Not_found -> Hstring.empty

  let print_list fmt = function
    | [] -> ()
    | z :: l ->
      Format.fprintf fmt "%a" X.print z;
      List.iter (Format.fprintf fmt ", %a" X.print) l

  let ale = Hstring.make "<="
  let alt = Hstring.make "<"

  let print fmt a =
    let lbl = Hstring.view (label a) in
    let lbl = if String.length lbl = 0 then lbl else lbl^":" in
    match view a with
      | Eq (z1, z2) ->
	Format.fprintf fmt "%s %a = %a" lbl X.print z1 X.print z2

      | Distinct (b,(z::l)) ->
	let b = if b then "~ " else "" in
	Format.fprintf fmt "%s %s%a" lbl b X.print z;
	List.iter (fun x -> Format.fprintf fmt " <> %a" X.print x) l

      | Builtin (true, n, [v1;v2]) when Hstring.equal n ale ->
	Format.fprintf fmt "%s %a <= %a" lbl X.print v1 X.print v2

      | Builtin (true, n, [v1;v2]) when Hstring.equal n alt ->
	Format.fprintf fmt "%s %a < %a" lbl X.print v1 X.print v2

      | Builtin (false, n, [v1;v2]) when Hstring.equal n ale ->
	Format.fprintf fmt "%s %a > %a" lbl X.print v1 X.print v2

      | Builtin (false, n, [v1;v2]) when Hstring.equal n alt ->
	Format.fprintf fmt "%s %a >= %a" lbl X.print v1 X.print v2

      | Builtin (b, n, l) ->
	let b = if b then "" else "~" in
	Format.fprintf fmt "%s %s %s(%a)" lbl b (Hstring.view n) print_list l

      | Pred (p,b) ->
        Format.fprintf fmt "%s %a = %s" lbl X.print p
          (if b then "false" else "true")

      | Distinct (_, _) -> assert false

  module V = struct
    type elt = atom

    let eq a1 a2 =
      match a1.value, a2.value with
        | EQ(t1, t2), EQ(u1, u2) -> X.compare t1 u1 = 0 && X.compare t2 u2 = 0
        | BT(n1, l1), BT(n2, l2) ->
	  begin
            try
	      Hstring.equal n1 n2
              && List.for_all2 (fun x y -> X.compare x y = 0) l1 l2
	    with Invalid_argument _ -> false
          end
        | PR p1, PR p2 -> X.compare p1 p2 = 0
        | EQ_LIST l1, EQ_LIST l2 ->
	  begin
            try List.for_all2 (fun x y -> X.compare x y = 0) l1 l2
	    with Invalid_argument _ -> false
          end
	| _ -> false

    let hash a = match a.value with
      | EQ(t1, t2) -> abs (19 * (X.hash t1 + X.hash t2))
      | BT(n, l) ->
	abs
	  (List.fold_left
	     (fun acc t-> acc*13 + X.hash t) (Hstring.hash n+7) l)
      | PR p -> abs (17 * X.hash p) (*XXX * 29 ?*)
      | EQ_LIST l ->
        abs (List.fold_left (fun acc t-> acc*31 + X.hash t) 1 l)

    let set_id n v = {v with uid = n}

    let initial_size = 4096

    let disable_weaks () = Options.disable_weaks ()

  end

  module H = Make(V)

  let normalize_eq_bool t1 t2 is_neg =
    if X.compare t1 (X.bot()) = 0 then Pred(t2, not is_neg)
    else if X.compare t2 (X.bot()) = 0 then Pred(t1, not is_neg)
    else if X.compare t1 (X.top()) = 0 then Pred(t2, is_neg)
    else if X.compare t2 (X.top()) = 0 then Pred(t1, is_neg)
    else if is_neg then Distinct (false, [t1;t2]) (* XXX assert ? *)
    else Eq(t1,t2) (* should be translated into iff *)

  let normalize_eq t1 t2 is_neg =
    let c = X.compare t1 t2 in
    if c = 0 then Pred(X.top(), is_neg)
    else
      let t1, t2 = if c < 0 then t1, t2 else t2, t1 in
      if X.type_info t1 == Ty.Tbool then normalize_eq_bool t1 t2 is_neg
      else if is_neg then Distinct (false, [t1;t2]) (* XXX assert ? *)
      else Eq(t1,t2) (* should be translated into iff *)

  let normalize_view t = match t with
    | Eq(t1,t2) -> normalize_eq t1 t2 false
    | Distinct (b, [t1;t2]) -> normalize_eq t1 t2 (not b)
    | Distinct (b, l) ->
      Distinct (b, List.fast_sort X.compare l)
    | Builtin (_, _, _) | Pred (_, _) -> t

  let make_aux av is_neg =
    let av = {value = av; uid = -1} in
    let at = H.make av in
    if is_neg then
      {at = at; neg = is_neg; tpos = 2*at.uid+1; tneg = 2*at.uid}
    else
      {at = at; neg = is_neg; tneg = 2*at.uid+1; tpos = 2*at.uid}

  let make t = match normalize_view t with
    | Eq(t1,t2)       -> make_aux (EQ(t1,t2)) false
    | Builtin (b,n,l) -> make_aux (BT (n,l)) (not b)
    | Pred (x,y)      -> make_aux (PR x) y
    | Distinct(false, [t1;t2]) -> make_aux (EQ(t1,t2)) true
    | Distinct (b,l)  -> make_aux (EQ_LIST l) (not b)

  (************)

  (*
    let mk_eq_bool t1 t2 is_neg =
    if X.compare t1 (X.bot()) = 0 then make_aux (PR t2) (not is_neg)
    else if X.compare t2 (X.bot()) = 0 then make_aux (PR t1) (not is_neg)
    else if X.compare t1 (X.top()) = 0 then make_aux (PR t2) is_neg
    else if X.compare t2 (X.top()) = 0 then make_aux (PR t1) is_neg
    else make_aux (EQ(t1,t2)) is_neg

    let mk_equa t1 t2 is_neg =
    let c = X.compare t1 t2 in
    if c = 0 then make_aux (PR (X.top())) is_neg
    else
    let t1, t2 = if c < 0 then t1, t2 else t2, t1 in
    if X.type_info t1 = Ty.Tbool then mk_eq_bool t1 t2 is_neg
    else make_aux (EQ(t1, t2)) is_neg

    let make t = match t with
    | Eq(t1,t2) -> mk_equa t1 t2 false

    | Distinct (b, [t1;t2]) -> mk_equa t1 t2 (not b)

    | Builtin (b,n,l) -> make_aux (BT (n,l)) (not b)

    | Distinct (_,_) -> assert false (* TODO *)

    | Pred (x,y) -> make_aux (PR x) y
  *)

  let mk_eq t1 t2 = make (Eq(t1,t2))

  let mk_distinct is_neg tl = make (Distinct(is_neg, tl))

  let mk_builtin is_pos n l = make (Builtin(is_pos, n, l))

  let mk_pred t is_neg = make (Pred(t, is_neg))


  let mkv_eq t1 t2 = normalize_view (Eq(t1,t2))

  let mkv_distinct is_neg tl = normalize_view (Distinct(is_neg, tl))

  let mkv_builtin is_pos n l = normalize_view (Builtin(is_pos, n, l))

  let mkv_pred t is_neg = normalize_view (Pred(t, is_neg))

end

module type S_Term = sig

  include S with type elt = Term.t

  val vrai : t
  val faux : t

  val apply_subst : Term.subst -> t -> t

  val terms_nonrec : t -> Term.Set.t
  val terms_rec : t -> Term.Set.t
  val ground_terms : t -> Term.Set.t

  val vars_of : t -> Ty.t Symbols.Map.t -> Ty.t Symbols.Map.t
  val is_ground : t -> bool
  val is_in_model : t -> bool

(*  module SetEq : Set.S with type elt = t * Term.t * Term.t*)
end

module LT : S_Term = struct

  module L = Make(Term)
  include L

  let vrai = mk_pred Term.vrai false
  let faux = neg vrai

  let apply_subst subst a =
    match view a with
    | Pred (t1, b) ->
      let t1' = Term.apply_subst subst t1 in
      if t1 == t1' then a else make (Pred(t1', b))

    | Eq (t1, t2) ->
      let t1' = Term.apply_subst subst t1 in
      let t2' = Term.apply_subst subst t2 in
      if t1 == t1' && t2 == t2' then a else make (Eq(t1', t2'))

    | Distinct (b, lt) ->
      let lt, same = Lists.apply (Term.apply_subst subst) lt in
      if same then a else make (Distinct (b, lt))

    | Builtin (b, n, l) ->
      let l, same = Lists.apply (Term.apply_subst subst) l in
      if same then a else make (Builtin(b, n, l))

  let terms_nonrec a =
    match atom_view a with
      | EQ(a,b), _ -> Term.Set.add a (Term.Set.singleton b)
      | PR a, _    -> Term.Set.singleton a
      | BT (_,l), _ | EQ_LIST l, _ ->
        List.fold_left (fun z t -> Term.Set.add t z) Term.Set.empty l

  let ground_terms a =
    let res = terms_nonrec a in
    let tmp =
      Term.Set.fold
        (fun t acc ->
          if Term.is_ground t then Term.Set.add t acc
          else Term.subterms acc t
        )res Term.Set.empty
    in
    Term.Set.filter Term.is_ground tmp

  let terms_rec a =
    Term.Set.fold
      (fun t z -> Term.subterms z t)(terms_nonrec a) Term.Set.empty

  let vars_of a acc = Term.Set.fold Term.vars_of (terms_nonrec a) acc

  let is_ground a = Term.Set.for_all Term.is_ground (terms_nonrec a)

  let is_in_model l =
    match view l with
      | Eq (t1, t2) ->
        Term.is_in_model t1 || Term.is_in_model t2
      | Distinct (_, tl) | Builtin (_, _, tl) ->
        List.exists Term.is_in_model tl
      | Pred (t1, b) ->
        Term.is_in_model t1

  let apply_subst s a =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Literal Timers.F_apply_subst;
        let res = apply_subst s a in
        Timers.exec_timer_pause Timers.M_Literal Timers.F_apply_subst;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Literal Timers.F_apply_subst;
        raise e
    else apply_subst s a

end


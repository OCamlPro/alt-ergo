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

module T = Term
module Sy = Symbols

type binders = (Ty.t * int) Sy.Map.t (*int tag in globally unique *)

type semantic_trigger =
| Interval of Term.t * Symbols.bound * Symbols.bound
| MapsTo of Hstring.t * Term.t
| NotTheoryConst of Term.t
| IsTheoryConst of Term.t
| LinearDependency of Term.t * Term.t

type trigger = {
  content : T.t list;
  semantic : semantic_trigger list;
  hyp : t list;
  depth : int;
  from_user : bool;
  guard : Literal.LT.t option
}

and quantified = {
  name : string;
  main : t;

  triggers : trigger list;
  backward_triggers : trigger list Lazy.t;
  forward_triggers : trigger list Lazy.t;

  binders : binders;

  (* These fields should be (ordered) lists ! important for skolemization *)
  free_v : T.t list;
  free_vty : Ty.t list;
  loc : Loc.t; (* location of the "GLOBAL" axiom containing this quantified
                  formula. It forms with name a unique id *)
}

and llet = {
  let_var: Symbols.t;
  let_subst : Term.subst;
  let_term : Term.t;
  let_f : t;
}

and view =
    Unit of t*t
  | Clause of t*t*bool
  | Literal of Literal.LT.t
  | Lemma of quantified
  | Skolem of quantified
  | Let of llet

and iview = { pos : view ; neg : view ; size : int; tag : int ;
              negation : iview}

and t = iview * int

type gformula = {
  f: t;
  nb_reductions : int;
  trigger_depth : int;
  age: int;
  lem: t option;
  origin_name : string;
  from_terms : Term.t list;
  mf: bool;
  gf: bool;
  gdist : int; (* dist to goal *)
  hdist : int; (* dist to hypotheses *)
  theory_elim : bool;
}

let size (t,_) = t.size

let compare ((v1,_) as f1) ((v2,_) as f2) =
  let c = Pervasives.compare (size f1) (size f2) in
  if c=0 then Pervasives.compare v1.tag v2.tag else c

let equal (f1,_) (f2,_) =
  assert ((f1 == f2) == (f1.tag == f2.tag));
  f1 == f2

let equal_binders b1 b2 = Sy.Map.equal (fun (_,i) (_,j) -> i = j) b1 b2

let equal_free_vars =
  let set_of l =
    List.fold_left (fun z t -> T.Set.add t z) T.Set.empty l
  in
  fun l1 l2 ->
    let st2 = set_of l2 in
    List.for_all (fun ty -> T.Set.mem ty st2) l1

let equal_free_vty =
  let set_of l =
    List.fold_left (fun z t -> Ty.Set.add t z) Ty.Set.empty l in
  fun l1 l2 ->
    let st2 = set_of l2 in
    List.for_all (fun ty -> Ty.Set.mem ty st2) l1

module MST = Map.Make(T.Set)

let equal_triggers =
  let map_of l =
    List.fold_left
      (fun mp {content=mtr; guard = opt} ->
        let st = List.fold_left (fun z t -> T.Set.add t z) T.Set.empty mtr in
        MST.add st opt mp
      )MST.empty l
  in
  let equal_opt o1 o2 = match o1, o2 with
    | None, None -> true
    | Some a, Some b -> Literal.LT.equal a b
    | _ -> false
  in
  fun trs1 trs2 -> MST.equal equal_opt (map_of trs1) (map_of trs2)

let equal_quant
    {main=f1; binders=b1; free_v=free_v1; free_vty=free_vty1; triggers=trs1}
    {main=f2; binders=b2; free_v=free_v2; free_vty=free_vty2; triggers=trs2} =
  equal f1 f2
  && equal_binders b1 b2
  && equal_free_vars free_v1 free_v2
  && equal_free_vty free_vty1 free_vty2
  && equal_triggers trs1 trs2

let hash (f, _) = f.tag

let view (t,_) = t.pos


let hash_quant acc q =
  let {
    name = name;
    main = main;
    triggers = triggers;
    binders = binders;
    free_v = free_v;
    free_vty = free_vty;
  } = q in
  let acc = (fst main).tag + 13*acc in
  let acc =
    Sy.Map.fold
      (fun sy (ty, i) acc -> i * (Ty.hash ty) + 13*acc) binders acc in
  let acc =
    List.fold_left
      (fun acc t -> (T.hash t) + 13*acc) acc free_v in
  let acc =
    List.fold_left
      (fun acc ty -> (Ty.hash ty) + 13*acc) acc free_vty in
  acc

let rec is_positive v =
  match v with
  | Unit _ | Lemma _ -> true
  | Clause _ | Skolem _ -> false
  | Literal a ->  snd (Literal.LT.atom_view a)
  | Let llet -> is_positive (view llet.let_f)


module View = struct
  type elt = iview

  let eqc c1 c2 = match c1,c2 with
    | Literal x , Literal y -> Literal.LT.equal x y
    | Unit(f1,f2), Unit(g1,g2) | Clause(f1,f2,_), Clause(g1,g2,_) ->
      equal f1 g1 && equal f2 g2 || equal f1 g2 && equal f2 g1

    | Lemma q1, Lemma q2 | Skolem q1, Skolem q2  ->
      equal_quant q1 q2

    | Let l1, Let l2 ->
      fst l1.let_f == fst l2.let_f
      && Sy.equal l1.let_var l2.let_var
      && Term.equal l1.let_term l2.let_term
      && Term.compare_subst l1.let_subst l2.let_subst = 0

    | _, _ -> false

  let hashlt = List.fold_left (fun acc x->acc*19 + T.hash x)
  let hashllt = List.fold_left (fun acc (x, _) ->acc*19 + hashlt 0 x)

  let hashc acc = function
    | Literal x -> Literal.LT.hash x

    | Unit((f1,_),(f2,_)) -> (* XXX : Same as Clause ? *)
      let min = min f1.tag f2.tag in
      let max = max f1.tag f2.tag in
      (acc*19 + min)*19 + max

    | Clause((f1,_),(f2,_),_) ->
      let min = min f1.tag f2.tag in
      let max = max f1.tag f2.tag in
      (acc*19 + min)*19 + max

    | Lemma q -> 2*hash_quant acc q

    | Skolem q -> 1 + 2*hash_quant acc q

    | Let ({let_var=lvar; let_term=lterm;
	    let_subst=s; let_f=(lf,_)}) ->
      T.fold_subst_term
	(fun s t acc ->acc * 19 + Sy.hash s) s
	(lf.tag * 19 * 19 + Sy.hash lvar * 19 + acc)

  let eq f1 f2 = eqc f1.pos f2.pos && eqc f1.neg f2.neg

  let hash f = abs (hashc (hashc 1 f.pos) f.neg)

  let set_id tag {pos=pos; neg=neg; size=size} =
    (*assert (is_positive (pos));*)
    let rec p = {pos = pos; neg = neg; size = size; tag = 2*tag; negation = n}
    and n = {pos = neg; neg = pos; size = size; tag = 2*tag+1; negation = p} in
    p

  let initial_size = 4096

  let disable_weaks () = Options.disable_weaks ()

end

module H = Make(View)

let iview f = f

let id (_,id) = id

let print_binders =
  let print_one fmt (sy, (ty, _)) =
    fprintf fmt "%a:%a" Sy.print sy Ty.print ty
  in fun fmt b ->
    match Sy.Map.bindings b with
    | [] ->
      (* can happen when quantifying only on type variables *)
      fprintf fmt "(no term variables)"
    | e::l ->
      print_one fmt e;
      List.iter (fun e -> fprintf fmt ", %a" print_one e) l

let rec print fmt f =
  match view f with
    | Literal a ->
      Literal.LT.print fmt a
    | Lemma {triggers = trs; main = f; name = n; binders} ->
      if verbose () then
	let first = ref true in
	fprintf fmt "(lemma: %s forall %a.)[%a]@  %a"
	  n
          print_binders binders
	  (fun fmt ->
	    List.iter (fun {content=l} ->
	      fprintf fmt "%s%a"
		(if !first then "" else " | ") T.print_list l;
	      first := false;
	    ))
	  trs print f
      else
	fprintf fmt "lem %s" n

    | Unit(f1, f2) -> fprintf fmt "@[(%a /\\@ %a)@]" print f1 print f2

    | Clause(f1, f2,_) -> fprintf fmt "@[(%a \\/@ %a)@]" print f1 print f2

    | Skolem{main=f; binders} ->
      fprintf fmt "<sko exists %a.> (%a)" print_binders binders print f

    | Let l ->
      fprintf fmt
	"let %a =@ %a in@ %a" Sy.print l.let_var
	Term.print l.let_term print l.let_f

(* let print fmt ((_,id) as f) = *)
(*   fprintf fmt "(%d)%a" id print f *)


let union_subst s1 ((s2,s2_ty) as subst) =
  Sy.Map.fold
    (fun k x s2 -> Sy.Map.add k x s2) (Sy.Map.map (T.apply_subst subst)  s1) s2

let mk_not (f,id) =
  f.negation, id

(* smart constructors *)
let make pos neg size id =
  let rec p = {pos = pos; neg = neg; size = size; tag = -1; negation = n}
  and n = {pos = neg; neg = pos; size = size; tag = -1; negation = p} in
  if is_positive pos then H.make p, id else mk_not (H.make n, id)

let vrai = make (Literal Literal.LT.vrai) (Literal Literal.LT.faux) 1 0
let faux = mk_not vrai

let mk_binders =
  let cpt = ref 0 in
  fun st ->
    T.Set.fold
      (fun t sym ->
        incr cpt;
        match T.view t with
          | {T.f=(Sy.Var _) as v; ty=ty} -> Sy.Map.add v (ty, !cpt) sym
          | _ -> assert false
      )st Sy.Map.empty

module F_Htbl =
  Hashtbl.Make(struct
    type t'=t
    type t=t'
    let hash = hash
    let equal = equal
  end)

let merge_maps acc b =
  Sy.Map.merge
    (fun sy a b ->
      match a, b with
      | None, None -> assert false
      | Some _, None -> a
      | _ -> b
    ) acc b

let free_vars =
  let rec free_rec acc f =
    match view f with
      | Literal a   -> Literal.LT.vars_of a acc
      | Unit(f1,f2) -> free_rec (free_rec acc f1) f2
      | Clause(f1,f2,_) -> free_rec (free_rec acc f1) f2
      | Lemma {binders = binders; main = f}
      | Skolem {binders = binders; main = f} ->
	let mp = free_rec Sy.Map.empty f in
        let mp = Sy.Map.filter (fun sy _ -> not (Sy.Map.mem sy binders)) mp in
        merge_maps mp acc

      | Let {let_subst = (subst, _); let_term = t; let_f = lf} ->
        let mp = free_rec Sy.Map.empty lf in
        let mp = Term.vars_of t mp in
        let mp = Sy.Map.fold
	  (fun sy t mp ->
	    if Sy.Map.mem sy mp then
              (* 'let' bindings are removed since they are mapped to fresh terms
                 'vars' that are not nrmalized are replaced with the vars of
                 their normal form w.r.t. subst *)
              Term.vars_of t (Sy.Map.remove sy mp)
	    else mp
	  ) subst mp
        in
        merge_maps mp acc
  in
  fun f -> free_rec Sy.Map.empty f

let type_variables f =
  let rec aux acc f =
    match view f with
      | Unit(f1,f2) | Clause(f1,f2,_) -> aux (aux acc f1) f2
      | Lemma lem | Skolem lem -> aux acc lem.main
      | Let llet -> aux acc llet.let_f
      | Literal a ->
        Term.Set.fold
          (fun t z -> Ty.Svty.union z (T.vty_of t))
          (Literal.LT.terms_nonrec a) acc
  in
  Ty.Svty.fold
    (fun i z -> Ty.Set.add (Ty.Tvar {Ty.v=i; value = None}) z)
    (aux Ty.Svty.empty f) Ty.Set.empty



let has_semantic_triggers trs =
  List.exists (fun tr -> tr.semantic != []) trs

let has_hypotheses trs =
  List.exists (fun tr -> tr.hyp != []) trs

let find_particular_subst =
  let exception Out of Sy.t * T.t in
  (* ex: in "forall x, y : int. x <> 1 or f(y) = x+1 or P(x,y)",
     x can be replaced with 1 *)
  let rec find_subst v tv f =
    match view f with
    | Unit _ | Lemma _ | Skolem _ | Let _ -> ()
    | Clause(f1, f2,_) -> find_subst v tv f1; find_subst v tv f2
    | Literal a ->
      match Literal.LT.view a with
      | Literal.Distinct (false, [a;b]) when T.equal tv a && T.is_ground b ->
        raise (Out (v, b))

      | Literal.Distinct (false, [a;b]) when T.equal tv b && T.is_ground a ->
        raise (Out (v, a))

      | Literal.Pred (t, is_neg) when T.equal tv t ->
        raise (Out (v, if is_neg then T.vrai else T.faux))

      | _ -> ()
  in
  fun binders free_vty trs f ->
    if not (Ty.Set.is_empty free_vty) || has_hypotheses trs ||
      has_semantic_triggers trs
    then None
    else
      try
        assert (not (Sy.Map.is_empty binders));
        let acc, full =
          Sy.Map.fold
            (fun v (ty, _) (acc, full) ->
              try
                find_subst v (T.make v [] ty) f;
                  (*TODO: (re-) test partial substs: acc, false*)
                raise Exit
              with Out (x, t) ->
                Sy.Map.add x t acc, full
            )binders (Sy.Map.empty, true)
        in
        if Sy.Map.is_empty acc then None else Some (acc, full)
      with Exit -> None


let resolution_of_literal a binders free_vty acc =
  match Literal.LT.view a with
  | Literal.Pred(t, _) ->
    let cond =
      Ty.Svty.subset free_vty (Term.vty_of t) &&
        let vars = Term.vars_of t Symbols.Map.empty in
        Symbols.Map.for_all (fun sy ty -> Sy.Map.mem sy vars) binders
    in
    if cond then Term.Set.add t acc else acc
  | _ -> acc


let rec resolution_of_disj is_back f binders free_vty acc =
  match view f with
  | Literal a -> resolution_of_literal a binders free_vty acc
  | Clause(g,f, true) ->
    if is_back then resolution_of_disj is_back f binders free_vty acc
    else resolution_of_disj is_back g binders free_vty acc
  | _ -> acc


let rec resolution_of_toplevel_conj is_back f binders free_vty acc =
  match view f with
  | Unit(f1, f2) ->
    resolution_of_toplevel_conj is_back f2 binders free_vty
      (resolution_of_toplevel_conj is_back f1 binders free_vty acc)
  | _ -> resolution_of_disj is_back f binders free_vty acc

let sub_terms_of_formula f =
  let rec aux f acc =
    match view f with
    | Literal a -> Term.Set.union acc (Literal.LT.terms_rec a)
    | Unit(f1, f2) -> aux f2 (aux f1 acc)
    | Clause(f1, f2, _) -> aux f2 (aux f1 acc)
    | Skolem q | Lemma q -> aux q.main acc
    | Let llet -> Term.subterms (aux llet.let_f acc) llet.let_term
  in
  aux f Term.Set.empty

(* unification/matching like function, to detect when a backward triggers
   is too permessive (general)
*)
let cand_is_more_general cand other =
  let rec matches cand other =
    match Term.view cand, Term.view other with
    | {T.f=Sy.Var _}, _ -> ()
    | {T.f=f1; xs=xs1}, {T.f=f2; xs=xs2} when Sy.equal f1 f2 ->
      List.iter2 matches xs1 xs2
    | _ -> raise Exit
  in
  try matches cand other; true
  with Exit -> false


let resolution_triggers is_back f name binders free_vty =
  let free_vty =
    Ty.Set.fold
      (fun ty svty ->
        match ty with
        | Ty.Tvar {Ty.v; value = None} -> Ty.Svty.add v svty
        | _ -> assert false
      )free_vty Ty.Svty.empty
  in
  let cand =
    resolution_of_toplevel_conj is_back f binders free_vty Term.Set.empty in
  let others =
    Term.Set.filter (fun t -> not (Term.Set.mem t cand))
      (sub_terms_of_formula f)
  in
  Term.Set.fold
    (fun t acc ->
      if Term.Set.exists (cand_is_more_general t) others then acc
      else
        { content = [t];
          hyp = [];
          semantic = [];
          depth = (Term.view t).Term.depth;
          from_user = false;
          guard = None
        } :: acc
    )cand []


let mk_forall_aux =
  let env = F_Htbl.create 101 in
  (*fun up bv trs f name id ->*)
  fun name loc binders triggers f id ext_free free_v_f free_vty ->
      let bkw_trs = lazy (resolution_triggers true  f name binders free_vty) in
      let frw_trs = lazy (resolution_triggers false f name binders free_vty) in
      let free_v, free_vty = match ext_free with
        | Some (fv, fv_ty) -> fv, fv_ty
        | None ->
          let free_v = (* compute free vars (as terms) of f *)
            Sy.Map.fold
              (fun sy ty fv ->
                if Sy.Map.mem sy binders then fv
                else (Term.make sy [] ty) ::fv) free_v_f []
          in
          free_v, Ty.Set.elements free_vty
      in
      let new_q = {
        name = name;
        backward_triggers = bkw_trs;
        forward_triggers = frw_trs;
        main = f;
        triggers = triggers;
        binders = binders;
        free_v = free_v;
        free_vty = free_vty;
        loc = loc }
      in
      try
        let lem = F_Htbl.find env f in
        let q = match view lem with Lemma q -> q | _ -> assert false in
        assert (equal q.main f (* should be true *));
        if not (equal_quant q new_q) then raise Exit;
        if debug_warnings () then
          eprintf "[warning] (sub) axiom %s replaced with %s@." name q.name;
        lem
      with Not_found | Exit ->
        let sko = {new_q with main = mk_not f} in
        let res = make (Lemma new_q) (Skolem sko) (size f) id in
        F_Htbl.add env f res;
        res


(* forall up. let bv = t in f *)
let mk_let _up bv t f id =
  let {Term.ty=ty} = Term.view t in
  let up = Term.vars_of t Sy.Map.empty in
  let up = Sy.Map.fold (fun sy ty acc -> (Term.make sy [] ty)::acc) up [] in
  let subst = Sy.Map.add bv (T.make (Sy.fresh "_let") up ty) Sy.Map.empty in
  make
    (Let{let_var=bv; let_subst=(subst, Ty.esubst); let_term=t; let_f=f})
    (Let{let_var=bv; let_subst=(subst, Ty.esubst); let_term=t; let_f=mk_not f})
    (size f) id

let mk_and f1 f2 is_impl id =
  if equal f1 (mk_not f2) then faux
  else
    if equal f1 f2 then f1
    else if equal f1 vrai then f2
    else if equal f2 vrai then f1
    else if (equal f1 faux) || (equal f2 faux) then faux
    else
      let f1, f2 = if is_impl || compare f1 f2 < 0 then f1, f2 else f2, f1 in
      let size = size f1 + size f2 in
      make (Unit(f1,f2)) (Clause(mk_not f1,mk_not f2,is_impl)) size id

let mk_or f1 f2 is_impl id =
  if equal f1 (mk_not f2) then vrai
  else
    if equal f1 f2 then f1
    else if equal f1 faux then f2
    else if equal f2 faux then f1
    else if equal f1 vrai || equal f2 vrai then vrai
    else
      let f1, f2 = if is_impl || compare f1 f2 < 0 then f1, f2 else f2, f1 in
      let size = size f1 + size f2 in
      make (Clause(f1,f2,is_impl)) (Unit(mk_not f1,mk_not f2)) size id

let mk_imp f1 f2 id = mk_or (mk_not f1) f2 true id

(* using simplifications of mk_or and mk_and is not always efficient !! *)
let mk_iff f1 f2 id = (* try to interpret iff as a double implication *)
  let a = mk_or (mk_not f1) f2 true id in
  let b = mk_or (mk_not f2) f1 true id in
  mk_and a b false id

let translate_eq_to_iff s t =
  (T.view s).T.ty == Ty.Tbool &&
  not
  (T.equal s T.vrai || T.equal s T.faux || T.equal t T.vrai ||T.equal t T.faux)

let mk_lit a id = match Literal.LT.view a with
  | Literal.Eq(s,t) when translate_eq_to_iff s t ->
    let a1 = Literal.LT.mk_pred s false in
    let a2 = Literal.LT.mk_pred t false in
    let f1 = make (Literal a1) (Literal (Literal.LT.neg a1)) 1 id in
    let f2 = make (Literal a2) (Literal (Literal.LT.neg a2)) 1 id in
    mk_iff f1 f2 id

  | Literal.Distinct(false,[s;t]) when translate_eq_to_iff s t ->
    let a1 = Literal.LT.mk_pred s false in
    let a2 = Literal.LT.mk_pred t false in
    let f1 = make (Literal a1) (Literal (Literal.LT.neg a1)) 1 id in
    let f2 = make (Literal a2) (Literal (Literal.LT.neg a2)) 1 id in
    mk_not (mk_iff f1 f2 id)

  | _ -> make (Literal a) (Literal (Literal.LT.neg a)) 1 id

let mk_if t f2 f3 id =
  let lit = mk_lit (Literal.LT.mk_pred t false) id in
  mk_or (mk_and lit f2 true id) (mk_and (mk_not lit) f3 true id) false id

let no_capture_issue s_t binders =
  true (* TODO *)

module Msbt =
  Map.Make
    (struct
      type t = Term.t T.Subst.t
      let compare a b = T.Subst.compare T.compare a b
     end)

module Msbty =
  Map.Make
    (struct
      type t = Ty.t Ty.M.t
      let compare a b = Ty.M.compare Ty.compare a b
     end)

module Set = Set.Make(struct type t'=t type t=t' let compare=compare end)
module Map = Map.Make(struct type t'=t type t=t' let compare=compare end)

let apply_subst_trigger subst ({content; guard} as tr) =
  {tr with
    content = List.map (T.apply_subst subst) content;
    guard =
      match guard with
      | None -> guard
      | Some g -> Some (Literal.LT.apply_subst subst g)
  }

(* this function should only be applied with ground substitutions *)
let rec apply_subst =
  fun subst ((f, id) as ff) ->
    let {pos=p;neg=n;size=s} = iview f in
    let sp, sn, same = iapply_subst subst p n in
    if same then ff
    else
      match sp with
      | Literal a      -> mk_lit a id     (* this may simplifies the res *)
      | Unit (f1, f2)  ->
        let is_impl = match sn with Clause(_,_,b) -> b | _ -> assert false in
        mk_and f1 f2 is_impl id (* this may simplifies the res *)

      | Clause (f1,f2,is_impl) -> mk_or f1 f2 is_impl id
      (* this may simplifies the res *)

      | Lemma q  ->
        mk_forall
          q.name q.loc q.binders q.triggers q.main id
          (Some (q.free_v, q.free_vty))

      | Skolem q  ->
        mk_exists
          q.name q.loc q.binders q.triggers q.main id
          (Some (q.free_v, q.free_vty))

      | _              -> make sp sn s id

and iapply_subst ((s_t,s_ty) as subst) p n = match p, n with
  | Literal a, Literal _ ->
    let sa = Literal.LT.apply_subst subst a in
    let nsa = Literal.LT.neg sa in
    if a == sa then p, n, true
    else Literal sa, Literal nsa , false

  | Lemma lem, Skolem sko | Skolem sko, Lemma lem ->
    let { main = f; triggers = trs; binders = binders;
          free_v = fr_v; free_vty = fr_vty } = lem in
    assert (no_capture_issue s_t binders);
    let s_t = Sy.Map.fold (fun sy _ s_t -> Sy.Map.remove sy s_t) binders s_t in
    let s_t = (* discard the variables of s_t that are not in free_v *)
      List.fold_left
        (fun s_t' tv ->
          match T.view tv with
          | {T.f=(Sy.Var _) as x; xs = []} when Sy.Map.mem x s_t ->
            Sy.Map.add x (Sy.Map.find x s_t) s_t'
          | _ -> s_t'
        )Sy.Map.empty fr_v
    in
    (* should do the same filtering for fr_vty *)
    if (Sy.Map.is_empty s_t) && (Ty.M.is_empty s_ty) then
      p, n, true (* (s_t, s_ty) does not apply *)
    else
      let subst = s_t , s_ty in
      let f = apply_subst subst f in
      let trs = List.map (apply_subst_trigger subst) trs in
      let binders =
        Sy.Map.fold
          (fun sy (ty,i) bders ->
            let ty' = Ty.apply_subst s_ty ty in
            if Ty.compare ty ty' = 0 then bders
            else Sy.Map.add sy (ty', i) bders
          )binders binders
      in
      let fr_v = List.rev (List.rev_map (T.apply_subst subst) fr_v) in
      let fr_vty = List.rev (List.rev_map (Ty.apply_subst s_ty) fr_vty) in
      let lem = {lem with main = f; triggers = trs; binders = binders;
        free_v = fr_v; free_vty = fr_vty }
      in
      let slem = Lemma lem in
      let ssko = Skolem {lem with main = mk_not f} in
      (match p, n with
      | Lemma _, Skolem _ -> slem, ssko, false (* a lot of cmp needed to hcons*)
      | Skolem _, Lemma _ -> ssko, slem, false
      | _ -> assert false)

  | Unit(f1, f2), Clause(_,_, is_impl) ->
    let sf1 = apply_subst subst f1 in
    let sf2 = apply_subst subst f2 in
    if sf1 == f1 && sf2 == f2 then p, n, true
    else Unit(sf1, sf2), Clause(mk_not sf1, mk_not sf2, is_impl), false

  | Clause(f1, f2, is_impl), _ ->
    let sf1 = apply_subst subst f1 in
    let sf2 = apply_subst subst f2 in
    if sf1 == f1 && sf2 == f2 then p, n, true
    else Clause(sf1, sf2, is_impl), Unit(mk_not sf1, mk_not sf2), false

  | Let ({let_subst = s; let_term = lterm; let_f = lf} as e), Let _ ->
    let lterm = T.apply_subst subst lterm in
    let se = { e with let_subst = T.union_subst s subst; let_term = lterm } in
    let sne = { se with let_f = mk_not lf } in
    Let se, Let sne, false

  | _ -> assert false

and mk_exists name loc binders triggers f id ext_free =
  mk_not (mk_forall name loc binders triggers (mk_not f) id ext_free)

and mk_forall name loc binders triggers f id ext_free =
  let free_vty = type_variables f in (* type variables of f*)
  let free_v_f = free_vars f in (* free variables of f *)
  let binders =  (* ignore binders that are not used in f *)
    Sy.Map.filter (fun sy _ -> Sy.Map.mem sy free_v_f) binders
  in
  if Sy.Map.is_empty binders && Ty.Set.is_empty free_vty
  then
    (* not quantified ==> should fix save-used-context to be able to
       save "non-quantified axioms", or use a cache to save the name
       of axioms as labels, but they should be unique in this case *)
    f
  else
    match find_particular_subst binders free_vty triggers f with
    | None ->
      mk_forall_aux name loc binders triggers f id ext_free free_v_f free_vty

    | Some (sbs, covers_all_binders) ->
      assert (Ty.Set.is_empty free_vty);
      let subst = sbs, Ty.esubst in
      let triggers =
        List.map (apply_subst_trigger subst) triggers
      in
      let f = apply_subst subst f in

      if covers_all_binders
      then f
      else
        let binders =
          Sy.Map.filter (fun x _ -> not (Sy.Map.mem x sbs)) binders
        in
        let ext_free = match ext_free with
          | None -> None
          | Some (fr_v, fvty) ->
            Some (List.map (T.apply_subst subst) fr_v, fvty)
        in
        mk_forall name loc binders triggers f id ext_free


let apply_subst =
  let (cache : t Msbty.t Msbt.t Map.t ref) = ref Map.empty in
  fun ((sbt, sbty) as s) f ->
    let ch = !cache in
    try Map.find f ch |> Msbt.find sbt |> Msbty.find sbty
    with Not_found ->
      let nf = apply_subst s f in
      let c_sbt = try Map.find f ch with Not_found -> Msbt.empty in
      let c_sbty = try Msbt.find sbt c_sbt with Not_found -> Msbty.empty in
      cache := Map.add f (Msbt.add sbt (Msbty.add sbty nf c_sbty) c_sbt) ch;
      nf


let add_label lbl f =
  match view f with
    | Literal a ->
      Literal.LT.add_label lbl a;
      Literal.LT.add_label lbl (Literal.LT.neg a)
    | _ -> ()

let label f =
  match view f with
    | Literal l -> Literal.LT.label l
    | _ -> Hstring.empty

let label_model h =
  try Pervasives.(=) (String.sub (Hstring.view h) 0 6) "model:"
  with Invalid_argument _ -> false

let is_in_model f =
  match view f with
    | Literal l ->
      label_model (Literal.LT.label l) || Literal.LT.is_in_model l
    | _ -> false

let ground_terms_rec =
  let rec terms acc f = match view f with
    | Literal a ->
      let s =
	T.Set.filter
	  (fun t->
	    Sy.Map.is_empty (T.vars_of t Sy.Map.empty)
            && Ty.Svty.is_empty (T.vty_of t)
	  ) (Literal.LT.terms_rec a)
      in
      T.Set.union s acc
    | Lemma {main = f} | Skolem {main = f} -> terms acc f
    | Unit(f1,f2) -> terms (terms acc f1) f2
    | Clause(f1,f2,_) -> terms (terms acc f1) f2
    | Let {let_term=t; let_f=lf} ->
      let st =
	T.Set.filter
          (fun t->
            Sy.Map.is_empty (T.vars_of t Sy.Map.empty)
            && Ty.Svty.is_empty (T.vty_of t))
	  (Term.subterms Term.Set.empty t)
      in
      terms (T.Set.union st acc) lf
  in terms T.Set.empty

let atoms_rec =
  let rec atoms only_ground acc f = match view f with
    | Literal a ->
      if not only_ground || Literal.LT.is_ground a then
        Literal.LT.Set.add a acc
      else acc

    | Lemma {main = f} | Skolem {main = f} ->
      atoms only_ground acc f
        [@ocaml.ppwarning "is this what we want ?"]

    | Unit(f1,f2) -> atoms only_ground (atoms only_ground acc f1) f2
    | Clause(f1,f2,_) -> atoms only_ground (atoms only_ground acc f1) f2
    | Let {let_term=t; let_f=lf} -> atoms only_ground acc lf
  in
  fun ~only_ground f acc ->
    atoms only_ground acc f

let skolemize {main=f; binders=binders; free_v=free_v; free_vty=free_vty} =
  let tyvars =
    ignore (flush_str_formatter ());
    List.iter (fun ty ->
      assert (Ty.Svty.is_empty (Ty.vty_of ty));
      fprintf str_formatter "<%a>" Ty.print ty
    ) free_vty;
    flush_str_formatter ()
  in
  let mk_sym cpt s =
    (* garder le suffixe "__" car cela influence l'ordre *)
    Sy.name (Format.sprintf "!?__%s%s!%d" s tyvars cpt)
  in
  let sbt =
    Symbols.Map.fold
      (fun x (ty,i) m ->
        Sy.Map.add x (T.make (mk_sym i "_sko") free_v ty) m)
      binders Sy.Map.empty
  in
  apply_subst (sbt, Ty.esubst) f

let apply_subst s f =
  if Options.timers() then
    try
      Timers.exec_timer_start Timers.M_Formula Timers.F_apply_subst;
      let res = apply_subst s f in
      Timers.exec_timer_pause Timers.M_Formula Timers.F_apply_subst;
      res
    with e ->
      Timers.exec_timer_pause Timers.M_Formula Timers.F_apply_subst;
      raise e
  else apply_subst s f

let max_term_depth f =
  let rec aux f mx =
    match view f with
    | Literal a ->
        T.Set.fold
          (fun t mx -> max mx (T.view t).T.depth)
          (Literal.LT.terms_nonrec a) mx

    | Clause(f1, f2,_) | Unit(f1, f2) -> aux f2 (aux f1 mx)
    | Lemma q | Skolem q -> aux q.main mx
    | Let q -> max (aux q.let_f mx) (T.view q.let_term).T.depth
  in
  aux f 0

let name_of_lemma f =
  match view f with
  | Lemma {name} -> name
  | _ -> assert false

let name_of_lemma_opt opt =
  match opt with
  | None -> "(Lemma=None)"
  | Some f -> name_of_lemma f

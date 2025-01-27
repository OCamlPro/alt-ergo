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

module Sy = Symbols
module E  = Expr
module A  = Xliteral
module L  = List

module X = Shostak.Combine
module Ex = Explanation

module LR = Uf.LX

(* In this module, we follow the below conventions in the comments:
   - A get term refers to a term of the form `(select a i)` for an array `a` and
     an index `i`.
   - A set term refers to a term of the form `(store a i v)` for an array `a`
     and an index `i`.
   - A relevant index is any term that appears as an index in get or set terms.
   - A get or set term is known if it has been encountered in [assume]. *)

let src = Logs.Src.create ~doc:"Arrays_rel" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

module Tmap = struct
  include E.Map
  let update t a mp =
    try add t (E.Set.add a (find t mp)) mp
    with Not_found -> add t (E.Set.singleton a) mp
  let splited t a mp = try E.Set.mem a (find t mp) with Not_found -> false
end

module LRset= LR.Set

module Conseq =
  Set.Make
    (struct
      type t = E.t * Ex.t
      let compare (lt1,_) (lt2,_) = E.compare lt1 lt2
    end)

module LRmap = struct
  include LR.Map
  let find k mp = try find k mp with Not_found -> Conseq.empty
  let add k v ex mp = add k (Conseq.add (v,ex) (find k mp)) mp
end

(* Set of get terms. *)
type gtype = {g:Expr.t; gt:Expr.t; gi:Expr.t}
module G = Set.Make
    (struct type t = gtype let compare t1 t2 = E.compare t1.g t2.g end)

(* Set of set terms. *)
type stype = {s:E.t; st:E.t; si:E.t; sv:E.t}
module S = Set.Make
    (struct type t = stype let compare t1 t2 = E.compare t1.s t2.s end)

module TBS = struct
  include Map.Make(E)
  let find k mp = try find k mp with Not_found -> S.empty
  let add k v mp = add k (S.add v (find k mp)) mp
end

let timer = Timers.M_Arrays

module H = Ephemeron.K1.Make (Expr)

type t = {
  gets : G.t;
  (* Set of all the known get terms. *)

  tbset : S.t TBS.t;
  (* Set of all the known set terms, indexed by array. *)

  split : LRset.t;
  (* Set of equalities or disequalities on relevant indices.
     These are the hypotheses of consequences in the field [conseq].

     We split on these literals in [case_split].

     If we see one of these literals in [assume], we remove it of this set
     and directly propagate its associated consequences. *)

  conseq : Conseq.t LRmap.t;
  (* Map of consequences. More precisely, it is a map of literals [l] to
     explained formulas [(f, ex)] such that [l => f] is an instantiation
     of one of the axioms of the array theory. The formula [l => f] is true in
     all contexts where the explanation [ex] holds.

     The literals [l] are in the set [split] if there have not already be seen
     by [assume] or splitted in [case_split]. *)

  seen : E.Set.t Tmap.t;
  (* Cache used to prevent from generating several times the same instantiation
     in [get_of_set]. *)

  new_terms : E.Set.t;
  (* Set of get and set terms produced by the theory. These terms
     are supposed to be sent to the instantiation engine. *)

  cached_relevant_terms : (G.t * S.t TBS.t) H.t;
  (* Weak cache used to accelerate the exploration of new terms in order to
     find new get or set terms. *)
}


let empty uf = {
  gets  = G.empty;
  tbset = TBS.empty;
  split = LRset.empty;
  conseq   = LRmap.empty;
  seen  = Tmap.empty;
  new_terms = E.Set.empty;
  (* size_splits = Numbers.Q.one; *)
  cached_relevant_terms = H.create 1024;
}, Uf.domains uf

(*BISECT-IGNORE-BEGIN*)
module Debug = struct
  let assume la =
    let pp_lit ppf (a, _, _, _) = LR.print ppf (LR.make a) in
    if not @@ Compat.List.is_empty la then
      Log.debug (fun k -> k "assume@ %a"
                    Fmt.(list ~sep:comma pp_lit) la)

  let pp_select ppf t = E.print ppf t.g
  let pp_store ppf t = E.print ppf t.s

  let env env =
    if Options.get_verbose () then begin
      Log.debug (fun k -> k "selects:@ %a"
                    Fmt.(box @@ braces
                         @@ iter ~sep:comma G.iter pp_select) env.gets);
      Log.debug (fun k -> k "stores:@ %a"
                    Fmt.(box @@ braces @@ iter_bindings ~sep:comma TBS.iter
                         @@ pair ~sep:(any "->@,") E.print
                         @@ box @@ braces
                         @@ iter ~sep:comma S.iter pp_store) env.tbset);
      Log.debug (fun k -> k "splits:@ %a"
                    Fmt.(box @@ braces
                         @@ iter ~sep:comma LRset.iter LR.print) env.split)
    end
end
(*BISECT-IGNORE-END*)

let merge_revelant_terms (gets, tbset) (g, t) =
  let gets = G.union gets g in
  let tbset =
    TBS.merge
      (fun _ s1 s2 ->
         match s1, s2 with
         | Some s1, Some s2 -> Some (S.union s1 s2)
         | Some s, None | None, Some s -> Some s
         | None, None -> None
      ) tbset t
  in
  gets, tbset

(* Collects all the select or store subterms of the term [t]
   for the instantiation engine. Use a weak cache to avoid a bottleneck in
   presence of very large terms in the problem.

   See issue https://github.com/OCamlPro/alt-ergo/issues/1123 *)
let rec relevant_terms env t =
  let { E.f; xs; _ } = E.term_view t in
  let gets, tbset =
    List.fold_left
      (fun acc x ->
         merge_revelant_terms acc (cached_relevant_terms env x)
      ) (G.empty, TBS.empty) xs
  in
  match Sy.is_get f, Sy.is_set f, xs with
  | true , false, [a;i]   -> G.add {g=t; gt=a; gi=i} gets, tbset
  | false, true , [a;i;v] ->
    gets, TBS.add a {s=t; st=a; si=i; sv=v} tbset
  | false, false, _ -> (gets,tbset)
  | _  -> assert false

and cached_relevant_terms env t =
  match H.find env.cached_relevant_terms t with
  | r -> r
  | exception Not_found ->
    let r = relevant_terms env t in
    H.add env.cached_relevant_terms t r;
    r

(* Search for all the set and get terms within the subterms of literals in the
   list [la]. *)
let new_terms env la =
  let fct acc r =
    List.fold_left
      (fun acc x ->
         match X.term_extract x with
         | Some t, _ ->
           merge_revelant_terms acc @@ cached_relevant_terms env t
         | None, _   -> acc
      )acc (X.leaves r)
  in
  let gets, tbset =
    L.fold_left
      (fun acc (a,_,_,_)->
         match a with
         | A.Eq (r1,r2) -> fct (fct acc r1) r2
         | A.Builtin (_,_,l) | A.Distinct (_, l) -> L.fold_left fct acc l
         | A.Pred (r1,_) -> fct acc r1
      ) (env.gets,env.tbset) la
  in
  {env with gets; tbset}

module type UF = module type of Uf

(* Add the consequences `p => p_ded` and `n => n_ded`. If the literal [p]
   (respectively [q]) is already true, we do not add the consequence. *)
let update_env (module Uf : UF) uf dep env acc gi si p p_ded n n_ded =
  match Uf.are_equal uf ~added_terms:true gi si, Uf.are_distinct uf gi si with
  | Some (idep, _) , None ->
    let conseq = LRmap.add n n_ded dep env.conseq in
    {env with conseq = conseq},
    Conseq.add (p_ded, Ex.union dep idep) acc

  | None, Some (idep, _) ->
    let conseq = LRmap.add p p_ded dep env.conseq in
    {env with conseq = conseq},
    Conseq.add (n_ded, Ex.union dep idep) acc

  | None, None ->
    let sp = LRset.add p env.split in
    let conseq = LRmap.add p p_ded dep env.conseq in
    let conseq = LRmap.add n n_ded dep conseq in
    { env with split = sp; conseq = conseq }, acc

  | Some _,  Some _ ->
    (* This case cannot occur because we cannot have `gi = si` and
       `gi <> si` at the same time. *)
    assert false

(* Produce a formula to propagate a get term over a set term.

   More precisely, assume that [gtype] represents the get term `(select a i)`.
   For all set terms `(store b j v)` in the equivalence class of `a`, we create
   the formulas:

     i <> j -> (select a i) = (select b i)

   and

     i = j -> (select a i) = v.

   Moreover, the get term `(select b i)` is sent to the instantiation engine. *)
let get_of_set (module Uf : UF) uf gtype (env, acc) =
  let {g=get; gt=gtab; gi=gi} = gtype in
  E.Set.fold
    (fun set (env, acc) ->
       if Tmap.splited get set env.seen then (env, acc)
       else
         let env = {env with seen = Tmap.update get set env.seen} in
         let { E.f; xs; _ } = E.term_view set in
         match Sy.is_set f, xs with
         | true , [stab;si;sv] ->
           let xi, _ = X.make gi in
           let xj, _ = X.make si in
           let get_stab  = E.ArraysEx.select stab gi in
           let p       = LR.mk_eq xi xj in
           let p_ded   = E.mk_eq ~iff:false get sv in
           let n     = LR.mk_distinct false [xi;xj] in
           let n_ded = E.mk_eq ~iff:false get get_stab in
           let dep =
             match Uf.are_equal uf ~added_terms:true gtab set with
             | Some (dep, _) -> dep
             | None -> assert false
           in
           let env =
             {env with new_terms =
                         E.Set.add get_stab env.new_terms } in
           update_env (module Uf) uf dep env acc gi si p p_ded n n_ded
         | _ -> (env,acc)
    ) (Uf.class_of uf gtab) (env,acc)

(* Assume that [stype] represents the set term `(store b j v)`.
   For all known set terms of the form `(store a i w)` such that `a` and
   `b` are equal, we create the formula:

      (select (store a i w) i) = w

   Moreover, the term `(select (store a i w) i)` is sent to instantiation
   engine. *)
let get_from_set (module Uf : UF) uf stype (env, acc) =
  let sets =
    E.Set.fold
      (fun t acc -> S.union acc (TBS.find t env.tbset))
      (Uf.class_of uf stype.st) (S.singleton stype)
  in
  S.fold (fun { s = set; si = si; sv = sv; _ } (env,acc) ->
      let get = E.ArraysEx.select set si in
      if Tmap.splited get set env.seen then (env,acc)
      else
        let env = {env with
                   seen = Tmap.update get set env.seen;
                   new_terms = E.Set.add get env.new_terms }
        in
        let p_ded = E.mk_eq ~iff:false get sv in
        env, Conseq.add (p_ded, Ex.empty) acc
    ) sets (env,acc)

(* Assume that [gtype] represents the get term `(select a i)`.
   For all known set terms of the form `(store b j v)` such that `b` and
   `a` are equal, we create the formulas:

     i <> j -> (select (store b j v) i) = (select b i).

   and

     i = j -> (select (store b j v) i) = v

   Moreover the terms `(select (store b j v))` and `(select b j)` are
   sent to the instantiation engine. *)
let get_and_set (module Uf : UF) uf gtype (env, acc) =
  let {g=get; gt=gtab; gi=gi} = gtype in

  let suff_sets =
    E.Set.fold
      (fun t acc -> S.union acc (TBS.find t env.tbset))
      (Uf.class_of uf gtab) S.empty
  in
  S.fold
    (fun  {s=set; st=stab; si=si; sv=sv; _ } (env,acc) ->
       if Tmap.splited get set env.seen then (env,acc)
       else
         begin
           let env = {env with seen = Tmap.update get set env.seen} in
           let xi, _ = X.make gi in
           let xj, _ = X.make si in
           let get_stab  = E.ArraysEx.select stab gi in
           let gt_of_st  = E.ArraysEx.select set gi in
           let p       = LR.mk_eq xi xj in
           let p_ded   = E.mk_eq ~iff:false gt_of_st sv in
           let n     = LR.mk_distinct false [xi;xj] in
           let n_ded = E.mk_eq ~iff:false gt_of_st get_stab in
           let dep =
             match Uf.are_equal uf ~added_terms:true gtab stab with
             | Some (dep, _) -> dep
             | None -> assert false
           in
           let env =
             {env with
              new_terms =
                E.Set.add get_stab (E.Set.add gt_of_st env.new_terms) }
           in
           update_env (module Uf) uf dep env acc gi si p p_ded n n_ded
         end
    ) suff_sets (env,acc)

(* Generate new consequences of the axioms. *)
let new_splits uf_mod uf env =
  let acc =
    G.fold
      (fun gt_info acc ->
         let acc = get_of_set uf_mod uf gt_info acc in
         get_and_set uf_mod uf gt_info acc
      ) env.gets (env, Conseq.empty)
  in
  TBS.fold (fun _ tbs acc ->
      S.fold (fun stype acc -> get_from_set uf_mod uf stype acc) tbs acc
    ) env.tbset acc

(* For each disequality `r <> s` where `r` and `s` are two arrays,
   we produce the formula:
     exists i:ty. (select r i) <> (select s i),
   where `ty` denotes the type of indices of `r` and `s`. *)
let extensionality accu la =
  List.fold_left
    (fun ((env, acc) as accu) (a, _, dep,_) ->
       match a with
       | A.Distinct(false, [r;s]) ->
         begin
           match X.type_info r, X.term_extract r, X.term_extract s with
           | Ty.Tfarray (ty, _), (Some t1, _), (Some t2, _)  ->
             let i  = E.fresh_name ty in
             let g1 = E.ArraysEx.select t1 i in
             let g2 = E.ArraysEx.select t2 i in
             let d  = E.mk_distinct ~iff:false [g1;g2] in
             let acc = Conseq.add (d, dep) acc in
             let env =
               {env with new_terms =
                           E.Set.add g2 (E.Set.add g1 env.new_terms) } in
             env, acc
           | _ -> accu
         end
       | _ -> accu
    ) accu la

(* Remove all the splits of [env.split] that are subsumed by literals [la].
   If a split is subsumed by a literal with the explanation [ex], this
   explanation is added to all the consequences of this split. *)
let implied_consequences env eqs la =
  let spl, eqs =
    L.fold_left
      (fun (spl,eqs) (a,_,dep,_) ->
         let a = LR.make a in
         let spl = LRset.remove (LR.neg a) (LRset.remove a spl) in
         let eqs =
           Conseq.fold
             (fun (fact,ex) acc -> Conseq.add (fact, Ex.union ex dep) acc)
             (LRmap.find a env.conseq) eqs
         in
         spl, eqs
      )(env.split, eqs) la
  in
  {env with split=spl}, eqs

(* deduction de nouvelles dis/egalites *)
let new_equalities env eqs la =
  let la = L.filter
      (fun (a,_,_,_) -> match a with A.Builtin _  -> false | _ -> true) la
  in
  let env, eqs = extensionality (env, eqs) la in
  implied_consequences env eqs la

let two = Numbers.Q.from_int 2

(* Choose an equality or disequality between relevant indices to split on it. *)
let case_split env _uf ~for_model:_ =
  try
    let a = LR.neg (LRset.choose env.split) in
    Log.debug (fun k -> k "case split@ %a" LR.print a);
    [LR.view a, true, Th_util.CS (Th_util.Th_arrays, two)]
  with Not_found ->
    Log.debug (fun k -> k "no case split");
    []

let optimizing_objective _env _uf _o = None

let assume env uf la =
  (* Instantiations of the array axioms. *)
  Debug.assume la;
  let env = new_terms env la in
  let env, atoms = new_splits (module Uf : UF) uf env in
  let env, atoms = new_equalities env atoms la in
  Debug.env env;
  Log.debug (fun k -> k "%d implied equalities:@ %a"
                (Conseq.cardinal atoms)
                Fmt.(iter ~sep:sp Conseq.iter
                     @@ pair ~sep:(any ":") E.print Ex.print) atoms);
  let l =
    Conseq.fold (fun (a,ex) l ->
        ((Literal.LTerm a, ex, Th_util.Other)::l)) atoms []
  in
  env, Uf.domains uf, { Sig_rel.assume = l; remove = [] }

let query _ _ _ = None
let add env uf _ _ = env, Uf.domains uf, []

let new_terms env = env.new_terms
let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Arrays ->
    failwith "This Theory does not support theories extension"
  | _ -> t

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

module A = Xliteral
module X = Shostak.Combine
module Ex = Explanation
module E = Expr
module LX = Uf.LX

(* The theory of arrays with extensionality, using global domains on the
   representatives of the union-find:

   - known values: [a[i] = v], from [(select a i)] and [a = (store _ i v)]

   - edges: [a --i-- b], from [b = (store a i _)] or [a = (store b i _)]. Which
   means: [forall j. j <> i -> a[j] = b[j]] *)

let src = Logs.Src.create ~doc:"Arrays_rel" __MODULE__

module Log = (val Logs.src_log src : Logs.LOG)

let timer = Timers.M_Arrays

let add_loc k a locs =
  X.Map.update k
    (function
      | None -> Some (X.Set.singleton a) | Some s -> Some (X.Set.add a s))
    locs

module Domain = struct
  type t =
    { values : (X.r * Ex.t) X.Map.t X.Map.t;
      (* [a -> k -> (v, ex)]: [a[k] = v] with the explanation [ex]. *)
      edges : (X.r * Ex.t) X.Map.t X.Map.t;
      (* [a -> b -> (i, ex)]: the edge [a --i-- b] with the explanation [ex].
         The edges are stored in both directions, with at most one edge between
         two arrays (see [add_edge]). *)
      value_locs : X.Set.t X.Map.t;
      (* Map of indices to the arrays that have a value at this index. *)
      edge_locs : X.Set.t X.Map.t;
      (* Map of indices to the arrays that have an edge labelled by this
         index. *)
      edge_splits : (X.r * X.r * X.r * X.r * Ex.t) list;
      (* [(a, b, i, j, ex)]: the edge [a --j-- b] that was not added because of
         the edge [a --i-- b], to decide with a case split on [i = j] (see
         [add_edge]). *)
      split_locs : LX.Set.t X.Map.t;
      (* Map of indices to the case splits on this index. *)
      dirty : X.Set.t;
      (* Arrays whose values have to be propagated again through their edges. *)
      split_todo : LX.Set.t;
      (* Case splits whose indices have been merged with others. *)
      eqs : (X.r * X.r * Ex.t) list
          (* Deduced equalities that have not been propagated yet. *)
    }

  type _ Uf.id += Id : t Uf.id

  let empty =
    { values = X.Map.empty;
      edges = X.Map.empty;
      value_locs = X.Map.empty;
      edge_locs = X.Map.empty;
      edge_splits = [];
      split_locs = X.Map.empty;
      dirty = X.Set.empty;
      split_todo = LX.Set.empty;
      eqs = []
    }

  let pp ppf t =
    let pp_value ppf (k, (v, _)) = Fmt.pf ppf "[%a] = %a" X.print k X.print v in
    let pp_values ppf (a, m) =
      Fmt.pf ppf "%a%a" X.print a
        Fmt.(iter_bindings ~sep:sp X.Map.iter pp_value)
        m
    in
    Fmt.pf ppf "@[<v>Arrays values:@,  %a@]"
      Fmt.(iter_bindings ~sep:cut X.Map.iter pp_values)
      t.values

  (* Indices and values can be of any type. *)
  let filter_ty _ = true

  let init _ t = t

  exception Inconsistent of Ex.t

  let values_of a t =
    Option.value ~default:X.Map.empty (X.Map.find_opt a t.values)

  let edges_of a t =
    Option.value ~default:X.Map.empty (X.Map.find_opt a t.edges)

  (* Add the value [a[k] = v]. If [a] already has a value at [k], deduce the
     equality of the two values instead. Returns [true] if the known value is
     new. *)
  let add_value a k ((v, ex) as rd) t =
    let m = values_of a t in
    match X.Map.find k m with
    | v', ex' -> { t with eqs = (v, v', Ex.union ex ex') :: t.eqs }, false
    | exception Not_found ->
      ( { t with
          values = X.Map.add a (X.Map.add k rd m) t.values;
          value_locs = add_loc k a t.value_locs
        },
        true )

  (* Add the edge [a --i-- b] in both directions. There is at most one edge
     between two arrays: if there is already an edge [a --j-- b], the new edge
     is not added but kept in [edge_splits], since [a] and [b] are equal if [i
     <> j]. *)
  let add_edge a i b ex t =
    if X.equal a b
    then t
    else
      match X.Map.find_opt b (edges_of a t) with
      | Some (j, _) when X.equal i j -> t
      | Some (j, ex_j) ->
        { t with edge_splits = (a, b, j, i, Ex.union ex ex_j) :: t.edge_splits }
      | None ->
        let add_dir a b edges =
          let am = Option.value ~default:X.Map.empty (X.Map.find_opt a edges) in
          X.Map.add a (X.Map.add b (i, ex) am) edges
        in
        { t with
          edges = add_dir a b (add_dir b a t.edges);
          edge_locs = add_loc i a (add_loc i b t.edge_locs)
        }

  (* The index [rr] is replaced by [nrr]: the values at [rr], the edges labelled
     by [rr] and the case splits on [rr] are moved to [nrr]. *)
  let subst_index ~ex rr nrr t =
    let t =
      match X.Map.find rr t.value_locs with
      | exception Not_found -> t
      | arrs ->
        let t = { t with value_locs = X.Map.remove rr t.value_locs } in
        X.Set.fold
          (fun a t ->
            let m = values_of a t in
            match X.Map.find rr m with
            | exception Not_found -> t
            | v, ex_v ->
              let t =
                { t with
                  values = X.Map.add a (X.Map.remove rr m) t.values;
                  dirty = X.Set.add a t.dirty
                }
              in
              fst (add_value a nrr (v, Ex.union ex ex_v) t))
          arrs t
    in
    let t =
      match X.Map.find rr t.edge_locs with
      | exception Not_found -> t
      | arrs ->
        let edges =
          X.Set.fold
            (fun a edges ->
              match X.Map.find a edges with
              | exception Not_found -> edges
              | am ->
                let am =
                  X.Map.map
                    (fun ((i, e) as edge) ->
                      if X.equal i rr then nrr, Ex.union ex e else edge)
                    am
                in
                X.Map.add a am edges)
            arrs t.edges
        in
        { t with
          edges;
          edge_locs =
            X.Set.fold (add_loc nrr) arrs (X.Map.remove rr t.edge_locs);
          dirty = X.Set.union arrs t.dirty
        }
    in
    match X.Map.find rr t.split_locs with
    | exception Not_found -> t
    | lits ->
      let split_locs = X.Map.remove rr t.split_locs in
      let s =
        Option.value ~default:LX.Set.empty (X.Map.find_opt nrr split_locs)
      in
      { t with
        split_locs = X.Map.add nrr (LX.Set.union lits s) split_locs;
        split_todo = LX.Set.union lits t.split_todo
      }

  (* The array [rr] is replaced by [nrr]: its values and edges are moved to
     [nrr]. *)
  let subst_array ~ex rr nrr t =
    let t =
      X.Map.fold
        (fun k (v, ex_v) t -> fst (add_value nrr k (v, Ex.union ex ex_v) t))
        (values_of rr t)
        { t with values = X.Map.remove rr t.values }
    in
    let t =
      X.Map.fold
        (fun b (i, e) t ->
          let bm = X.Map.remove rr (X.Map.find b t.edges) in
          let t = { t with edges = X.Map.add b bm t.edges } in
          add_edge nrr i b (Ex.union ex e) t)
        (edges_of rr t)
        { t with edges = X.Map.remove rr t.edges }
    in
    if X.Map.mem nrr t.values && X.Map.mem nrr t.edges
    then { t with dirty = X.Set.add nrr t.dirty }
    else t

  let subst ~ex rr nrr t =
    (* A value can be used both as an index and as an array if we have arrays
       indexed by arrays. *)
    subst_array ~ex rr nrr (subst_index ~ex rr nrr t)
end

let get_domain uf = Uf.GlobalDomains.find (module Domain) (Uf.domains uf)

let set_domain uf dom = Uf.GlobalDomains.add (module Domain) dom (Uf.domains uf)

(* The value [a[k] = v] with its explanation. *)
type value =
  { a : X.r;
    k : X.r;
    v : X.r;
    ex : Ex.t
  }

(* The consequences of a case split [k = i] if [k <> i]. *)
type conseq =
  | Value of value  (** The value [b[k] = v], propagated through an edge. *)
  | Equal of X.r * X.r * Ex.t
      (** The arrays [a = b], for two edges [a --k-- b] and [a --i-- b]. *)

module Conseqs = Set.Make (struct
  type t = conseq

  let compare c1 c2 =
    match c1, c2 with
    | Value v1, Value v2 ->
      let c = X.hash_cmp v1.a v2.a in
      if c <> 0
      then c
      else
        let c = X.hash_cmp v1.k v2.k in
        if c <> 0 then c else X.hash_cmp v1.v v2.v
    | Equal (a1, b1, _), Equal (a2, b2, _) ->
      let c = X.hash_cmp a1 a2 in
      if c <> 0 then c else X.hash_cmp b1 b2
    | Value _, Equal _ -> -1
    | Equal _, Value _ -> 1
end)

type t =
  { splits : Conseqs.t LX.Map.t;
    (* Map of the case splits [k = i] to their consequences if [k <> i]. *)
    new_terms : E.Set.t;
    (* Terms produced by the theory that are sent to the instantiation
       engine. *)
    term_eqs : value list
        (* Values [b[k] = v] deduced by the theory whose equality [(select b k)
           = v] between terms has to be added to the congruence closure (for the
           instantiation engine/matching). *)
  }

let empty uf =
  ( { splits = LX.Map.empty; new_terms = E.Set.empty; term_eqs = [] },
    (* The domain is only registered when the first select or store term is
       added: without arrays, the union-find does not update it. *)
    Uf.domains uf )

let same_class uf r1 r2 =
  match Uf.are_equal_r uf r1 r2 with Entailed _ -> true | Unknown -> false

let update_split_locs f r locs =
  X.Map.update r
    (fun s -> Option.value ~default:LX.Set.empty s |> f |> Option.some)
    locs

let add_split env (dom : Domain.t) k i conseq =
  let lit = LX.mk_eq k i in
  match LX.Map.find lit env.splits with
  | ps ->
    { env with splits = LX.Map.add lit (Conseqs.add conseq ps) env.splits }, dom
  | exception Not_found ->
    let add = update_split_locs (LX.Set.add lit) in
    ( { env with splits = LX.Map.add lit (Conseqs.singleton conseq) env.splits },
      { dom with split_locs = add k (add i dom.split_locs) } )

(* Remove the case split [k = i], which is decided. *)
let remove_split uf env (dom : Domain.t) lit k i =
  let remove r = update_split_locs (LX.Set.remove lit) (fst (Uf.find_r uf r)) in
  ( { env with splits = LX.Map.remove lit env.splits },
    { dom with split_locs = remove k (remove i dom.split_locs) } )

(* A term of the class of [r], with the explanation of its membership. *)
let term_of uf r =
  let r, ex_r = Uf.find_r uf r in
  (* The term extracted from [r] may not be known by the union-find, in that
     case we take a term of the class of [r]. *)
  let t =
    match X.term_extract r with
    | Some t, _ when Uf.mem uf t -> Some t
    | _ -> E.Set.min_elt_opt (Uf.rclass_of uf r)
  in
  match t with
  | Some t -> Some (t, Ex.union ex_r (snd (Uf.find uf t)))
  | None -> None

(* Give the term [(select b k)] to the instantiation engine. *)
let add_new_term uf env b k =
  match term_of uf b, term_of uf k with
  | Some (b, _), Some (k, _) ->
    { env with new_terms = E.Set.add (E.ArraysEx.select b k) env.new_terms }
  | _ -> env

(* Add the value [b[k] = v] and push it on [todo] if it is new. [from_select] is
   [true] if the value comes from the term [(select b k)] itself, which the
   instantiation engine and the congruence closure already know. Otherwise the
   term is given to the instantiation engine and the equality [(select b k) = v]
   between terms is added later (see [term_eqs]). *)
let add_value ?(from_select = false) uf (env, dom, todo) b k v ex =
  let b, ex_b = Uf.find_r uf b in
  let k, ex_k = Uf.find_r uf k in
  let ex = Ex.union ex (Ex.union ex_b ex_k) in
  let dom, is_new = Domain.add_value b k (v, ex) dom in
  if is_new
  then
    let value = { a = b; k; v; ex } in
    let env =
      if not from_select
      then
        let env = add_new_term uf env b k in
        { env with term_eqs = value :: env.term_eqs }
      else env
    in
    env, dom, value :: todo
  else env, dom, todo

(* Propagate the value [a[k] = v] through the edge [a --i-- b]: add [b[k] = v]
   if [k <> i], otherwise create a case split on [k = i]. *)
let cross uf ((env, dom, todo) as acc) { k; v; ex; _ } b i eex =
  if same_class uf k i
  then acc
  else
    let ex = Ex.union ex eex in
    match Uf.are_distinct_r uf k i with
    | Entailed { ex = ex_d; _ } -> add_value uf acc b k v (Ex.union ex ex_d)
    | Unknown ->
      let env, dom = add_split env dom k i (Value { a = b; k; v; ex }) in
      (* As the value may only be propagated during the case-split search of the
         theory, its term is given to the instantiation engine now. *)
      add_new_term uf env b k, dom, todo

(* Propagate the values of [todo] through the edges of their arrays. *)
let rec propagate uf (env, (dom : Domain.t), todo) =
  match todo with
  | [] -> env, dom
  | ({ a; _ } as value) :: todo ->
    propagate uf
      (X.Map.fold
         (fun b (i, eex) acc -> cross uf acc value b i eex)
         (Domain.edges_of a dom) (env, dom, todo))

(* Propagate again the values of the arrays whose values or edges changed. *)
let process_dirty uf env (dom : Domain.t) =
  let todo =
    X.Set.fold
      (fun a todo ->
        let a, _ = Uf.find_r uf a in
        X.Map.fold
          (fun k (v, ex) todo -> { a; k; v; ex } :: todo)
          (Domain.values_of a dom) todo)
      dom.dirty []
  in
  propagate uf (env, { dom with dirty = X.Set.empty }, todo)

(* Decide the case splits [lits] whose indices are now equal or distinct. *)
let resolve_splits uf env dom lits =
  propagate uf
    (LX.Set.fold
       (fun lit ((env, dom, todo) as acc) ->
         match LX.Map.find lit env.splits, LX.view lit with
         | exception Not_found -> acc
         | ps, A.Eq (k, i) -> (
           if same_class uf k i
           then
             let env, dom = remove_split uf env dom lit k i in
             env, dom, todo
           else
             match Uf.are_distinct_r uf k i with
             | Th_util.Entailed { ex; _ } ->
               let env, dom = remove_split uf env dom lit k i in
               Conseqs.fold
                 (fun c ((env, (dom : Domain.t), todo) as acc) ->
                   match c with
                   | Value { a = b; k; v; ex = ex_p } ->
                     add_value uf acc b k v (Ex.union ex ex_p)
                   | Equal (a, b, ex_e) ->
                     ( env,
                       { dom with eqs = (a, b, Ex.union ex ex_e) :: dom.eqs },
                       todo ))
                 ps (env, dom, todo)
             | Th_util.Unknown ->
               (* Normalize splits *)
               let k', ex_k = Uf.find_r uf k in
               let i', ex_i = Uf.find_r uf i in
               if X.equal k k' && X.equal i i'
               then acc
               else
                 let ex = Ex.union ex_k ex_i in
                 let env, dom = remove_split uf env dom lit k i in
                 let env, dom =
                   Conseqs.fold
                     (fun c (env, dom) ->
                       let c =
                         match c with
                         | Value p -> Value { p with ex = Ex.union ex p.ex }
                         | Equal (a, b, ex_e) -> Equal (a, b, Ex.union ex ex_e)
                       in
                       add_split env dom k' i' c)
                     ps (env, dom)
                 in
                 env, dom, todo)
         | _ -> acc)
       lits (env, dom, []))

(* The case splits that may be decided by the literals of [la]. *)
let decided_splits uf (dom : Domain.t) la =
  let locs acc r =
    match X.Map.find (fst (Uf.find_r uf r)) dom.split_locs with
    | s -> LX.Set.union s acc
    | exception Not_found -> acc
  in
  List.fold_left
    (fun acc (a, _, _, _) ->
      match a with
      | A.Eq _ -> LX.Set.add (LX.make a) acc
      | A.Distinct (false, l) -> List.fold_left locs acc l
      | _ -> acc)
    dom.split_todo la

(* For the edge [a --i-- b] and the edge [a --j-- b] that was not added (see
   [Domain.add_edge]): [a = b] if [i <> j], since [a] and [b] agree on all the
   indices, otherwise a case split on [i = j] is created. If [i = j], the edge
   [a --i-- b] is the only one. *)
let split_edges uf env (dom : Domain.t) =
  List.fold_left
    (fun (env, (dom : Domain.t)) (a, b, i, j, ex) ->
      if same_class uf a b || same_class uf i j
      then env, dom
      else
        match Uf.are_distinct_r uf i j with
        | Entailed { ex = ex_d; _ } ->
          env, { dom with eqs = (a, b, Ex.union ex ex_d) :: dom.eqs }
        | Unknown -> add_split env dom i j (Equal (a, b, ex)))
    (env, { dom with edge_splits = [] })
    dom.edge_splits

(* The deduced equalities that are not known yet. *)
let flush_eqs uf (dom : Domain.t) =
  let eqs =
    List.filter_map
      (fun (v, w, ex) ->
        if same_class uf v w then None else Some (LX.mkv_eq v w, ex))
      (List.rev dom.eqs)
  in
  eqs, { dom with eqs = [] }

(* For each disequality [r <> s] where [r] and [s] are two arrays, we produce
   the formula: exists i:ty. (select r i) <> (select s i), where [ty] denotes
   the type of indices of [r] and [s]. *)
let extensionality_pair (env, acc) dep r s =
  match X.type_info r, X.term_extract r, X.term_extract s with
  | Ty.Tfarray (ty, _), (Some t1, _), (Some t2, _) ->
    let i = E.fresh_name ty in
    let g1 = E.ArraysEx.select t1 i in
    let g2 = E.ArraysEx.select t2 i in
    let d = E.mk_distinct ~iff:false [g1; g2] in
    let env =
      { env with new_terms = E.Set.add g2 (E.Set.add g1 env.new_terms) }
    in
    env, (Literal.LTerm d, dep, Th_util.Other) :: acc
  | _ -> env, acc

let extensionality acc (a, _, dep, _) =
  match a with
  | A.Distinct (false, (_ :: _ :: _ as l)) ->
    let rec aux acc = function
      | [] | [_] -> acc
      | r :: rl ->
        aux
          (List.fold_left (fun acc s -> extensionality_pair acc dep r s) acc rl)
          rl
    in
    aux acc l
  | _ -> acc

(* Whether the class of [v] has a term [(select b' k')] with [b'] in the class
   of [b] and [k'] in the class of [k]. *)
let has_select uf b k v =
  E.Set.exists
    (fun t ->
      match E.term_view t with
      | { f = Op Select; xs = [b'; k']; _ } ->
        same_class uf b (fst (Uf.find uf b'))
        && same_class uf k (fst (Uf.find uf k'))
      | _ -> false)
    (Uf.rclass_of uf (fst (Uf.find_r uf v)))

(* The equalities [(select b k) = v] between terms for the pending values,
   unless the class of [v] already has such a term. The terms are chosen in the
   current classes of [b], [k] and [v]. *)
let term_eqs uf env =
  List.fold_left
    (fun l { a = b; k; v; ex } ->
      if has_select uf b k v
      then l
      else
        match term_of uf b, term_of uf k, term_of uf v with
        | Some (b, ex_b), Some (k, ex_k), Some (v, ex_v) ->
          let ex = List.fold_left Ex.union ex [ex_b; ex_k; ex_v] in
          let eq = E.mk_eq ~iff:false (E.ArraysEx.select b k) v in
          (Literal.LTerm eq, ex, Th_util.Other) :: l
        | _ -> l)
    [] env.term_eqs

let assume env uf la =
  let dom = get_domain uf in
  let env, domains, l =
    if X.Map.is_empty dom.values && LX.Map.is_empty env.splits
    then
      (* No select or store terms: nothing to propagate. *)
      env, Uf.domains uf, []
    else
      let env, dom = process_dirty uf env dom in
      let lits = decided_splits uf dom la in
      let env, dom =
        resolve_splits uf env { dom with split_todo = LX.Set.empty } lits
      in
      let env, dom = split_edges uf env dom in
      let eqs, dom = flush_eqs uf dom in
      let l =
        List.rev_map (fun (eq, ex) -> Literal.LSem eq, ex, Th_util.Other) eqs
      in
      let l = List.rev_append (term_eqs uf env) l in
      { env with term_eqs = [] }, set_domain uf dom, l
  in
  let env, l = List.fold_left extensionality (env, l) la in
  env, domains, { Sig_rel.assume = l; remove = [] }

let two = Numbers.Q.from_int 2

(* Split on a case split [k = i] and try [k <> i] first: this branch propagates
   the values. *)
let case_split env _uf ~for_model:_ =
  match LX.Map.min_binding_opt env.splits with
  | Some (lit, _) ->
    let lit = LX.neg lit in
    Log.debug (fun k -> k "case split@ %a" LX.print lit);
    [LX.view lit, true, Th_util.CS (Th_util.Th_arrays, two)]
  | None -> []

let optimizing_objective _env _uf _o = None

let query _ _ _ = Th_util.Unknown

(* Propagate the values of [a] through the edge [a --i-- b]. *)
let cross_edge uf ((_, (dom : Domain.t), _) as acc) a i b =
  match X.Map.find_opt b (Domain.edges_of a dom) with
  | Some (j, eex) when X.equal i j ->
    X.Map.fold
      (fun k (v, ex) acc -> cross uf acc { a; k; v; ex } b i eex)
      (Domain.values_of a dom) acc
  | _ -> acc

(* Register the value and the edge of the select and store terms. *)
let add env uf r t =
  let register env dom =
    let { E.f; xs; _ } = E.term_view t in
    match f, xs with
    | Symbols.Op Select, [a; i] ->
      let v, ex_v = Uf.find_r uf r in
      let ra, ex_a = Uf.find uf a in
      let ri, ex_i = Uf.find uf i in
      let ex = Ex.union ex_v (Ex.union ex_a ex_i) in
      propagate uf (add_value ~from_select:true uf (env, dom, []) ra ri v ex)
    | Symbols.Op Store, [a; i; v] ->
      let s, ex_s = Uf.find_r uf r in
      let ra, ex_a = Uf.find uf a in
      let ri, ex_i = Uf.find uf i in
      let rv, ex_v = Uf.find uf v in
      let dom =
        Domain.add_edge ra ri s (Ex.union ex_a (Ex.union ex_i ex_s)) dom
      in
      (* The values of both arrays are propagated through the new edge. *)
      let acc = cross_edge uf (cross_edge uf (env, dom, []) ra ri s) s ri ra in
      propagate uf
        (add_value uf acc s ri rv (Ex.union ex_s (Ex.union ex_i ex_v)))
    | _ -> env, dom
  in
  match E.term_view t with
  | { f = Op (Select | Store); _ } ->
    let env, dom = register env (get_domain uf) in
    let env, dom = split_edges uf env dom in
    let eqs, dom = flush_eqs uf dom in
    env, set_domain uf dom, eqs
  | _ -> env, Uf.domains uf, []

let new_terms env = env.new_terms

let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Arrays -> failwith "This Theory does not support theories extension"
  | _ -> t

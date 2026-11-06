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

(* Sets of pairs [(a, k)] of an array and an index. *)
module XXSet = Set.Make (struct
  type t = X.r * X.r

  let compare (a1, k1) (a2, k2) =
    let c = X.hash_cmp a1 a2 in
    if c <> 0 then c else X.hash_cmp k1 k2
end)

(* The theory of arrays with extensionality, using global domains on the
   representatives of the union-find:

   - known values: [a[i] = v], from [(select a i)] and [a = (store _ i v)]

   - edges: [a --i-- b], from [b = (store a i _)] or [a = (store b i _)]. Which
   means: [forall j. j <> i -> a[j] = b[j]]

   - constant arrays: [a = (const c)], whose values are all equal to [c] *)

let src = Logs.Src.create ~doc:"Arrays_rel" __MODULE__

module Log = (val Logs.src_log src : Logs.LOG)

let timer = Timers.M_Arrays

let add_loc k a locs =
  X.Map.update k
    (function
      | None -> Some (X.Set.singleton a) | Some s -> Some (X.Set.add a s))
    locs

let remove_loc k a locs =
  X.Map.update k
    (function
      | None -> None
      | Some s ->
        let s = X.Set.remove a s in
        if X.Set.is_empty s then None else Some s)
    locs

let add_cell v cell cells =
  X.Map.update v
    (function
      | None -> Some (XXSet.singleton cell) | Some s -> Some (XXSet.add cell s))
    cells

let remove_cell v cell cells =
  X.Map.update v
    (function
      | None -> None
      | Some s ->
        let s = XXSet.remove cell s in
        if XXSet.is_empty s then None else Some s)
    cells

module Domain = struct
  type t =
    { values : (X.r * Ex.t) X.Map.t X.Map.t;
      (* [a -> k -> (v, ex)]: [a[k] = v] with the explanation [ex]. [v] is a
         representative. *)
      consts : (X.r * Ex.t) X.Map.t;
      (* [a -> (c, ex)]: [a] is the constant array [(const c)] with the
         explanation [ex]. *)
      edges : (X.r * Ex.t) X.Map.t X.Map.t;
      (* [a -> b -> (i, ex)]: the edge [a --i-- b] with the explanation [ex].
         The edges are stored in both directions, with at most one edge between
         two arrays (see [add_edge]). *)
      index_locs : X.Set.t X.Map.t;
      (* Map of indices to the arrays that have a value at this index. *)
      value_locs : XXSet.t X.Map.t;
      (* Map of values [v] to the pairs [(a, k)] such that [a[k] = v]. *)
      edge_locs : X.Set.t X.Map.t;
      (* Map of indices to the arrays that have an edge labelled by this
         index. *)
      edge_splits : (X.r * X.r * X.r * X.r * Ex.t) list;
      (* [(a, b, i, j, ex)]: the edge [a --j-- b] that was not added because of
         the edge [a --i-- b], to decide with a case split on [i = j] (see
         [add_edge]). *)
      split_locs : LX.Set.t X.Map.t;
      (* Map of indices to the case splits on this index. *)
      terms : E.t X.Map.t;
      (* A term of the class of each array, index and value of the domain. *)
      dirty : X.Set.t;
      (* Arrays whose values have to be propagated again through their edges. *)
      merged : (X.r * X.Set.t * X.Set.t) list;
      (* [(a, idxs, nbrs)]: the array [a] has been merged with an array whose
         values were at the indices [idxs] and whose neighbours were [nbrs].
         Only the values of each side have to be propagated through the edges of
         the other side (see [process_dirty]). *)
      merged_values : X.Set.t;
      (* Values that have been merged with others, to check again (see
         [check_merged_values]). *)
      split_todo : LX.Set.t;
      (* Case splits whose indices have been merged with others. *)
      eqs : (X.r * X.r * Ex.t) list;
      (* Deduced equalities that have not been propagated yet. *)
      neqs : (X.r * X.r * Ex.t) list
          (* Deduced disequalities that have not been propagated yet. *)
    }

  type _ Uf.id += Id : t Uf.id

  let empty =
    { values = X.Map.empty;
      consts = X.Map.empty;
      edges = X.Map.empty;
      index_locs = X.Map.empty;
      value_locs = X.Map.empty;
      edge_locs = X.Map.empty;
      edge_splits = [];
      split_locs = X.Map.empty;
      terms = X.Map.empty;
      dirty = X.Set.empty;
      merged = [];
      merged_values = X.Set.empty;
      split_todo = LX.Set.empty;
      eqs = [];
      neqs = []
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

  (* Record [tm] as the term of the class of [r], unless it already has one. *)
  let add_term r tm t =
    if X.Map.mem r t.terms then t else { t with terms = X.Map.add r tm t.terms }

  (* Add the value [a[k] = v]. If [a] already has a value at [k], deduce the
     equality of the two values instead. If [a] is a constant array, deduce the
     equality of [v] and its constant. Returns [true] if the known value is
     new. *)
  let add_value a k ((v, ex) as rd) t =
    let m = values_of a t in
    match X.Map.find k m with
    | v', ex' -> { t with eqs = (v, v', Ex.union ex ex') :: t.eqs }, false
    | exception Not_found ->
      let eqs =
        match X.Map.find_opt a t.consts with
        | Some (c, ex_c) -> (v, c, Ex.union ex ex_c) :: t.eqs
        | None -> t.eqs
      in
      ( { t with
          values = X.Map.add a (X.Map.add k rd m) t.values;
          index_locs = add_loc k a t.index_locs;
          value_locs = add_cell v (a, k) t.value_locs;
          eqs
        },
        true )

  (* Add the constant array [a = (const c)]: the values of [a] are equal to [c].
     If [a] is already a constant array, deduce the equality of the two
     constants instead. *)
  let add_const a ((c, ex) as cst) t =
    match X.Map.find_opt a t.consts with
    | Some (c', ex') -> { t with eqs = (c, c', Ex.union ex ex') :: t.eqs }
    | None ->
      let eqs =
        X.Map.fold
          (fun _ (v, ex_v) eqs -> (v, c, Ex.union ex ex_v) :: eqs)
          (values_of a t) t.eqs
      in
      { t with consts = X.Map.add a cst t.consts; eqs }

  (* Remove the value of [a] at [k], which is [v]. *)
  let remove_value a k v t =
    let m = X.Map.remove k (values_of a t) in
    { t with
      values =
        (if X.Map.is_empty m
         then X.Map.remove a t.values
         else X.Map.add a m t.values);
      index_locs = remove_loc k a t.index_locs;
      value_locs = remove_cell v (a, k) t.value_locs
    }

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
      match X.Map.find rr t.index_locs with
      | exception Not_found -> t
      | arrs ->
        let t = { t with index_locs = X.Map.remove rr t.index_locs } in
        X.Set.fold
          (fun a t ->
            let m = values_of a t in
            match X.Map.find rr m with
            | exception Not_found -> t
            | v, ex_v ->
              let t = remove_value a rr v t in
              let t = { t with dirty = X.Set.add a t.dirty } in
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

  (* The array [rr] is replaced by [nrr]: its constant, values and edges are
     moved to [nrr]. *)
  let subst_array ~ex rr nrr t =
    let rvalues = values_of rr t and redges = edges_of rr t in
    let nvalues = values_of nrr t and nedges = edges_of nrr t in
    let t =
      match X.Map.find_opt rr t.consts with
      | None -> t
      | Some (c, ex_c) ->
        add_const nrr
          (c, Ex.union ex ex_c)
          { t with consts = X.Map.remove rr t.consts }
    in
    let t =
      X.Map.fold
        (fun k (v, ex_v) t ->
          let t = remove_value rr k v t in
          fst (add_value nrr k (v, Ex.union ex ex_v) t))
        rvalues t
    in
    let t =
      X.Map.fold
        (fun b (i, e) t ->
          let bm = X.Map.remove rr (X.Map.find b t.edges) in
          let t = { t with edges = X.Map.add b bm t.edges } in
          add_edge nrr i b (Ex.union ex e) t)
        redges
        { t with edges = X.Map.remove rr t.edges }
    in
    (* Something has to be propagated only if one side has values and the other
       side has edges. *)
    if
      ((not (X.Map.is_empty rvalues)) && not (X.Map.is_empty nedges))
      || ((not (X.Map.is_empty nvalues)) && not (X.Map.is_empty redges))
    then
      let keys m = X.Map.fold (fun k _ s -> X.Set.add k s) m X.Set.empty in
      { t with merged = (nrr, keys rvalues, keys redges) :: t.merged }
    else t

  (* The value [rr] is replaced by [nrr] in the values of the arrays. The values
     in the class of [nrr] are checked again, as two of them may now be equal
     (see [check_edge]). *)
  let subst_value ~ex rr nrr t =
    match X.Map.find rr t.value_locs with
    | exception Not_found -> t
    | cells ->
      XXSet.fold
        (fun ((a, k) as cell) t ->
          let m = values_of a t in
          let _, ex_v = X.Map.find k m in
          { t with
            values =
              X.Map.add a (X.Map.add k (nrr, Ex.union ex ex_v) m) t.values;
            value_locs = add_cell nrr cell t.value_locs
          })
        cells
        { t with
          value_locs = X.Map.remove rr t.value_locs;
          merged_values = X.Set.add nrr t.merged_values
        }

  (* The term of [rr] becomes a term of [nrr]. *)
  let subst_term rr nrr t =
    match X.Map.find_opt rr t.terms with
    | None -> t
    | Some tm -> add_term nrr tm { t with terms = X.Map.remove rr t.terms }

  let subst ~ex rr nrr t =
    (* A value can be used both as an index and as an array if we have arrays
       indexed by arrays. *)
    subst_term rr nrr
      (subst_value ~ex rr nrr
         (subst_array ~ex rr nrr (subst_index ~ex rr nrr t)))
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

(* The case splits are chosen by creation order, the most recent first (see
   [case_split]). Each case split gets a stamp when it is created, and [order]
   maps the stamps of the pending case splits to them. Adding a consequence to a
   pending case split does not change its position, but a case split that is
   removed and created again gets a new position. *)
type t =
  { splits : (int * Conseqs.t) LX.Map.t;
    (* Map of the case splits [k = i] to their stamp and their consequences if
       [k <> i]. *)
    order : LX.t Util.MI.t;
    (* Map of the stamps of the pending case splits to these case splits. *)
    next_stamp : int;
    (* The stamp of the next case split. *)
    new_terms : E.Set.t;
    (* Terms produced by the theory that are sent to the instantiation
       engine. *)
    term_eqs : value list
        (* Values [b[k] = v] deduced by the theory whose equality [(select b k)
           = v] between terms has to be added to the congruence closure (for the
           instantiation engine/matching). *)
  }

let empty uf =
  ( { splits = LX.Map.empty;
      order = Util.MI.empty;
      next_stamp = 0;
      new_terms = E.Set.empty;
      term_eqs = []
    },
    (* The domain is only registered when the first select or store term is
       added: without arrays, the union-find does not update it. *)
    Uf.domains uf )

let same_class uf r1 r2 =
  match Uf.are_equal_r uf r1 r2 with Entailed _ -> true | Unknown -> false

(* The explanation of [r1 <> r2], if they are distinct. *)
let distinct_ex uf r1 r2 =
  match Uf.are_distinct_light uf r1 r2 with
  | Th_util.Entailed { ex; _ } -> Some ex
  | Unknown -> None

(* The value of [a] at [k], if any. *)
let find_value uf (dom : Domain.t) a k =
  let a, ex_a = Uf.find_r uf a in
  let k, ex_k = Uf.find_r uf k in
  match X.Map.find_opt k (Domain.values_of a dom) with
  | Some (w, ex) -> Some (w, Ex.union ex (Ex.union ex_a ex_k))
  | None -> None

(* The explanation of [a[k] <> v], if [a] has a value at [k] that is distinct
   from [v]. *)
let distinct_value uf dom a k v =
  match find_value uf dom a k with
  | Some (w, ex_w) -> Option.map (Ex.union ex_w) (distinct_ex uf v w)
  | None -> None

let update_split_locs f r locs =
  X.Map.update r
    (fun s -> Option.value ~default:LX.Set.empty s |> f |> Option.some)
    locs

let add_split env (dom : Domain.t) k i conseq =
  let lit = LX.mk_eq k i in
  match LX.Map.find lit env.splits with
  | n, ps ->
    ( { env with splits = LX.Map.add lit (n, Conseqs.add conseq ps) env.splits },
      dom )
  | exception Not_found ->
    let n = env.next_stamp in
    let add = update_split_locs (LX.Set.add lit) in
    ( { env with
        splits = LX.Map.add lit (n, Conseqs.singleton conseq) env.splits;
        order = Util.MI.add n lit env.order;
        next_stamp = n + 1
      },
      { dom with split_locs = add k (add i dom.split_locs) } )

(* Remove the case split [k = i], which is decided. *)
let remove_split uf env (dom : Domain.t) lit k i =
  let remove r = update_split_locs (LX.Set.remove lit) (fst (Uf.find_r uf r)) in
  let n, _ = LX.Map.find lit env.splits in
  ( { env with
      splits = LX.Map.remove lit env.splits;
      order = Util.MI.remove n env.order
    },
    { dom with split_locs = remove k (remove i dom.split_locs) } )

(* The term of the class of [r] (see [Domain.terms]), with the explanation of
   its membership. *)
let term_of uf (dom : Domain.t) r =
  let r, ex_r = Uf.find_r uf r in
  match X.Map.find_opt r dom.terms with
  | Some t -> Some (t, Ex.union ex_r (snd (Uf.find uf t)))
  | None -> None

(* Give the term [(select b k)] to the instantiation engine. *)
let add_new_term uf env dom b k =
  match term_of uf dom b, term_of uf dom k with
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
  let v, ex_v = Uf.find_r uf v in
  let ex = List.fold_left Ex.union ex [ex_b; ex_k; ex_v] in
  let dom, is_new = Domain.add_value b k (v, ex) dom in
  if is_new
  then
    let value = { a = b; k; v; ex } in
    let env =
      if not from_select
      then
        let env = add_new_term uf env dom b k in
        { env with term_eqs = value :: env.term_eqs }
      else env
    in
    env, dom, value :: todo
  else env, dom, todo

(* The value of [a] at [i], or its constant. *)
let value_at (dom : Domain.t) a i =
  match X.Map.find_opt i (Domain.values_of a dom) with
  | None -> X.Map.find_opt a dom.consts
  | w -> w

(* For the edge [a --i-- b], with [k = i], and the values [a[k] = a_k] and [b[k]
   = b_k], or the constant of [b]: [a = b] if [a_k = b_k], since [a] and [b]
   agree on all the other indices, and [a <> b] if [a_k <> b_k]. *)
let check_edge uf (env, (dom : Domain.t), todo) { a; k; v = a_k; ex } b eex =
  let k, ex_k = Uf.find_r uf k in
  match value_at dom b k with
  | None -> env, dom, todo
  | Some (b_k, ex_b) -> (
    let a_k, ex_a' = Uf.find_r uf a_k in
    let b_k, ex_b' = Uf.find_r uf b_k in
    let ex = List.fold_left Ex.union ex [ex_k; ex_b; ex_a'; ex_b'; eex] in
    if X.equal a_k b_k
    then
      if same_class uf a b
      then env, dom, todo
      else env, { dom with eqs = (a, b, ex) :: dom.eqs }, todo
    else
      match distinct_ex uf a_k b_k with
      | Some ex_d ->
        env, { dom with neqs = (a, b, Ex.union ex ex_d) :: dom.neqs }, todo
      | None -> env, dom, todo)

(* Propagate the value [a[k] = a_k] through the edge [a --i-- b]: add [b[k] =
   a_k] if [k <> i], call [check_edge] if [k = i]. Otherwise:

   - if [b[k] = a_k] already holds, there is nothing to propagate;

   - if [b[k] <> a_k], then [k = i], since [a] and [b] agree on all the other
   indices;

   - if [a[i] <> a_k], then [k <> i] and [b[k] = a_k];

   - otherwise, a case split on [k = i] is created. *)
let cross uf acc ({ a; k; v = a_k; ex } as value) b i eex =
  if same_class uf k i
  then check_edge uf acc value b eex
  else
    let ex = Ex.union ex eex in
    match Uf.are_distinct_light uf k i with
    | Entailed { ex = ex_d; _ } -> add_value uf acc b k a_k (Ex.union ex ex_d)
    | Unknown -> (
      let env, dom, todo = acc in
      match find_value uf dom b k with
      | Some (b_k, _) when same_class uf a_k b_k -> acc
      | _ -> (
        match distinct_value uf dom b k a_k with
        | Some ex_w ->
          env, { dom with eqs = (k, i, Ex.union ex ex_w) :: dom.eqs }, todo
        | None -> (
          match distinct_value uf dom a i a_k with
          | Some ex_w -> add_value uf acc b k a_k (Ex.union ex ex_w)
          | None ->
            let env, dom =
              add_split env dom k i (Value { a = b; k; v = a_k; ex })
            in
            (* As the value may only be propagated during the case-split search
               of the theory, its term is given to the instantiation engine
               now. *)
            add_new_term uf env dom b k, dom, todo)))

(* Propagate the values of [todo] through the edges of their arrays. *)
let rec propagate uf (env, (dom : Domain.t), todo) =
  match todo with
  | [] -> env, dom
  | ({ a; _ } as value) :: todo ->
    propagate uf
      (X.Map.fold
         (fun b (i, eex) acc -> cross uf acc value b i eex)
         (Domain.edges_of a dom) (env, dom, todo))

(* Propagate again the values of the arrays whose values or edges changed, and
   the values of the merged arrays through the edges of the other side. *)
let process_dirty uf env (dom : Domain.t) =
  let norm s = X.Set.map (fun r -> fst (Uf.find_r uf r)) s in
  let values a =
    let a, _ = Uf.find_r uf a in
    a, Domain.values_of a dom
  in
  let todo =
    X.Set.fold
      (fun a todo ->
        let a, m = values a in
        X.Map.fold (fun k (v, ex) todo -> { a; k; v; ex } :: todo) m todo)
      dom.dirty []
  in
  let acc = env, { dom with dirty = X.Set.empty; merged = [] }, todo in
  propagate uf
    (List.fold_left
       (fun acc (a, idxs, nbrs) ->
         let a, m = values a in
         let idxs = norm idxs and nbrs = norm nbrs in
         X.Map.fold
           (fun b (i, eex) acc ->
             let other = X.Set.mem b nbrs in
             X.Map.fold
               (fun k (v, ex) acc ->
                 if Bool.equal (X.Set.mem k idxs) other
                 then acc
                 else cross uf acc { a; k; v; ex } b i eex)
               m acc)
           (Domain.edges_of a dom) acc)
       acc dom.merged)

(* Decide the case splits [lits] whose indices are now equal or distinct. *)
let resolve_splits uf env dom lits =
  propagate uf
    (LX.Set.fold
       (fun lit ((env, dom, todo) as acc) ->
         match LX.Map.find lit env.splits, LX.view lit with
         | exception Not_found -> acc
         | (_, ps), A.Eq (k, i) -> (
           if same_class uf k i
           then
             let env, dom = remove_split uf env dom lit k i in
             env, dom, todo
           else
             match Uf.are_distinct_light uf k i with
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

(* The values [a[k] = v] with [v] in the class of [r]. *)
let values_of_class uf (dom : Domain.t) todo r =
  let r = fst (Uf.find_r uf r) in
  match X.Map.find_opt r dom.value_locs with
  | Some cells ->
    XXSet.fold
      (fun (a, k) todo ->
        let v, ex = X.Map.find k (Domain.values_of a dom) in
        { a; k; v; ex } :: todo)
      cells todo
  | None -> todo

(* The values of the disequalities of [la], to propagate again: they may now be
   distinct from other values (see [cross]). *)
let distinct_values uf dom la =
  List.fold_left
    (fun todo (a, _, _, _) ->
      match a with
      | A.Distinct (false, l) -> List.fold_left (values_of_class uf dom) todo l
      | _ -> todo)
    [] la

(* The values that have been merged with others are checked against the edges
   labelled by their index: two of them may now be equal (see [check_edge]). *)
let check_merged_values uf env (dom : Domain.t) =
  let values =
    X.Set.fold
      (fun r todo -> values_of_class uf dom todo r)
      dom.merged_values []
  in
  let check acc ({ a; k; _ } as value) =
    X.Map.fold
      (fun b (i, eex) acc ->
        if same_class uf k i then check_edge uf acc value b eex else acc)
      (Domain.edges_of a dom) acc
  in
  let env, dom, _ =
    List.fold_left check
      (env, { dom with merged_values = X.Set.empty }, [])
      values
  in
  env, dom

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
        match Uf.are_distinct_light uf i j with
        | Entailed { ex = ex_d; _ } ->
          env, { dom with eqs = (a, b, Ex.union ex ex_d) :: dom.eqs }
        | Unknown -> add_split env dom i j (Equal (a, b, ex)))
    (env, { dom with edge_splits = [] })
    dom.edge_splits

(* The deduced equalities and disequalities that are not known yet. *)
let flush_eqs uf (dom : Domain.t) =
  let eqs =
    List.filter_map
      (fun (v, w, ex) ->
        if same_class uf v w then None else Some (LX.mkv_eq v w, ex))
      (List.rev dom.eqs)
  in
  let neqs =
    List.filter_map
      (fun (a, b, ex) ->
        match Uf.are_distinct_light uf a b with
        | Th_util.Entailed _ -> None
        | Unknown -> Some (LX.mkv_distinct false [a; b], ex))
      (List.rev dom.neqs)
  in
  eqs @ neqs, { dom with eqs = []; neqs = [] }

let diff = Symbols.name ~ns:Internal "@diff"

(* Whether a known index [k] has [r[k] <> s[k]]. *)
let has_witness uf dom r s =
  let r, _ = Uf.find_r uf r in
  X.Map.exists
    (fun k (v, _) -> Option.is_some (distinct_value uf dom s k v))
    (Domain.values_of r dom)

(* For each disequality [r <> s] where [r] and [s] are two arrays, we produce
   the formula: (select r i) <> (select s i) where [i] is the index [(@diff r
   s)], unless a known index already distinguishes them. The same index is used
   for the same arrays. *)
let extensionality_pair uf dom (env, acc) dep r s =
  match X.type_info r, X.term_extract r, X.term_extract s with
  | Ty.Tfarray (ty, _), (Some t1, _), (Some t2, _)
    when not (has_witness uf dom r s) ->
    let t1, t2 = if E.compare t1 t2 <= 0 then t1, t2 else t2, t1 in
    let i = E.mk_term diff [t1; t2] ty in
    let g1 = E.ArraysEx.select t1 i in
    let g2 = E.ArraysEx.select t2 i in
    let d = E.mk_distinct ~iff:false [g1; g2] in
    let env =
      { env with new_terms = E.Set.add g2 (E.Set.add g1 env.new_terms) }
    in
    env, (Literal.LTerm d, dep, Th_util.Other) :: acc
  | _ -> env, acc

let extensionality uf dom acc (a, _, dep, _) =
  match a with
  | A.Distinct (false, (_ :: _ :: _ as l)) ->
    let rec aux acc = function
      | [] | [_] -> acc
      | r :: rl ->
        aux
          (List.fold_left
             (fun acc s -> extensionality_pair uf dom acc dep r s)
             acc rl)
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
   unless the class of [v] already has such a term. *)
let term_eqs uf env dom =
  List.fold_left
    (fun l { a = b; k; v; ex } ->
      if has_select uf b k v
      then l
      else
        match term_of uf dom b, term_of uf dom k, term_of uf dom v with
        | Some (b, ex_b), Some (k, ex_k), Some (v, ex_v) ->
          let ex = List.fold_left Ex.union ex [ex_b; ex_k; ex_v] in
          let eq = E.mk_eq ~iff:false (E.ArraysEx.select b k) v in
          (Literal.LTerm eq, ex, Th_util.Other) :: l
        | _ -> l)
    [] env.term_eqs

let assume env uf la =
  let dom = get_domain uf in
  let env, domains, l =
    if
      X.Map.is_empty dom.values && LX.Map.is_empty env.splits
      && Compat.List.is_empty dom.eqs
    then
      (* No select or store terms: nothing to propagate. The equalities can come
         from two constant arrays that are merged. *)
      env, Uf.domains uf, []
    else
      let env, dom = process_dirty uf env dom in
      let env, dom = check_merged_values uf env dom in
      let env, dom = propagate uf (env, dom, distinct_values uf dom la) in
      let lits = decided_splits uf dom la in
      let env, dom =
        resolve_splits uf env { dom with split_todo = LX.Set.empty } lits
      in
      let env, dom = split_edges uf env dom in
      let eqs, dom = flush_eqs uf dom in
      let l =
        List.rev_map (fun (eq, ex) -> Literal.LSem eq, ex, Th_util.Other) eqs
      in
      let l = List.rev_append (term_eqs uf env dom) l in
      { env with term_eqs = [] }, set_domain uf dom, l
  in
  let dom = Uf.GlobalDomains.find (module Domain) domains in
  let env, l = List.fold_left (extensionality uf dom) (env, l) la in
  env, domains, { Sig_rel.assume = l; remove = [] }

let two = Numbers.Q.from_int 2

(* Split on the most recent case split [k = i] and try [k <> i] first: this
   branch propagates the values. *)
let case_split env _uf ~for_model:_ =
  match Util.MI.max_binding_opt env.order with
  | Some (_, lit) ->
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

(* Register the value and the edge of the select and store terms, the constant
   arrays, and their terms (see [Domain.terms]). *)
let add env uf r t =
  let register env dom =
    let { E.f; xs; _ } = E.term_view t in
    match f, xs with
    | Symbols.Op Const_array, [c] ->
      let ra, ex_a = Uf.find_r uf r in
      let rc, ex_c = Uf.find uf c in
      env, Domain.add_const ra (rc, Ex.union ex_a ex_c) dom
    | Symbols.Op Select, [a; i] ->
      let v, ex_v = Uf.find_r uf r in
      let ra, ex_a = Uf.find uf a in
      let ri, ex_i = Uf.find uf i in
      let dom = Domain.(add_term v t (add_term ra a (add_term ri i dom))) in
      let ex = Ex.union ex_v (Ex.union ex_a ex_i) in
      propagate uf (add_value ~from_select:true uf (env, dom, []) ra ri v ex)
    | Symbols.Op Store, [a; i; v] ->
      let s, ex_s = Uf.find_r uf r in
      let ra, ex_a = Uf.find uf a in
      let ri, ex_i = Uf.find uf i in
      let rv, ex_v = Uf.find uf v in
      let dom =
        Domain.(
          add_term s t (add_term ra a (add_term ri i (add_term rv v dom))))
      in
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
  | { f = Op (Select | Store | Const_array); _ } ->
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

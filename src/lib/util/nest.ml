(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2024 --- OCamlPro SAS                                *)
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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module DStd = Dolmen.Std
module DE = DStd.Expr
module DT = DE.Ty
module B = DStd.Builtin

(* A nest is the set of all the constructors of a mutually recursive definition
   of ADTs.

   For each type ty of a nest, we denote by S(ty) the set of all the
   constructors of this type in this nest and G(ty) the set of the constructors
   with an argument of type ty in this nest.

   Recall that a (directed) hypergraph is a set of nodes and hyperedges between
   subsets of these nodes.

   To generate our total order of a nest, we build in [build_graph] a hypergraph
   where:
   - the nodes are all the constructors of the nest;
   - for all type ty of the nest, there is a hyperedge from S(ty) to G(ty).

   In particular, our graph has exactly one outgoing hyperedge per node. *)

(* Node of the hypergraph. *)
type node = {
  id : DE.term_cst;
  (* Dolmen constructor identifier. *)

  weight : int;
  (* This weight is used to prioritize constructors with less destructors
     during the sorting (see [add_nest]). *)

  outgoing : edge;
  (* Hyperedge from a subset S in S(ty) to a subset G in G(ty) where ty is
     the type of [id]. At the beginning, we have S = S(ty) and G = G(ty).

     One use a double indirection because this hyperedge is shared between
     all the elements of S. *)

  mutable in_degree : int;
  (* Number of hyperedges into this constructor. *)
}

(* Type of a hyperedge. *)
and edge = node list ref

module Hp =
  Heap.MakeOrdered
    (struct
      type t = node
      let compare { weight = w1; _ } { weight = w2; _ } = w1 - w2

      let default =
        let dummy_edge : node list ref = ref [] in
        {
          id = DE.Term.Const.Int.int "0" (* dummy *);
          outgoing = dummy_edge;
          in_degree = -1;
          weight = -1;
        }
    end)

let (let*) = Option.bind

(* Return the type definition of the return type of the destructor [dstr]. *)
let def_of_dstr dstr =
  let* ty_cst =
    match dstr with
    | DE.{ builtin = B.Destructor _; id_ty; _ } ->
      begin match DT.view id_ty with
        | `Arrow (_, ty) ->
          begin match DT.view ty with
            | `App (`Generic ty_cst, _) -> Some ty_cst
            | _ -> None
          end
        | _ -> None
      end
    | _ -> assert false
  in
  DT.definition ty_cst

(* Build the hypergraph of dependencies between the constructors of the
   nest [defs].

   @return a heap that contains all the nodes of this graph without ingoing
   hyperedges. *)
let build_graph (defs : DE.ty_def list) : Hp.t =
  let map : (DE.ty_def, edge) Hashtbl.t = Hashtbl.create 17 in
  let hp : Hp.t = Hp.create 17 in
  List.iter (fun d -> Hashtbl.add map d (ref [])) defs;
  List.iter
    (fun def ->
       match def with
       | DE.Abstract -> assert false
       | DE.Adt { cases; _ } ->
         Array.iter
           (fun DE.{ cstr; dstrs; _ } ->
              let node = {
                id = cstr;
                outgoing = Hashtbl.find map def;
                in_degree = -1; (* dummy value *)
                weight = Array.length dstrs
              }
              in
              let in_degree =
                Array.fold_left
                  (fun acc dstr ->
                     match Option.bind dstr def_of_dstr with
                     | Some d ->
                       begin match Hashtbl.find map d with
                         | edge -> edge := node :: !edge; acc + 1
                         | exception Not_found -> acc
                       end
                     | None -> acc
                  ) 0 dstrs
              in
              node.in_degree <- in_degree;
              if in_degree = 0 then Hp.insert hp node
           ) cases
    ) defs;
  hp

module H = struct
  include Hashtbl.Make (DE.Ty.Const)

  let add_constr t (ty : DE.ty_cst) (constr : DE.term_cst) =
    match find t ty with
    | len, constrs ->
      add t ty (len + 1, constr :: constrs); len
    | exception Not_found ->
      add t ty (1, [constr]); 0
end

let ty_cst_of_constr DE.{ builtin; _ } =
  match builtin with
  | B.Constructor { adt; _ } -> adt
  | _ -> Fmt.failwith "expect an ADT constructor"

let attach_orders defs =
  let hp = build_graph defs in
  let r : (int * DE.term_cst list) H.t = H.create 17 in
  while not @@ Hp.is_empty hp do
    (* Loop invariant: the set of nodes in heap [hp] is exactly
       the set of the nodes of the graph without ingoing hyperedge. *)
    let { id; outgoing; in_degree;  _ } = Hp.pop_min hp in
    let ty = ty_cst_of_constr id in
    let o = H.add_constr r ty id in
    DE.Term.Const.set_tag id Uid.order_tag o;
    assert (in_degree = 0);
    List.iter
      (fun node ->
         assert (node.in_degree > 0);
         node.in_degree <- node.in_degree - 1;
         if node.in_degree = 0 then
           Hp.insert hp node
      ) !outgoing;
    outgoing := [];
  done

let perfect_hash id =
  match (id : _ Uid.t) with
  | Term_cst ({ builtin = B.Constructor _; _ } as id) ->
    begin match DE.Term.Const.get_tag id Uid.order_tag with
      | Some h -> h
      | None ->
        (* Cannot occur as we eliminate this case in the smart constructor
           [Uid.of_term_cst]. *)
        assert false
    end
  | Term_cst _ -> invalid_arg "Nest.perfect_hash"
  | _ -> .

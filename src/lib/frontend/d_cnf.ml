
open Options
open D_loop

module E = Expr
module SE = E.Set

module C = Commands
module Sy = Symbols
module SM = Sy.Map

module DE = DStd.Expr
module DT = DE.Ty
module Id = DStd.Id
module B = DStd.Builtin

module HT = Hashtbl.Make(
  struct
    type t = int
    let equal = (=)
    let hash = Fun.id
  end)

(** Helper function: returns the basename of a dolmen path, since in AE
    the problems are contained in one-file (for now at least), the path is
    irrelevant and only the basename matters *)
let get_basename = function
  | DStd.Path.Local { name; }
  | Absolute { name; path = []; } -> name
  | Absolute { name; path; } ->
    failwith (
      Format.asprintf
        "Expected an empty path to the basename: \"%s\" but got: [%a]."
        name (fun fmt l ->
            match l with
            | h :: t ->
              Format.fprintf fmt "%s" h;
              List.iter (Format.fprintf fmt "; %s") t
            | _ -> ()
          ) path
    )

module Cache = struct

  let ae_sy_ht: Sy.t HT.t = HT.create 100

  let ae_ty_ht: Ty.t HT.t = HT.create 100

  let store_sy ind sy =
    HT.add ae_sy_ht ind sy

  let store_ty ind ty =
    HT.add ae_ty_ht ind ty

  let find_sy ind =
    HT.find ae_sy_ht ind

  let find_ty ind =
    HT.find ae_ty_ht ind

  let fresh_ty ?(is_var = true) ?(name = None) () =
    if is_var
    then Ty.fresh_tvar ()
    else
      match name with
      | Some n -> Ty.text [] n
      | None -> Ty.fresh_empty_text ()

  let update_ty_store ?(is_var = true) ?name ind =
    let ty = fresh_ty ~is_var ~name () in
    store_ty ind ty

  let update_ty_store_ret ?(is_var = true) ?name ind =
    let ty = fresh_ty ~is_var ~name () in
    store_ty ind ty;
    ty

  let find_update_ty ?(is_var = true) ind =
    match HT.find_opt ae_ty_ht ind with
    | Some ty -> ty
    | None ->
      update_ty_store_ret ~is_var ind

  let store_tyv ?(is_var = true) ({ DE.path; _ } as t_v) =
    let name = get_basename path in
    update_ty_store ~is_var ~name (DE.Ty.Var.hash t_v)

  let store_tyvl ?(is_var = true) (tyvl: DE.ty_var list) =
    List.iter (store_tyv ~is_var) tyvl

  let store_tyv_ret ?(is_var = true) ({ DE.path; _ } as t_v) =
    let name = get_basename path in
    update_ty_store_ret ~is_var ~name (DE.Ty.Var.hash t_v)

  let store_tyvl_ret ?(is_var = true) (tyvl: DE.ty_var list) =
    List.map (store_tyv_ret ~is_var) tyvl

  let store_sy_vl_names (tvl: DE.term_var list) =
    List.iter (
      fun ({ DE.path; _ } as tv) ->
        let name = get_basename path in
        store_sy (DE.Term.Var.hash tv) (Sy.name name)
    ) tvl

  let store_ty_vars ?(is_var = true) ty =
    match DT.view ty with
    | `Var ty_v ->
      store_tyv ~is_var ty_v
    | `Pi (tyvl, _) ->
      store_tyvl ~is_var tyvl
    | _-> ()

  let store_ty_vars_ret ?(is_var = true) ty =
    match DT.view ty with
    | `Var ty_v ->
      [store_tyv_ret ~is_var ty_v]
    | `Pi (tyvl, _) ->
      store_tyvl_ret ~is_var tyvl
    | _-> []
  (* Assumes that the two cases are the only cases in which type variables are
     introduced *)

  let clear () =
    HT.clear ae_sy_ht;
    HT.clear ae_ty_ht

end

(** Translates dolmen locs to Alt-Ergo's locs *)
let dl_to_ael dloc_file (compact_loc: DStd.Loc.t) =
  DStd.Loc.(lexing_positions (loc dloc_file compact_loc))

(** clears the cache in the [Cache] module. *)
let clear_cache () = Cache.clear ()

(** [dty_to_ty update is_var subst tyv_substs dty]

    Converts a Dolmen type to an Alt-Ergo type.
    - If [update] is [true] then for each type variable of type [DE.Ty.Var.t],
      if it was not encountered before, a new type variable of type [Ty.t] is
      created and added to the cache.
    - If [dty] is a type application, or an arrow type, only its return type
      is converted since those have no counterpart in AE's [Ty] module. The
      function arguments' types or the type paramters ought to be converted
      individually.
*)
let rec dty_to_ty ?(update = false) ?(is_var = false) dty =
  let aux = dty_to_ty ~update ~is_var in
  match DT.view dty with
  | `Prop | `App (`Builtin B.Prop, []) -> Ty.Tbool
  | `Int  | `App (`Builtin B.Int, []) -> Ty.Tint
  | `Real | `App (`Builtin B.Real, []) -> Ty.Treal
  | `Array (ity, vty) ->
    let ity = aux ity in
    let vty = aux vty in
    Ty.Tfarray (ity, vty)
  | `Bitv n -> Ty.Tbitv n

  | `App (`Builtin B.Unit, []) -> Ty.Tunit
  | `App (`Builtin _, [ty]) -> aux ty
  | `App (`Generic c, l) -> handle_ty_app ~update c l

  | `Var ty_v when update ->
    Cache.find_update_ty (DE.Ty.Var.hash ty_v)
  | `Var ty_v ->
    Cache.find_ty (DE.Ty.Var.hash ty_v)

  | `Arrow (_, ty) -> aux ty
  | `Pi (tyvl, ty) ->
    if update then
      Cache.store_tyvl ~is_var tyvl;
    aux ty
  | _ -> failwith (
      Format.asprintf "Unsupported Type %a" DE.Ty.print dty
    )

and handle_ty_app ?(update = false) ty_c l =
  (* Applies the substitutions in [tysubsts] to each encountered type
     variable. *)
  let rec apply_ty_substs tysubsts ty =
    match ty with
    | Ty.Tvar { v; _ } ->
      Ty.M.find v tysubsts

    | Text (tyl, hs) ->
      Ty.Text (List.map (apply_ty_substs tysubsts) tyl, hs)

    | Tfarray (ti, tv) ->
      Tfarray (
        apply_ty_substs tysubsts ti,
        apply_ty_substs tysubsts tv
      )

    | Tadt (hs, tyl) ->
      Tadt (hs, List.map (apply_ty_substs tysubsts) tyl)

    | Trecord ({ args; lbs; _ } as rcrd) ->
      Trecord {
        rcrd with
        args = List.map (apply_ty_substs tysubsts) args;
        lbs = List.map (
            fun (hs, t) ->
              hs, apply_ty_substs tysubsts t
          ) lbs;
      }

    | _ -> ty
  in
  let tyl = List.map (dty_to_ty ~update) l in
  (* Recover the initial versions of the types and apply them on the provided
     type arguments stored in [tyl]. *)
  match Cache.find_ty (DE.Ty.Const.hash ty_c) with
  | Tadt (hs, _) -> Tadt (hs, tyl)

  | Trecord { args; _ } as ty ->
    let tysubsts =
      List.fold_left2 (
        fun acc tv ty ->
          match tv with
          | Ty.Tvar { v; _ } -> Ty.M.add v ty acc
          | _ -> assert false
      ) Ty.M.empty args tyl
    in
    apply_ty_substs tysubsts ty

  | Tsum _ as ty -> ty
  | Text (_, s) -> Text (tyl, s)
  | _ -> assert false

(** Handles a simple type declaration. *)
let mk_ty_decl (ty_c: DE.ty_cst) =
  match DT.definition ty_c with
  | Some (
      Adt { cases = [| { cstr = { id_ty; _ }; dstrs; _ } |]; _ }
    ) ->
    (* Records and adts that only have one case are treated in the same way,
       and considered as records. *)
    let tyvl = Cache.store_ty_vars_ret id_ty in
    let rev_lbs =
      Array.fold_left (
        fun acc c ->
          match c with
          | Some DE.{ path; id_ty; _ } ->
            let pn = get_basename path in
            let pty = dty_to_ty id_ty in
            (pn, pty) :: acc
          | _ -> failwith (
              Format.asprintf
                "Unexpected null label for some field of the record type \
                 %a"
                DE.Ty.Const.print ty_c
            )
      ) [] dstrs
    in
    let lbs = List.rev rev_lbs in
    let ty = Ty.trecord tyvl (get_basename ty_c.path) lbs in
    Cache.store_ty (DE.Ty.Const.hash ty_c) ty

  | Some (
      ( Adt { cases; _ } as _adt)
    ) ->
    let name = get_basename ty_c.path in
    let tyvl = Cache.store_ty_vars_ret cases.(0).cstr.id_ty in
    let rev_cs, is_enum =
      Array.fold_left (
        fun (accl, is_enum) DT.{ cstr = { path; _ }; dstrs; _ } ->
          let is_enum =
            if is_enum
            then
              if Array.length dstrs = 0
              then true
              else (
                let ty = Ty.t_adt name tyvl in
                Cache.store_ty (DE.Ty.Const.hash ty_c) ty;
                false
              )
            else false
          in
          let rev_fields =
            Array.fold_left (
              fun acc tc_o ->
                match tc_o with
                | Some DE.{ id_ty; path; _ } ->
                  (get_basename path, dty_to_ty id_ty) :: acc
                | None -> assert false
            ) [] dstrs
          in
          let name = get_basename path in
          (name, List.rev rev_fields) :: accl, is_enum
      ) ([], true) cases
    in
    if is_enum
    then
      let cstrs =
        List.map (fun s -> fst s) (List.rev rev_cs)
      in
      let ty = Ty.tsum name cstrs in
      Cache.store_ty (DE.Ty.Const.hash ty_c) ty
    else
      let body = Some (List.rev rev_cs) in
      let ty = Ty.t_adt ~body name tyvl in
      Cache.store_ty (DE.Ty.Const.hash ty_c) ty

  | None | Some Abstract ->
    let name = get_basename ty_c.path in
    let ty_params = []
    (* List.init ty_c.id_ty.arity (fun _ -> Ty.fresh_tvar ()) *)
    in
    let ty = Ty.text ty_params name in
    Cache.store_ty (DE.Ty.Const.hash ty_c) ty

(** Handles term declaration by storing the eventual present type variables
    in the cache as well as the symbol associated to the term. *)
let mk_term_decl ({ id_ty; path; tags; _ } as tcst: DE.term_cst) =
  let name = get_basename path in
  let sy =
    begin match DStd.Tag.get tags DE.Tags.ac with
      | Some () -> Sy.name ~kind:Sy.Ac name
      | _ -> Sy.name name
    end
  in
  Cache.store_sy (DE.Term.Const.hash tcst) sy;
  (* Adding polymorphic types to the cache. *)
  Cache.store_ty_vars id_ty

(** Handles the definitions of a list of mutually recursive types.
    - If one of the types is an ADT, the ADTs that have only one case are
      considered as ADTs as well and not as records. *)
let mk_mr_ty_decls (tdl: DE.ty_cst list) =
  let handle_ty_decl (ty: Ty.t) (tdef: DE.Ty.def option) =
    match ty, tdef with
    | Trecord { args; name; record_constr; _ },
      Some (
        Adt { cases = [| { dstrs; _ } |]; ty = ty_c; _ }
      ) ->
      let rev_lbs =
        Array.fold_left (
          fun acc c ->
            match c with
            | Some DE.{ path; id_ty; _ } ->
              let pn = get_basename path in
              let pty = dty_to_ty id_ty in
              (pn, pty) :: acc
            | _ -> failwith (
                Format.asprintf
                  "Unexpected null label for some field of the record type \
                   %a"
                  DE.Ty.Const.print ty_c
              )
        ) [] dstrs
      in
      let lbs = List.rev rev_lbs in
      let name = Hstring.view name in
      let record_constr = Hstring.view record_constr in
      let ty =
        Ty.trecord ~record_constr args name lbs
      in
      Cache.store_ty (DE.Ty.Const.hash ty_c) ty

    | Tadt (hs, tyl),
      Some (
        Adt { cases; ty = ty_c; _ }
      ) ->
      let rev_cs =
        Array.fold_left (
          fun (accl) DT.{ cstr = { path; _ }; dstrs; _ } ->
            let rev_fields =
              Array.fold_left (
                fun acc tc_o ->
                  match tc_o with
                  | Some DE.{ id_ty; path; _ } ->
                    (get_basename path, dty_to_ty id_ty) :: acc
                  | None -> assert false
              ) [] dstrs
            in
            let name = get_basename path in
            (name, List.rev rev_fields) :: accl
        ) [] cases
      in
      let body = Some (List.rev rev_cs) in
      let args = tyl in
      let ty = Ty.t_adt ~body (Hstring.view hs) args in
      Cache.store_ty (DE.Ty.Const.hash ty_c) ty

    | _ -> assert false
  in
  (* If there are adts in the list of type declarations then records are
     converted to adts, because that's how it's done in the legacy typechecker.
     But it might be more efficient not to do that. *)
  let rev_tdefs, contains_adts =
    List.fold_left (
      fun (acc, ca) ty_c ->
        match DT.definition ty_c with
        | Some (Adt { record; cases; _ }) as df
          when not record && Array.length cases > 1 ->
          df :: acc, true
        | df -> df :: acc, ca
    ) ([], false) tdl
  in
  let rev_l =
    List.fold_left (
      fun acc tdef ->
        match tdef with
        | Some (
            (DT.Adt { cases; record; ty = ty_c; }) as adt
          ) ->
          let tyvl = Cache.store_ty_vars_ret cases.(0).cstr.id_ty in
          let name = get_basename ty_c.path in

          let cns, is_enum =
            Array.fold_right (
              fun DE.Ty.{ dstrs; cstr = { path; _ }; _ } (nacc, is_enum) ->
                get_basename path :: nacc,
                Array.length dstrs = 0 && is_enum
            ) cases ([], true)
          in
          if is_enum
          then (
            let ty = Ty.tsum name cns in
            Cache.store_ty (DE.Ty.Const.hash ty_c) ty;
            (* If it's an enum we don't need the second iteration. *)
            acc
          )
          else (
            let ty =
              if (record || Array.length cases = 1) && not contains_adts
              then Ty.trecord tyvl name []
              else Ty.t_adt name tyvl
            in
            Cache.store_ty (DE.Ty.Const.hash ty_c) ty;
            (ty, Some adt) :: acc
          )
        | None
        | Some Abstract ->
          assert false (* unreachable in the second iteration *)
    ) [] (List.rev rev_tdefs)
  in
  List.iter (
    fun (t, d) -> handle_ty_decl t d
  ) (List.rev rev_l)

(** Helper function hadle variables that are encoutered in patterns. *)
let handle_patt_var name (DE.{ term_descr; _ } as term)  =
  match term_descr with
  | Cst ({ builtin = B.Base; id_ty; _ } as ty_c) ->
    let ty = dty_to_ty id_ty in
    let n = Hstring.make name in
    let v = Var.of_hstring n in
    let sy = Sy.Var v in
    Cache.store_sy (DE.Term.Var.hash ty_c) sy;
    v, n, ty

  | Var ({ builtin = B.Base; id_ty; _ } as ty_v) ->
    let ty = dty_to_ty id_ty in
    let n = Hstring.make name in
    let v = Var.of_hstring n in
    let sy = Sy.Var v in
    Cache.store_sy (DE.Term.Var.hash ty_v) sy;
    v, n, ty

  | _ -> failwith (
      Format.asprintf
        "Expected a variable in a case match but got %a"
        DE.Term.print term
    )

(** Helper function to translate patterns in a pattern-matching from a Dolmen
    Term.t to an Alt-Ergo Expr.t *)
let mk_pattern DE.{ term_descr; _ } =
  match term_descr with
  | App (
      { term_descr =
          Cst { builtin = B.Constructor { adt; case; }; path; _ }; _
      }, _, pargs
    ) ->
    let name = Hstring.make (get_basename path) in
    let rev_vnames =
      begin match DT.definition adt with
        | Some (Adt { cases; _ }) ->
          let { DT.dstrs; _ } = cases.(case) in
          Array.fold_left (
            fun acc v ->
              match v with
              | Some DE.{ path; _ } -> get_basename path :: acc
              | _ -> assert false
          ) [] dstrs
        | _ -> failwith (
            Format.asprintf
              "Expected a constructor for an algebraic data type but got\
               something else for the definition of: %a"
              DE.Ty.Const.print adt
          )
      end
    in
    let rev_args =
      List.fold_left2 (
        fun acc rn arg ->
          let v, n, ty = handle_patt_var rn arg in
          (v, n, ty) :: acc
      ) [] (List.rev rev_vnames) pargs
    in
    let args = List.rev rev_args in
    Typed.Constr {name; args}

  | Cst { builtin = B.Constructor _; path; _ } ->
    let name = Hstring.make (get_basename path) in
    let args = [] in
    Typed.Constr {name; args}

  | Var ({ builtin = B.Base; path; _ } as t_v) ->
    (* Should the type be passed as an argument
       instead of re-evaluating it here? *)
    let v = Var.of_string (get_basename path) in
    let sy = Sy.var v in
    Cache.store_sy (DE.Term.Var.hash t_v) sy;
    (* Adding the matched variable to the store *)
    Typed.Var v

  | _ -> assert false

(** Makes an upper or lower interval bound of a given variable or constant *)
let mk_bound (DE.{ term_descr; term_ty; _ } as term) is_open is_lower =
  let kind =
    match term_descr with
    | Cst { builtin = B.Integer s; _ } ->
      Sy.ValBnd (Numbers.Q.from_string s)
    | Cst { builtin = B.Base; path; _ }
    | Var { path;  _ } ->
      Sy.VarBnd (Var.of_string (get_basename path))
    | _ -> failwith (
        Format.asprintf
          "Expected bound to be either an integer constant or variable but\
           got: %a"
          DE.Term.print term
      )
  in
  let sort = dty_to_ty term_ty in
  Sy.mk_bound kind sort ~is_open ~is_lower

(* Helper functions *)

let mk_lt translate ty x y =
  if ty == `Int then
    let e3 =
      E.mk_term (Sy.Op Sy.Minus) [translate y; E.int "1"] Ty.Tint
    in
    let e1 = translate x in
    E.mk_builtin ~is_pos:true Sy.LE [e1; e3]
  else
    E.mk_builtin ~is_pos:true Sy.LT [translate x; translate y]

let mk_gt translate ty x y =
  if ty == `Int then
    let e3 =
      E.mk_term (Sy.Op Sy.Minus) [translate x; E.int "1"] Ty.Tint
    in
    let e2 = translate y in
    E.mk_builtin ~is_pos:true Sy.LE [e2; e3]
  else
    E.mk_builtin ~is_pos:true Sy.LT [translate y; translate x]

let mk_add translate sy ty l =
  let rec aux_mk_add l =
    match l with
    | h :: t ->
      let args = aux_mk_add t in
      let e = translate h in
      E.concat_chainable sy ty e args
    | [] -> []
  in
  let args = aux_mk_add l in
  E.mk_term sy (List.fast_sort E.compare args) ty

(** [mk_expr ~loc ~name_base ~toplevel ~decl_kind term]

    Builds an Alt-Ergo hashconsed expression from a dolmen term
*)
let rec mk_expr ?(loc = Loc.dummy) ?(name_base = "")
    ?(toplevel = false) ~decl_kind dt =
  let name_tag = ref 0 in
  let rec aux_mk_expr ?(toplevel = false)
      (DE.{ term_descr; term_ty; term_tags = root_tags; _ } as term) =
    let res =
      match term_descr with
      | Cst ({ builtin; path; _ } as tcst) ->
        begin match builtin with
          | B.True -> E.vrai
          | B.False -> E.faux
          | B.Integer s -> E.int s
          | B.Decimal s -> E.real s
          | B.Bitvec s ->
            let ty = dty_to_ty term_ty in
            E.bitv s ty

          | B.Base ->
            let sy = Cache.find_sy (DE.Term.Const.hash tcst) in
            let ty = dty_to_ty term_ty in
            E.mk_term sy [] ty

          | B.Constructor _ ->
            let name = get_basename path in
            let ty = dty_to_ty term_ty in
            let sy = Sy.Op (Sy.Constr (Hstring.make name)) in
            E.mk_term sy [] ty

          | _ -> failwith (
              Format.asprintf "Unsupported constant term %a" DE.Term.print term
            )
        end

      | Var ({ id_ty; _ } as ty_v) ->
        let ty = dty_to_ty id_ty in
        let sy = Cache.find_sy (DE.Term.Var.hash ty_v) in
        E.mk_term sy [] ty

      | App (
          { term_descr = Cst ({
                builtin;
                path; _
              } as tcst); _
          } as app_term, _, args
        ) ->
        begin match builtin, args with
          (* Unary applications *)

          | B.Neg, [x] ->
            E.neg (aux_mk_expr x)

          | B.Minus mty, [x] ->
            let e1, ty =
              if mty == `Int then E.int "0", Ty.Tint else E.real "0",Ty.Treal
            in
            E.mk_term (Sy.Op Sy.Minus) [e1; aux_mk_expr x] ty

          | B.Bitv_extract { i; j; n }, [x] ->
            let q = E.int (Int.to_string i) in
            let p = E.int (Int.to_string j) in
            E.mk_term (Sy.Op Sy.Extract) [aux_mk_expr x; p; q] (Ty.Tbitv n)

          | B.Destructor { case; field; adt; _ }, [x] ->
            begin match DT.definition adt with
              | Some (Adt { cases; record; _ }) ->
                begin match cases.(case).dstrs.(field) with
                  | Some { path; _ } ->
                    let name = get_basename path in
                    let ty = dty_to_ty term_ty in
                    let e = aux_mk_expr x in
                    let sy =
                      if record || Array.length cases = 1
                      then
                        Sy.Op (Sy.Access (Hstring.make name))
                      else
                        Sy.destruct ~guarded:true name
                    in
                    E.mk_term sy [e] ty
                  | _ -> failwith (
                      Format.asprintf
                        "Adt Destructor error: Can't find %dth field of %dth \
                         case of the type %a."
                        field case DE.Ty.Const.print adt
                    )
                end
              | None | Some Abstract -> failwith (
                  Format.asprintf
                    "Can't find the adt %a to which the destructor %a belongs"
                    DE.Ty.Const.print adt DE.Term.print app_term
                )
            end

          | B.Tester {
              cstr = { builtin = B.Constructor _; path; _ }; _
            }, [x] ->
            let name = get_basename path in
            let builtin = Sy.IsConstr (Hstring.make name) in
            E.mk_builtin ~is_pos:true builtin [aux_mk_expr x]

          (* Binary applications *)

          | B.Bitv_concat { n; m; }, [ x; y ] ->
            let rty = Ty.Tbitv (n+m) in
            E.mk_term (Sy.Op Sy.Concat) [aux_mk_expr x; aux_mk_expr y] rty

          | B.Select, [ x; y ] ->
            let rty = dty_to_ty term_ty in
            E.mk_term (Sy.Op Sy.Get) [aux_mk_expr x; aux_mk_expr y] rty

          | B.Maps_to, [ x; y ] ->
            begin match x.term_descr with
              | Var t_v ->
                begin match Cache.find_sy (DE.Term.Var.hash t_v) with
                  | Sy.Var v ->
                    let rty = dty_to_ty term_ty in
                    let sy = Sy.mk_maps_to v in
                    let e2 = aux_mk_expr y in
                    assert (rty == Ty.Tbool);
                    E.mk_term sy [e2] rty
                  | sym -> failwith (
                      Format.asprintf
                        "Cache error: Expected to find a variable symbol\
                         associated to (%a), instead found (%a)"
                        DE.Term.print x Sy.print sym
                    )
                end
              | _ -> failwith (
                  Format.asprintf
                    "Maps_to: expected a variable but got: %a"
                    DE.Term.print x
                )
            end

          (* Ternary applications *)

          | B.Ite, [ x; y; z ] ->
            let e1 = aux_mk_expr x in
            let e2 = aux_mk_expr y in
            let e3 = aux_mk_expr z in
            E.mk_ite e1 e2 e3 0

          | B.Store, [ x; y; z ] ->
            let ty = dty_to_ty term_ty in
            let e1 = aux_mk_expr x in
            let e2 = aux_mk_expr y in
            let e3 = aux_mk_expr z in
            E.mk_term (Sy.Op Sy.Set) [e1; e2; e3] ty

          | B.In_interval (b1, b2), [ x; y; z ] ->
            let ty = dty_to_ty term_ty in
            let e1 = aux_mk_expr x in
            let lb_sy = mk_bound y b1 true in
            let ub_sy = mk_bound z b2 false in
            let sy = Sy.mk_in lb_sy ub_sy in
            assert (ty == Ty.Tbool);
            E.mk_term sy [e1] ty

          (* N-ary applications *)

          | B.Base, _ ->
            let ty = dty_to_ty term_ty in
            let sy = Cache.find_sy (DE.Term.Const.hash tcst) in
            let l = List.map (fun t -> aux_mk_expr t) args in
            Fpa_rounding.make_adequate_app sy l ty

          | B.And, h :: (_ :: _ as t) ->
            List.fold_left (
              fun acc x ->
                E.mk_and acc (aux_mk_expr x) false 0
            ) (aux_mk_expr h) t

          | B.Or, h :: (_ :: _ as t) ->
            List.fold_left (
              fun acc x ->
                E.mk_or acc (aux_mk_expr x) false 0
            ) (aux_mk_expr h) t

          | B.Xor, h :: (_ :: _ as t) ->
            List.fold_left (
              fun acc x ->
                E.mk_xor acc (aux_mk_expr x) 0
            ) (aux_mk_expr h) t

          | B.Imply, _ ->
            begin match List.rev_map aux_mk_expr args with
              | h :: t ->
                List.fold_left (
                  fun acc x ->
                    E.mk_imp x acc 0
                ) h t
              | _ -> assert false
            end

          | B.Equiv, h :: (_ :: _ as t) ->
            List.fold_left (
              fun acc x ->
                E.mk_iff acc (aux_mk_expr x) 0
            ) (aux_mk_expr h) t

          | B.Lt ty, h1 :: h2 :: t ->
            let (res, _) =
              List.fold_left (
                fun (acc, curr) next ->
                  E.mk_and acc
                    (mk_lt aux_mk_expr ty curr next) false 0,
                  next
              ) (mk_lt aux_mk_expr ty h1 h2, h2) t
            in res

          | B.Gt ty, h1 :: h2 :: t ->
            let (res, _) =
              List.fold_left (
                fun (acc, curr) next ->
                  E.mk_and acc
                    (mk_gt aux_mk_expr ty curr next) false 0,
                  next
              ) (mk_gt aux_mk_expr ty h1 h2, h2) t
            in res

          | B.Leq _, h1 :: h2 :: t ->
            let (res, _) =
              List.fold_left (
                fun (acc, curr) next ->
                  E.mk_and acc (
                    E.mk_builtin ~is_pos:true Sy.LE
                      [aux_mk_expr curr; aux_mk_expr next]
                  ) false 0,
                  next
              ) (
                E.mk_builtin ~is_pos:true Sy.LE
                  [aux_mk_expr h1; aux_mk_expr h2],
                h2
              ) t
            in res

          | B.Geq _, h1 :: h2 :: t ->
            let (res, _) =
              List.fold_left (
                fun (acc, curr) next ->
                  E.mk_and acc (
                    E.mk_builtin ~is_pos:true Sy.LE
                      [aux_mk_expr next; aux_mk_expr curr]
                  ) false 0,
                  next
              ) (
                E.mk_builtin ~is_pos:true Sy.LE
                  [aux_mk_expr h2; aux_mk_expr h1],
                h2
              ) t
            in res

          | B.Add ty, _ ->
            let rty = if ty == `Int then Ty.Tint else Treal in
            let sy = Sy.Op Sy.Plus in
            mk_add aux_mk_expr sy rty args

          | B.Sub ty, h :: t ->
            let rty = if ty == `Int then Ty.Tint else Treal in
            let sy = Sy.Op Sy.Minus in
            let args = List.rev_map aux_mk_expr (List.rev t) in
            List.fold_left
              (fun x y -> E.mk_term sy [x; y] rty) (aux_mk_expr h) args

          | B.Mul ty, h :: t ->
            let rty = if ty == `Int then Ty.Tint else Treal in
            let sy = Sy.Op Sy.Mult in
            let args = List.rev_map aux_mk_expr (List.rev t) in
            List.fold_left
              (fun x y -> E.mk_term sy [x; y] rty) (aux_mk_expr h) args

          | (B.Div _ | B.Div_e (`Real | `Rat)), h :: t ->
            let sy = Sy.Op Sy.Div in
            let args = List.rev_map aux_mk_expr (List.rev t) in
            List.fold_left
              (fun x y -> E.mk_term sy [x; y] Ty.Treal) (aux_mk_expr h) args

          | B.Div_e `Int, h :: t ->
            let sy = Sy.Op Sy.Div in
            let args = List.rev_map aux_mk_expr (List.rev t) in
            List.fold_left
              (fun x y -> E.mk_term sy [x; y] Ty.Tint) (aux_mk_expr h) args

          | B.Modulo_e ty, h :: t ->
            let rty = if ty == `Int then Ty.Tint else Treal in
            let sy = Sy.Op Sy.Modulo in
            let args = List.rev_map aux_mk_expr (List.rev t) in
            List.fold_left
              (fun x y -> E.mk_term sy [x; y] rty) (aux_mk_expr h) args

          | B.Pow ty, h :: t ->
            let rty = if ty == `Int then Ty.Tint else Treal in
            let sy = Sy.Op Sy.Pow in
            let args = List.rev_map aux_mk_expr (List.rev t) in
            List.fold_left
              (fun x y -> E.mk_term sy [x; y] rty) (aux_mk_expr h) args

          | B.Equal, h1 :: h2 :: t ->
            begin match h1.term_ty.ty_descr with
              | TyApp ({builtin = B.Prop; _ }, _) ->
                let (res, _) =
                  List.fold_left (
                    fun (acc, curr) next ->
                      E.mk_and acc (
                        let e1 = aux_mk_expr curr in
                        let e2 = aux_mk_expr next in
                        E.mk_iff e1 e2 0
                      ) false 0,
                      next
                  ) (
                    let e1 = aux_mk_expr h1 in
                    let e2 = aux_mk_expr h2 in
                    E.mk_iff e1 e2 0,
                    h2
                  ) t
                in res
              | _ ->
                let (res, _) =
                  List.fold_left (
                    fun (acc, curr) next ->
                      E.mk_and acc (
                        E.mk_eq
                          ~iff:false (aux_mk_expr curr) (aux_mk_expr next)
                      ) false 0,
                      next
                  ) (
                    E.mk_eq ~iff:false (aux_mk_expr h1) (aux_mk_expr h2),
                    h2
                  ) t
                in res
            end

          | B.Distinct, _ ->
            E.mk_distinct ~iff:true (List.map (fun t -> aux_mk_expr t) args)

          | B.Constructor _, _ ->
            let name = get_basename path in
            let ty = dty_to_ty term_ty in
            begin match ty with
              | Ty.Tadt (_, _) ->
                let sy = Sy.Op (Sy.Constr (Hstring.make name)) in
                let l = List.map (fun t -> aux_mk_expr t) args in
                E.mk_term sy l ty
              | Ty.Trecord _ ->
                let l = List.map (fun t -> aux_mk_expr t) args in
                E.mk_term (Sy.Op Sy.Record) l ty
              | _ -> failwith (
                  Format.asprintf
                    "Constructor error: %a does not belong to a record nor an\
                     algebraic data type"
                    DE.Term.print app_term
                )
            end

          | _, _ -> failwith (
              Format.asprintf "Unsupported Application Term %a"
                DE.Term.print term
            )
        end

      | Match (t, pats) ->
        let e = aux_mk_expr t in
        let pats =
          List.rev_map (
            fun (p, t) ->
              let patt = mk_pattern p in
              let e = aux_mk_expr t in
              patt, e
          ) (List.rev pats)
        in
        E.mk_match e pats

      | Binder ((Let_par ls | Let_seq ls) as let_binder, body) ->
        let lsbis =
          List.map (
            fun ({ DE.path; _ } as tv, t) ->
              let name = get_basename path in
              let sy = Symbols.var @@ Var.of_string name in
              Cache.store_sy (DE.Term.Var.hash tv) sy;
              sy,t
          ) ls
        in
        let binders =
          List.rev_map (
            fun (sy, t) ->
              (sy, aux_mk_expr t)
          ) (
            match let_binder with
            | Let_par _ ->
              List.rev lsbis
            | Let_seq _ -> lsbis
            | _ -> assert false
          )
        in
        let body = aux_mk_expr body in
        List.fold_left (
          fun acc (sy, e) ->
            E.mk_let sy e acc 0
            [@ocaml.ppwarning "TODO: should introduce fresh vars"]
        ) body binders

      | Binder ((Forall (tyvl, tvl) | Exists (tyvl, tvl)) as e, body) ->
        if tvl == []
        then (Cache.store_tyvl tyvl; aux_mk_expr ~toplevel body)
        else
          let name =
            if !name_tag = 0 then name_base
            else Format.sprintf "#%s#sub-%d" name_base !name_tag
          in
          incr name_tag;
          if tyvl != [] then Cache.store_tyvl tyvl;

          (* the following is done in two iterations to preserve the order *)
          (* quantified variables *)
          let ntvl = List.rev_map (
              fun (DE.{ path; id_ty; _ } as t_v) ->
                dty_to_ty id_ty,
                Var.of_string (get_basename path),
                DE.Term.Var.hash t_v
            ) tvl
          in
          (* Set of binders *)
          let qvs =
            List.fold_left (
              fun vl (ty, v, hash) ->
                let sy = Sy.var v in
                Cache.store_sy hash sy;
                let e = E.mk_term sy [] ty in
                SE.add e vl
            ) SE.empty ntvl
          in
          let binders = E.mk_binders qvs in

          (* filters *)
          let hyp =
            begin match DStd.Tag.get root_tags DE.Tags.filters with
              | Some t -> t
              | _ -> []
            end
          in
          let hyp = List.map aux_mk_expr hyp in

          (* triggers *)
          let trgs =
            begin match DStd.Tag.get root_tags DE.Tags.triggers with
              | Some t -> t
              | _ -> []
            end
          in
          let in_theory = decl_kind == E.Dtheory in
          let f = aux_mk_expr ~toplevel body in
          let qbody = E.purify_form f in
          (*  All the triggers that are encoutered at this level are assumed
              to be user-defined. *)
          let triggers =
            List.rev_map (
              fun t ->
                make_trigger ~loc ~name_base ~decl_kind ~in_theory
                  name hyp (t, true)
            ) trgs
            (* double reverse to produce expressions with the right tags. *)
          in


          let mk = begin match e with
            | Forall _ -> E.mk_forall
            | Exists _ -> E.mk_exists
            | _ -> assert false (* unreachable *)
          end
          in
          mk name loc binders triggers qbody (-42) ~toplevel ~decl_kind

      | _ -> failwith (
          Format.asprintf "Unsupported Term %a" DE.Term.print term
        )
    in
    match DStd.Tag.get root_tags DE.Tags.named with
    | Some s ->
      let lbl = Hstring.make s in
      E.add_label lbl res;
      res
    | _ -> res
  in aux_mk_expr ~toplevel dt

and make_trigger ?(loc = Loc.dummy) ~name_base ~decl_kind
    ~(in_theory: bool) (name: string) (hyp: E.t list)
    (e, from_user: DE.term list * bool) =
  let mk_expr =
    mk_expr ~loc ~name_base ~decl_kind
  in
  let content, guard =
    match e with
    | [{
        term_descr = App ({
            term_descr = Cst { builtin = B.Base; path; _ }; _
          }, [], t1::t2::l); _
      }] when Sy.equal (Sy.name (get_basename path)) (Sy.fake_eq) ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map mk_expr trs in
      let t1' = mk_expr t1 in
      let t2' = mk_expr t2 in
      let lit = E.mk_eq ~iff:true t1' t2' in
      trs, Some lit

    | [{
        term_descr = App ({
            term_descr = Cst { builtin = B.Base; path; _ }; _
          }, [], t1::t2::l); _
      }] when Sy.equal (Sy.name (get_basename path)) (Sy.fake_neq) ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map mk_expr trs in
      let lit = E.mk_distinct ~iff:true [mk_expr t1; mk_expr t2] in
      trs, Some lit

    | [{
        term_descr = App ({
            term_descr = Cst { builtin = B.Base; path; _ }; _
          }, [], t1::t2::l); _
      }] when Sy.equal (Sy.name (get_basename path)) (Sy.fake_le) ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map mk_expr trs in
      let t1' = mk_expr t1 in
      let t2' = mk_expr t2 in
      let lit = E.mk_builtin ~is_pos:true Sy.LE [t1'; t2'] in
      trs, Some lit

    | [{
        term_descr = App ({
            term_descr = Cst { builtin = B.Base; path; _ }; _
          }, [], t1::t2::l); _
      }] when Sy.equal (Sy.name (get_basename path)) (Sy.fake_lt) ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map mk_expr trs in
      let t1' = mk_expr t1 in
      let t2' = mk_expr t2 in
      let lit = E.mk_builtin ~is_pos:true Sy.LT [t1'; t2'] in
      trs, Some lit

    | lt -> List.map mk_expr lt, None

  in
  let t_depth =
    List.fold_left (fun z t -> max z (E.depth t)) 0 content in
  (* clean trigger:
     remove useless terms in multi-triggers after inlining of lets*)
  let trigger =
    { E.content; guard; t_depth; semantic = []; (* will be set by theories *)
      hyp; from_user; }
  in
  E.clean_trigger ~in_theory name trigger


(** Preprocesses the body of a goal by:
    - removing the top-level universal quantifiers and considering their
      quantified variables as uninsterpreted symbols.
    - transforming a given formula: [a[1] -> a[2] -> ... -> a[n]] in which
      the [a[i]]s are subformulas and [->] is a logical implication, to a set of
      hypotheses [{a[1]; ...; a[n-1]}], and a goal [a[n]] whose validity is
      verified by the solver.

    Returns a list of hypotheses and the new goal body
*)
let pp_query t =
  (*  Removes top-level universal quantifiers of a goal's body, and binds
      the quantified variables to uninterpreted symbols.
  *)
  let rec elim_toplevel_forall bnot DE.({ term_descr;  _ } as t) =
    match term_descr with
    | Binder (Forall (tyvl, tvl), body) when bnot ->
      Cache.store_tyvl ~is_var:false tyvl;
      Cache.store_sy_vl_names tvl;
      elim_toplevel_forall bnot body

    | App (
        { term_descr = Cst { builtin = B.Neg; _ }; _ },
        _tyl, [x]
      ) ->
      elim_toplevel_forall (not bnot) x

    | App (
        { term_descr = Cst { builtin = B.And; _ }; _ },
        tyl, [x; y]
      ) when not bnot ->
      let e1 = elim_toplevel_forall false x in
      let e2 = elim_toplevel_forall false y in
      DE.Term.apply_cst DE.Term.Const.and_ tyl [e1; e2]

    | App (
        { term_descr = Cst { builtin = B.Or;  _ }; _ },
        tyl, [x; y]
      ) when bnot ->
      let e1 = elim_toplevel_forall true x in
      let e2 = elim_toplevel_forall true y in
      DE.Term.apply_cst DE.Term.Const.and_ tyl [e1; e2]

    | App (
        { term_descr = Cst { builtin = B.Imply; _ }; _ },
        tyl, [x; y]
      ) when bnot ->
      let e1 = elim_toplevel_forall false x in
      let e2 = elim_toplevel_forall true y in
      DE.Term.apply_cst DE.Term.Const.and_ tyl [e1; e2]

    | _ when bnot -> DE.Term.neg t
    | _ -> t
  in

  (* Extracts hypotheses from toplevel sequences of implications *)
  let rec intro_hypothesis valid_mode DE.({ term_descr; _ } as t) =
    match term_descr with
    | App (
        { term_descr = Cst { builtin = B.Imply; _ }; _ }, _, [x; y]
      ) when valid_mode ->
      let nx = elim_toplevel_forall false x in
      let axioms, goal = intro_hypothesis true y in
      nx::axioms, goal

    | Binder (Forall (tyvl, tvl), body) when valid_mode ->
      Cache.store_tyvl ~is_var:false tyvl;
      Cache.store_sy_vl_names tvl;
      intro_hypothesis true body

    | Binder (Exists (tyvl, tvl), body) when not valid_mode ->
      Cache.store_tyvl ~is_var:false tyvl;
      Cache.store_sy_vl_names tvl;
      intro_hypothesis false body

    | _ ->
      [], elim_toplevel_forall valid_mode t
  in

  intro_hypothesis true t

let make_form name_base f loc ~decl_kind =
  let ff =
    mk_expr ~loc ~name_base ~toplevel:true ~decl_kind f
  in
  assert (SM.is_empty (E.free_vars ff SM.empty));
  let ff = E.purify_form ff in
  if Ty.Svty.is_empty (E.free_type_vars ff) then ff
  else
    let id = E.id ff in
    E.mk_forall name_base loc SM.empty [] ff id ~toplevel:true ~decl_kind

let make dloc_file acc stmt =
  let rec aux acc (stmt: Typer_Pipe.typechecked Typer_Pipe.stmt) =
    match stmt with

    (* Push and Pop commands *)
    | { contents = `Pop n; loc; _ } ->
      let st_loc = dl_to_ael dloc_file loc in
      let st_decl = C.Pop n in
      C.{ st_decl; st_loc } :: acc

    | { contents = `Push n; loc; _ } ->
      let st_loc = dl_to_ael dloc_file loc in
      let st_decl = C.Push n in
      C.{ st_decl; st_loc } :: acc

    (* Goal definitions *)
    | { id = Id.{name = Simple name; _}; contents = `Goal t; loc; } ->
      let st_loc = dl_to_ael dloc_file loc in
      let _hyps, t = pp_query t in
      let rev_hyps_c =
        List.fold_left (
          fun acc t ->
            let ns = DStd.Namespace.Decl in
            let name = Ty.fresh_hypothesis_name Ty.Thm in
            let decl: Typer_Pipe.typechecked Typer_Pipe.stmt = {
              id = Id.mk ns name;
              contents = `Hyp t; loc;
            }
            in
            aux acc decl
        ) [] _hyps
      in
      let e = make_form "" t st_loc ~decl_kind:E.Dgoal in
      let st_decl = C.Query (name, e, Thm) in
      C.{st_decl; st_loc} :: List.rev_append (List.rev rev_hyps_c) acc

    (* Axiom definitions *)
    | { id = Id.{name = Simple name; _}; contents = `Hyp t; loc; } ->
      let st_loc = dl_to_ael dloc_file loc in
      let e = make_form name t st_loc ~decl_kind:E.Daxiom in
      let st_decl = C.Assume (name, e, true) in
      C.{ st_decl; st_loc } :: acc

    (* Function and premdicate definitions *)
    | { contents = `Defs defs; loc; _ } ->
      (* For a mutually recursive definition, we have to add all the function
         names in a row. *)
      List.iter (fun (def : Typer_Pipe.def) ->
          match def with
          | `Term_def (_, ({ path; _ } as tcst), _, _, _) ->
            let name_base = get_basename path in
            let sy = Sy.name name_base in
            Cache.store_sy (DE.Term.Const.hash tcst) sy
          | _ -> ()
        ) defs;
      List.map (fun (def : Typer_Pipe.def) ->
          match def with
          | `Term_def ( _, ({ path; tags; _ } as tcst), tyvars, terml, body) ->
            Cache.store_tyvl tyvars;
            let st_loc = dl_to_ael dloc_file loc in
            let name_base = get_basename path in

            let binders_set, defn =
              let rty = dty_to_ty body.term_ty in
              let binders_set, rev_args =
                List.fold_left (
                  fun (binders_set, acc) (DE.{ path; id_ty; _ } as tv) ->
                    let ty = dty_to_ty id_ty in
                    let sy = Sy.var (Var.of_string (get_basename path)) in
                    Cache.store_sy (DE.Term.Var.hash tv) sy;
                    let e = E.mk_term sy [] ty in
                    SE.add e binders_set, e :: acc
                ) (SE.empty, []) terml
              in
              let sy = Cache.find_sy (DE.Term.Const.hash tcst) in
              let e = E.mk_term sy (List.rev rev_args) rty in
              binders_set, e
            in

            let loc = st_loc in

            begin match DStd.Tag.get tags DE.Tags.predicate with
              | Some () ->
                let decl_kind = E.Dpredicate defn in
                let ff =
                  mk_expr ~loc ~name_base
                    ~toplevel:false ~decl_kind body
                in
                let qb = E.mk_eq ~iff:true defn ff in
                let binders = E.mk_binders binders_set in
                let ff =
                  E.mk_forall name_base Loc.dummy binders [] qb (-42)
                    ~toplevel:true ~decl_kind
                in
                assert (Sy.Map.is_empty (E.free_vars ff Sy.Map.empty));
                let ff = E.purify_form ff in
                let e =
                  if Ty.Svty.is_empty (E.free_type_vars ff) then ff
                  else
                    let id = E.id ff in
                    E.mk_forall name_base loc
                      Symbols.Map.empty [] ff id ~toplevel:true ~decl_kind
                in
                C.{ st_decl = C.PredDef (e, name_base); st_loc }
              | None ->
                let decl_kind = E.Dfunction defn in
                let ff =
                  mk_expr ~loc ~name_base
                    ~toplevel:false ~decl_kind body
                in
                let qb = E.mk_eq ~iff:false defn ff in
                let binders = E.mk_binders binders_set in
                let ff =
                  E.mk_forall name_base Loc.dummy binders [] qb (-42)
                    ~toplevel:true ~decl_kind
                in
                assert (Sy.Map.is_empty (E.free_vars ff Sy.Map.empty));
                let ff = E.purify_form ff in
                let e =
                  if Ty.Svty.is_empty (E.free_type_vars ff) then ff
                  else
                    let id = E.id ff in
                    E.mk_forall name_base loc
                      Symbols.Map.empty [] ff id ~toplevel:true ~decl_kind
                in
                C.{ st_decl = C.Assume (name_base, e, true); st_loc }
            end
          | _ -> assert false
        ) defs |> List.rev_append acc

    | {contents = `Decls [td]; _ } ->
      begin match td with
        | `Type_decl td -> mk_ty_decl td
        | `Term_decl td -> mk_term_decl td
      end;
      acc

    | {contents = `Decls dcl; _ } ->
      let rec aux acc tdl =
        (* for now, when acc has more than one element it is assumed that the
           types are mutually recursive. Which is not necessarily the case.
           But it doesn't affect the execution.
        *)
        match tdl with
        | `Term_decl td :: tl ->
          begin match acc with
            | [] -> ()
            | [otd] -> mk_ty_decl otd
            | _ -> mk_mr_ty_decls (List.rev acc)
          end;
          mk_term_decl td;
          aux [] tl

        | `Type_decl td :: tl ->
          aux (td :: acc) tl

        | [] ->
          begin match acc with
            | [] -> ()
            | [otd] -> mk_ty_decl otd
            | _ ->  mk_mr_ty_decls (List.rev acc)
          end
      in
      aux [] dcl;
      acc

    | _ -> acc
    (* TODO:
       - Separate statements that should be ignored from unsupported
         statements and throw exception or print a warning when an unsupported
         statement is encountered.
    *)
  in
  aux acc stmt

let make_list dloc_file l = List.fold_left (make dloc_file) [] l

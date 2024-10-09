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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

open D_loop

module E = Expr
module SE = E.Set

module C = Commands
module Sy = Symbols
module SM = Sy.Map

module DE = DStd.Expr
module DT = DE.Ty
module B = DStd.Builtin

let unsupported msg =
  Fmt.kstr
    (fun str -> Errors.(run_error (Unsupported_feature str)))
    msg

type id = Id : 'a DE.id -> id[@@unboxed]

module HT =
  Hashtbl.Make (struct
    type t = id

    let equal (Id id1) (Id id2) = DE.Id.equal id1 id2

    let hash (Id i)= DE.Id.hash i
  end)

(** Helper function: returns the basename of a dolmen path, since in AE
    the problems are contained in one-file (for now at least), the path is
    irrelevant and only the basename matters *)
let get_basename = function
  | DStd.Path.Local { name; }
  | Absolute { name; path = []; } -> name
  | Absolute { name; path; } ->
    Fmt.failwith
      "Expected an empty path to the basename: \"%s\" but got: [%a]."
      name (fun fmt l ->
          match l with
          | h :: t ->
            Format.fprintf fmt "%s" h;
            List.iter (Format.fprintf fmt "; %s") t
          | _ -> ()
        ) path

module Cache = struct

  let ae_sy_ht: Sy.t HT.t = HT.create 100

  let ae_ty_ht: Ty.t HT.t = HT.create 100

  let store_sy id sy =
    HT.add ae_sy_ht (Id id) sy

  let store_ty id ty =
    HT.add ae_ty_ht (Id id) ty

  let find_sy id =
    HT.find ae_sy_ht (Id id)

  let find_var ind =
    match find_sy ind with
    | Sy.Var v -> v
    | sym ->
      Fmt.failwith
        "Internal error: Expected to find a variable symbol,\
         instead found (%a)"
        Sy.print sym

  let store_var ind v =
    store_sy ind (Sy.var v)

  let find_ty id =
    HT.find ae_ty_ht (Id id)

  let fresh_ty ?(is_var = true) () =
    if is_var
    then Ty.fresh_tvar ()
    else Ty.fresh_empty_text ()

  let update_ty_store_ret ?(is_var = true) id =
    let ty = fresh_ty ~is_var () in
    store_ty id ty;
    ty

  let find_update_ty ?(is_var = true) id =
    match HT.find_opt ae_ty_ht (Id id) with
    | Some ty -> ty
    | None ->
      update_ty_store_ret ~is_var id

  let store_tyv ?(is_var = true) t_v =
    let ty = fresh_ty ~is_var () in
    store_ty t_v ty

  let store_tyvl ?(is_var = true) (tyvl: DE.ty_var list) =
    List.iter (store_tyv ~is_var) tyvl

  let store_tyv_ret ?(is_var = true) t_v =
    update_ty_store_ret ~is_var t_v

  let store_tyvl_ret ?(is_var = true) (tyvl: DE.ty_var list) =
    List.map (store_tyv_ret ~is_var) tyvl

  let store_sy_vl_names (tvl: DE.term_var list) =
    List.iter (
      fun ({ DE.path; _ } as tv) ->
        let name = get_basename path in
        store_sy tv (Sy.name name)
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

(** Builtins *)
type _ DStd.Builtin.t +=
  | Float
  | AERound of int * int
  (** Equivalent of Float for the SMT2 format. *)
  | Integer_round
  | Abs_real
  | Sqrt_real
  | Sqrt_real_default
  | Sqrt_real_excess
  | Ceiling_to_int of [ `Real ]
  | Max_real
  | Min_real
  | Max_int
  | Min_int
  | Integer_log2
  (* Internal use for semantic triggers -- do not expose outside of theories *)
  | Not_theory_constant | Is_theory_constant | Linear_dependency

let builtin_term t = Dl.Typer.T.builtin_term t

let builtin_ty t = Dl.Typer.T.builtin_ty t

let ty (ty_cst : DE.ty_cst) ty =
  let name = get_basename ty_cst.path in
  DStd.Id.Map.add { name = DStd.Name.simple name; ns = Sort } @@
  fun env s ->
  builtin_ty @@
  Dolmen_type.Base.app0 (module Dl.Typer.T) env s ty

let fpa_rounding_mode, rounding_modes, add_rounding_modes =
  match DT.view Fpa_rounding.fpa_rounding_mode_dty with
  | `App ((`Generic ty_cst), []) ->
    let constrs = Fpa_rounding.d_constrs in
    let add_constrs map =
      List.fold_left (fun map (c : DE.term_cst) ->
          let name = get_basename c.path in
          DStd.Id.Map.add { name = DStd.Name.simple name; ns = Term }
            (fun env _ ->
               builtin_term @@
               Dolmen_type.Base.term_app_cst
                 (module Dl.Typer.T) env c) map)
        map constrs
    in
    Cache.store_ty ty_cst Fpa_rounding.fpa_rounding_mode;
    Fpa_rounding.fpa_rounding_mode_dty,
    constrs,
    fun map ->
      map
      |> ty ty_cst Fpa_rounding.fpa_rounding_mode_dty
      |> add_constrs
  | _ -> assert false

module Const = struct
  open DE

  let smt_round =
    with_cache (fun (n, m) ->
        let name = "ae.round" in
        DE.Id.mk
          ~name
          ~builtin:(AERound (n, m))
          (DStd.Path.global name)
          Ty.(arrow [fpa_rounding_mode; real] real))
end

let smt_round n m rm t =
  DE.Term.apply_cst (Const.smt_round (n, m)) [] [rm; t]

(** Takes a dolmen identifier [id] and injects it in Alt-Ergo's registered
    identifiers.
    It transforms "fpa_rounding_mode", the Alt-Ergo builtin type into the SMT2
    rounding type "RoundingMode". Also injects each constructor into their SMT2
    equivalent *)
let inject_ae_to_smt2 id =
  match id with
  | DStd.Id.{name = Simple n; _} ->
    begin
      if String.equal n Fpa_rounding.fpa_rounding_mode_ae_type_name then
        (* Injecting the type name as the SMT2 Type name. *)
        let name =
          Dolmen_std.Name.simple Fpa_rounding.fpa_rounding_mode_type_name
        in
        {id with name}
      else
        match Fpa_rounding.rounding_mode_of_ae n with
        | rm ->
          let name =
            Dolmen_std.Name.simple (Fpa_rounding.string_of_rounding_mode rm)
          in
          {id with name}
        | exception (Failure _) ->
          id
    end
  | id -> id

let ae_fpa_builtins =
  let (->.) args ret = (args, ret) in
  let dterm name f =
    DStd.Id.Map.add { name = DStd.Name.simple name; ns = Term } @@
    fun env s ->
    builtin_term @@
    Dolmen_type.Base.term_app1 (module Dl.Typer.T) env s f
  in
  let op ?(tyvars = []) name builtin (args, ret) =
    let ty = DT.pi tyvars @@ DT.arrow args ret in
    let cst = DE.Id.mk ~name ~builtin (DStd.Path.global name) ty in
    DStd.Id.Map.add { name = DStd.Name.simple name; ns = Term } @@
    fun env _ ->
    builtin_term @@
    Dolmen_type.Base.term_app_cst
      (module Dl.Typer.T) env cst
  in
  let float_cst =
    let ty = DT.(arrow [int; int; fpa_rounding_mode; real] real) in
    DE.Id.mk ~name:"float" ~builtin:Float (DStd.Path.global "float") ty
  in
  let float prec exp mode x =
    DE.Term.apply_cst float_cst [] [prec; exp; mode; x]
  in
  let mode m =
    let cst =
      List.find (fun cst ->
          match cst.DE.path with
          | Absolute { name; _ } -> String.equal name m
          | Local _ -> false)
        rounding_modes
    in
    DE.Term.apply_cst cst [] []
  in
  let float32 = float (DE.Term.int "24") (DE.Term.int "149") in
  let float32d x = float32 (mode "NearestTiesToEven") x in
  let float64 = float (DE.Term.int "53") (DE.Term.int "1074") in
  let float64d x = float64 (mode "NearestTiesToEven") x in
  let partial1 name f =
    DStd.Id.Map.add { name = DStd.Name.simple name; ns = Term } @@
    fun env s ->
    builtin_term @@
    Dolmen_type.Base.term_app1 (module Dl.Typer.T) env s f
  in
  let partial2 name f =
    DStd.Id.Map.add { name = DStd.Name.simple name; ns = Term } @@
    fun env s ->
    builtin_term @@
    Dolmen_type.Base.term_app2 (module Dl.Typer.T) env s f
  in
  let is_theory_constant =
    let open DT in
    let a = Var.mk "alpha" in
    op
      ~tyvars:[a]
      "is_theory_constant"
      Is_theory_constant
      ([of_var a] ->. prop)
  in
  let fpa_builtins =
    let open DT in
    DStd.Id.Map.empty

    |> add_rounding_modes

    (* the first argument is mantissas' size (including the implicit bit),
       the second one is the exp of the min representable normalized number,
       the third one is the rounding mode, and the last one is the real to
       be rounded *)
    |> op "float" Float ([int; int; fpa_rounding_mode; real] ->. real)

    |> partial2 "float32" float32
    |> partial1 "float32d" float32d

    |> partial2 "float64" float64
    |> partial1 "float64d" float64d

    (* rounds to nearest integer *)
    |> op "integer_round" Integer_round ([fpa_rounding_mode; real] ->. int)

    (* type cast: from int to real *)
    |> dterm "real_of_int" DE.Term.Int.to_real

    (* type check: integers *)
    |> dterm "real_is_int" DE.Term.Real.is_int

    (* abs value of a real *)
    |> op "abs_real" Abs_real ([real] ->. real)

    (* sqrt value of a real *)
    |> op "sqrt_real" Sqrt_real ([real] ->. real)

    (* sqrt value of a real by default *)
    |> op "sqrt_real_default" Sqrt_real_default ([real] ->. real)

    (* sqrt value of a real by excess *)
    |> op "sqrt_real_excess" Sqrt_real_excess ([real] ->. real)

    (* abs value of an int *)
    |> dterm "abs_int" DE.Term.Int.abs

    (* (integer) floor of a rational *)
    |> dterm "int_floor" DE.Term.Real.floor_to_int

    (* (integer) ceiling of a ratoinal *)
    |> op "int_ceil" (Ceiling_to_int `Real) ([real] ->. int)

    (* The functions below are only interpreted when applied on constants.
       Aximatization for the general case are not currently imlemented *)

    (* maximum of two reals *)
    |> op "max_real" Max_real ([real; real] ->. real)

    (* minimum of two reals *)
    |> op "min_real" Min_real ([real; real] ->. real)

    (* maximum of two ints *)
    |> op "max_int" Max_int ([int; int] ->. int)

    (* minimum of two ints *)
    |> op "min_int" Min_int ([int; int] ->. int)

    (* computes an integer log2 of a real. The function is only
       interpreted on (non-zero) positive real constants. When applied on a
       real 'm', the result 'res' of the function is such that: 2^res <= m <
       2^(res+1) *)
    |> op "integer_log2" Integer_log2 ([real] ->. int)

    (* only used for arithmetic. It should not be used for x in float(x)
       to enable computations modulo equality *)

    |> op "not_theory_constant" Not_theory_constant ([real] ->. prop)
    |> is_theory_constant
    |> op "linear_dependency" Linear_dependency ([real; real] ->. prop)
  in
  fun env s ->
    let search_id id =
      try
        DStd.Id.Map.find_exn id fpa_builtins env s
      with Not_found -> `Not_found
    in
    match s with
    | Dl.Typer.T.Id id ->
      let new_id = inject_ae_to_smt2 id in
      search_id new_id
    | Builtin _ -> `Not_found

let smt_fpa_builtins =
  let term_app env s f =
    Dl.Typer.T.builtin_term @@
    Dolmen_type.Base.term_app2 (module Dl.Typer.T) env s f
  in
  let other_builtins =
    DStd.Id.Map.empty
    |> add_rounding_modes
  in
  fun env s ->
    match s with
    | Dl.Typer.T.Id {
        ns = Term ;
        name = Indexed {
            basename = "ae.round" ;
            indexes = [ i; j ] } } ->
      begin match
          int_of_string i,
          int_of_string j
        with
        | n, m -> term_app env s (smt_round n m)
        | exception Failure _ -> `Not_found
      end
    | Id { ns = Term ; name = Simple "ae.float16" } ->
      term_app env s (smt_round 11 24)
    | Id { ns = Term ; name = Simple "ae.float32" } ->
      term_app env s (smt_round 24 149)
    | Id { ns = Term ; name = Simple "ae.float64" } ->
      term_app env s (smt_round 53 1074)
    | Id { ns = Term ; name = Simple "ae.float128" } ->
      term_app env s (smt_round 113 16494)
    | Dl.Typer.T.Id id -> begin
        match DStd.Id.Map.find_exn id other_builtins env s with
        | e -> e
        | exception Not_found -> `Not_found
      end
    | _ -> `Not_found

(* Custom attribute used to name lemmas. *)
let lemma_name_attr : string DStd.Tag.t = DStd.Tag.create ()

type _ Dl.Typer.T.err +=
  | Invalid_lemma_name

let smt_tag_builtins =
  let module Type = Dl.Typer.T in
  let make_op env s f =
    Dl.Typer.T.builtin_tags @@
    Dolmen_type.Base.make_op1 (module Dl.Typer.T) env s f
  in
  fun env s ->
    match s with
    | Type.Id { ns = Attr ; name = Simple ":lemma" } ->
      make_op env s (fun ast t ->
          match t with
          | { term = Symbol { name = Simple name; _ }; _ } ->
            [Type.Set (lemma_name_attr, name)]
          | _ ->
            (* TODO: add a custom printer as soon as the issue
               https://github.com/Gbury/dolmen/issues/218 is solved. *)
            Type._error env (Ast ast) Invalid_lemma_name
        )
    | _ -> `Not_found

let builtins =
  fun _st (lang : Typer.lang) ->
  match lang with
  | `Logic Alt_ergo -> ae_fpa_builtins
  | `Logic (Smtlib2 _) ->
    (fun env s ->
       match smt_fpa_builtins env s with
       | `Not_found -> smt_tag_builtins env s
       | r -> r)
  | _ -> fun _ _ -> `Not_found

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
  | `Bitv n ->
    if n <= 0 then Errors.typing_error (NonPositiveBitvType n) Loc.dummy;
    Ty.Tbitv n

  | `App (`Builtin B.Unit, []) -> Ty.tunit
  | `App (`Builtin _, [ty]) -> aux ty
  | `App (`Generic c, l) -> handle_ty_app ~update c l

  | `Var ty_v when update ->
    Cache.find_update_ty ty_v
  | `Var ty_v ->
    Cache.find_ty ty_v

  | `Arrow (_, ty) -> aux ty
  | `Pi (tyvl, ty) ->
    if update then
      Cache.store_tyvl ~is_var tyvl;
    aux ty
  | _ -> unsupported "Type %a" DE.Ty.print dty

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
  match Cache.find_ty ty_c with
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

  | Text (_, s) -> Text (tyl, s)
  | _ -> assert false

(** Handles a simple type declaration. *)
let mk_ty_decl (ty_c: DE.ty_cst) =
  match DT.definition ty_c with
  | Some (
      (Adt
         { cases = [| { cstr = { id_ty; _ } as cstr; dstrs; _ } |]; _ } as adt)
    ) ->
    (* Records and adts that only have one case are treated in the same way,
       and considered as records. *)
    Nest.attach_orders [adt];
    let tyvl = Cache.store_ty_vars_ret id_ty in
    let lbs =
      Array.fold_right (
        fun c acc ->
          match c with
          | Some (DE.{ id_ty; _ } as id) ->
            let pty = dty_to_ty id_ty in
            (id, pty) :: acc
          | _ ->
            Fmt.failwith
              "Unexpected null label for some field of the record type %a"
              DE.Ty.Const.print ty_c

      ) dstrs []
    in
    let ty = Ty.trecord ~record_constr:cstr tyvl ty_c lbs in
    Cache.store_ty ty_c ty

  | Some (Adt { cases; _ } as adt) ->
    Nest.attach_orders [adt];
    let tyvl = Cache.store_ty_vars_ret cases.(0).cstr.id_ty in
    Cache.store_ty ty_c (Ty.t_adt ty_c tyvl);
    let cs =
      Array.fold_right (
        fun DE.{ cstr; dstrs; _ } accl ->
          let fields =
            Array.fold_right (
              fun tc_o acc ->
                match tc_o with
                | Some (DE.{ id_ty; _ } as field) ->
                  (field, dty_to_ty id_ty) :: acc
                | None -> assert false
            ) dstrs []
          in
          (cstr, fields) :: accl
      ) cases []
    in
    let ty = Ty.t_adt ~body:(Some cs) ty_c tyvl in
    Cache.store_ty ty_c ty

  | None | Some Abstract ->
    let ty_params = []
    (* List.init ty_c.id_ty.arity (fun _ -> Ty.fresh_tvar ()) *)
    in
    let ty = Ty.text ty_params ty_c in
    Cache.store_ty ty_c ty

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
  Cache.store_sy tcst sy;
  (* Adding polymorphic types to the cache. *)
  Cache.store_ty_vars id_ty;
  let arg_tys, ret_ty =
    match DT.view id_ty with
    | `Arrow (arg_tys, ret_ty) ->
      List.map dty_to_ty arg_tys, dty_to_ty ret_ty
    | _ -> [], dty_to_ty id_ty
  in
  (Hstring.make name, arg_tys, ret_ty)

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
      let lbs =
        Array.fold_right (
          fun c acc ->
            match c with
            | Some (DE.{ id_ty; _ } as id) ->
              let pty = dty_to_ty id_ty in
              (id, pty) :: acc
            | _ ->
              Fmt.failwith
                "Unexpected null label for some field of the record type %a"
                DE.Ty.Const.print ty_c
        ) dstrs []
      in
      let ty =
        Ty.trecord ~record_constr args name lbs
      in
      Cache.store_ty ty_c ty

    | Tadt (hs, tyl), Some (Adt { cases; ty = ty_c; _ }) ->
      let cs =
        Array.fold_right (
          fun DE.{ cstr; dstrs; _ } accl ->
            let fields =
              Array.fold_right (
                fun tc_o acc ->
                  match tc_o with
                  | Some (DE.{ id_ty; _ } as id) ->
                    (id, dty_to_ty id_ty) :: acc
                  | None -> assert false
              ) dstrs []
            in
            (cstr, fields) :: accl
        ) cases []
      in
      let ty = Ty.t_adt ~body:(Some cs) hs tyl in
      Cache.store_ty ty_c ty

    | _ -> assert false
  in
  (* If there are adts in the list of type declarations then records are
     converted to adts, because that's how it's done in the legacy typechecker.
     But it might be more efficient not to do that. *)
  let rev_tdefs, contains_adts =
    List.fold_left (
      fun (acc, ca) ty_c ->
        match DT.definition ty_c with
        | Some (Adt { record; cases; _ } as df)
          when not record && Array.length cases > 1 ->
          df :: acc, true
        | Some (Adt _ as df) ->
          df :: acc, ca
        | Some Abstract | None ->
          assert false
    ) ([], false) tdl
  in
  Nest.attach_orders rev_tdefs;
  let rev_l =
    List.fold_left (
      fun acc tdef ->
        match tdef with
        | DE.Adt { cases; record; ty = ty_c; } as adt ->
          let tyvl = Cache.store_ty_vars_ret cases.(0).cstr.id_ty in
          let record_constr = cases.(0).cstr in
          let ty =
            if (record || Array.length cases = 1) && not contains_adts
            then
              Ty.trecord ~record_constr tyvl ty_c []
            else
              Ty.t_adt ty_c tyvl
          in
          Cache.store_ty ty_c ty;
          (ty, Some adt) :: acc

        | Abstract ->
          assert false (* unreachable in the second iteration *)
    ) [] (List.rev rev_tdefs)
  in
  List.iter (
    fun (t, d) -> handle_ty_decl t d
  ) (List.rev rev_l)

(** Helper function hadle variables that are encoutered in patterns. *)
let handle_patt_var id (DE.{ term_descr; _ } as term)  =
  match term_descr with
  | Cst ({ builtin = B.Base; id_ty; _ } as ty_c) ->
    let ty = dty_to_ty id_ty in
    let v = Var.of_string @@ Fmt.to_to_string DE.Term.Const.print id in
    let sy = Sy.Var v in
    Cache.store_sy ty_c sy;
    v, id, ty

  | Var ({ builtin = B.Base; id_ty; _ } as ty_v) ->
    let ty = dty_to_ty id_ty in
    let v = Var.of_string @@ Fmt.to_to_string DE.Term.Const.print id in
    let sy = Sy.Var v in
    Cache.store_sy ty_v sy;
    v, id, ty

  | _ ->
    Fmt.failwith
      "Expected a variable in a case match but got %a"
      DE.Term.print term

(** Helper function to translate patterns in a pattern-matching from a Dolmen
    Term.t to an Alt-Ergo Expr.t *)
let mk_pattern DE.{ term_descr; _ } =
  match term_descr with
  | App (
      { term_descr =
          Cst ({ builtin = B.Constructor { adt; case; }; _ } as cst); _
      }, _, pargs
    ) ->
    let vnames =
      begin match DT.definition adt with
        | Some (Adt { cases; _ }) ->
          let { DE.dstrs; _ } = cases.(case) in
          Array.fold_right (
            fun v acc ->
              match v with
              | Some dstr -> dstr :: acc
              | _ -> assert false
          ) dstrs []
        | _ ->
          Fmt.failwith
            "Expected a constructor for an algebraic data type but got\
             something else for the definition of: %a"
            DE.Ty.Const.print adt
      end
    in
    let rev_args =
      List.fold_left2 (
        fun acc rn arg ->
          let v, n, ty = handle_patt_var rn arg in
          (v, n, ty) :: acc
      ) [] vnames pargs
    in
    let args = List.rev rev_args in
    Typed.Constr {name = cst; args}

  | Cst ({ builtin = B.Constructor _; _ } as cst) ->
    Typed.Constr {name = cst; args = []}

  | Var ({ builtin = B.Base; path; _ } as t_v) ->
    (* Should the type be passed as an argument
       instead of re-evaluating it here? *)
    let v = Var.of_string (get_basename path) in
    let sy = Sy.var v in
    Cache.store_sy t_v sy;
    (* Adding the matched variable to the store *)
    Typed.Var v

  | _ -> assert false

let arith_ty = function
  | `Int -> Ty.Tint
  | `Real -> Ty.Treal
  | `Rat -> unsupported "rationals"

(* Parse a semantic bound [x `b` y] and returns a tuple [(sort, lb, ub)] where:

   - One of [x] or [y] *MUST* be the variable [var]
   - [sort] is the sort of the bound ([Ty.Tint] or [Ty.Treal])
   - [lb] is the (optional) lower bound for the variable [var]
   - [ub] is the (optional) upper bound for the variable [var]
*)
let parse_semantic_bound ?(loc = Loc.dummy) ~var b x y =
  let is_main_var { DE.term_descr; _ } =
    match term_descr with
    | DE.Var v -> DE.Id.equal v var
    | _ -> false
  in
  assert (is_main_var x || is_main_var y);
  let op, t =
    match b with
    | B.Lt t -> `Lt, t
    | B.Leq t -> `Le, t
    | B.Gt t -> `Gt, t
    | B.Geq t -> `Ge, t
    | _ ->
      Fmt.failwith
        "%aInternal error: invalid semantic bound"
        Loc.report loc
  in
  let sort = arith_ty t in
  let parse_bound_kind { DE.term_descr; _ } =
    match term_descr with
    | Cst { builtin = (B.Integer s | B.Rational s | B.Decimal s); _ } ->
      Sy.ValBnd (Numbers.Q.from_string s)
    | Var v -> Sy.VarBnd (Cache.find_var v)
    | _ ->
      Fmt.failwith
        "%aInternal error: invalid semantic bound"
        Loc.report loc
  in
  (* Parse [main_var `op` b] *)
  let parse_bound ?(flip = false) b =
    let b = parse_bound_kind b in
    let is_open =
      match op with
      | `Lt | `Gt -> true
      | `Le | `Ge -> false
    and is_lower =
      match op with
      | `Lt | `Le -> flip
      | `Gt | `Ge -> not flip
    in
    Sy.mk_bound b sort ~is_open ~is_lower
  in
  let bnd =
    if is_main_var x then
      parse_bound y
    else
      parse_bound ~flip:true x
  in
  if bnd.is_lower then sort, Some bnd, None else sort, None, Some bnd

let destruct_let e =
  match e.DE.term_descr with
  | Binder (Let_seq ls, body) ->
    Some (ls, body)
  | _ -> None

let destruct_app e =
  match e.DE.term_descr with
  | App ({ term_descr = Cst cst; _ }, _, args) ->
    Some (cst.builtin, args)
  | _ -> None

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
      translate h :: args
    | [] -> []
  in
  let args = aux_mk_add l in
  E.mk_term sy args ty

let mk_rounding fpar =
  let tcst = Fpa_rounding.term_cst_of_rounding_mode fpar in
  let ty = Fpa_rounding.fpa_rounding_mode in
  E.mk_constr tcst [] ty

(** [mk_expr ~loc ~name_base ~toplevel ~decl_kind term]

    Builds an Alt-Ergo hashconsed expression from a dolmen term
*)
let rec mk_expr
    ?(loc = Loc.dummy) ?(name_base = "") ?(toplevel = false)
    ~decl_kind dt =
  let name_tag = ref 0 in
  let rec aux_mk_expr ?(toplevel = false)
      (DE.{ term_descr; term_ty; term_tags = root_tags; _ } as term) =
    let mk = aux_mk_expr in
    let res =
      match term_descr with
      | Cst ({ builtin; _ } as tcst) ->
        begin match builtin with
          | B.True -> E.vrai
          | B.False -> E.faux
          | B.Integer s -> E.int s
          | B.Decimal s -> E.real s
          | B.Bitvec s ->
            let ty = dty_to_ty term_ty in
            E.bitv s ty

          | B.Base ->
            let sy = Cache.find_sy tcst in
            let ty = dty_to_ty term_ty in
            E.mk_term sy [] ty

          | B.Constructor _ ->
            begin match dty_to_ty term_ty with
              | Trecord _ as ty ->
                E.mk_record [] ty
              | Tadt _ as ty ->
                E.mk_constr tcst [] ty
              | ty ->
                Fmt.failwith "unexpected type %a@." Ty.print ty
            end

          | _ -> unsupported "Constant term %a" DE.Term.print term
        end

      | Var ({ id_ty; _ } as ty_v) ->
        let ty = dty_to_ty id_ty in
        let sy = Cache.find_sy ty_v in
        E.mk_term sy [] ty

      | App (
          { term_descr = Cst ({
                builtin; _
              } as tcst); _
          } as app_term, _, args
        ) ->
        let op op =
          E.mk_term (Sy.Op op) (List.map (fun a -> aux_mk_expr a) args)
            (dty_to_ty term_ty)
        in
        begin match builtin, args with
          (* Unary applications *)

          | B.Neg, [x] ->
            E.neg (aux_mk_expr x)

          | B.Minus mty, [x] ->
            let e1, ty =
              if mty == `Int then E.int "0", Ty.Tint else E.real "0",Ty.Treal
            in
            E.mk_term (Sy.Op Sy.Minus) [e1; aux_mk_expr x] ty

          | B.Destructor { case; field; adt; _ }, [x] ->
            begin match DT.definition adt with
              | Some (Adt { cases;  _ }) ->
                begin match cases.(case).dstrs.(field) with
                  | Some destr ->
                    let ty = dty_to_ty term_ty in
                    let e = aux_mk_expr x in
                    let sy =
                      match Cache.find_ty adt with
                      | Trecord _ ->
                        Sy.Op (Sy.Access destr)
                      | Tadt _ ->
                        Sy.destruct destr
                      | _ -> assert false
                    in
                    E.mk_term sy [e] ty
                  | _ ->
                    Fmt.failwith
                      "Adt Destructor error: Can't find %dth field of %dth \
                       case of the type %a."
                      field case DE.Ty.Const.print adt
                end
              | None | Some Abstract ->
                Fmt.failwith
                  "Can't find the adt %a to which the destructor %a belongs"
                  DE.Ty.Const.print adt DE.Term.print app_term
            end

          | B.Tester {
              cstr = { builtin = B.Constructor { adt; _ }; _ } as cstr; _
            }, [x] ->
            begin
              let ty_c =
                match DT.definition adt with
                | Some (
                    Adt { ty = ty_c; _ }
                  ) -> ty_c
                | _ -> assert false
              in
              match Cache.find_ty ty_c with
              | Ty.Tadt _ ->
                E.mk_tester cstr (aux_mk_expr x)

              | Ty.Trecord _ ->
                (* The typechecker allows only testers whose the
                   two arguments have the same type. Thus, we can always
                   replace the tester of a record by the true literal. *)
                E.vrai
              | _ -> assert false
            end

          | B.Semantic_trigger, [trigger] ->
            (* Interval triggers contain a let-bound variable that represent the
               "main" term of the interval. For instance, [e in [i, ?]]
               becomes `semantic_trigger (let x = e in i ≤ x)`.
            *)
            let xs, trigger =
              Option.value ~default:([], trigger) @@ destruct_let trigger
            in
            let var =
              match xs with
              | [] -> None
              | [ var, value ] -> Some (var, value)
              | _ ->
                Fmt.failwith
                  "%asemantic trigger should have at most one bound variable"
                  Loc.report loc
            in
            semantic_trigger ~loc ?var trigger

          (* Unary functions from FixedSizeBitVectors theory *)
          | B.Bitv_extract { i; j; _ }, [ x ] -> E.BV.extract i j (mk x)
          | B.Bitv_not _, [ x ] -> E.BV.bvnot (mk x)
          | B.Bitv_neg _, [ x ] -> E.BV.bvneg (mk x)

          (* Unary functions from QF_BV logic *)
          | B.Bitv_repeat { k; _ }, [ x ] -> E.BV.repeat k (mk x)
          | B.Bitv_zero_extend { k; _ }, [ x ] -> E.BV.zero_extend k (mk x)
          | B.Bitv_sign_extend { k; _ }, [ x ] -> E.BV.sign_extend k (mk x)
          | B.Bitv_rotate_left { i; _ }, [ x ] -> E.BV.rotate_left i (mk x)
          | B.Bitv_rotate_right { i; _ }, [ x ] -> E.BV.rotate_right i (mk x)

          (* Binary applications *)

          | B.Select, [ x; y ] ->
            let rty = dty_to_ty term_ty in
            E.mk_term (Sy.Op Sy.Get) [aux_mk_expr x; aux_mk_expr y] rty

          (* Binary functions from FixedSizeBitVectors theory *)
          | B.Bitv_concat _, [ x; y ] -> E.BV.concat (mk x) (mk y)
          | B.Bitv_and _, [ x; y ] -> E.BV.bvand (mk x) (mk y)
          | B.Bitv_or _, [ x; y ] -> E.BV.bvor (mk x) (mk y)
          | B.Bitv_add _, [ x; y ] -> E.BV.bvadd (mk x) (mk y)
          | B.Bitv_mul _, [ x; y ] -> E.BV.bvmul (mk x) (mk y)
          | B.Bitv_udiv _, [ x; y ] -> E.BV.bvudiv (mk x) (mk y)
          | B.Bitv_urem _, [ x; y ] -> E.BV.bvurem (mk x) (mk y)
          | B.Bitv_shl _, [ x; y ] -> E.BV.bvshl (mk x) (mk y)
          | B.Bitv_lshr _, [ x; y ] -> E.BV.bvlshr (mk x) (mk y)
          | B.Bitv_ult _, [ x; y ] -> E.BV.bvult (mk x) (mk y)

          (* Binary functions from QF_BV logic *)
          | B.Bitv_nand _, [ x; y ] -> E.BV.bvnand (mk x) (mk y)
          | B.Bitv_nor _, [ x; y ] -> E.BV.bvnor (mk x) (mk y)
          | B.Bitv_xor _, [ x; y ] -> E.BV.bvxor (mk x) (mk y)
          | B.Bitv_xnor _, [ x; y ] -> E.BV.bvxnor (mk x) (mk y)
          | B.Bitv_comp _, [ x; y ] -> E.BV.bvcomp (mk x) (mk y)
          | B.Bitv_sub _, [ x; y ] -> E.BV.bvsub (mk x) (mk y)
          | B.Bitv_sdiv _, [ x; y ] -> E.BV.bvsdiv (mk x) (mk y)
          | B.Bitv_srem _, [ x; y ] -> E.BV.bvsrem (mk x) (mk y)
          | B.Bitv_smod _, [ x; y ] -> E.BV.bvsmod (mk x) (mk y)
          | B.Bitv_ashr _, [ x; y ] -> E.BV.bvashr (mk x) (mk y)

          | B.Bitv_ule _, [ x; y ] -> E.BV.bvule (mk x) (mk y)
          | B.Bitv_ugt _, [ x; y ] -> E.BV.bvugt (mk x) (mk y)
          | B.Bitv_uge _, [ x; y ] -> E.BV.bvuge (mk x) (mk y)
          | B.Bitv_slt _, [ x; y ] -> E.BV.bvslt (mk x) (mk y)
          | B.Bitv_sle _, [ x; y ] -> E.BV.bvsle (mk x) (mk y)
          | B.Bitv_sgt _, [ x; y ] -> E.BV.bvsgt (mk x) (mk y)
          | B.Bitv_sge _, [ x; y ] -> E.BV.bvsge (mk x) (mk y)

          (* Ternary applications *)

          | B.Ite, [ x; y; z ] ->
            let e1 = aux_mk_expr x in
            let e2 = aux_mk_expr y in
            let e3 = aux_mk_expr z in
            E.mk_ite e1 e2 e3

          | B.Store, [ x; y; z ] ->
            let ty = dty_to_ty term_ty in
            let e1 = aux_mk_expr x in
            let e2 = aux_mk_expr y in
            let e3 = aux_mk_expr z in
            E.mk_term (Sy.Op Sy.Set) [e1; e2; e3] ty

          (* N-ary applications *)

          | B.Base, _ ->
            let ty = dty_to_ty term_ty in
            let sy = Cache.find_sy tcst in
            let l = List.map (fun t -> aux_mk_expr t) args in
            E.mk_term sy l ty

          | B.And, h :: (_ :: _ as t) ->
            List.fold_left (
              fun acc x ->
                E.mk_and acc (aux_mk_expr x) false
            ) (aux_mk_expr h) t

          | B.Or, h :: (_ :: _ as t) ->
            List.fold_left (
              fun acc x ->
                E.mk_or acc (aux_mk_expr x) false
            ) (aux_mk_expr h) t

          | B.Xor, h :: (_ :: _ as t) ->
            List.fold_left (
              fun acc x ->
                E.mk_xor acc (aux_mk_expr x)
            ) (aux_mk_expr h) t

          | B.Imply, _ ->
            begin match List.rev_map aux_mk_expr args with
              | h :: t ->
                List.fold_left (
                  fun acc x ->
                    E.mk_imp x acc
                ) h t
              | _ -> assert false
            end

          | B.Equiv, h :: (_ :: _ as t) ->
            List.fold_left (
              fun acc x ->
                E.mk_iff acc (aux_mk_expr x)
            ) (aux_mk_expr h) t

          | B.Lt ty, h1 :: h2 :: t ->
            let (res, _) =
              List.fold_left (
                fun (acc, curr) next ->
                  E.mk_and acc
                    (mk_lt aux_mk_expr ty curr next) false,
                  next
              ) (mk_lt aux_mk_expr ty h1 h2, h2) t
            in res

          | B.Gt ty, h1 :: h2 :: t ->
            let (res, _) =
              List.fold_left (
                fun (acc, curr) next ->
                  E.mk_and acc
                    (mk_gt aux_mk_expr ty curr next) false,
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
                  ) false,
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
                  ) false,
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
                        E.mk_iff e1 e2
                      ) false,
                      next
                  ) (
                    let e1 = aux_mk_expr h1 in
                    let e2 = aux_mk_expr h2 in
                    E.mk_iff e1 e2,
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
                      ) false,
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
            let ty = dty_to_ty term_ty in
            begin match ty with
              | Ty.Tadt _ ->
                let l = List.map (fun t -> aux_mk_expr t) args in
                E.mk_constr tcst l ty
              | Ty.Trecord _ ->
                let l = List.map (fun t -> aux_mk_expr t) args in
                E.mk_record l ty
              | _ ->
                Fmt.failwith
                  "Constructor error: %a does not belong to a record nor an\
                   algebraic data type"
                  DE.Term.print app_term
            end

          | B.Coercion, [ x ] ->
            begin match DT.view (DE.Term.ty x), DT.view term_ty with
              | `Int, `Real -> op Real_of_int
              | _ -> unsupported "coercion: %a" DE.Term.print term
            end
          | Float, _ -> op Float
          | AERound(i, j), _ ->
            let args =
              let i = E.Ints.of_int i in
              let j = E.Ints.of_int j in
              i :: j :: List.map (fun a -> aux_mk_expr a) args in
            E.mk_term
              (Sy.Op Float)
              args
              (dty_to_ty term_ty)
          | Integer_round, _ -> op Integer_round
          | Abs_real, _ -> op Abs_real
          | Sqrt_real, _ -> op Sqrt_real
          | B.Bitv_of_int { n }, _ -> op (Int2BV n)
          | B.Bitv_to_nat { n = _ }, _ -> op BV2Nat
          | Sqrt_real_default, _ -> op Sqrt_real_default
          | Sqrt_real_excess, _ -> op Sqrt_real_excess
          | B.Abs, _ -> op Abs_int
          | B.Floor_to_int `Real, _ -> op Int_floor
          | B.Is_int `Real, _ -> op Real_is_int
          | Ceiling_to_int `Real, _ -> op Int_ceil
          | Max_real, _ -> op Max_real
          | Min_real, _ -> op Min_real
          | Max_int, _ -> op Max_int
          | Min_int, _ -> op Min_int
          | Integer_log2, _ -> op Integer_log2
          | Not_theory_constant, _ -> op Not_theory_constant
          | Is_theory_constant, _ -> op Is_theory_constant
          | Linear_dependency, _ -> op Linear_dependency
          | B.RoundNearestTiesToEven, _ -> mk_rounding NearestTiesToEven
          | B.RoundNearestTiesToAway, _ -> mk_rounding NearestTiesToAway
          | B.RoundTowardPositive, _ -> mk_rounding Up
          | B.RoundTowardNegative, _ -> mk_rounding Down
          | B.RoundTowardZero, _ -> mk_rounding ToZero
          | _, _ -> unsupported "Application Term %a" DE.Term.print term
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
              let v = Var.of_string name in
              Cache.store_sy tv (Sy.var v);
              v, t
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
            E.mk_let sy e acc
            [@ocaml.ppwarning "TODO: should introduce fresh vars"]
        ) body binders

      | Binder ((Forall (tyvl, tvl) | Exists (tyvl, tvl)) as e, body) ->
        if not toplevel && tyvl != [] then
          Fmt.failwith "Non-prenex polymorphism in the term %a"
            DE.Term.print term
        else if tvl == []
        then begin
          Cache.store_tyvl tyvl;
          aux_mk_expr ~toplevel:true body
        end
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
                t_v
            ) tvl
          in
          (* Set of binders *)
          let binders =
            List.fold_left (
              fun vl (ty, v, tv) ->
                let sy = Sy.var v in
                Cache.store_sy tv sy;
                Var.Map.add v ty vl
            ) Var.Map.empty ntvl
          in

          (* filters *)
          let hyp =
            begin match DStd.Tag.get body.term_tags DE.Tags.filters with
              | Some t -> t
              | _ -> []
            end
          in
          let hyp = List.map aux_mk_expr hyp in

          (* triggers *)
          let trgs =
            begin match DStd.Tag.get body.term_tags DE.Tags.triggers with
              | Some t -> t
              | _ -> []
            end
          in
          let in_theory = decl_kind == E.Dtheory in
          let f = aux_mk_expr ~toplevel:false body in
          let qbody = E.purify_form f in
          (*  All the triggers that are encoutered at this level are assumed
              to be user-defined. *)
          let triggers =
            List.map (
              fun t ->
                make_trigger ~loc ~name_base ~decl_kind ~in_theory
                  name hyp (t, true)
            ) trgs
          in

          let mk = begin match e with
            | Forall _ -> E.mk_forall
            | Exists _ -> E.mk_exists
            | _ -> assert false (* unreachable *)
          end
          in
          mk name loc binders triggers qbody ~toplevel ~decl_kind
      | _ -> unsupported "Term %a" DE.Term.print term
    in
    match DStd.Tag.get root_tags DE.Tags.named with
    | Some s ->
      let lbl = Hstring.make s in
      E.add_label lbl res;
      res
    | _ -> res

  and semantic_trigger ?var ?(loc = Loc.dummy) t =
    let cst, args =
      match destruct_app t with
      | Some (cst, args) -> cst, args
      | None ->
        Fmt.failwith
          "invalid semantic trigger: %a"
          DE.Term.print t
    in
    match cst, args with
    (* x |-> y *)
    | B.Maps_to, [ x; y ] ->
      (* There should be no variable bound at the [semantic_trigger] level for
         maps-to. *)
      assert (Option.is_none var);
      begin match x.term_descr with
        | Var t_v ->
          let v = Cache.find_var t_v in
          let sy = Sy.mk_maps_to v in
          let e2 = aux_mk_expr y in
          E.mk_term sy [e2] Ty.Tbool
        | _ ->
          Fmt.failwith
            "%aMaps_to: expected a variable but got: %a"
            Loc.report loc DE.Term.print x
      end

    (* open-ended in interval *)
    | (B.Lt _ | B.Leq _ | B.Gt _ | B.Geq _) as b, [x; y] ->
      let main_var, main_expr = Option.get var in
      let qm = Sy.Unbounded in
      let sort, lb, ub = parse_semantic_bound ~loc ~var:main_var b x y in
      let lb =
        match lb with
        | Some lb -> lb
        | None -> Sy.mk_bound qm sort ~is_open:true ~is_lower:true
      and ub =
        match ub with
        | Some ub -> ub
        | None -> Sy.mk_bound qm sort ~is_open:true ~is_lower:false
      in
      E.mk_term (Sy.mk_in lb ub) [aux_mk_expr main_expr] Ty.Tbool

    (* conjunction *)
    | B.And, [x; y] ->
      let main_var, main_expr = Option.get var in
      begin match destruct_app x, destruct_app y with
        | Some (b, [l; r]), Some (b', [l'; r']) ->
          let sort, lb, ub =
            parse_semantic_bound ~loc ~var:main_var b l r
          and sort', lb', ub' =
            parse_semantic_bound ~loc ~var:main_var b' l' r'
          in
          assert Stdlib.(sort = sort');
          let lb =
            match lb, lb' with
            | Some lb, None | None, Some lb -> lb
            | _ -> assert false
          in
          let ub =
            match ub, ub' with
            | Some ub, None | None, Some ub -> ub
            | _ -> assert false
          in
          E.mk_term (Sy.mk_in lb ub) [aux_mk_expr main_expr] Ty.Tbool
        | _ ->
          Fmt.failwith "%aInvalid semantic trigger: %a"
            Loc.report loc DE.Term.print t
      end

    | _ ->
      Fmt.failwith "%aInvalid semantic trigger: %a"
        Loc.report loc DE.Term.print t

  in aux_mk_expr ~toplevel dt

and make_trigger ?(loc = Loc.dummy) ~name_base ~decl_kind
    ~(in_theory: bool) (name: string) (hyp: E.t list)
    (e, from_user: DE.term * bool) =
  (* Dolmen adds an existential quantifier to bind the '?xxx' variables *)
  let e =
    match e with
    | { DE.term_descr = Binder (Exists (_, qm_vars), e); _ } ->
      List.iter
        (fun (v : DE.term_var) ->
           let var =
             match v.path with
             | Local { name } -> Var.local name
             | _ -> assert false
           in
           Cache.store_var v var)
        qm_vars;
      e
    | e ->  e
  in
  (* And a [Multi_trigger] wrapper for multi-triggers *)
  let e =
    match e with
    | { DE.term_descr = App ({
        term_descr = Cst { builtin = B.Multi_trigger ; _ }; _
      }, _, es)
      ; _ }
      -> es
    | e -> [e]
  in
  let mk_expr =
    mk_expr ~loc ~name_base ~decl_kind
  in
  let content = List.map mk_expr e in
  (* clean trigger:
     remove useless terms in multi-triggers after inlining of lets*)
  let trigger = E.mk_trigger ~user:from_user ~hyp content in
  if not in_theory && not (Compat.List.is_empty trigger.semantic) then
    Errors.typing_error ThSemTriggerError loc;
  E.clean_trigger ~in_theory name trigger

(** Preprocesses the body of a goal by:
    - removing the top-level universal quantifiers and considering their
      quantified variables as uninterpreted symbols.
    - transforming a given formula: [a[1] -> a[2] -> ... -> a[n]] in which
      the [a[i]]s are subformulas and [->] is a logical implication, to a set of
      hypotheses [{a[1]; ...; a[n-1]}], and a goal [a[n]] whose validity is
      verified by the solver.

    If additional hypotheses are provided in [hyps], they are preprocessed and
    added to the set of hypotheses in the same way as the left-hand side of
    implications. In other words, [pp_query ~hyps:[h1; ...; hn] t] is the same
    as [pp_query (h1 -> ... -> hn t)], but more convenient if the some
    hypotheses are already separated from the goal.

    Returns a list of hypotheses and the new goal body
*)
let pp_query ?(hyps =[]) t =
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
        tyl, es
      ) when not bnot ->
      let es = List.map (elim_toplevel_forall false) es in
      DE.Term.apply_cst DE.Term.Const.and_ tyl es

    | App (
        { term_descr = Cst { builtin = B.Or;  _ }; _ },
        tyl, es
      ) when bnot ->
      let es = List.map (elim_toplevel_forall true) es in
      DE.Term.apply_cst DE.Term.Const.and_ tyl es

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
  let rec intro_hypothesis DE.({ term_descr; _ } as t) =
    match term_descr with
    | App (
        { term_descr = Cst { builtin = B.Imply; _ }; _ }, _, [x; y]
      ) ->
      let nx = elim_toplevel_forall false x in
      let axioms, goal = intro_hypothesis y in
      nx::axioms, goal

    | Binder (Forall (tyvl, tvl), body) ->
      Cache.store_tyvl ~is_var:false tyvl;
      Cache.store_sy_vl_names tvl;
      intro_hypothesis body

    | _ ->
      [], elim_toplevel_forall true t
  in

  let axioms, goal = intro_hypothesis t in
  List.rev_append (List.rev_map (elim_toplevel_forall false) hyps) axioms, goal

let make_form name_base f loc ~decl_kind =
  let ff =
    mk_expr ~loc ~name_base ~toplevel:true ~decl_kind f
  in
  assert (Var.Map.is_empty (E.free_vars ff Var.Map.empty));
  let ff = E.purify_form ff in
  if Ty.Svty.is_empty (E.free_type_vars ff) then ff
  else
    E.mk_forall name_base loc Var.Map.empty [] ff ~toplevel:true ~decl_kind

(* Helper function used to check if the expression defining an objective
   function is a pure term. *)
let rec is_pure_term t =
  let E.{ f; xs; _ } = E.term_view t in
  match f with
  | (Sy.Let | Lit _ | Form _) -> false
  | Sy.Op Tite -> false
  | _ -> List.for_all is_pure_term xs

let make dloc_file acc stmt =
  let rec aux acc (stmt: _ Typer_Pipe.stmt) =
    match stmt with
    (* Optimize terms *)
    | { contents = `Optimize (t, is_max); loc; _ } ->
      let st_loc = dl_to_ael dloc_file loc in
      let e =
        mk_expr ~loc:st_loc ~toplevel:true ~decl_kind:Dobjective t
      in
      let fn = Objective.Function.mk ~is_max e in
      if not @@ is_pure_term e then
        begin
          Printer.print_wrn
            "the expression %a is not a valid objective function. \
             Only terms without let bindings or ite subterms can be optimized."
            E.print e;
          acc
        end
      else
        let st_decl = C.Optimize fn in
        C.{ st_decl; st_loc } :: acc

    (* Push and Pop commands *)
    | { contents = `Pop n; loc; _ } ->
      let st_loc = dl_to_ael dloc_file loc in
      let st_decl = C.Pop n in
      C.{ st_decl; st_loc } :: acc

    | { contents = `Push n; loc; _ } ->
      let st_loc = dl_to_ael dloc_file loc in
      let st_decl = C.Push n in
      C.{ st_decl; st_loc } :: acc

    (* Goal and check-sat definitions *)
    | {
      id; loc; attrs;
      contents = (`Goal _ | `Check _) as contents;
      implicit;
    } ->
      let name =
        match id.name with
        | Simple name -> name
        | Indexed _ | Qualified _ -> assert false
      in
      let goal_sort =
        match contents with
        | `Goal _ -> Ty.Thm
        | `Check _ -> Ty.Sat
      in
      let st_loc = dl_to_ael dloc_file loc in
      let _hyps, t =
        match contents with
        | `Goal t ->
          pp_query t
        | `Check hyps ->
          pp_query ~hyps (DStd.Expr.Term.(of_cst Const._false))
      in
      let rev_hyps_c =
        List.fold_left (
          fun acc t ->
            let ns = DStd.Namespace.Decl in
            let name = Ty.fresh_hypothesis_name goal_sort in
            let decl: _ Typer_Pipe.stmt = {
              id = DStd.Id.mk ns name;
              contents = `Hyp t; loc; attrs; implicit
            }
            in
            aux acc decl
        ) [] _hyps
      in
      let e = make_form "" t st_loc ~decl_kind:E.Dgoal in
      let st_decl = C.Query (name, e, goal_sort) in
      C.{st_decl; st_loc} :: List.rev_append (List.rev rev_hyps_c) acc

    | { contents = `Solve _; _ } ->
      (* Filtered out by the solving_loop *)
      (* TODO: Remove them from the types *)
      assert false

    (* Axiom definitions *)
    | { id = DStd.Id.{name = Simple name; _}; contents = `Hyp t; loc; attrs;
        implicit=_ } ->
      let name =
        match DStd.Tag.get t.term_tags lemma_name_attr with
        | Some n -> n
        | None ->
          match DStd.Tag.get t.term_tags DE.Tags.named with
          | Some n -> n
          | None -> name
      in
      let dloc = DStd.Loc.(loc dloc_file stmt.loc) in
      let aloc = DStd.Loc.lexing_positions dloc in
      (* Dolmen adds information about theory extensions and case splits in the
         [attrs] field of the parsed statements. [attrs] can be arbitrary terms,
         where the information we care about is encoded as a [Colon]-list of
         symbols.

         The few helper functions below are used to extract the information from
         the [attrs]. More specifically:

         - "case split" statements have the [DStd.Id.case_split] symbol as an
            attribute

         - Theory elements have a 3-length list of symbols as an attribute, of
            the form [theory_decl; name; extends], where [theory_decl] is the
            symbol [DStd.Id.theory_decl] and [name] and [extends] are the theory
            extension name and the base theory name, respectively.
      *)
      let rec symbols = function
        | DStd.Term. { term = Colon ({ term = Symbol sy; _ }, xs); _ } ->
          Option.bind (symbols xs) @@ fun sys ->
          Some (sy :: sys)
        | { term = Symbol sy; _ } -> Some [sy]
        | _ -> None
      in
      let sy_attrs = List.filter_map symbols attrs in
      let is_case_split =
        let is_case_split = function
          | [ sy ] when DStd.Id.(equal sy case_split) -> true
          | _ -> false
        in
        List.exists is_case_split sy_attrs
      in
      let theory =
        let theory =
          let open DStd.Id in
          function
          | [ td; name; extends] when DStd.Id.(equal td theory_decl) ->
            let name = match name.name with
              | Simple name -> name
              | _ ->
                Fmt.failwith
                  "Internal error: invalid theory extension: %a"
                  print name
            in
            let extends = match extends.name with
              | Simple name ->
                begin match Util.th_ext_of_string name with
                  | Some extends -> extends
                  | None ->
                    Errors.typing_error (ThExtError name) aloc
                end
              | _ ->
                Fmt.failwith
                  "Internal error: invalid base theory name: %a"
                  print extends
            in
            Some (name, extends)
          | _ -> None
        in
        match List.filter_map theory sy_attrs with
        | [] -> None
        | [name, extends] -> Some (name, extends)
        | _ ->
          Fmt.failwith
            "%a: Internal error: multiple theories."
            DStd.Loc.fmt dloc
      in
      let decl_kind, assume =
        match theory with
        | Some (th_name, extends) ->
          let axiom_kind =
            if is_case_split then Util.Default else Util.Propagator
          in
          let th_assume name e =
            let th_elt = {
              Expr.th_name;
              axiom_kind;
              extends;
              ax_form = e;
              ax_name = name;
            } in
            C.ThAssume th_elt
          in
          E.Dtheory, th_assume
        | None -> E.Daxiom, fun name e -> C.Assume (name, e, true)
      in
      let st_loc = dl_to_ael dloc_file loc in
      let e = make_form name t st_loc ~decl_kind in
      let st_decl = assume name e in
      C.{ st_decl; st_loc } :: acc

    (* Function and predicate definitions *)
    | { contents = `Defs defs; loc; _ } ->
      (* For a mutually recursive definition, we have to add all the function
         names in a row. *)
      List.iter (fun (def : Typer_Pipe.def) ->
          match def with
          | `Term_def (_, ({ path; _ } as tcst), _, _, _) ->
            let name_base = get_basename path in
            let sy = Sy.name ~defined:true name_base in
            Cache.store_sy tcst sy
          | `Type_alias _ -> ()
          | `Instanceof _ ->
            (* These statements are only used in models when completing a
               polymorphic partially-defined bulitin and should not end up
               here. *)
            assert false
        ) defs;
      let append xs = List.append xs acc in
      append @@
      List.filter_map (fun (def : Typer_Pipe.def) ->
          match def with
          | `Term_def ( _, ({ path; tags; _ } as tcst), tyvars, terml, body) ->
            Cache.store_tyvl tyvars;
            let st_loc = dl_to_ael dloc_file loc in
            let name_base = get_basename path in

            let binders, defn =
              let rty = dty_to_ty body.term_ty in
              let binders, rev_args =
                List.fold_left (
                  fun (binders, acc) (DE.{ path; id_ty; _ } as tv) ->
                    let ty = dty_to_ty id_ty in
                    let v = Var.of_string (get_basename path) in
                    let sy = Sy.var v in
                    Cache.store_sy tv sy;
                    let e = E.mk_term sy [] ty in
                    Var.Map.add v ty binders, e :: acc
                ) (Var.Map.empty, []) terml
              in
              let sy = Cache.find_sy tcst in
              let e = E.mk_term sy (List.rev rev_args) rty in
              binders, e
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
                let ff =
                  E.mk_forall name_base Loc.dummy binders [] qb ~toplevel:true
                    ~decl_kind
                in
                assert (Var.Map.is_empty (E.free_vars ff Var.Map.empty));
                let ff = E.purify_form ff in
                let e =
                  if Ty.Svty.is_empty (E.free_type_vars ff) then ff
                  else
                    E.mk_forall name_base loc
                      Var.Map.empty [] ff ~toplevel:true ~decl_kind
                in
                Some C.{ st_decl = C.PredDef (e, name_base); st_loc }
              | None ->
                let decl_kind = E.Dfunction defn in
                let ff =
                  mk_expr ~loc ~name_base
                    ~toplevel:false ~decl_kind body
                in
                let iff = Ty.equal (Expr.type_info defn) (Ty.Tbool) in
                let qb = E.mk_eq ~iff defn ff in
                let ff =
                  E.mk_forall name_base Loc.dummy binders [] qb ~toplevel:true
                    ~decl_kind
                in
                assert (Var.Map.is_empty (E.free_vars ff Var.Map.empty));
                let ff = E.purify_form ff in
                let e =
                  if Ty.Svty.is_empty (E.free_type_vars ff) then ff
                  else
                    E.mk_forall name_base loc
                      Var.Map.empty [] ff ~toplevel:true ~decl_kind
                in
                if Options.get_verbose () then
                  Format.eprintf "defining term of %a@." DE.Term.print body;
                Some C.{ st_decl = C.Assume (name_base, e, true); st_loc }
            end
          | `Type_alias _ -> None
          | `Instanceof _ ->
            (* These statements are only used in models when completing a
               polymorphic partially-defined bulitin and should not end up
               here. *)
            assert false
        ) defs

    | {contents = `Decls [td]; loc; _ } ->
      begin match td with
        | `Type_decl (td, _def) ->
          mk_ty_decl td;
          acc

        | `Term_decl td ->
          let st_loc = dl_to_ael dloc_file loc in
          C.{ st_decl = Decl (mk_term_decl td); st_loc } :: acc
      end

    | {contents = `Decls dcl; loc; _ } ->
      let rec aux ty_decls tdl acc =
        (* for now, when acc has more than one element it is assumed that the
           types are mutually recursive. Which is not necessarily the case.
           But it doesn't affect the execution.
        *)
        match tdl with
        | `Term_decl td :: tl ->
          begin match ty_decls with
            | [] -> ()
            | [otd] -> mk_ty_decl otd
            | _ -> mk_mr_ty_decls (List.rev ty_decls)
          end;
          let st_loc = dl_to_ael dloc_file loc in
          C.{ st_decl = Decl (mk_term_decl td); st_loc } :: aux [] tl acc

        | `Type_decl (td, _def) :: tl ->
          aux (td :: ty_decls) tl acc

        | [] ->
          begin
            let () =
              match ty_decls with
              | [] -> ()
              | [otd] -> mk_ty_decl otd
              | _ ->  mk_mr_ty_decls (List.rev ty_decls)
            in
            acc
          end
      in
      aux [] dcl acc

    | { contents = `Set_logic _ | `Set_info _ | `Get_info _ ; _ } -> acc

    | { contents = #Typer_Pipe.typechecked; _ } as stmt ->
      (* TODO:
         - Separate statements that should be ignored from unsupported
           statements and throw exception or print a warning when an unsupported
           statement is encountered.
      *)
      Printer.print_dbg ~header:true
        "Ignoring statement: %a" Typer_Pipe.print stmt;
      acc
  in
  aux acc stmt

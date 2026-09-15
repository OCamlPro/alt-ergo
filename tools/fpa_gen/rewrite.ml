module Path = Dolmen.Std.Path
module DE = Dolmen.Std.Expr
module B = Dolmen.Std.Builtin
open Literals

let strip_suffix suffix s =
  if String.ends_with ~suffix s
  then String.sub s 0 (String.length s - String.length suffix)
  else s

let transform s = "ae.fp." ^ strip_suffix "64" (strip_suffix "1" s)

let const_rename_table : (string * string) list =
  List.map
    (fun (lit, name) -> lit, transform name)
    [ max_int_s, "max_int";
      max_real_s, "max_real";
      pow2sb_s, "pow2sb";
      pow2sb_real_s, "pow2sb_real";
      half_pow2sb_real_s, "half_pow2sb_real";
      abs_err_rne_s, "abs_err_rne_denom";
      abs_err_s, "abs_err_denom" ]

let op_rename_table : (string * string) list =
  ("ae.float64", "ae.float")
  :: ("tqtreal", transform "to_real")
  :: ("tqtisFinite", transform "is_finite")
  :: ("zeroF", transform "zero")
  :: List.map
       (fun s -> s, transform s)
       [ "add";
         "sub";
         "mul";
         "div1";
         "abs1";
         "neg";
         "fma";
         "sqrt1";
         "roundToIntegral";
         "le";
         "lt";
         "eq";
         "min";
         "max";
         "is_zero";
         "is_infinite";
         "is_nan";
         "is_positive";
         "is_negative";
         "of_int";
         "to_int1";
         "from_real";
         "is_int1";
         "is_plus_infinity";
         "is_minus_infinity";
         "is_not_nan";
         "in_range";
         "in_int_range";
         "no_overflow";
         "in_safe_int_range";
         "same_sign";
         "diff_sign";
         "product_sign";
         "overflow_value";
         "sign_zero_result";
         "same_sign_real" ]

type ctx =
  { cst_cache : (string, DE.Term.Const.t) Hashtbl.t;
    var_subst : (DE.Term.Var.t * DE.Term.Var.t) list;
    pow2_builtin : bool;
    sqrt_builtin : bool
  }

type state =
  { seen_set_logic : bool;
    seen_set_info : bool;
    seen_sort_decl : bool;
    pending_ae_float_decl : Loop.Typer.typechecked Loop.Typer.stmt option;
    pending_hyp : Loop.Typer.typechecked Loop.Typer.stmt option
  }

let ae_fp_ty = DE.Ty.Const.mk (Path.global "ae.fp.t") 0

let rec rewrite_ty (ty : DE.Ty.t) : DE.Ty.t =
  match ty.ty_descr with
  | DE.TyVar _ -> ty
  | DE.TyApp (tc, args) ->
    let tc' =
      match tc.path with
      | Path.Absolute { path = []; name = "t" } | Path.Local { name = "t" } ->
        ae_fp_ty
      | _ -> tc
    in
    let args' = List.map rewrite_ty args in
    DE.Ty.apply tc' args'
  | DE.Arrow (params, ret) ->
    let params' = List.map rewrite_ty params in
    let ret' = rewrite_ty ret in
    DE.Ty.arrow params' ret'
  | DE.Pi (vars, body) ->
    let body' = rewrite_ty body in
    DE.Ty.pi vars body'

let rewrite_var ctx (v : DE.Term.Var.t) : ctx * DE.Term.Var.t =
  let ty = DE.Term.Var.ty v in
  let ty' = rewrite_ty ty in
  if DE.Ty.equal ty' ty
  then ctx, v
  else
    let name =
      match v.path with
      | Path.Absolute { path = []; name } | Path.Local { name } -> name
      | _ -> assert false
    in
    let v' = DE.Term.Var.mk name ty' in
    { ctx with var_subst = (v, v') :: ctx.var_subst }, v'

let rewrite_vars ctx (vs : DE.Term.Var.t list) : ctx * DE.Term.Var.t list =
  List.fold_right
    (fun v (ctx, vs') ->
      let ctx, v' = rewrite_var ctx v in
      ctx, v' :: vs')
    vs (ctx, [])

(* The two format parameters shared across the whole transformation. *)
let eb_var = DE.Term.Var.mk "eb" DE.Ty.int

let sb_var = DE.Term.Var.mk "sb" DE.Ty.int

let eb_term = DE.Term.of_var eb_var

let sb_term = DE.Term.of_var sb_var

(* Add (=> (and (< 1 eb) (< 1 sb)) ...) before an FP axiom *)
let eb_sb_guard =
  let one = DE.Term.Int.mk "1" in
  DE.Term._and [DE.Term.Int.lt one eb_term; DE.Term.Int.lt one sb_term]

(* Add eb and sb as first arguments to a function call *)
let apply_with_eb_sb ?(args = []) new_cst =
  DE.Term.apply_cst new_cst [] (eb_term :: sb_term :: args)

let pow2_ty = DE.Ty.arrow [DE.Ty.int] DE.Ty.int

let sqrt2_ty = DE.Ty.arrow [DE.Ty.real] DE.Ty.real

let create_ctx ?(pow2_builtin = true) ?(sqrt_builtin = true) () =
  { cst_cache = Hashtbl.create 32; var_subst = []; pow2_builtin; sqrt_builtin }

let init_state =
  { seen_set_logic = false;
    seen_set_info = false;
    seen_sort_decl = false;
    pending_ae_float_decl = None;
    pending_hyp = None
  }

let cst_path_name (c : DE.Term.Const.t) : string =
  match DE.Term.Const.path c with
  | Path.Absolute { path = []; name } | Path.Local { name } -> name
  | _ -> assert false

let get_cst (ctx : ctx) name (ty : DE.Ty.t) : DE.Term.Const.t =
  match Hashtbl.find_opt ctx.cst_cache name with
  | Some c -> c
  | None ->
    let c = DE.Term.Const.mk (Path.global name) ty in
    Hashtbl.add ctx.cst_cache name c;
    c

let add_eb_sb_args_type ctx name (orig_ty : DE.Ty.t) : DE.Term.Const.t =
  let _, f_args, ret = DE.Ty.poly_sig orig_ty in
  let f_args = List.map rewrite_ty f_args in
  let ret = rewrite_ty ret in
  get_cst ctx name (DE.Ty.arrow (DE.Ty.int :: DE.Ty.int :: f_args) ret)

let lookup_op_rename ctx name orig_ty =
  match List.assoc_opt name op_rename_table with
  | Some new_name -> Some (add_eb_sb_args_type ctx new_name orig_ty)
  | None -> Hashtbl.find_opt ctx.cst_cache name

let lookup_rename ctx name orig_ty =
  match List.assoc_opt name const_rename_table with
  | Some new_name -> Some (add_eb_sb_args_type ctx new_name orig_ty)
  | None -> lookup_op_rename ctx name orig_ty

let declare_fp_constants (ctx : ctx)
    (stmt : Loop.Typer.typechecked Loop.Typer.stmt) :
    Loop.Typer.typechecked Loop.Typer.stmt list =
  Fmt.pr "; --- interpreted type-dependent constants ---@.";
  List.map
    (fun (lit, name) ->
      let ty = if String.contains lit '.' then DE.Ty.real else DE.Ty.int in
      let c = get_cst ctx name (DE.Ty.arrow [DE.Ty.int; DE.Ty.int] ty) in
      { stmt with contents = `Decls (false, [`Term_decl c]) })
    const_rename_table

let rec rewrite_term ctx (t : DE.Term.t) : DE.Term.t =
  match t.term_descr with
  | DE.Var v -> begin
    match
      List.find_opt (fun (v', _) -> DE.Term.Var.equal v v') ctx.var_subst
    with
    | Some (_, v') -> DE.Term.of_var v'
    | None -> t
  end
  | Cst c -> (
    let name = cst_path_name c in
    match lookup_rename ctx name c.id_ty with
    | Some new_c -> apply_with_eb_sb new_c
    | None -> ( match name with "11" -> eb_term | "53" -> sb_term | _ -> t))
  | App (f, tys, args) -> (
    let args = List.map (rewrite_term ctx) args in
    let tys = List.map rewrite_ty tys in
    match f.term_descr with
    | Cst c -> (
      let name = cst_path_name c in
      match lookup_op_rename ctx name c.id_ty with
      | Some new_c -> apply_with_eb_sb ~args new_c
      | None when ctx.pow2_builtin && String.equal name pow2_name ->
        DE.Term.apply_cst (get_cst ctx builtin_pow2_name pow2_ty) [] args
      | None when ctx.sqrt_builtin && String.equal name sqrt2_name ->
        DE.Term.apply_cst (get_cst ctx builtin_sqrt2_name sqrt2_ty) [] args
      | None -> DE.Term.apply (rewrite_term ctx f) tys args)
    | _ -> DE.Term.apply (rewrite_term ctx f) tys args)
  | Binder (Forall (tyvs, vs), body) ->
    let ctx, vs = rewrite_vars ctx vs in
    DE.Term.all (tyvs, vs) (rewrite_binder_body ctx body)
  | Binder (Exists (tyvs, vs), body) ->
    let ctx, vs = rewrite_vars ctx vs in
    DE.Term.ex (tyvs, vs) (rewrite_binder_body ctx body)
  | Binder (Let_seq bindings, body) ->
    let ctx, bindings = rewrite_let_bindings ctx bindings in
    DE.Term.letin bindings (rewrite_term ctx body)
  | Binder (Let_par bindings, body) ->
    let ctx, bindings = rewrite_let_bindings ctx bindings in
    DE.Term.letand bindings (rewrite_term ctx body)
  | _ -> t

and rewrite_let_bindings ctx bindings =
  List.fold_right
    (fun (v, term) (ctx, acc) ->
      let ctx, v = rewrite_var ctx v in
      let term = rewrite_term ctx term in
      ctx, (v, term) :: acc)
    bindings (ctx, [])

and rewrite_binder_body ctx body =
  let triggers = DE.Term.get_tag_list body DE.Tags.triggers in
  let body' = rewrite_term ctx body in
  (* Preserve triggers after rewriting *)
  if triggers <> []
  then
    DE.Term.set_tag body' DE.Tags.triggers
      (List.map (rewrite_term ctx) triggers);
  body'

let rec term_uses_vars (vl : DE.Term.Var.t list) (t : DE.Term.t) : bool =
  match t.term_descr with
  | DE.Var v' -> List.mem v' vl
  | DE.Cst _ -> false
  | DE.App (f, _, args) ->
    term_uses_vars vl f || List.exists (term_uses_vars vl) args
  | DE.Binder (_, body) -> term_uses_vars vl body
  | _ -> false

let rec term_mentions (name : string) (t : DE.Term.t) : bool =
  match t.term_descr with
  | DE.Cst c -> String.equal (cst_path_name c) name
  | DE.App (f, _, args) ->
    term_mentions name f || List.exists (term_mentions name) args
  | DE.Binder (_, body) -> term_mentions name body
  | _ -> false

let rewrite_hyp (ctx : ctx) (t : DE.Term.t) : [`Keep of DE.Term.t | `Drop] =
  match t.term_descr with
  (* pow2 ground facts: (assert (= (pow2 _) _)), dropped when builtin `int.pow2`
     is used, otherwise kept. *)
  | DE.App
      ( { term_descr = Cst { builtin = B.Equal; _ }; _ },
        _,
        [{ term_descr = DE.App ({ term_descr = Cst c; _ }, [], [_]); _ }; _b] )
    when String.equal (cst_path_name c) pow2_name ->
    if ctx.pow2_builtin then `Drop else `Keep t
  (* Drop `match_mode` quantifiers. *)
  | DE.Binder (Forall (_ :: _, _), _) -> `Drop
  (* Drop (< 1 11) and (< 1 53). *)
  | DE.App
      ( { term_descr = Cst { builtin = B.Arith (Lt _); _ }; _ },
        [],
        [{ term_descr = DE.Cst one; _ }; { term_descr = DE.Cst n; _ }] )
    when String.equal "1" (cst_path_name one)
         && (String.equal "11" (cst_path_name n)
            || String.equal "53" (cst_path_name n)) ->
    `Drop
  | _ ->
    let body = rewrite_term ctx t in
    if term_uses_vars [eb_var; sb_var] body
    then
      (* Wrap with (forall (eb sb ...) (=> guard ...)), copying :pattern. *)
      let add_guard b =
        let triggers = DE.Term.get_tag_list b DE.Tags.triggers in
        let guarded = DE.Term.imply eb_sb_guard b in
        DE.Term.set_tag guarded DE.Tags.triggers triggers;
        guarded
      in
      match body.term_descr with
      | DE.Binder (Forall ([], vs), inner) ->
        (* Merge eb sb into the existing ground forall. *)
        `Keep (DE.Term.all ([], eb_var :: sb_var :: vs) (add_guard inner))
      | _ -> `Keep (DE.Term.all ([], [eb_var; sb_var]) (add_guard body))
    else if
      (ctx.pow2_builtin && term_mentions pow2_name t)
      || (ctx.sqrt_builtin && term_mentions sqrt2_name t)
    then `Drop
    else `Keep body

let generalize (ctx : ctx) (st : state)
    (stmt : Loop.Typer.typechecked Loop.Typer.stmt) :
    state * Loop.Typer.typechecked Loop.Typer.stmt list =
  (* add declaration ae.float and other builtins *)
  let st, added_early_decls =
    match st.pending_ae_float_decl with
    | Some ae_float_decl when st.seen_set_info ->
      let builtin_decl name ty =
        { ae_float_decl with
          contents = `Decls (false, [`Term_decl (get_cst ctx name ty)])
        }
      in
      let decls =
        List.filter_map
          (fun (enabled, name, ty) ->
            if enabled then Some (builtin_decl name ty) else None)
          [ ctx.pow2_builtin, builtin_pow2_name, pow2_ty;
            ctx.sqrt_builtin, builtin_sqrt2_name, sqrt2_ty ]
      in
      { st with pending_ae_float_decl = None }, ae_float_decl :: decls
    | _ -> st, []
  in
  let keep c = [{ stmt with contents = c }] in
  let st, result =
    match stmt.contents with
    | `Set_logic _ when not st.seen_set_logic ->
      (* Deduplicate: prelude repeats (set-logic ALL). *)
      { st with seen_set_logic = true }, [stmt]
    | `Set_info _ when not st.seen_set_info ->
      (* Deduplicate: prelude repeats (set-info :smt-lib-version ...). *)
      { st with seen_set_info = true }, [stmt]
    | `Solve _ | `Exit -> st, []
    | `Echo _ -> st, [stmt]
    | `Decls (_, [`Term_decl { path = Absolute { name = "match_mode"; _ }; _ }])
      ->
      st, []
    | `Decls (r, [decl]) -> begin
      let d' =
        match decl with
        | `Type_decl _ -> decl
        | `Term_decl c -> (
          let n = cst_path_name c in
          match List.assoc_opt n op_rename_table with
          | Some new_name ->
            `Term_decl (add_eb_sb_args_type ctx new_name c.id_ty)
          | None -> decl)
        | _ -> assert false
      in
      begin match d' with
      | `Type_decl ({ path = Absolute { name = "t"; _ }; _ }, None)
        when not st.seen_sort_decl ->
        (* When t is encountered, add const declarations and ae.fp.t's
           declaration *)
        let const_decls = declare_fp_constants ctx stmt in
        ( { st with seen_sort_decl = true },
          const_decls
          @ [{ stmt with contents = `Decls (r, [`Type_decl (ae_fp_ty, None)]) }]
        )
      | `Term_decl { path = Absolute { name = "ae.float"; _ }; _ }
        when not st.seen_set_info ->
        ( { st with
            pending_ae_float_decl =
              Some { stmt with contents = `Decls (r, [d']) }
          },
          [] )
      (* Drop declarations of pow2 and sqrt2 when their buitlin counterparts are
         used *)
      | `Term_decl { path = Absolute { name; _ }; _ }
        when (ctx.pow2_builtin && String.equal name pow2_name)
             || (ctx.sqrt_builtin && String.equal name sqrt2_name) ->
        st, []
      | _ when not st.seen_sort_decl -> st, []
      | _ -> st, keep (`Decls (r, [d']))
      end
    end
    | `Defs _ when not st.seen_sort_decl -> st, []
    | `Defs (r, [def]) -> begin
      match def with
      | `Type_alias _ -> st, [stmt]
      (* `sqr` is only used by sqrt2, so drop it when the builtin version of
         sqrt2 is used*)
      | `Term_def (_, c, _, _, _)
        when ctx.sqrt_builtin && String.equal (cst_path_name c) sqr_name ->
        st, []
      | `Term_def (tag, c, [], vars, body) ->
        let ctx, vars = rewrite_vars ctx vars in
        let body' = rewrite_term ctx body in
        let c, vars =
          if term_uses_vars [eb_var; sb_var] body'
          then
            (* Change the name of the defined function to follow the style of
               the other defined/declared operations *)
            let name =
              match List.assoc_opt (cst_path_name c) op_rename_table with
              | Some new_name -> new_name
              | None -> cst_path_name c
            in
            add_eb_sb_args_type ctx name c.id_ty, eb_var :: sb_var :: vars
          else c, vars
        in
        st, keep (`Defs (r, [`Term_def (tag, c, [], vars, body')]))
      | _ -> st, []
    end
    | `Hyp _ when not st.seen_sort_decl -> st, []
    | `Hyp t -> (
      match rewrite_hyp ctx t with
      | `Keep t' -> st, keep (`Hyp t')
      | `Drop -> st, [])
    | `End when st.seen_set_info -> st, [stmt]
    | _ -> st, []
  in
  st, added_early_decls @ result

let run (ctx : ctx) (st : state)
    (stmts : Loop.Typer.typechecked Loop.Typer.stmt list) :
    state * Loop.Typer.typechecked Loop.Typer.stmt list =
  let flush_pending st acc =
    match st.pending_hyp with
    | None -> st, acc
    | Some pending ->
      let st, batch = generalize ctx { st with pending_hyp = None } pending in
      st, batch :: acc
  in
  let st', batches =
    List.fold_left
      (fun (st, acc) (stmt : Loop.Typer.typechecked Loop.Typer.stmt) ->
        match stmt.contents with
        | `Hyp _ ->
          let st, acc = flush_pending st acc in
          { st with pending_hyp = Some stmt }, acc
        | `Solve _ ->
          let st, batch = generalize ctx { st with pending_hyp = None } stmt in
          st, batch :: acc
        | _ ->
          let st, acc = flush_pending st acc in
          let st, batch = generalize ctx st stmt in
          st, batch :: acc)
      (st, []) stmts
  in
  st', List.concat (List.rev batches)

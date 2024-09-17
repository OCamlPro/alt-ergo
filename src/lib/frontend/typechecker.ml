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

open Parsed
open Typed

module S = Set.Make(String)
module HSS = Hstring.Set

module MString =
  Map.Make(struct type t = string let compare = String.compare end)

module Types = struct

  (* environment for user-defined types *)
  type t = {
    to_ty : Ty.t MString.t;
    builtins : Ty.t MString.t;
    from_labels : string MString.t; }

  let to_tyvars = ref MString.empty

  let empty =
    { to_ty = MString.empty;
      builtins = MString.empty;
      from_labels = MString.empty }

  let fresh_vars ~recursive vars loc =
    List.map
      (fun x ->
         if recursive then
           try MString.find x !to_tyvars
           with Not_found -> assert false
         else
           begin
             if MString.mem x !to_tyvars then
               Errors.typing_error (TypeDuplicateVar x) loc;
             let nv = Ty.Tvar (Ty.fresh_var ()) in
             to_tyvars := MString.add x nv !to_tyvars;
             nv
           end
      ) vars

  let check_number_args loc lty ty =
    match ty with
    | Ty.Text (lty', s)
    | Ty.Trecord { Ty.args = lty'; name = s; _ }
    | Ty.Tadt (s,lty') ->
      if List.length lty <> List.length lty' then
        Errors.typing_error (WrongNumberofArgs (Uid.show s)) loc;
      lty'
    | _ -> assert false

  let equal_pp_vars lpp lvars =
    try
      List.for_all2
        (fun pp x ->
           match pp with
           | PPTvarid (y, _) -> String.equal x y
           | _ -> false
        ) lpp lvars
    with Invalid_argument _ -> false

  let rec ty_of_pp loc env rectype = function
    | PPTint -> Ty.Tint
    | PPTbool -> Ty.Tbool
    | PPTunit -> Ty.tunit
    | PPTreal -> Ty.Treal
    | PPTbitv n ->
      if n <= 0 then Errors.typing_error (NonPositiveBitvType n) loc;
      Ty.Tbitv n
    | PPTvarid (s, _) ->
      begin
        try MString.find s !to_tyvars
        with Not_found ->
          let nty = Ty.Tvar (Ty.fresh_var ()) in
          to_tyvars := MString.add s nty !to_tyvars;
          nty
      end
    | PPTexternal (l, s, loc) when String.equal s "farray" ->
      let t1,t2 = match l with
        | [t2] -> PPTint,t2
        | [t1;t2] -> t1,t2
        | _ -> Errors.typing_error (WrongArity(s,2)) loc in
      let ty1 = ty_of_pp loc env rectype t1 in
      let ty2 = ty_of_pp loc env rectype t2 in
      Ty.Tfarray (ty1, ty2)
    | PPTexternal (l, s, loc) ->
      begin
        match rectype with
        | Some (id, vars, ty) when String.equal s id &&
                                   equal_pp_vars l vars -> ty
        | _ ->
          try
            let lty = List.map (ty_of_pp loc env rectype) l in
            let ty = MString.find s env.to_ty in
            let vars = check_number_args loc lty ty in
            Ty.instantiate vars lty ty
          with Not_found ->
          try
            let lty = List.map (ty_of_pp loc env rectype) l in
            let ty = MString.find s env.builtins in
            let vars = check_number_args loc lty ty in
            Ty.instantiate vars lty ty
          with Not_found ->
            Errors.typing_error (UnknownType s) loc
      end

  let add_decl ~recursive env vars id body loc =
    if MString.mem id env.builtins then
      Printer.print_wrn "%a type `%s` shadows a builtin type"
        Loc.report loc id;
    if MString.mem id env.to_ty && not recursive then
      Errors.typing_error (ClashType id) loc;
    let ty_vars = fresh_vars ~recursive vars loc in
    match body with
    | Abstract ->
      let ty = Ty.text ty_vars (Uid.of_string id) in
      ty, { env with to_ty = MString.add id ty env.to_ty }
    | Enum l ->
      if not (Compat.List.is_empty ty_vars) then
        Errors.typing_error (PolymorphicEnum id) loc;
      let body = List.map (fun constr -> Uid.of_string constr, []) l in
      let ty = Ty.t_adt ~body:(Some body) (Uid.of_string id) [] in
      ty, { env with to_ty = MString.add id ty env.to_ty }
    | Record (record_constr, lbs) ->
      let lbs =
        List.map (fun (x, pp) -> x, ty_of_pp loc env None pp) lbs in
      let sort_fields = String.equal record_constr "{" in
      let record_constr =
        if sort_fields then
          Uid.of_string @@ Fmt.str "%s___%s" record_constr id
        else
          Uid.of_string record_constr
      in
      let ty =
        Ty.trecord ~sort_fields ~record_constr ty_vars
          (Uid.of_string id) (List.map (fun (s, ty) -> Uid.of_string s, ty) lbs)
      in
      ty, { to_ty = MString.add id ty env.to_ty;
            builtins = env.builtins;
            from_labels =
              List.fold_left
                (fun fl (l,_) -> MString.add l id fl) env.from_labels lbs }
    | Algebraic l ->
      let l = (* convert ppure_type to Ty.t in l *)
        List.map (fun (constr, l) ->
            Uid.of_string constr,
            List.map (fun (field, pp) ->
                Uid.of_string field, ty_of_pp loc env None pp) l
          ) l
      in
      let body =
        if l == [] then None (* in initialization step, no body *)
        else Some l
      in
      let ty = Ty.t_adt ~body (Uid.of_string id) ty_vars in
      ty, { env with to_ty = MString.add id ty env.to_ty }

  let add_builtin env id ty =
    { env with builtins = MString.add id ty env.builtins }

  module SH = Set.Make(Hstring)

  let check_labels lbs ty loc =
    let rec check_duplicates s = function
      | [] -> ()
      | (lb, _) :: l ->
        if Uid.Term_set.mem lb s then
          Errors.typing_error
            (DuplicateLabel (Hstring.make @@ Uid.show lb)) loc;
        check_duplicates (Uid.Term_set.add lb s) l
    in
    check_duplicates Uid.Term_set.empty lbs;
    match ty with
    | Ty.Trecord { Ty.lbs = l; _ } ->
      if List.length lbs <> List.length l then
        Errors.typing_error WrongNumberOfLabels loc;
      List.iter
        (fun (lb, _) ->
           try ignore (My_list.assoc Uid.equal lb l)
           with Not_found ->
             Errors.typing_error
               (WrongLabel((Hstring.make @@ Uid.show lb), ty)) loc) lbs;
      ty
    | _ -> assert false


  let from_labels env lbs loc =
    match lbs with
    | [] -> assert false
    | (l, _) :: _ ->
      try
        let ty =
          MString.find (MString.find (Uid.show l) env.from_labels) env.to_ty
        in
        check_labels lbs ty loc
      with Not_found ->
        Errors.typing_error (NoRecordType (Hstring.make @@ Uid.show l)) loc

  let rec monomorphized = function
    | PPTvarid (x, _) when not (MString.mem x !to_tyvars) ->
      to_tyvars := MString.add x (Ty.fresh_empty_text ()) !to_tyvars;

    | PPTexternal (args, _, _) ->
      List.iter monomorphized args

    | _ -> ()

end

module Env = struct

  type profile = { args : Ty.t list; result : Ty.t }

  type logic_kind =
    | RecordConstr
    | RecordDestr
    | AdtConstr
    | EnumConstr
    | AdtDestr
    | Other

  type builtin =
    [ `Term of (Symbols.t * profile * logic_kind)
    | `Builtin of (profile * (int atterm list -> int tt_desc))
    ]

  type t = {
    var_map : (Symbols.t * Ty.t) MString.t ; (* variables' map*)
    types : Types.t ;
    logics : (Symbols.t * profile * logic_kind) MString.t;
    (* logic symbols' map *)
    builtins : builtin MString.t ;
  }

  let builtin1 f =
    function
    | [ e ] -> f e
    | _ -> assert false

  let builtin2 f =
    function
    | [ x; y ] -> f x y
    | _ -> assert false

  let add_fpa_enum map =
    let ty = Fpa_rounding.fpa_rounding_mode in
    match ty with
    | Ty.Tadt (name, []) ->
      let cases = Ty.type_body name [] in
      let constrs = List.map (fun Ty.{ constr; _ } -> constr) cases in
      List.fold_left
        (fun m c ->
           match Fpa_rounding.translate_smt_rounding_mode
                   (Hstring.make @@ Uid.show c) with
           | None ->
             (* The constructors of the type are expected to be AE rounding
                modes. *)
             assert false
           | Some hs ->
             MString.add (Hstring.view hs) (`Term (
                 Symbols.Op (Constr c),
                 { args = []; result = ty },
                 Other
               ))
               m
        )
        map
        constrs
    | _ -> (* Fpa_rounding.fpa_rounding_mode is a sum type. *)
      assert false

  let find_builtin_constr ty n =
    match ty with
    | Ty.Tadt (name, []) ->
      let cases = Ty.type_body name [] in
      let constrs = List.map (fun Ty.{ constr; _ } -> constr) cases in
      List.find (Uid.equal n) constrs
    | _ ->
      assert false

  let add_fpa_builtins env =
    let (->.) args result = { args; result } in
    let int n = {
      c = { tt_desc = TTconst (Tint n); tt_ty = Ty.Tint} ;
      annot = new_id () ;
    } in
    let rm = Fpa_rounding.fpa_rounding_mode in
    let mode m =
      let h = find_builtin_constr rm m in
      {
        c = {
          tt_desc = TTapp (Symbols.(Op (Constr h)), []);
          tt_ty = rm
        };
        annot = new_id ()
      }
    in
    let float prec exp mode x =
      TTapp (Symbols.Op Float, [prec; exp; mode; x])
    in
    let nte = Fpa_rounding.string_of_rounding_mode NearestTiesToEven in
    let tname = Fpa_rounding.fpa_rounding_mode_ae_type_name in
    let float32 = float (int "24") (int "149") in
    let float32d = float32 (mode (Uid.of_string nte)) in
    let float64 = float (int "53") (int "1074") in
    let float64d = float64 (mode (Uid.of_string nte)) in
    let op n op profile =
      MString.add n @@ `Term (Symbols.Op op, profile, Other)
    in
    let partial n f profile =
      MString.add n (`Builtin (profile, f))
    in
    let bool = Ty.Tbool and int = Ty.Tint and real = Ty.Treal in
    let any = Ty.fresh_tvar in
    let env = {
      env with
      types = Types.add_builtin env.types tname rm ;
      builtins = add_fpa_enum env.builtins;
    } in
    let builtins =
      env.builtins

      (* the first argument is mantissas' size (including the implicit bit),
         the second one is the exp of the min representable normalized number,
         the third one is the rounding mode, and the last one is the real to
         be rounded *)
      |> op "float" Float ([int; int; rm; real] ->. real)

      (* syntactic sugar for simple precision floats:
         mantissas size = 24, min exp = 149 *)
      |> partial "float32" (builtin2 float32) ([rm; real] ->. real)

      (* syntactic sugar for simple precision floats with default rounding mode
         (i.e. NearestTiesToEven)*)
      |> partial "float32d" (builtin1 float32d) ([real] ->. real)

      (* syntactic sugar for double precision floats:
         mantissas size = 53, min exp = 1074 *)
      |> partial "float64" (builtin2 float64) ([rm; real] ->. real)

      (* syntactic sugar for double precision floats with default rounding mode
         (i.e. NearestTiesToEven) *)
      |> partial "float64d" (builtin1 float64d) ([real] ->. real)

      (* rounds to nearest integer *)
      |> op "integer_round" Integer_round ([rm; real] ->. int)

      (* type cast: from int to real *)
      |> op "real_of_int" Real_of_int ([int] ->. real)

      (* type check: integers *)
      |> op "real_is_int" Real_is_int ([real] ->. bool)

      (* abs value of a real *)
      |> op "abs_real" Abs_real ([real] ->. real)

      (* sqrt value of a real *)
      |> op "sqrt_real" Sqrt_real ([real] ->. real)

      (* sqrt value of a real by default *)
      |> op "sqrt_real_default" Sqrt_real_default ([real] ->. real)

      (* sqrt value of a real by excess *)
      |> op "sqrt_real_excess" Sqrt_real_excess ([real] ->. real)

      (* abs value of an int *)
      |> op "abs_int" Abs_int ([int] ->. int)

      (* (integer) floor of a rational *)
      |> op "int_floor" Int_floor ([real] ->. int)

      (* (integer) ceiling of a ratoinal *)
      |> op "int_ceil" Int_ceil ([real] ->. int)

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

      |> op "not_theory_constant" Not_theory_constant ([real] ->. bool)
      |> op "is_theory_constant" Is_theory_constant ([any ()] ->. bool)
      |> op "linear_dependency" Linear_dependency ([real; real] ->. bool)

    in
    { env with builtins }

  let empty = add_fpa_builtins {
      var_map = MString.empty;
      types = Types.empty;
      logics = MString.empty;
      builtins = MString.empty
    }

  let add env lv fvar ty =
    let vmap =
      List.fold_left
        (fun vmap x -> MString.add x (fvar x, ty) vmap) env.var_map lv in
    { env with var_map = vmap }

  let add_var env lv pp_ty loc  =
    let ty = Types.ty_of_pp loc env.types None pp_ty in
    let fvar s = Symbols.var @@ Var.of_string s in
    add env lv fvar ty

  let add_ty_var env lv ty  =
    let fvar s = Symbols.var @@ Var.of_string s in
    add env lv fvar ty

  let add_names env lv pp_ty loc =
    Types.monomorphized pp_ty;
    let ty = Types.ty_of_pp loc env.types None pp_ty in
    add env lv Symbols.name ty

  let add_names_lbl env lv pp_ty loc =
    Types.monomorphized pp_ty;
    let ty = Types.ty_of_pp loc env.types None pp_ty in
    let rlv =
      List.fold_left (fun acc (x, lbl) ->
          let lbl = Hstring.make lbl in
          if not (Hstring.equal lbl Hstring.empty) then
            Symbols.add_label lbl (Symbols.name x);
          x::acc
        ) [] lv in
    let lv = List.rev rlv in
    add env lv Symbols.name ty

  let add_logics ?(kind=Other) env mk_symb names pp_profile loc =
    let decl, profile =
      match pp_profile with
      | PPredicate args ->
        let args = List.map (Types.ty_of_pp loc env.types None) args in
        TPredicate args,
        { args = args; result = Ty.Tbool }
      (*| PFunction ([], PPTvarid (_, loc)) ->
          typing_error CannotGeneralize loc*)
      | PFunction(args, res) ->
        let args = List.map (Types.ty_of_pp loc env.types None) args in
        let res = Types.ty_of_pp loc env.types None res in
        TFunction (args, res),
        { args = args; result = res }
    in
    let logics =
      List.fold_left
        (fun logics (n, lbl) ->
           if MString.mem n env.builtins then
             Printer.print_wrn "%a symbol `%s` shadows a builtin symbol"
               Loc.report loc n;

           let sy = mk_symb n in
           if MString.mem n logics then
             Errors.typing_error (SymbAlreadyDefined n) loc;
           let lbl = Hstring.make lbl in
           if not (Hstring.equal lbl Hstring.empty) then
             Symbols.add_label lbl sy;

           MString.add n (sy, profile, kind) logics)
        env.logics names
    in
    decl, { env with logics }

  let add_constr ~record env constr args_ty ty loc =
    let pp_profile = PFunction (args_ty, ty) in
    let kind = if record then RecordConstr else AdtConstr in
    let mk_constr = fun s -> Symbols.constr @@ Uid.of_string s in
    add_logics ~kind env mk_constr [constr, ""] pp_profile loc

  let add_destr ~record env destr pur_ty lbl_ty loc =
    let pp_profile = PFunction ([pur_ty], lbl_ty) in
    let mk_sy s =
      if record then (Symbols.Op (Access (Uid.of_string s)))
      else Symbols.destruct (Uid.of_string s)
    in
    let kind = if record then RecordDestr else AdtDestr in
    add_logics ~kind env mk_sy [destr, ""] pp_profile loc

  let find { var_map = m; _ } n = MString.find n m

  let add_type_decl ?(recursive=false) env vars id body loc =
    let ty, types = Types.add_decl ~recursive env.types vars id body loc in
    ty, { env with types = types; }

  (* returns a type with fresh variables *)
  let fresh_type_or_builtin env n =
    try
      let s, { args = args; result = r}, kind = MString.find n env.logics in
      let args, subst = Ty.fresh_list args Ty.esubst in
      let res, _ = Ty.fresh r subst in
      `Term (s, { args = args; result = res }, kind)
    with Not_found ->
    match MString.find n env.builtins with
    | `Term (s,  { args; result }, kind) ->
      let args, subst = Ty.fresh_list args Ty.esubst in
      let result, _ = Ty.fresh result subst in
      `Term (s, { args ; result }, kind)
    | `Builtin ({ args; result }, f) ->
      let args, subst = Ty.fresh_list args Ty.esubst in
      let result, _ = Ty.fresh result subst in
      `Builtin ({ args; result }, f)
    | exception Not_found -> `Undefined

  let fresh_type env n loc =
    match fresh_type_or_builtin env n with
    | `Term t -> t
    | `Builtin _ | `Undefined -> Errors.typing_error (SymbUndefined n) loc

end

let symbol_of = function
    PPadd -> Symbols.Op Symbols.Plus
  | PPsub -> Symbols.Op Symbols.Minus
  | PPmul -> Symbols.Op Symbols.Mult
  | PPdiv -> Symbols.Op Symbols.Div
  | PPmod ->  Symbols.Op Symbols.Modulo
  | PPpow_int ->  Symbols.Op Symbols.Pow
  | PPpow_real ->  Symbols.Op Symbols.Pow
  | _ -> assert false

let append_type msg ty =
  Format.asprintf "%s %a" msg Ty.print ty

let type_var_desc env p loc =
  try
    let s,t = Env.find env p in
    Options.tool_req 1 (append_type "TR-Typing-Var$_\\Gamma$ type" t);
    TTvar s , t
  with Not_found ->
  match Env.fresh_type env p loc with
  | s,
    { Env.args = []; result = ty},
    (Env.Other | Env.AdtConstr | Env.EnumConstr) ->
    TTapp (s, []) , ty
  | _ -> Errors.typing_error (ShouldBeApply p) loc

let check_no_duplicates =
  let rec aux loc l ss =
    match l with
    | [] -> ()
    | e :: l ->
      if S.mem e ss then Errors.typing_error (ClashParam e) loc;
      aux loc l (S.add e ss)
  in
  fun loc args -> aux loc args S.empty

let filter_patterns pats ty_body _loc =
  let cases =
    List.fold_left
      (fun s {Ty.constr=c; _} -> Uid.Term_set.add c s)
      Uid.Term_set.empty ty_body
  in
  let missing, filtered_pats, dead =
    List.fold_left
      (fun (miss, filtered_pats, dead) ((p, _) as u) ->
         match p with
         | Constr { name; _ } ->
           assert (Uid.Term_set.mem name cases); (* pattern is well typed *)
           if Uid.Term_set.mem name miss then (* not encountered yet *)
             Uid.Term_set.remove name miss, u :: filtered_pats, dead
           else (* case already seen --> dead pattern *)
             miss, pats, p :: dead
         | Var _ ->
           if Uid.Term_set.is_empty miss then
             (* match already exhaussive -> dead case *)
             miss, filtered_pats, p :: dead
           else (* covers all remaining cases, miss becomes empty *)
             Uid.Term_set.empty, u :: filtered_pats, dead
      )(cases, [], []) pats
  in
  missing, List.rev filtered_pats, dead

let check_pattern_matching missing dead loc =
  if not (Uid.Term_set.is_empty missing) then begin
    let missing =
      List.map (fun m -> Hstring.make @@ Uid.show m)
        (Uid.Term_set.elements missing)
    in
    Errors.typing_error (MatchNotExhaustive missing) loc end;
  if dead != [] then
    let dead =
      List.rev_map
        (function
          | Constr { name; _ } -> Uid.show name |> Hstring.make
          | Var v -> Var.to_string v |> Hstring.make
        ) dead
    in
    Printer.print_wrn "%a"
      Errors.report (Typing_error(loc,MatchUnusedCases dead));
    Errors.warning_as_error ()

let mk_adequate_app p s te_args ty logic_kind =
  let hp = Hstring.make p in
  match logic_kind, te_args, ty with
  | (Env.AdtConstr | Env.EnumConstr | Env.Other), _, _ ->
    (* symbol 's' alreadt contains the information *)
    TTapp(s, te_args)

  | Env.RecordConstr, _, Ty.Trecord { Ty.lbs; _ } ->
    let lbs =
      try
        List.map2 (fun (hs, _) e -> Hstring.make @@ Uid.show hs, e) lbs te_args
      with Invalid_argument _ -> assert false
    in
    TTrecord lbs

  | Env.RecordDestr, [te], _ -> TTdot(te, hp)

  | Env.AdtDestr, [te], _ -> TTproject (te, hp)

  | Env.RecordDestr, _, _ -> assert false
  | Env.RecordConstr, _, _ -> assert false
  | Env.AdtDestr, _, _ -> assert false

let fresh_type_app env p loc =
  match Env.fresh_type_or_builtin env p with
  | `Term (s, profile, kind) ->
    profile, fun te_args -> mk_adequate_app p s te_args profile.result kind
  | `Builtin (profile, f) ->
    profile, f
  | `Undefined -> Errors.typing_error (SymbUndefined p) loc

let rec type_term ?(call_from_type_form=false) env f =
  let {pp_loc = loc; pp_desc} = f in
  let e, ty = match pp_desc with
    | PPconst ConstTrue ->
      Options.tool_req 1 (append_type "TR-Typing-Const type" Ty.Tbool);
      TTconst Ttrue, Ty.Tbool
    | PPconst ConstFalse ->
      Options.tool_req 1 (append_type "TR-Typing-Const type" Ty.Tbool);
      TTconst Tfalse, Ty.Tbool
    | PPconst ConstVoid ->
      Options.tool_req 1 (append_type "TR-Typing-Const type" Ty.tunit);
      TTconst Tvoid, Ty.tunit
    | PPconst (ConstInt n) ->
      Options.tool_req 1 (append_type "TR-Typing-Const type" Ty.Tint);
      TTconst(Tint n), Ty.Tint
    | PPconst (ConstReal n) ->
      Options.tool_req 1 (append_type "TR-Typing-Const type" Ty.Treal);
      TTconst(Treal n), Ty.Treal
    | PPconst (ConstBitv n) ->
      Options.tool_req 1
        (append_type "TR-Typing-Const type" (Ty.Tbitv (String.length n)));
      TTconst(Tbitv n), Ty.Tbitv (String.length n)
    | PPvar p ->
      type_var_desc env p loc

    | PPapp(p,args) ->
      begin
        let te_args = List.map (type_term env) args in
        let lt_args = List.map (
            fun { c = { tt_ty = t; _ }; _ } -> t
          ) te_args in
        let Env.{args = lt; result = t}, mk_app = fresh_type_app env p loc in
        try
          List.iter2 Ty.unify lt lt_args;
          Options.tool_req 1 (append_type "TR-Typing-App type" t);
          mk_app te_args, t
        with
        | Ty.TypeClash(t1,t2) -> Errors.typing_error (Unification(t1,t2)) loc
        | Invalid_argument _ -> Errors.typing_error (WrongNumberofArgs p) loc
      end

    | PPinfix(t1,(PPadd | PPsub | PPmul | PPdiv as op),t2) ->
      begin
        let s = symbol_of op in
        let te1 = type_term env t1 in
        let te2 = type_term env t2 in
        let ty1 = Ty.shorten te1.c.tt_ty in
        let ty2 = Ty.shorten te2.c.tt_ty in
        match ty1, ty2 with
        | Ty.Tint, Ty.Tint ->
          Options.tool_req 1 (append_type "TR-Typing-OpBin type" ty1);
          TTinfix(te1,s,te2) , ty1
        | Ty.Treal, Ty.Treal ->
          Options.tool_req 1 (append_type "TR-Typing-OpBin type" ty2);
          TTinfix(te1,s,te2), ty2
        | Ty.Tint, _ ->
          Errors.typing_error (ShouldHaveType(ty2,Ty.Tint)) t2.pp_loc
        | Ty.Treal, _ ->
          Errors.typing_error (ShouldHaveType(ty2,Ty.Treal)) t2.pp_loc
        | _ ->
          Errors.typing_error (ShouldHaveTypeIntorReal ty1) t1.pp_loc
      end
    | PPinfix(t1, PPmod, t2) ->
      begin
        let s = symbol_of PPmod in
        let te1 = type_term env t1 in
        let te2 = type_term env t2 in
        let ty1 = Ty.shorten te1.c.tt_ty in
        let ty2 = Ty.shorten te2.c.tt_ty in
        match ty1, ty2 with
        | Ty.Tint, Ty.Tint ->
          Options.tool_req 1 (append_type "TR-Typing-OpMod type" ty1);
          TTinfix(te1,s,te2) , ty1
        | _ -> Errors.typing_error (ShouldHaveTypeInt ty1) t1.pp_loc
      end
    | PPinfix(t1, (PPpow_int | PPpow_real as op), t2) ->
      begin
        let s = symbol_of op in
        let te1 = type_term env t1 in
        let te2 = type_term env t2 in
        let ty1 = Ty.shorten te1.c.tt_ty in
        let ty2 = Ty.shorten te2.c.tt_ty in
        match ty1, ty2, op with
        | Ty.Tint, Ty.Tint, PPpow_int ->
          Options.tool_req 1 (append_type "TR-Typing-Oppow_int type" ty1);
          TTinfix(te1,s,te2) , Ty.Tint

        | (Ty.Tint | Ty.Treal), (Ty.Tint | Ty.Treal), PPpow_real ->
          Options.tool_req 1 (append_type "TR-Typing-Oppow_real type" ty1);
          TTinfix(te1,s,te2) , Ty.Treal

        | Ty.Treal , _, PPpow_int ->
          Errors.typing_error (ShouldHaveTypeInt Ty.Tint) t1.pp_loc
        | _, Ty.Treal, PPpow_int ->
          Errors.typing_error (ShouldHaveTypeInt Ty.Tint) t2.pp_loc

        | _, _, PPpow_real ->
          Errors.typing_error (ShouldHaveTypeInt Ty.Treal) t1.pp_loc
        | _, _, PPpow_int ->
          Errors.typing_error (ShouldHaveTypeInt Ty.Tint) t1.pp_loc

        | _ -> assert false (* can't happen *)
      end
    | PPprefix(PPneg, { pp_desc=PPconst (ConstInt n); _ }) ->
      Options.tool_req 1 (append_type "TR-Typing-OpUnarith type" Ty.Tint);
      TTconst(Tint ("-"^n)), Ty.Tint
    | PPprefix(PPneg, { pp_desc=PPconst (ConstReal n); _ }) ->
      Options.tool_req 1 (append_type "TR-Typing-OpUnarith type" Ty.Treal);
      TTconst(Treal (Numbers.Q.minus n)), Ty.Treal
    | PPprefix(PPneg, e) ->
      let te = type_term env e in
      let ty = Ty.shorten te.c.tt_ty in
      if ty!=Ty.Tint && ty!=Ty.Treal then
        Errors.typing_error (ShouldHaveTypeIntorReal ty) e.pp_loc;
      Options.tool_req 1 (append_type "TR-Typing-OpUnarith type" ty);
      TTprefix(Symbols.Op Symbols.Minus, te), ty
    | PPconcat(t1, t2) ->
      begin
        let te1 = type_term env t1 in
        let te2 = type_term env t2 in
        let ty1 = Ty.shorten te1.c.tt_ty in
        let ty2 = Ty.shorten te2.c.tt_ty in
        match ty1, ty2 with
        | Ty.Tbitv n , Ty.Tbitv m ->
          Options.tool_req 1
            (append_type "TR-Typing-OpConcat type" (Ty.Tbitv (n+m)));
          TTconcat(te1, te2), Ty.Tbitv (n+m)
        | Ty.Tbitv _ , _ ->
          Errors.typing_error (ShouldHaveTypeBitv ty2) t2.pp_loc
        | _ , Ty.Tbitv _ ->
          Errors.typing_error (ShouldHaveTypeBitv ty1) t1.pp_loc
        | _ ->
          Errors.typing_error (ShouldHaveTypeBitv ty1) t1.pp_loc
      end
    | PPextract(e, i, j) ->
      begin
        let te = type_term env e in
        let tye = Ty.shorten te.c.tt_ty in
        match tye with
        | Ty.Tbitv n ->
          if i>j then Errors.typing_error (BitvExtract(i,j)) loc;
          if j>=n then Errors.typing_error (BitvExtractRange(n,j) ) loc;
          Options.tool_req 1
            (append_type "TR-Typing-OpExtract type" (Ty.Tbitv (j-i+1)));
          TTextract(te, i, j), Ty.Tbitv (j-i+1)
        | _ ->
          Errors.typing_error (ShouldHaveType(tye,Ty.Tbitv (j+1))) loc
      end
    | PPget (t1, t2) ->
      begin
        let te1 = type_term env t1 in
        let te2 = type_term env t2 in
        let tyarray = Ty.shorten te1.c.tt_ty in
        let tykey2 = Ty.shorten te2.c.tt_ty in
        match tyarray with
        | Ty.Tfarray (tykey,tyval) ->
          begin
            try
              Ty.unify tykey tykey2;
              Options.tool_req 1 (append_type "TR-Typing-OpGet type" tyval);
              TTget(te1, te2), tyval
            with
            | Ty.TypeClash(t1,t2) ->
              Errors.typing_error (Unification(t1,t2)) loc
          end
        | _ -> Errors.typing_error ShouldHaveTypeArray t1.pp_loc
      end
    | PPset (t1, t2, t3) ->
      begin
        let te1 = type_term env t1 in
        let te2 = type_term env t2 in
        let te3 = type_term env t3 in
        let ty1 = Ty.shorten te1.c.tt_ty in
        let tykey2 = Ty.shorten te2.c.tt_ty in
        let tyval2 = Ty.shorten te3.c.tt_ty in
        try
          match ty1 with
          | Ty.Tfarray (tykey,tyval) ->
            Ty.unify tykey tykey2;Ty.unify tyval tyval2;
            Options.tool_req 1 (append_type "TR-Typing-OpSet type" ty1);
            TTset(te1, te2, te3), ty1
          | _ -> Errors.typing_error ShouldHaveTypeArray t1.pp_loc
        with
        | Ty.TypeClash(t, t') -> Errors.typing_error (Unification(t, t')) loc
      end
    | PPif(cond,t2,t3) ->
      begin
        let cond = type_form env cond in
        (* TODO : should use _fv somewhere ? *)
        let te2 = type_term env t2 in
        let te3 = type_term env t3 in
        let ty2 = Ty.shorten te2.c.tt_ty in
        let ty3 = Ty.shorten te3.c.tt_ty in
        begin
          try Ty.unify ty2 ty3
          with Ty.TypeClash _ ->
            Errors.typing_error (ShouldHaveType(ty3,ty2)) t3.pp_loc;
        end;
        Options.tool_req 1 (append_type "TR-Typing-Ite type" ty2);
        TTite (cond, te2, te3) , ty2
      end
    | PPdot(t, a) ->
      begin
        let te = type_term env t in
        let ty = Ty.shorten te.c.tt_ty in
        match ty with
        | Ty.Trecord { Ty.name = g; lbs; _ } ->
          begin
            try
              TTdot(te, Hstring.make a),
              My_list.assoc Uid.equal (Uid.of_string a) lbs
            with Not_found ->
              let g = Uid.show g in
              Errors.typing_error (ShouldHaveLabel(g,a)) t.pp_loc
          end
        | _ -> Errors.typing_error (ShouldHaveTypeRecord ty) t.pp_loc
      end
    | PPrecord lbs ->
      begin
        let lbs =
          List.map (fun (lb, t) -> Hstring.make lb, type_term env t) lbs in
        let lbs = List.sort
            (fun (l1, _) (l2, _) -> Hstring.compare l1 l2) lbs in
        let fake_lbs =
          List.map (fun (lb, ty) -> Uid.of_hstring lb, ty) lbs
        in
        let ty = Types.from_labels env.Env.types fake_lbs loc in
        let ty, _ = Ty.fresh (Ty.shorten ty) Ty.esubst in
        match ty with
        | Ty.Trecord { Ty.lbs=ty_lbs; _ } ->
          begin
            try
              let lbs =
                List.map2
                  (fun (_, te) (lb,ty_lb)->
                     Ty.unify te.c.tt_ty ty_lb;
                     Hstring.make @@ Uid.show lb, te) lbs ty_lbs
              in
              TTrecord(lbs), ty
            with Ty.TypeClash(t1,t2) ->
              Errors.typing_error (Unification(t1,t2)) loc
          end
        | _ -> Errors.typing_error ShouldBeARecord loc
      end
    | PPwith(e, lbs) ->
      begin
        let te = type_term env e in
        let lbs =
          List.map
            (fun (lb, t) -> Hstring.make lb, (type_term env t, t.pp_loc)) lbs in
        let ty = Ty.shorten te.c.tt_ty in
        match ty with
        | Ty.Trecord { Ty.lbs = ty_lbs; _ } ->
          let ty_lbs =
            List.map (fun (uid, ty) -> Hstring.make @@ Uid.show uid, ty) ty_lbs
          in
          let nlbs =
            List.map
              (fun (lb, ty_lb) ->
                 try
                   let v, _ = Hstring.list_assoc lb lbs in
                   Ty.unify ty_lb v.c.tt_ty;
                   lb, v
                 with
                 | Not_found ->
                   lb, {c = { tt_desc = TTdot(te, lb); tt_ty = ty_lb};
                        annot = te.annot }
                 | Ty.TypeClash(t1,t2) ->
                   Errors.typing_error (Unification(t1,t2)) loc
              ) ty_lbs
          in
          List.iter
            (fun (lb, _) ->
               try ignore (Hstring.list_assoc lb ty_lbs)
               with Not_found ->
                 Errors.typing_error (NoLabelInType(lb, ty)) loc) lbs;
          TTrecord(nlbs), ty
        | _ ->  Errors.typing_error ShouldBeARecord loc
      end
    | PPlet(l, t2) ->
      let _ =
        List.fold_left (fun z (sy,_) ->
            if Util.SS.mem sy z then
              Errors.typing_error (DuplicatePattern sy) loc;
            Util.SS.add sy z
          )Util.SS.empty l
      in
      let rev_l = List.rev_map (fun (sy, t) -> sy, type_term env t) l in
      let env =
        List.fold_left
          (fun env (sy, te1) ->
             let ty1 = Ty.shorten te1.c.tt_ty in
             let fvar s = Symbols.var @@ Var.of_string s in
             Env.add env [sy] fvar ty1
          )env rev_l
      in
      let te2 = type_term env t2 in
      let ty2 = Ty.shorten te2.c.tt_ty in
      let l = List.rev_map (fun (sy, t) -> fst (Env.find env sy), t) rev_l in
      Options.tool_req 1 (append_type "TR-Typing-Let type" ty2);
      TTlet(l, te2), ty2

    (* | PPnamed(lbl, t) ->  *)
    (*     let te = type_term env t in *)
    (*     te.c.tt_desc, te.c.tt_ty *)

    | PPnamed (lbl, t) ->
      let te = type_term env t in
      let ty = Ty.shorten te.c.tt_ty in
      let lbl = Hstring.make lbl in
      TTnamed (lbl, te), ty

    | PPcast (t,ty) ->
      let ty = Types.ty_of_pp loc env.Env.types None ty in
      let te = type_term env t in
      begin try
          Ty.unify te.c.tt_ty ty;
          te.c.tt_desc, Ty.shorten te.c.tt_ty
        with
        | Ty.TypeClash(t1,t2) -> Errors.typing_error (Unification(t1,t2)) loc
      end

    | PPproject (t, lbl) ->
      let te = type_term env t in
      begin
        try
          match Env.fresh_type env lbl loc with
          | _, {Env.args = [arg] ; result}, Env.AdtDestr ->
            Ty.unify te.c.tt_ty arg;
            TTproject (te, Hstring.make lbl), Ty.shorten result

          | _, {Env.args = [arg] ; result}, Env.RecordDestr ->
            Ty.unify te.c.tt_ty arg;
            TTdot (te, Hstring.make lbl), Ty.shorten result
          | _ -> assert false
        with Ty.TypeClash(t1,t2) ->
          Errors.typing_error (Unification(t1,t2)) loc
      end

    | PPmatch (e, pats) ->
      (* we can match on ADTs including records and enumerations *)
      let e = type_term env e in
      let ty = Ty.shorten e.c.tt_ty in
      let ty_body = match ty with
        | Ty.Tadt (name, params) -> Ty.type_body name params
        | Ty.Trecord { Ty.record_constr; lbs; _ } ->
          [{Ty.constr = record_constr; destrs = lbs}]
        | _ -> Errors.typing_error (ShouldBeADT ty) loc
      in
      let pats =
        List.rev @@
        List.rev_map
          (fun (p, v) ->
             let p, env = type_pattern p env ty ty_body in
             p, type_term env v
          ) pats
      in
      let missing, filtered_pats, dead = filter_patterns pats ty_body loc in
      check_pattern_matching missing dead loc;
      let ty =
        match filtered_pats with
        | [] -> assert false
        | (_, e) :: l ->
          let ty = e.c.tt_ty in
          List.iter
            (fun (_, e) ->
               Ty.unify ty e.c.tt_ty;
               if not (Ty.equal ty e.c.tt_ty) then
                 Errors.typing_error (ShouldHaveType(e.c.tt_ty, ty)) loc
            )l;
          ty
      in
      TTmatch (e, filtered_pats), ty
    | _ ->
      if call_from_type_form then Errors.typing_error SyntaxError loc;
      TTform (type_form env f), Ty.Tbool
  in
  {c = { tt_desc = e ; tt_ty = Ty.shorten ty }; annot = new_id ()}


and join_forall f = match f.pp_desc with
  | PPforall(vs_ty, trs1, hyp1, f) ->
    let tyvars,trs2,hyp2, f = join_forall f in
    vs_ty @ tyvars , trs1@trs2 , hyp1@hyp2, f
  | PPforall_named (named_vs_ty, trs1, hyp1, f) ->
    let vs_ty = List.map (fun (v, _, ty) -> v, ty) named_vs_ty in
    join_forall {f with pp_desc = PPforall (vs_ty, trs1, hyp1, f)}
  | PPnamed(_, f) ->
    join_forall f
  | _ -> [] , [] , [], f

and join_exists f = match f.pp_desc with
  | PPexists (vs_ty, trs1, hyp1, f) ->
    let tyvars,trs2, hyp2,f = join_exists f in
    vs_ty @ tyvars , trs1@trs2, hyp1@hyp2,  f
  | PPexists_named (named_vs_ty, trs1, hyp1, f) ->
    let vs_ty = List.map (fun (v, _, ty) -> v, ty) named_vs_ty in
    join_exists {f with pp_desc = PPexists (vs_ty, trs1, hyp1, f)}
  | PPnamed (_, f) -> join_exists f
  | _ -> [] , [] , [], f


and type_bound env bnd ty ~is_open ~is_lower =
  let bk, ty_x = match bnd.pp_desc with
    | PPvar s ->
      assert (String.length s > 0);
      begin match s.[0] with
        | '?' ->
          let sy =
            if String.length s = 1 then
              Symbols.Unbounded
            else
              Symbols.VarBnd (Var.local s)
          in
          sy, ty
        | _ ->
          let vx, ty_x = type_var_desc env s bnd.pp_loc in
          let var_x =
            match vx with TTvar Symbols.Var vx -> vx | _ -> assert false
          in
          Symbols.VarBnd var_x, ty_x
      end
    | PPconst num ->
      let ty_x, q =
        try match num with
          | ConstInt s  ->
            Ty.Tint, Numbers.Q.from_string s
          | ConstReal s ->
            Ty.Treal, s
          | _ -> assert false
        with _ -> assert false (*numbers well constructed with regular exprs*)
      in
      Symbols.ValBnd q, ty_x
    | _ -> assert false
  in
  if not (Ty.equal ty ty_x) then
    Errors.typing_error (ShouldHaveType(ty, ty_x)) bnd.pp_loc;
  Symbols.mk_bound bk ty ~is_open ~is_lower

and mk_ta_eq t1 t2 =
  let c =
    if t1.c.tt_ty != Ty.Tbool then TAeq [t1; t2]
    else
      match t1.c.tt_desc, t2.c.tt_desc with
      | TTconst Ttrue, _  -> TApred (t2, false)
      | _, TTconst Ttrue  -> TApred (t1, false)
      | TTconst Tfalse, _ -> TApred (t2, true)
      | _, TTconst Tfalse -> TApred (t1, true)
      | _ -> TAeq [t1; t2]
  in
  {c ; annot=new_id ()}

and mk_ta_neq t1 t2 =
  let c =
    if t1.c.tt_ty != Ty.Tbool then TAneq [t1; t2]
    else
      match t1.c.tt_desc, t2.c.tt_desc with
      | TTconst Ttrue, _  -> TApred (t2, true)
      | _, TTconst Ttrue  -> TApred (t1, true)
      | TTconst Tfalse, _ -> TApred (t2, false)
      | _, TTconst Tfalse -> TApred (t1, false)
      | _ -> TAneq [t1; t2]
  in
  {c ; annot=new_id ()}

and type_form ?(in_theory=false) env f =
  let rec type_pp_desc pp_desc = match pp_desc with
    | PPconst ConstTrue ->
      Options.tool_req 1 "TR-Typing-True$_F$";
      TFatom {c=TAtrue; annot=new_id ()}
    | PPconst ConstFalse ->
      Options.tool_req 1 "TR-Typing-False$_F$";
      TFatom {c=TAfalse; annot=new_id ()}
    | PPvar p ->
      Options.tool_req 1 "TR-Typing-Var$_F$";
      let res =
        try
          (* allow type cast bool to predicate in some simple situations *)
          let s, ty = Env.find env p in
          Options.tool_req 1 (append_type "TR-Typing-Var$_\\Gamma$ type" ty);
          s, { Env.args = []; result = ty}
        with Not_found ->
          let s, p, kd = Env.fresh_type env p f.pp_loc in
          assert (kd == Env.Other);
          s, p
      in
      let r =
        match res with
        | s, { Env.args = []; result = Ty.Tbool} ->
          let t2 = {c = {tt_desc=TTconst Ttrue;tt_ty=Ty.Tbool};
                    annot = new_id ()} in
          let t1 = {c = {tt_desc=TTvar s; tt_ty=Ty.Tbool};
                    annot = new_id ()} in
          TFatom (mk_ta_eq t1 t2)
        | _ -> Errors.typing_error (NotAPropVar p) f.pp_loc
      in
      r

    | PPapp(p,args ) ->
      Options.tool_req 1 "TR-Typing-App$_F$";
      let te_args = List.map (type_term env) args in
      let lt_args =  List.map (fun { c = { tt_ty = t; _}; _ } -> t) te_args in
      let { Env.args = lt; result }, mk_app = fresh_type_app env p f.pp_loc in
      begin
        try
          if result != Ty.Tbool then (* consider polymorphic functions *)
            Ty.unify result Ty.Tbool;
          try
            List.iter2 Ty.unify lt lt_args;
            let app = mk_app te_args in
            let r =
              let t1 = {
                c = {tt_desc=app; tt_ty=Ty.Tbool};
                annot=new_id (); }
              in
              TFatom { c = TApred (t1, false); annot=new_id () }
            in
            r
          with
          | Ty.TypeClash(t1,t2) ->
            Errors.typing_error (Unification(t1,t2)) f.pp_loc
          | Invalid_argument _ ->
            Errors.typing_error (WrongNumberofArgs p) f.pp_loc
        with Ty.TypeClash _ -> Errors.typing_error (NotAPredicate p) f.pp_loc
      end

    | PPdistinct (args) ->
      Options.tool_req 1 "TR-Typing-Distinct$_F$";
      let r =
        begin
          let te_args = List.map (type_term env) args in
          let lt_args =  List.map (
              fun { c = { tt_ty = t; _ }; _ } -> t
            ) te_args in
          try
            let t = match lt_args with
              | t::_ -> t
              | [] ->
                Errors.typing_error (WrongNumberofArgs "distinct") f.pp_loc
            in
            List.iter (Ty.unify t) lt_args;
            TFatom { c = TAdistinct te_args; annot=new_id () }
          with
          | Ty.TypeClash(t1,t2) ->
            Errors.typing_error (Unification(t1,t2)) f.pp_loc
        end
      in r

    | PPinfix
        ({ pp_desc = PPinfix (_, (PPlt|PPle|PPgt|PPge|PPeq|PPneq), a); _ } as p,
         (PPlt | PPle | PPgt | PPge | PPeq | PPneq as r), b) ->
      Options.tool_req 1 "TR-Typing-OpComp$_F$";
      let r =
        let q = { pp_desc = PPinfix (a, r, b); pp_loc = f.pp_loc } in
        let f1 = type_form env p in
        let f2 = type_form env q in
        TFop(OPand, [f1;f2])
      in r
    | PPinfix(t1, (PPeq | PPneq as op), t2) ->
      Options.tool_req 1 "TR-Typing-OpBin$_F$";
      let r =
        let tt1 = type_term env t1 in
        let tt2 = type_term env t2 in
        try
          Ty.unify tt1.c.tt_ty tt2.c.tt_ty;
          match op with
          | PPeq -> TFatom (mk_ta_eq tt1 tt2)
          | PPneq -> TFatom (mk_ta_neq tt1 tt2)
          | _ -> assert false
        with Ty.TypeClash(t1,t2) ->
          Errors.typing_error (Unification(t1,t2)) f.pp_loc
      in r
    | PPinfix(t1, (PPlt | PPgt | PPge | PPle as op), t2) ->
      Options.tool_req 1 "TR-Typing-OpComp$_F$";
      let r =
        let tt1 = type_term env t1 in
        let tt2 = type_term env t2 in
        try
          Ty.unify tt1.c.tt_ty tt2.c.tt_ty;
          let ty = Ty.shorten tt1.c.tt_ty in
          match ty with
          | Ty.Tint | Ty.Treal ->
            let top =
              match op with
              | PPlt -> TAlt [tt1; tt2]
              | PPgt -> TAlt [tt2; tt1]
              | PPle -> TAle [tt1; tt2]
              | PPge -> TAle [tt2; tt1]
              | PPeq -> TAeq [tt1; tt2]
              | PPneq -> TAneq [tt1; tt2]
              | _ -> assert false
            in
            TFatom {c = top; annot=new_id ()}
          | _ -> Errors.typing_error (ShouldHaveTypeIntorReal ty) t1.pp_loc
        with Ty.TypeClash(t1,t2) ->
          Errors.typing_error (Unification(t1,t2)) f.pp_loc
      in r

    | PPisConstr (t,lbl) ->
      let tt = type_term env t in
      let _s, {Env.args = _lt; result}, kind =
        Env.fresh_type env lbl f.pp_loc in
      begin
        try
          Ty.unify tt.c.tt_ty result;
          let result = Ty.shorten result in
          match kind with
          | Env.AdtConstr ->
            let top = TTisConstr (tt, Hstring.make lbl) in
            let r = TFatom { c = top; annot = new_id () } in
            r
          | Env.EnumConstr ->
            let tt_desc, tt_ty = type_var_desc env lbl f.pp_loc in
            let rhs = { c = { tt_desc; tt_ty }; annot = new_id () } in
            TFatom (mk_ta_eq tt rhs)
          | _ ->
            begin match result with
              | Ty.Trecord _ ->
                (* The typechecker allows only testers whose the
                   two arguments have the same type. Thus, we can always
                   replace the tester of a record by the true literal. *)
                TFatom { c = TAtrue; annot = new_id () }
              | _ ->
                Errors.typing_error (NotAdtConstr (lbl, result)) f.pp_loc
            end
        with Ty.TypeClash(t1,t2) ->
          Errors.typing_error (Unification(t1,t2)) f.pp_loc
      end

    | PPinfix(f1,op ,f2) ->
      Options.tool_req 1 "TR-Typing-OpConnectors$_F$";
      begin
        let f1 = type_form env f1 in
        let f2 = type_form env f2 in
        (match op with
         | PPand ->
           TFop(OPand,[f1;f2])
         | PPor -> TFop(OPor,[f1;f2])
         | PPxor -> TFop(OPxor,[f1;f2])
         | PPimplies -> TFop(OPimp,[f1;f2])
         | PPiff -> TFop(OPiff,[f1;f2])
         | _ -> assert false)
      end
    | PPprefix(PPnot,f) ->
      Options.tool_req 1 "TR-Typing-OpNot$_F$";
      let f = type_form env f in
      TFop(OPnot,[f])
    | PPif(f1,f2,f3) ->
      Options.tool_req 1 "TR-Typing-Ite$_F$";
      let f1 = type_form env f1 in
      let f2 = type_form env f2 in
      let f3 = type_form env f3 in
      TFop(OPif, [f1; f2;f3])
    | PPnamed(lbl,f) ->
      let f = type_form env f in
      let lbl = Hstring.make lbl in
      TFnamed(lbl, f)
    | PPforall _ | PPexists _ ->
      let ty_vars, triggers, hyp, f' =
        match pp_desc with
        | PPforall(vs_ty,triggers,hyp,f') ->
          let ty_vars, triggers', hyp', f' = join_forall f' in
          vs_ty @ ty_vars, triggers@triggers', hyp @ hyp', f'
        | PPexists(vs_ty,triggers,hyp,f') ->
          let ty_vars, triggers', hyp', f' = join_exists f' in
          vs_ty @ ty_vars, triggers@triggers', hyp @ hyp', f'
        | _ -> assert false
      in
      let env' =
        List.fold_left
          (fun env (v, pp_ty) ->
             Env.add_var env [v] pp_ty f.pp_loc) env ty_vars in
      let f' = type_form env' f' in
      let ty_triggers =
        List.map (fun (tr, b) -> type_trigger in_theory env' tr, b) triggers in
      let qf_hyp = List.map (fun h -> type_form env' h) hyp in
      let bvars =
        List.fold_left
          (fun acc (v,_) ->
             let ty = Env.find env' v in
             ty :: acc) [] ty_vars
      in
      let qf_form = {
        qf_bvars = bvars ;
        qf_triggers = ty_triggers ;
        qf_hyp = qf_hyp;
        qf_form = f'}
      in
      (match pp_desc with
       | PPforall _ ->
         Options.tool_req 1 "TR-Typing-Forall$_F$";
         TFforall qf_form
       | PPexists _ ->
         Options.tool_req 1 "TR-Typing-Exists$_F$";
         TFexists qf_form
       | _ -> assert false)
    | PPlet (binders,f) ->
      Options.tool_req 1 "TR-Typing-Let$_F$";
      let _ =
        List.fold_left (fun z (sy,_) ->
            if Util.SS.mem sy z then
              Errors.typing_error (DuplicatePattern sy) f.pp_loc;
            Util.SS.add sy z
          )Util.SS.empty binders
      in
      let binders =
        List.fold_left
          (fun (binders) (sy, e) ->
             let xx, tty =
               try
                 (* try to type e as a term *)
                 let { c = { tt_ty = ttype; _ }; _} as tt = type_term env e in
                 TletTerm tt, ttype
               with _ ->
                 (* try to type e as a form *)
                 let fzz = type_form env e in
                 TletForm fzz, Ty.Tbool
             in
             (sy, Var.of_string sy, xx, tty):: binders
          )[] binders
      in
      let env =
        List.fold_left
          (fun env (v, sv, _, ty) ->
             {env with Env.var_map =
                         MString.add v (Symbols.var sv, ty) env.Env.var_map}
          ) env binders
      in
      let f = type_form env f in
      let binders =
        List.fold_left
          (fun binders (_,sv,e,_) -> (sv, e) :: binders)
          [] binders
      in
      TFlet (binders, f)

    (* Remove labels : *)
    | PPforall_named (vs_tys, trs, hyp, f) ->
      let vs_tys = List.map (fun (v, _, ty) -> v, ty) vs_tys in
      type_pp_desc (PPforall (vs_tys, trs, hyp, f))
    | PPexists_named (vs_tys, trs, hyp, f) ->
      let vs_tys = List.map (fun (v, _, ty) -> v, ty) vs_tys in
      type_pp_desc (PPexists (vs_tys, trs, hyp, f))

    | PPcheck _ | PPcut _ -> assert false

    | PPmatch (e, pats) ->
      let e = type_term env e in
      let ty = e.c.tt_ty in
      let ty_body = match ty with
        | Ty.Tadt (name, params) -> Ty.type_body name params
        | Ty.Trecord { Ty.record_constr; lbs; _ } ->
          [{Ty.constr = record_constr ; destrs = lbs}]

        | _ ->
          Errors.typing_error (ShouldBeADT ty) f.pp_loc
      in
      let pats =
        List.rev @@
        List.rev_map
          (fun (p, v) ->
             let p, env = type_pattern p env ty ty_body in
             p, type_form env v
          ) pats
      in
      let missing, filtered_pats, dead =
        filter_patterns pats ty_body f.pp_loc
      in
      check_pattern_matching missing dead f.pp_loc;
      TFmatch (e, filtered_pats)

    | _ ->
      let te1 = type_term env f in
      let ty = te1.c.tt_ty in
      match ty with
      | Ty.Tbool ->
        let te2 = {c = {tt_desc=TTconst Ttrue;tt_ty=Ty.Tbool};
                   annot = new_id ()}
        in
        TFatom (mk_ta_eq te1 te2)
      | _ -> Errors.typing_error ShouldHaveTypeProp f.pp_loc
  in
  let form = type_pp_desc f.pp_desc in
  {c = form; annot = new_id ()}

and type_pattern p env ty ty_body =
  let {pat_loc ; pat_desc = (f, args) } = p in
  check_no_duplicates pat_loc args;
  let hf = Hstring.make f in
  try
    let prof = Ty.assoc_destrs (Uid.of_hstring hf) ty_body in
    let env =
      try
        List.fold_left2
          (fun env v (_, ty) -> Env.add_ty_var env [v] ty) env args prof
      with
        Invalid_argument _ ->
        Errors.typing_error (WrongNumberofArgs f) pat_loc
    in
    let args =
      List.map2
        (fun v (destr, _) ->
           let tv, ty = type_var_desc env v pat_loc in
           let var_v =
             match tv with TTvar Symbols.Var vx -> vx | _ -> assert false
           in
           var_v, destr, ty
        )args prof
    in
    Constr { name = Uid.of_hstring hf ; args = args }, env
  with Not_found ->
    if args != [] then Errors.typing_error (NotAdtConstr (f, ty)) pat_loc;
    let env = Env.add_ty_var env [f] ty in
    let tv, _ = type_var_desc env f pat_loc in
    let var_f =
      match tv with TTvar Symbols.Var vx -> vx | _ -> assert false
    in
    Var var_f, env

and type_trigger in_theory env l =
  List.map
    (fun t ->
       match in_theory, t.pp_desc with
       | false, PPinInterval _ ->
         Errors.typing_error ThSemTriggerError t.pp_loc
       | false, PPmapsTo _ ->
         Errors.typing_error ThSemTriggerError t.pp_loc
       | true, PPinInterval (e, a,b, c, d) ->
         let te = type_term env e in
         let tt_ty = te.c.tt_ty in
         let tb = type_bound env b tt_ty ~is_open:a ~is_lower:true in
         let tc = type_bound env c tt_ty ~is_open:d ~is_lower:false in
         { c = { tt_desc = TTinInterval(te, tb , tc) ; tt_ty = Ty.Tbool};
           annot = new_id ()}

       | true, PPmapsTo (x, e) ->
         let vx, ty_x = type_var_desc env x t.pp_loc in
         let hs_x =
           match vx with TTvar Symbols.Var hs -> hs | _ -> assert false
         in
         let te = type_term env e in
         let tt_ty = te.c.tt_ty in
         if not (Ty.equal tt_ty ty_x) then
           Errors.typing_error (ShouldHaveType(ty_x,tt_ty)) t.pp_loc;
         { c = { tt_desc = TTmapsTo(hs_x, te) ; tt_ty = Ty.Tbool};
           annot = new_id ()}

       | _ ->
         try type_term env t
         with Errors.Error _ ->
           ignore (type_form env t);
           if Options.get_verbose () then
             Printer.print_dbg
               ~module_name:"Typechecker" ~function_name:"type_trigger"
               "%a The given trigger is not a term and is ignored"
               Loc.report t.pp_loc;
           (* hack to typecheck *)
           type_term env {t with pp_desc = PPconst ConstVoid}
    )l

let make_rules loc f = match f.c with
  | TFforall { qf_bvars = vars;
               qf_form = { c = TFatom { c = TAeq [t1; t2]; _ }; _ }; _ } ->
    {rwt_vars = vars; rwt_left = t1; rwt_right = t2}
  | TFatom { c = TAeq [t1; t2]; _} ->
    {rwt_vars = []; rwt_left = t1; rwt_right = t2}
  | _ -> Errors.typing_error SyntaxError loc


let fresh_var =
  let cpt = ref 0 in
  fun x -> incr cpt; ("_"^x^(string_of_int !cpt))

let rec no_alpha_renaming_b ((up, m) as s) f =
  match f.pp_desc with
  | PPvar x ->
    (try
       let y = MString.find x m in
       assert (String.compare x y <> 0);
       raise Exit
     with Not_found -> ())

  | PPmapsTo(x, e) ->
    (try
       let y = MString.find x m in
       assert (String.compare x y <> 0);
       raise Exit
     with Not_found -> ());
    no_alpha_renaming_b s e

  | PPapp(_, l) ->
    List.iter (no_alpha_renaming_b s) l

  | PPinInterval(e, _,_,_,_) ->
    no_alpha_renaming_b s e

  | PPdistinct l ->
    List.iter (no_alpha_renaming_b s) l

  | PPconst _ -> ()

  | PPinfix(f1, _, f2) ->
    no_alpha_renaming_b s f1; no_alpha_renaming_b s f2

  | PPprefix(_, f1) ->
    no_alpha_renaming_b s f1

  | PPget(f1,f2) ->
    no_alpha_renaming_b s f1; no_alpha_renaming_b s f2


  | PPset(f1, f2, f3) ->
    no_alpha_renaming_b s f1;
    no_alpha_renaming_b s f2;
    no_alpha_renaming_b s f3


  | PPextract(f1, _, _) ->
    no_alpha_renaming_b s f1

  | PPconcat(f1, f2) ->
    no_alpha_renaming_b s f1; no_alpha_renaming_b s f2

  | PPif(f1, f2, f3) ->
    no_alpha_renaming_b s f1;
    no_alpha_renaming_b s f2;
    no_alpha_renaming_b s f3

  | PPnamed(_, f1) ->
    no_alpha_renaming_b s f1

  | PPdot(f1, _) ->
    no_alpha_renaming_b s f1

  | PPrecord l ->
    List.iter (fun (_,e) -> no_alpha_renaming_b s e) l

  | PPwith(e, l) ->
    List.iter (fun (_,e) -> no_alpha_renaming_b s e) l;
    no_alpha_renaming_b s e

  | PPlet(l, f2) ->
    let _ =
      List.fold_left (fun z (sy,_) ->
          if Util.SS.mem sy z then
            Errors.typing_error (DuplicatePattern sy) f.pp_loc;
          Util.SS.add sy z
        )Util.SS.empty l
    in
    List.iter (fun (_, f) -> no_alpha_renaming_b s f) l;
    let s =
      List.fold_left
        (fun (up, m) (x, _) ->
           if S.mem x up then
             let nx = fresh_var x in
             let m = MString.add x nx m in
             (S.add nx up, m)
           else (S.add x up, m)
        )(up, m) l
    in
    no_alpha_renaming_b s f2

  | PPcheck f' ->
    no_alpha_renaming_b s f'

  | PPcut f' ->
    no_alpha_renaming_b s f'

  | PPcast (f',_) ->
    no_alpha_renaming_b s f'

  | PPforall(xs, trs, hyp, f1) ->
    let xs1, xs2 = List.partition (fun (x, _) -> S.mem x up) xs in
    let nv = List.map (fun (x, ty) -> fresh_var x, ty) xs1 in
    let m = List.fold_left2
        (fun m (x, _) (nx, _) -> MString.add x nx m) m xs1 nv in
    let xs = nv @ xs2 in
    let up = List.fold_left (fun up (x, _) -> S.add x up) up xs in
    let s = (up, m) in
    List.iter (no_alpha_renaming_b s) hyp;
    no_alpha_renaming_b s f1;
    List.iter (fun (l, _) -> List.iter (no_alpha_renaming_b s) l) trs

  | PPforall_named (xs, trs, hyp, f1) ->
    let xs1, xs2 = List.partition (fun (x, _, _) -> S.mem x up) xs in
    let nv = List.map (fun (x, lbl, ty) -> fresh_var x, lbl, ty) xs1 in
    let m = List.fold_left2
        (fun m (x, _, _) (nx, _, _) -> MString.add x nx m) m xs1 nv in
    let xs = nv @ xs2 in
    let up = List.fold_left (fun up (x, _, _) -> S.add x up) up xs in
    let s = (up, m) in
    List.iter (no_alpha_renaming_b s) hyp;
    no_alpha_renaming_b s f1;
    List.iter (fun (l, _) -> List.iter (no_alpha_renaming_b s) l) trs

  | PPexists(lx, trs, hyp, f1) ->
    let s, _ =
      List.fold_left
        (fun (_, lx) (x, _) ->
           if S.mem x up then
             let nx = fresh_var x in
             let m = MString.add x nx m in
             let up = S.add nx up in
             (up, m), nx :: lx
           else
             (S.add x up, m), x :: lx)
        (s, []) lx
    in
    no_alpha_renaming_b s f1;
    List.iter (no_alpha_renaming_b s) hyp;
    List.iter (fun (l, _) -> List.iter (no_alpha_renaming_b s) l) trs

  | PPexists_named (lx, trs, hyp, f1) ->
    let s, _ =
      List.fold_left
        (fun (_, lx) (x, _, _) ->
           if S.mem x up then
             let nx = fresh_var x in
             let m = MString.add x nx m in
             let up = S.add nx up in
             (up, m), nx :: lx
           else
             (S.add x up, m), x :: lx)
        (s, []) lx
    in
    no_alpha_renaming_b s f1;
    List.iter (no_alpha_renaming_b s) hyp;
    List.iter (fun (l, _) -> List.iter (no_alpha_renaming_b s) l) trs

  | PPmatch(e, cases) ->
    no_alpha_renaming_b s e;
    List.iter (fun (_, e) -> no_alpha_renaming_b s e) cases

  | PPisConstr (e, _) ->
    no_alpha_renaming_b s e

  | PPproject (e, _) ->
    no_alpha_renaming_b s e

let rec alpha_renaming_b ((up, m) as s) f =
  match f.pp_desc with
  | PPvar x ->
    (try
       let y = MString.find x m in
       assert (String.compare x y <> 0);
       {f with pp_desc = PPvar y}
     with Not_found -> f)

  | PPmapsTo (x, e) ->
    let x' =
      try
        let y = MString.find x m in
        assert (String.compare x y <> 0);
        y
      with Not_found -> x
    in
    let e' = alpha_renaming_b s e in
    if x == x' && e == e' then f
    else {f with pp_desc = PPmapsTo(x', e')}

  | PPapp(k, l) ->
    let l2 = List.rev (List.rev_map (alpha_renaming_b s) l) in
    if List.for_all2 (fun a b -> a == b) l l2 then f
    else {f with pp_desc = PPapp(k, l2)}

  | PPinInterval (e,a,b,c,d) ->
    let e' = alpha_renaming_b s e in
    if e == e' then e
    else {f with pp_desc = PPinInterval(e', a,b,c,d)}

  | PPdistinct l ->
    let l2 = List.rev (List.rev_map (alpha_renaming_b s) l) in
    if List.for_all2 (fun a b -> a == b) l l2 then f
    else {f with pp_desc = PPdistinct l2}

  | PPconst _ -> f

  | PPinfix(f1, op, f2) ->
    let ff1 = alpha_renaming_b s f1 in
    let ff2 = alpha_renaming_b s f2 in
    if f1 == ff1 && f2 == ff2 then f
    else {f with pp_desc = PPinfix(ff1, op, ff2)}

  | PPprefix(op, f1) ->
    let ff1 = alpha_renaming_b s f1 in
    if f1 == ff1 then f
    else {f with pp_desc = PPprefix(op, ff1)}

  | PPget(f1,f2) ->
    let ff1 = alpha_renaming_b s f1 in
    let ff2 = alpha_renaming_b s f2 in
    if f1 == ff1 && f2 == ff2 then f
    else {f with pp_desc = PPget(ff1, ff2)}

  | PPset(f1, f2, f3) ->
    let ff1 = alpha_renaming_b s f1 in
    let ff2 = alpha_renaming_b s f2 in
    let ff3 = alpha_renaming_b s f3 in
    if f1 == ff1 && f2 == ff2 && f3 == ff3 then f
    else {f with pp_desc = PPset(ff1, ff2, ff3)}

  | PPextract(f1, i, j) ->
    let ff1 = alpha_renaming_b s f1 in
    if f1 == ff1 then f
    else {f with pp_desc = PPextract(ff1, i, j)}

  | PPconcat(f1, f2) ->
    let ff1 = alpha_renaming_b s f1 in
    let ff2 = alpha_renaming_b s f2 in
    if ff1 == f1 && ff2 == f2 then f
    else {f with pp_desc = PPconcat(ff1, ff2)}

  | PPif(f1, f2, f3) ->
    let ff1 = alpha_renaming_b s f1 in
    let ff2 = alpha_renaming_b s f2 in
    let ff3 = alpha_renaming_b s f3 in
    if f1 == ff1 && f2 == ff2 && f3 == ff3 then f
    else {f with pp_desc = PPif(ff1, ff2, ff3)}

  | PPnamed(n, f1) ->
    let ff1 = alpha_renaming_b s f1 in
    if f1 == ff1 then f
    else {f with pp_desc = PPnamed(n, ff1)}

  | PPdot(f1, a) ->
    let ff1 = alpha_renaming_b s f1 in
    if f1 == ff1 then f
    else {f with pp_desc = PPdot(ff1, a)}

  | PPrecord l ->
    let l2 =
      List.rev (List.rev_map (fun (a,e) -> a, alpha_renaming_b s e) l) in
    if List.for_all2 (fun a b -> a == b) l l2 then f
    else {f with pp_desc = PPrecord l2}

  | PPwith(e, l) ->
    let l2 =
      List.rev (List.rev_map (fun (a,e) -> a, alpha_renaming_b s e) l) in
    let ee = alpha_renaming_b s e in
    if List.for_all2 (fun a b -> a == b) l l2 && e == ee then f
    else {f with pp_desc = PPwith(ee, l2)}

  | PPlet(l, f2) ->
    let _ =
      List.fold_left (fun z (sy,_) ->
          if Util.SS.mem sy z then
            Errors.typing_error (DuplicatePattern sy) f.pp_loc;
          Util.SS.add sy z
        )Util.SS.empty l
    in
    let same_fi = ref true in
    let rev_l =
      List.rev_map (fun (x, f1) ->
          let ff1 = alpha_renaming_b s f1 in
          same_fi := !same_fi && f1 == ff1;
          x, ff1
        ) l
    in
    let s, l =
      List.fold_left
        (fun ((up,m), l) (x, f1) ->
           if S.mem x up then
             let nx = fresh_var x in
             let m = MString.add x nx m in
             (S.add nx up, m), (nx, f1) :: l
           else
             (S.add x up, m), (x, f1) :: l
        )((up,m), []) rev_l
    in
    let ff2 = alpha_renaming_b s f2 in
    if !same_fi && f2 == ff2 then f
    else {f with pp_desc = PPlet(l, ff2)}

  | PPcheck f' ->
    let ff = alpha_renaming_b s f' in
    if f' == ff then f
    else {f with pp_desc = PPcheck ff}

  | PPcut f' ->
    let ff = alpha_renaming_b s f' in
    if f' == ff then f
    else {f with pp_desc = PPcut ff}

  | PPcast (f',ty) ->
    let ff = alpha_renaming_b s f' in
    if f' == ff then f
    else {f with pp_desc = PPcast (ff,ty)}

  | PPforall(xs, trs, hyp, f1) ->
    let xs1, xs2 = List.partition (fun (x, _) -> S.mem x up) xs in
    let nv = List.map (fun (x, ty) -> fresh_var x, ty) xs1 in
    let m = List.fold_left2
        (fun m (x, _) (nx, _) -> MString.add x nx m) m xs1 nv in
    let xs = nv @ xs2 in
    let up = List.fold_left (fun up (x, _) -> S.add x up) up xs in
    let s = (up, m) in
    let ff1 = alpha_renaming_b s f1 in
    let trs2 =
      List.map (fun (l, tuser) ->
          List.map (alpha_renaming_b s) l, tuser) trs
    in
    let hyp2 = List.map (alpha_renaming_b s) hyp in
    if f1==ff1 && List.for_all2 (fun a b -> a==b) trs trs2
       && List.for_all2 (fun a b -> a==b) hyp hyp2 then f
    else {f with pp_desc = PPforall(xs, trs2, hyp2, ff1)}

  | PPforall_named (xs, trs, hyp, f1) ->
    let xs1, xs2 = List.partition (fun (x, _, _) -> S.mem x up) xs in
    let nv = List.map (fun (x, lbl, ty) -> fresh_var x, lbl, ty) xs1 in
    let m = List.fold_left2
        (fun m (x, _, _) (nx, _, _) -> MString.add x nx m) m xs1 nv in
    let xs = nv @ xs2 in
    let up = List.fold_left (fun up (x, _, _) -> S.add x up) up xs in
    let s = (up, m) in
    let ff1 = alpha_renaming_b s f1 in
    let trs2 =
      List.map (fun (l, tuser) ->
          List.map (alpha_renaming_b s) l, tuser) trs
    in
    let hyp2 = List.map (alpha_renaming_b s) hyp in
    if f1==ff1 && List.for_all2 (fun a b -> a==b) trs trs2
       && List.for_all2 (fun a b -> a==b) hyp hyp2 then f
    else {f with pp_desc = PPforall_named (xs, trs2, hyp2, ff1)}

  | PPexists(lx, trs, hyp, f1) ->
    let s, lx =
      List.fold_left
        (fun (_, lx) (x, ty) ->
           if S.mem x up then
             let nx = fresh_var x in
             let m = MString.add x nx m in
             let up = S.add nx up in
             (up, m), (nx, ty) :: lx
           else
             (S.add x up, m), (x, ty) :: lx)
        (s, []) lx
    in
    let trs2 =
      List.map
        (fun (l, tuser) -> List.map (alpha_renaming_b s) l, tuser) trs
    in
    let ff1 = alpha_renaming_b s f1 in
    let hyp2 = List.map (alpha_renaming_b s) hyp in
    if f1==ff1 && List.for_all2 (fun a b -> a==b) trs trs2
       && List.for_all2 (fun a b -> a==b) hyp hyp2 then f
    else {f with pp_desc = PPexists(lx, trs2, hyp2, ff1)}

  | PPexists_named (lx, trs, hyp, f1) ->
    let s, lx =
      List.fold_left
        (fun (_, lx) (x, lbl, ty) ->
           if S.mem x up then
             let nx = fresh_var x in
             let m = MString.add x nx m in
             let up = S.add nx up in
             (up, m), (nx, lbl, ty) :: lx
           else
             (S.add x up, m), (x, lbl, ty) :: lx)
        (s, []) lx
    in
    let ff1 = alpha_renaming_b s f1 in
    let trs2 =
      List.map
        (fun (l, tuser) -> List.map (alpha_renaming_b s) l, tuser) trs
    in
    let hyp2 = List.map (alpha_renaming_b s) hyp in
    if f1==ff1 && List.for_all2 (fun a b -> a==b) trs trs2
       && List.for_all2 (fun a b -> a==b) hyp hyp2 then f
    else {f with pp_desc = PPexists_named (lx, trs2, hyp2, ff1)}

  | PPmatch(e, cases) ->
    let e' = alpha_renaming_b s e in
    let same_cases = ref true in
    let cases' =
      List.map
        (fun (p, e) ->
           let e' = alpha_renaming_b s e in
           same_cases := !same_cases && e == e';
           p, e'
        ) cases
    in
    if !same_cases && e == e' then f
    else
      let cases' = if !same_cases then cases else cases' in
      { f with pp_desc = PPmatch(e', cases') }

  | PPproject(f1, a) ->
    let ff1 = alpha_renaming_b s f1 in
    if f1 == ff1 then f
    else {f with pp_desc = PPproject(ff1, a)}

  | PPisConstr(f1, a) ->
    let ff1 = alpha_renaming_b s f1 in
    if f1 == ff1 then f
    else {f with pp_desc = PPisConstr(ff1, a)}

let alpha_renaming_b s f =
  try no_alpha_renaming_b s f; f
  with Exit -> alpha_renaming_b s f

let alpha_renaming_env env =
  let up = MString.fold (fun s _ up -> S.add s up)
      env.Env.logics S.empty in
  let up = MString.fold (fun s _ up -> S.add s up) env.Env.var_map up in
  alpha_renaming_b (up, MString.empty)


let rec elim_toplevel_forall env bnot f =
  (* bnot = true : nombre impaire de not *)
  match f.pp_desc with
  | PPforall (lv, _, _, f) when bnot ->
    let env = List.fold_left (fun env (v, ty) ->
        Env.add_names env [v] ty f.pp_loc
      ) env lv in
    elim_toplevel_forall env bnot f

  | PPforall_named (lvb, _, _, f) when bnot->
    let env = List.fold_left (fun env (v, lbl, ty) ->
        Env.add_names_lbl env [v, lbl] ty f.pp_loc
      ) env lvb in
    elim_toplevel_forall env bnot f

  | PPinfix (f1, PPand, f2) when not bnot ->
    let f1 , env = elim_toplevel_forall env false f1 in
    let f2 , env = elim_toplevel_forall env false
        (alpha_renaming_env env f2) in
    { f with pp_desc = PPinfix(f1, PPand , f2)}, env

  | PPinfix (f1, PPor, f2) when bnot ->
    let f1 , env = elim_toplevel_forall env true f1 in
    let f2 , env = elim_toplevel_forall env true
        (alpha_renaming_env env f2) in
    { f with pp_desc = PPinfix(f1, PPand , f2)}, env

  | PPinfix (f1, PPimplies, f2) when bnot ->
    let f1 , env = elim_toplevel_forall env false f1 in
    let f2 , env = elim_toplevel_forall env true
        (alpha_renaming_env env f2) in
    { f with pp_desc = PPinfix(f1,PPand,f2)}, env

  | PPprefix (PPnot, f) -> elim_toplevel_forall env (not bnot) f


  | _ when bnot ->
    { f with pp_desc = PPprefix (PPnot, f) }, env

  | _  -> f , env


let rec intro_hypothesis env valid_mode f =
  match f.pp_desc with
  | PPinfix(f1,PPimplies,f2) when valid_mode ->
    let ((_, env) as f1_env) =
      elim_toplevel_forall env (not valid_mode) f1 in
    let axioms, goal = intro_hypothesis env valid_mode
        (alpha_renaming_env env f2) in
    f1_env::axioms, goal
  (*    | PPlet(var,{pp_desc=PPcast(t1,ty); pp_loc = ty_loc},f2) ->
        let env = Env.add_names env [var] ty ty_loc in
        let var = {pp_desc = PPvar var; pp_loc = f.pp_loc} in
        let feq = {pp_desc = PPinfix(var,PPeq,t1); pp_loc = f.pp_loc} in
        let axioms, goal = intro_hypothesis env valid_mode
          (alpha_renaming_env env f2) in
        (feq,env)::axioms, goal
  *)
  | PPforall (lv, _, _, f) when valid_mode ->
    let env = List.fold_left (fun env (v, ty) ->
        Env.add_names env [v] ty f.pp_loc
      ) env lv in
    intro_hypothesis env valid_mode f
  | PPexists (lv, _, _, f) when not valid_mode->
    let env = List.fold_left (fun env (v, ty) ->
        Env.add_names env [v] ty f.pp_loc
      ) env lv in
    intro_hypothesis env valid_mode f
  | PPforall_named (lvb, _, _, f) when valid_mode ->
    let env = List.fold_left (fun env (v, lbl, ty) ->
        Env.add_names_lbl env [v, lbl] ty f.pp_loc
      ) env lvb in
    intro_hypothesis env valid_mode f
  | PPexists_named (lvb, _, _, f) when not valid_mode->
    let env = List.fold_left (fun env (v, lbl, ty) ->
        Env.add_names_lbl env [v, lbl] ty f.pp_loc
      ) env lvb in
    intro_hypothesis env valid_mode f
  | _ ->
    let f_env = elim_toplevel_forall env valid_mode f in
    [] , f_env

let fresh_check_name =
  let cpt = ref 0 in fun () -> incr cpt; "check_"^(string_of_int !cpt)

let fresh_cut_name =
  let cpt = ref 0 in fun () -> incr cpt; "cut_"^(string_of_int !cpt)

let check_duplicate_params l =
  let rec loop l acc =
    match l with
    | [] -> ()
    | (loc,x,_)::rem ->
      if List.mem x acc then
        Errors.typing_error (ClashParam x) loc
      else loop rem (x::acc)
  in
  loop l []

let rec make_pred loc trs f = function
    [] ->  f
  | [x,t] ->
    { pp_desc = PPforall([x,t],trs,[],f) ; pp_loc = loc }
  | (x,t)::l ->
    { pp_desc = PPforall([x,t],[],[],(make_pred loc trs f l)) ;
      pp_loc = loc }

let monomorphize_var (s,ty) = s, Ty.monomorphize ty

let rec mono_term {c = {tt_ty=tt_ty; tt_desc=tt_desc}; annot = id} =
  let tt_desc = match tt_desc with
    | TTconst _ | TTvar _ ->
      tt_desc
    | TTinfix (t1, sy, t2) ->
      TTinfix(mono_term t1, sy, mono_term t2)
    | TTprefix (sy,t) ->
      TTprefix(sy, mono_term t)
    | TTapp (sy,tl) ->
      TTapp (sy, List.map mono_term tl)
    | TTinInterval (e, lb, ub) ->
      TTinInterval(mono_term e, lb, ub)
    | TTmapsTo (x, e) ->
      TTmapsTo(x, mono_term e)
    | TTget (t1,t2) ->
      TTget (mono_term t1, mono_term t2)
    | TTset (t1,t2,t3) ->
      TTset(mono_term t1, mono_term t2, mono_term t3)
    | TTextract (t1,i,j) ->
      TTextract(mono_term t1, i, j)
    | TTconcat (t1,t2)->
      TTconcat (mono_term t1, mono_term t2)
    | TTdot (t1, a) ->
      TTdot (mono_term t1, a)
    | TTrecord lbs ->
      TTrecord (List.map (fun (x, t) -> x, mono_term t) lbs)
    | TTlet (l,t2)->
      let l = List.rev_map (fun (x, t1) -> x, mono_term t1) (List.rev l) in
      TTlet (l, mono_term t2)
    | TTnamed (lbl, t)->
      TTnamed (lbl, mono_term t)
    | TTite (cond, t1, t2) ->
      TTite (monomorphize_form cond, mono_term t1, mono_term t2)

    | TTproject (t, lbl) ->
      TTproject (mono_term t, lbl)
    | TTmatch (e, pats) ->
      let e = mono_term e in
      let pats = List.rev_map (fun (p, f) -> p, mono_term f) (List.rev pats) in
      TTmatch (e, pats)

    | TTform f -> TTform (monomorphize_form f)

  in
  { c = {tt_ty = Ty.monomorphize tt_ty; tt_desc=tt_desc}; annot = id}


and monomorphize_atom tat =
  let c = match tat.c with
    | TAtrue | TAfalse -> tat.c
    | TAeq tl -> TAeq (List.map mono_term tl)
    | TAneq tl -> TAneq (List.map mono_term tl)
    | TAle tl -> TAle (List.map mono_term tl)
    | TAlt tl -> TAlt (List.map mono_term tl)
    | TAdistinct tl -> TAdistinct (List.map mono_term tl)
    | TApred (t, negated) -> TApred (mono_term t, negated)
    | TTisConstr (t, lbl) -> TTisConstr (mono_term t, lbl)
  in
  { tat with c = c }

and monomorphize_form tf =
  let c = match tf.c with
    | TFatom tat -> TFatom (monomorphize_atom tat)
    | TFop (oplogic , tfl) ->
      TFop(oplogic, List.map monomorphize_form tfl)
    | TFforall qf ->
      TFforall
        {  qf_bvars = List.map monomorphize_var qf.qf_bvars;
           qf_hyp = List.map monomorphize_form qf.qf_hyp;
           qf_form = monomorphize_form qf.qf_form;
           qf_triggers =
             List.map (fun (l, b) -> List.map mono_term l, b) qf.qf_triggers}
    | TFexists qf ->
      TFexists
        {  qf_bvars = List.map monomorphize_var qf.qf_bvars;
           qf_hyp = List.map monomorphize_form qf.qf_hyp;
           qf_form = monomorphize_form qf.qf_form;
           qf_triggers =
             List.map (fun (l, b) -> List.map mono_term l, b) qf.qf_triggers}

    | TFlet (binders, tf) ->
      let binders =
        List.rev_map
          (fun (sy, e) ->
             match e with
             | TletTerm tt -> sy, TletTerm (mono_term tt)
             | TletForm ff -> sy, TletForm (monomorphize_form ff)
          )(List.rev binders)
      in
      TFlet(binders, monomorphize_form tf)

    | TFnamed (hs,tf) ->
      TFnamed(hs, monomorphize_form tf)

    | TFmatch(e, pats) ->
      let e = mono_term e in
      let pats =
        List.rev_map
          (fun (p, f) -> p, monomorphize_form f) (List.rev pats)
      in
      TFmatch (e, pats)
  in
  { tf with c = c }

let axioms_of_rules loc name lf acc env =
  let acc =
    List.fold_left
      (fun acc f ->
         let name =
           Fmt.str "%s_%s"
             (Id.Namespace.Internal.fresh ())
             name
         in
         let td = {c = TAxiom(loc,name,Util.Default, f); annot = new_id () } in
         (td, env)::acc
      ) acc lf
  in
  acc, env



let type_hypothesis acc env_f loc sort f =
  let f = type_form env_f f in
  let f = monomorphize_form f in
  let td =
    {c = TAxiom(loc, Ty.fresh_hypothesis_name sort,Util.Default, f);
     annot = new_id () } in
  (td, env_f)::acc


let type_goal acc env_g loc sort n goal =
  let goal = type_form env_g goal in
  let goal = monomorphize_form goal in
  let td = {c = TGoal(loc, sort, n, goal); annot = new_id () } in
  (td, env_g)::acc


let rec type_and_intro_goal acc env sort n f =
  let axioms, (goal, env_g) =
    intro_hypothesis env (match sort with Ty.Sat -> false | _ -> true) f in
  let loc = f.pp_loc in
  let acc =
    List.fold_left
      (fun acc (f, env_f) -> match f.pp_desc with
         | PPcut f ->
           let acc = type_and_intro_goal
               acc env_f Ty.Cut (fresh_cut_name ()) f in
           type_hypothesis acc env_f loc sort f

         | PPcheck f ->
           type_and_intro_goal
             acc env_f Check (fresh_check_name ()) f

         | _ ->
           type_hypothesis acc env_f loc sort f
      ) acc axioms
  in
  type_goal acc env_g loc sort n goal



let type_one_th_decl env e =
  (* NB: we always keep triggers for axioms of theories *)
  match e with
  | Axiom(loc,name,ax_kd,f)  ->
    let f = type_form ~in_theory:true env f in
    {c = TAxiom (loc,name,ax_kd,f); annot = new_id ()}

  | Optimize (loc, _, _)
  | Theory (loc, _, _, _)
  | Logic (loc, _, _, _)
  | Rewriting(loc, _, _)
  | Goal(loc, _, _)
  | Check_sat(loc, _, _)
  | Predicate_def(loc,_,_,_)
  | Function_def(loc,_,_,_,_)
  | MutRecDefs ((loc,_,_,_,_) :: _)
  | TypeDecl ((loc, _, _, _)::_)
  | Push (loc,_) | Pop (loc,_) | Reset loc | Exit loc ->
    Errors.typing_error WrongDeclInTheory loc
  | MutRecDefs []
  | TypeDecl [] -> assert false

let is_recursive_type =
  let rec exit_if_has_type s ppty =
    match ppty with
    | PPTint | PPTbool | PPTreal | PPTunit | PPTbitv _ | PPTvarid _ -> ()
    | PPTexternal (args, n, _loc) ->
      if String.equal s n then raise Exit;
      List.iter (exit_if_has_type s) args
  in
  fun s body ->
    match body with
    | Abstract | Enum _ | Record _ -> false
    | Algebraic cases ->
      try
        List.iter
          (fun (_c, args_ty) ->
             List.iter (fun (_lbl, ppty) -> exit_if_has_type s ppty) args_ty
          )cases;
        false
      with Exit ->
        true

let user_types_of_body =
  let rec aux acc ppty =
    match ppty with
    | PPTint | PPTbool | PPTreal | PPTunit | PPTbitv _ | PPTvarid _ -> acc
    | PPTexternal (args, n, _loc) -> List.fold_left aux (S.add n acc) args
  in
  fun body ->
    match body with
    | Abstract
    | Enum _   -> S.empty
    | Record (_, args_ty) ->
      List.fold_left (fun acc (_lbl, ppty) -> aux acc ppty) S.empty args_ty

    | Algebraic cases ->
      List.fold_left
        (fun acc (_c, args_ty) ->
           List.fold_left (fun acc (_lbl, ppty) -> aux acc ppty) acc args_ty
        )S.empty cases


(* Could do better with topological ordering and cycles detection *)
let partition_non_rec =
  let detect_non_rec non_rec pending =
    let tys =
      List.fold_left (fun acc (_,s, _) -> S.add s acc) S.empty pending
    in
    List.fold_left
      (fun (non_rec, pending) ((e, _, body_deps) as ee) ->
         let new_deps = S.inter body_deps tys in
         if S.is_empty new_deps then e :: non_rec, pending
         else non_rec, ee :: pending
      )(non_rec, []) (List.rev pending)
  in
  let rec aux non_rec pending =
    let non_rec', pending' = detect_non_rec non_rec pending in
    if non_rec' != non_rec then aux non_rec' pending'
    else List.rev non_rec', List.map (fun (e,_,_) -> e) pending'
  in
  fun l ->
    aux [] @@
    List.rev_map
      (fun ((_loc, _, s, body) as e) -> (e, s, user_types_of_body body))
      (List.rev l)

let refine_body_of_non_recursive_adt body =
  match body with
  | Algebraic [c, []] ->
    (*  enum with one constructor *)
    Enum [c]

  | Algebraic [c, l] ->
    (* record *)
    Record (c,l)

  | Algebraic l ->
    begin
      try Enum (List.map (fun (c, l) -> if l != [] then raise Exit; c) l)
      with Exit -> body
    end

  | _ -> body


let type_user_defined_type_body ~is_recursive env acc (loc, ls, s, body) =
  let tls = List.map (fun s -> PPTvarid (s,loc)) ls in
  let pur_ty = PPTexternal(tls, s, loc) in
  match body with
  | Enum lc ->
    assert (not is_recursive); (* Enum types are not recursive *)
    let lcl = List.map (fun c -> c, "") lc in (* empty labels *)
    let ty = PFunction([], pur_ty) in
    let tlogic, env =
      (* can also use List.fold Env.add_constr *)
      let constr = fun s -> Symbols.constr @@ Uid.of_string s in
      Env.add_logics ~kind:Env.EnumConstr env constr lcl ty loc
    in
    let td2_a = { c = TLogic(loc, lc, tlogic); annot=new_id () } in
    (td2_a,env)::acc, env

  | Record (constr, lrec) ->
    (* Records types are not recursive. They remain Algebraic in this
       case *)
    assert (not is_recursive);
    let acc, env =
      if String.equal constr "{" then
        (* do not register default "{ . }" constructor *)
        acc, env
      else
        let args_ty = List.map snd lrec in
        let tlogic, env =
          Env.add_constr ~record:true env constr args_ty pur_ty loc
        in
        ({c = TLogic(loc, [constr], tlogic); annot=new_id ()}, env)::acc, env
    in
    List.fold_left (* register fields *)
      (fun (acc, env) (lbl, ty_lbl) ->
         let tlogic, env =
           Env.add_destr ~record:true env lbl pur_ty ty_lbl loc
         in
         ({c = TLogic(loc, [lbl], tlogic); annot=new_id ()}, env) :: acc, env
      )(acc, env) lrec

  | Algebraic lc ->
    List.fold_left
      (fun (acc, env) (constr, lbl_args_ty) ->
         let args_ty = List.map snd lbl_args_ty in
         let tty, env =
           Env.add_constr ~record:false env constr args_ty pur_ty loc
         in
         let acc =
           ({c = TLogic(loc, [constr], tty); annot=new_id ()}, env) :: acc
         in
         List.fold_left (* register destructors *)
           (fun (acc, env) (lbl, ty_lbl) ->
              let tty, env =
                Env.add_destr ~record:false env lbl pur_ty ty_lbl loc
              in
              ({c = TLogic(loc, [lbl], tty); annot=new_id ()}, env) :: acc, env
           )(acc, env) lbl_args_ty
      )(acc, env) lc

  | Abstract ->
    assert (not is_recursive); (* Abstract types are not recursive *)
    acc, env

let declare_fun env loc n ?(defined=false) ?ret_ty l  =
  check_duplicate_params l;
  let infix, ty  =
    let l = List.map (fun (_,_,x) -> x) l in
    match ret_ty with
    | None | Some PPTbool ->
      PPiff, PPredicate l
    | Some ty ->
      PPeq, PFunction(l,ty)
  in
  let mk_symb hs = Symbols.name hs ~defined ~kind:Symbols.Other in
  let tlogic, env = Env.add_logics env mk_symb [n] ty loc in (* TODO *)
  env, infix, tlogic

let define_fun (acc, env) loc n l tlogic ?ret_ty infix e =
  let l = List.map (fun (_,x,t) -> (x,t)) l in
  let n = fst n in
  let lvar = List.map (fun (x,_) -> {pp_desc=PPvar x;pp_loc=loc}) l in
  let p = { pp_desc=PPapp(n,lvar) ; pp_loc=loc } in
  let f = { pp_desc = PPinfix(p,infix,e) ; pp_loc = loc } in
  let f = make_pred loc [] f l in
  let f = type_form env f in
  let t_typed, l_typed =
    match tlogic with
    | TPredicate args ->
      Ty.Tbool, List.map2 (fun (x, _) ty -> x, Ty.shorten ty) l args
    | TFunction (args, ret) ->
      Ty.shorten ret, List.map2 (fun (x, _) ty -> x, Ty.shorten ty) l args
  in
  let td =
    match ret_ty with
    | None ->
      Options.tool_req 1 "TR-Typing-LogicPred$_F$";
      TPredicate_def(loc,n,l_typed,f)
    | Some _ ->
      Options.tool_req 1 "TR-Typing-LogicFun$_F$";
      TFunction_def(loc,n,l_typed,t_typed,f)
  in
  let td_a = { c = td; annot=new_id () } in
  (td_a, env)::acc, env

let type_fun (acc, env) loc n l ?ret_ty e =
  let env, infix, tlogic =
    declare_fun env loc n ~defined:true ?ret_ty l
  in
  define_fun (acc, env) loc n l tlogic ?ret_ty infix e

let rec type_decl (acc, env) d assertion_stack =
  Types.to_tyvars := MString.empty;
  match d with
  | Push (loc,n) ->
    if n < 0 then
      Errors.typing_error (ShouldBePositive n) loc;
    Util.loop ~f:(fun _n env () -> Stack.push env assertion_stack)
      ~max:n ~elt:env ~init:();
    let td = {c = TPush(loc,n); annot = new_id () } in
    (td,env) :: acc, env
  | Pop (loc,n) ->
    if n < 0 then
      Errors.typing_error (ShouldBePositive n) loc;
    let assertion_context_number = Stack.length assertion_stack in
    if n > assertion_context_number then
      Errors.typing_error
        (BadPopCommand {pushed = assertion_context_number; to_pop = n}) loc
    else
      let old_env = env in
      let env = Util.loop ~f:(fun _n () _env -> Stack.pop assertion_stack)
          ~max:n ~elt:() ~init:env in
      let td = {c = TPop(loc,n); annot = new_id () } in
      (td,old_env) :: acc, env

  | Theory (loc, name, ext, l) ->
    Options.tool_req 1 "TR-Typing-TheoryDecl$_F$";
    let tl = List.map (type_one_th_decl env) l in
    let ext = match Util.th_ext_of_string ext with
      | Some res -> res
      | None ->
        Errors.typing_error (ThExtError ext) loc
    in
    let td = {c = TTheory(loc, name, ext, tl); annot = new_id () } in
    (td, env)::acc, env

  | Logic (loc, ac, lp, pp_ty) ->
    Options.tool_req 1 "TR-Typing-LogicFun$_F$";
    let mk_symb hs = Symbols.name hs ~kind:ac in
    let tlogic, env' = Env.add_logics env mk_symb lp pp_ty loc in
    let lp = List.map fst lp in
    let td = {c = TLogic(loc,lp,tlogic); annot = new_id () } in
    (td, env)::acc, env'

  | Axiom(loc,name,ax_kd,f) ->
    Options.tool_req 1 "TR-Typing-AxiomDecl$_F$";
    let f = type_form env f in
    let td = {c = TAxiom(loc,name,ax_kd,f); annot = new_id () } in
    (td, env)::acc, env

  | Rewriting(loc, name, lr) ->
    let lf = List.map (type_form env) lr in
    if Options.get_rewriting () then
      let rules = List.map (fun f -> make_rules loc f) lf in
      let td = {c = TRewriting(loc, name, rules); annot = new_id () } in
      (td, env)::acc, env
    else
      axioms_of_rules loc name lf acc env

  | Goal (_loc, n, f) ->
    Options.tool_req 1 "TR-Typing-GoalDecl$_F$";
    (*let f = move_up f in*)
    let f = alpha_renaming_env env f in
    type_and_intro_goal acc env Thm n f, env

  | Optimize (loc, expr, is_max) ->
    Options.tool_req 1 "TR-Typing-Optimize$_F$";
    let expr = type_term env expr in
    let td = { c = TOptimize (loc, expr, is_max); annot = new_id () } in
    (td, env) :: acc, env

  | Check_sat(_loc, n, f) ->
    Options.tool_req 1 "TR-Typing-CheckSatDecl$_F$";
    (*let f = move_up f in*)
    let f = alpha_renaming_env env f in
    type_and_intro_goal acc env Sat n f, env

  | MutRecDefs l ->
    let rev_l, env =
      List.fold_left (
        fun (acc, env) (loc,n,l,ret_ty,e) ->
          let env, infix, tlogic = declare_fun env loc n ?ret_ty l in
          (loc, n, l, tlogic, ret_ty, infix, e) :: acc, env
      ) ([], env) l
    in
    List.fold_left (
      fun (acc, env) (loc, n, l, tlogic, ret_ty, infix, e) ->
        define_fun (acc, env) loc n l tlogic ?ret_ty infix e
    ) (acc, env) (List.rev rev_l)

  | Predicate_def(loc,n,l,e) ->
    type_fun (acc, env) loc n l e

  | Function_def(loc,n,l,ret_ty,e) ->
    type_fun (acc, env) loc n l ~ret_ty e

  | TypeDecl [] ->
    assert false

  | TypeDecl [loc, ls, s, body] when not (is_recursive_type s body) ->
    let body = refine_body_of_non_recursive_adt body in
    Options.tool_req 1 "TR-Typing-TypeDecl$_F$";
    let ty1, env = Env.add_type_decl env ls s body loc in
    let acc = ({c = TTypeDecl(loc, ty1); annot=new_id ()}, env) :: acc in
    type_user_defined_type_body ~is_recursive:false env acc (loc, ls, s, body)

  | TypeDecl l ->
    let not_rec, are_rec = partition_non_rec l in

    (* A. Typing types that are not recursive *)
    let acc, env =
      List.fold_left
        (fun accu x ->
           type_decl accu (TypeDecl [x]) assertion_stack) (acc, env) not_rec
    in

    (* B. Typing types that are recursive *)

    (* step 1: with body == (Algebraic []) *)
    let env, tyvars_of_ty =
      List.fold_left
        (fun (env, tyvars_of_ty) (loc, ls, s, _) ->
           Types.to_tyvars := MString.empty;
           let _, env = Env.add_type_decl env ls s (Parsed.Algebraic []) loc in
           env, MString.add s !(Types.to_tyvars) tyvars_of_ty
        )(env, MString.empty) are_rec
    in

    (* step 2: right body, but without adding constrs and destrs *)
    let acc, env =
      List.fold_left
        (fun (acc, env) (loc, ls, s, body) ->
           Types.to_tyvars :=
             (try MString.find s tyvars_of_ty with Not_found -> assert false);
           let tty, env =
             Env.add_type_decl ~recursive:true env ls s body loc in
           ({c = TTypeDecl(loc, tty); annot=new_id ()}, env)::acc, env
        )(acc, env) are_rec
    in
    (* step 3: register constrs and destrs as function symbols *)
    List.fold_left
      (fun (acc, env) ty_d ->
         type_user_defined_type_body ~is_recursive:true env acc ty_d)
      (acc, env) are_rec

  | Reset l ->
    let td = {c = TReset l; annot = new_id () } in
    (td,Env.empty) :: acc, Env.empty

  | Exit l ->
    let td = {c = TExit l; annot = new_id () } in
    (td,env) :: acc, env

let type_parsed env s d =
  let l, env' = type_decl ([], env) d s in
  List.rev_map fst l, env'

let type_file ld =
  let env = Env.empty in
  let assertion_stack = Stack.create () in
  let ltd, env =
    List.fold_left
      (fun acc d -> type_decl acc d assertion_stack) ([], env) ld
  in
  List.rev ltd, env

let split_goals_aux f l =
  let _, _, _, ret =
    List.fold_left
      (fun (ctx, global_hyp, local_hyp, ret) (td, env) ->
         match td.c with
         | TGoal (_, (Check | Cut), name, _) ->
           ctx, global_hyp, [],
           (f td env (local_hyp@global_hyp@ctx), name) :: ret

         | TGoal (_, _, name, _) ->
           ctx, [], [],
           (f td env (local_hyp@global_hyp@ctx), name) :: ret

         | TAxiom (_, s, _, _) when Ty.is_global_hyp s ->
           ctx, (f td env global_hyp), local_hyp,
           ret

         | TAxiom (_, s, _, _) when Ty.is_local_hyp s ->
           ctx, global_hyp, (f td env local_hyp),
           ret

         | _ ->
           (f td env ctx), global_hyp, local_hyp,
           ret

      ) ([],[],[],[]) l
  in
  List.rev_map (fun (l, goal_name) -> List.rev l, goal_name) ret

let split_goals l =
  split_goals_aux (fun e env acc -> (e, env) :: acc) l

let split_goals_and_cnf l =
  split_goals_aux (fun td _env acc -> Cnf.make acc td) l

let type_expr env vars t =
  let vmap =
    List.fold_left
      (fun m (s,ty)->
         let str = Symbols.to_string_clean s in
         MString.add str (s,ty) m
      ) env.Env.var_map vars in
  let env = { env with Env.var_map = vmap } in
  type_term env t

type env = Env.t

let empty_env = Env.empty

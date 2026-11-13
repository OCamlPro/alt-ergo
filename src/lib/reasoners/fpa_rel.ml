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

module X = Shostak.Combine
module E = Expr
module Sy = Symbols
module Ex = Explanation
module Q = Numbers.Q
module Z = Numbers.Z
module MX = Shostak.MXH
module Names = E.FP.Names

let src = Logs.Src.create ~doc:"Fpa_rel" __MODULE__

module Log = (val Logs.src_log src : Logs.LOG)

let timer = Timers.M_Fpa

module IntPairSet = Set.Make (struct
  type t = int * int

  let compare (a1, b1) (a2, b2) =
    let c = Int.compare a1 a2 in
    if c <> 0 then c else Int.compare b1 b2
end)

module AEFloat_arg_watch = struct
  type args =
    { eb : int;
      sb : int;
      mode : E.t
    }

  type t =
    { apps : args E.Map.t;
      (* ae.float application -> its (eb, sb, mode) arguments *)
      watched_args : E.Set.t MX.t;
      (* mode value -> ae.float applications that use it as an argument *)
      ready : args E.Map.t
          (* ae.float applications whose mode is now known to be a literal *)
    }

  type _ Uf.id += Id : t Uf.id

  exception Inconsistent of Ex.t

  let empty =
    { apps = E.Map.empty; watched_args = MX.empty; ready = E.Map.empty }

  let pp ppf t =
    Fmt.pf ppf "{float_watch: %d pending, %d ready}" (E.Map.cardinal t.apps)
      (E.Map.cardinal t.ready)

  let filter_ty ty = Ty.equal ty Fpa_rounding.fpa_rounding_mode

  let init _ t = t

  let add_by_arg r term watched_args =
    let s =
      match MX.find_opt r watched_args with Some s -> s | None -> E.Set.empty
    in
    MX.add r (E.Set.add term s) watched_args

  let register term args r_mode t =
    if E.Map.mem term t.apps || E.Map.mem term t.ready
    then t
    else if X.is_constant r_mode
    then { t with ready = E.Map.add term args t.ready }
    else
      { t with
        apps = E.Map.add term args t.apps;
        watched_args = add_by_arg r_mode term t.watched_args
      }

  (* The mode's value and explanation are retrieved with [Uf.find] when the
     application is processed. *)
  let subst ~ex:_ rr nrr t =
    match MX.find_opt rr t.watched_args with
    | None -> t
    | Some terms ->
      let t = { t with watched_args = MX.remove rr t.watched_args } in
      let nrr_lit = X.is_constant nrr in
      E.Set.fold
        (fun term t ->
          match E.Map.find_opt term t.apps with
          | None -> t
          | Some args ->
            if nrr_lit
            then
              { apps = E.Map.remove term t.apps;
                watched_args = t.watched_args;
                ready = E.Map.add term args t.ready
              }
            else { t with watched_args = add_by_arg nrr term t.watched_args })
        terms t

  let flush_ready t = t.ready, { t with ready = E.Map.empty }
end

(* Conversion applications reasoned about by [Conv_watch]. *)
type conv_kind =
  | Of_bits  (** [Sy.Float_of_bits] applied to [eb sb s e m] *)
  | Of_int  (** [ae.fp.of_int eb sb mode i] *)
  | Of_real  (** [ae.fp.from_real eb sb mode r] *)
  | To_int  (** [ae.fp.to_int eb sb mode x] *)
  | To_fp  (** [Sy.Float_to_fp] applied to [eb sb mode x] *)
  | To_bv of bool * int
      (** [Sy.Float_to_sbv n] ([true]) or [Sy.Float_to_ubv n] ([false]) applied
          to [eb sb mode x] *)

let conv_kind term =
  match E.term_view term with
  | { E.f = Sy.Op Float_of_bits; xs = [_; _; _; _; _]; _ } -> Some Of_bits
  | { E.f = Sy.Op Float_to_fp; xs = [_; _; _; _]; _ } -> Some To_fp
  | { E.f = Sy.Op (Float_to_ubv n); xs = [_; _; _; _]; _ } ->
    Some (To_bv (false, n))
  | { E.f = Sy.Op (Float_to_sbv n); xs = [_; _; _; _]; _ } ->
    Some (To_bv (true, n))
  | { E.f = Sy.Name { hs; _ }; xs = [_; _; _; _]; ty = Ty.Tfloat _; _ }
    when String.equal (Hstring.view hs) Names.of_int ->
    Some Of_int
  | { E.f = Sy.Name { hs; _ }; xs = [_; _; _; _]; ty = Ty.Tfloat _; _ }
    when String.equal (Hstring.view hs) Names.of_real ->
    Some Of_real
  | { E.f = Sy.Name { hs; _ }; xs = [_; _; _; _]; ty = Ty.Tint; _ }
    when String.equal (Hstring.view hs) Names.to_int ->
    Some To_int
  | _ -> None

let value_of_repr view r =
  if X.is_constant r then Option.bind (X.to_model_term r) view else None

let bv_value_of_repr =
  value_of_repr (fun t ->
      match E.term_view t with
      | { E.f = Sy.Bitv (_, z); _ } -> Some z
      | _ -> None)

let int_value_of_repr =
  value_of_repr (fun t ->
      match E.term_view t with { E.f = Sy.Int z; _ } -> Some z | _ -> None)

let real_value_of_repr =
  value_of_repr (fun t ->
      match E.term_view t with { E.f = Sy.Real q; _ } -> Some q | _ -> None)

let fp_value_of_repr = value_of_repr E.FP.float_view

let mode_of_repr = value_of_repr E.rounding_mode_view

(* Value of [r] if it is a constant, with [ex]. *)
let get_value value_of (r, ex) = Option.map (fun v -> v, ex) (value_of r)

let get_bv_value = get_value bv_value_of_repr

let get_int_value = get_value int_value_of_repr

let get_real_value = get_value real_value_of_repr

let get_fp_value = get_value fp_value_of_repr

(* Mode of [rep] if known, with its explanation. *)
let known_mode rep =
  match get_value mode_of_repr rep with
  | Some (m, ex) -> Some m, ex
  | None -> None, Ex.empty

let float_format t =
  match E.type_info t with Ty.Tfloat (eb, sb) -> eb, sb | _ -> assert false

(* Integers [[lo, hi)] of an [n]-bit bit-vector. *)
let bv_range ~signed n =
  if signed
  then
    let p = Z.shift_left Z.one (n - 1) in
    Z.minus p, p
  else Z.zero, Z.shift_left Z.one n

let lit_fact ex f = Literal.LTerm f, ex, Th_util.Other

let eq_lit_fact ex r t =
  ( Literal.LSem (Shostak.L.view (Shostak.L.mk_eq r (fst (X.make t)))),
    ex,
    Th_util.Other )

(* [t = v], as a term so that [v] gets its literal facts. *)
let eq_float_fact ex t v eb sb =
  lit_fact ex (E.mk_eq ~iff:false t (E.float v eb sb))

(* Evaluation of the conversions of [conv_kind] once their arguments are
   constants.

   An application keeps its representative and those of its arguments, with
   explanations. Its rules run when it is registered, and when one of these
   representatives changes. *)
module Conv_watch = struct
  type args =
    | Bits of
        { sign : X.r * Ex.t;
          exp : X.r * Ex.t;
          mant : X.r * Ex.t
        }  (** of [fp sign exp mant] *)
    | Rounded of
        { mode : X.r * Ex.t;
          arg : X.r * Ex.t
        }  (** of the other conversions, applied to [mode] and [arg] *)

  type app =
    { kind : conv_kind;
      r : X.r * Ex.t;  (** the application *)
      args : args
    }

  let reps app =
    match app.args with
    | Bits { sign; exp; mant } -> [app.r; sign; exp; mant]
    | Rounded { mode; arg } -> [app.r; mode; arg]

  type t =
    { apps : app E.Map.t;
      watched : E.Set.t MX.t;  (** representative -> applications using it *)
      dirty : E.Set.t;  (** applications to rerun *)
      facts : X.r Sig_rel.fact list  (** pending facts *)
    }

  type _ Uf.id += Id : t Uf.id

  exception Inconsistent of Ex.t

  let empty =
    { apps = E.Map.empty; watched = MX.empty; dirty = E.Set.empty; facts = [] }

  let pp ppf t =
    Fmt.pf ppf "{conv_watch: %d applications}" (E.Map.cardinal t.apps)

  let filter_ty _ = true

  let init _ t = t

  (* [term = fp s e m]. *)
  let of_bits term ~sign ~exp ~mant =
    let eb, sb = float_format term in
    match get_bv_value sign, get_bv_value exp, get_bv_value mant with
    | Some (zs, ex_s), Some (ze, ex_e), Some (zm, ex_m) ->
      let v =
        Fp_value.mk_fp_literal ~neg:(Z.equal zs Z.one)
          ~biased_exp:(Option.get (Z.to_machine_int ze))
          ~mantissa:zm ~eb ~sb
      in
      [eq_float_fact (Ex.union ex_s (Ex.union ex_e ex_m)) term v eb sb]
    | _ -> []

  (* [term = of_int mode i]. *)
  let of_int term ~mode ~arg =
    let eb, sb = float_format term in
    match known_mode mode, get_int_value arg with
    | (Some m, ex_m), Some (i, ex_i) ->
      [ eq_float_fact (Ex.union ex_m ex_i) term
          (Fp_value.of_q ~eb ~sb m (Q.from_z i))
          eb sb ]
    | _ -> []

  (* [term = from_real mode r]. *)
  let of_real term ~mode ~arg =
    let eb, sb = float_format term in
    match known_mode mode, get_real_value arg with
    | (Some m, ex_m), Some (q, ex_q) ->
      [eq_float_fact (Ex.union ex_m ex_q) term (Fp_value.of_q ~eb ~sb m q) eb sb]
    | _ -> []

  (* [term = to_int mode x], where specified. *)
  let to_int (r, ex_r) ~mode ~arg =
    let m, ex_m = known_mode mode in
    match get_fp_value arg with
    | Some (v, ex_x) -> (
      match Fp_value.to_integer m v with
      | Some z ->
        [eq_lit_fact (Ex.union ex_r (Ex.union ex_m ex_x)) r (E.Ints.of_Z z)]
      | None -> [])
    | None -> []

  (* [term = to_fp mode x]. Widening is exact, so it does not need [mode]. *)
  let to_fp term ~mode ~arg =
    match E.term_view term with
    | { E.xs = [_; _; _; x]; ty = Ty.Tfloat (eb2, sb2); _ } -> (
      let eb1, sb1 = float_format x in
      let m, ex_m =
        if eb1 <= eb2 && sb1 <= sb2
        then Some Dolmen.Std.Builtin.Float.RoundNearestTiesToEven, Ex.empty
        else known_mode mode
      in
      match get_fp_value arg with
      | Some (v, ex_x) -> (
        match Fp_value.convert ~eb:eb2 ~sb:sb2 m v with
        | Some v -> [eq_float_fact (Ex.union ex_m ex_x) term v eb2 sb2]
        | None -> [])
      | None -> [])
    | _ -> assert false

  (* [term = to_ubv n mode x] ([signed = false]) or [term = to_sbv n mode x],
     where specified: [x] finite and in range once rounded. *)
  let to_bv ~signed n (r, ex_r) ~mode ~arg =
    let lo, hi = bv_range ~signed n in
    let m, ex_m = known_mode mode in
    match get_fp_value arg with
    | Some (v, ex_x) -> (
      match Fp_value.to_integer m v with
      | Some z when Z.compare lo z <= 0 && Z.compare z hi < 0 ->
        [ eq_lit_fact
            (Ex.union ex_r (Ex.union ex_m ex_x))
            r (E.BV.of_Z ~size:n z) ]
      | _ -> [])
    | None -> []

  (* Runs the rules of [term] and queues their facts. *)
  let apply_conv_rules term app t =
    let facts =
      match app.kind, app.args with
      | Of_bits, Bits { sign; exp; mant } -> of_bits term ~sign ~exp ~mant
      | Of_int, Rounded { mode; arg } -> of_int term ~mode ~arg
      | Of_real, Rounded { mode; arg } -> of_real term ~mode ~arg
      | To_int, Rounded { mode; arg } -> to_int app.r ~mode ~arg
      | To_fp, Rounded { mode; arg } -> to_fp term ~mode ~arg
      | To_bv (signed, n), Rounded { mode; arg } ->
        to_bv ~signed n app.r ~mode ~arg
      | _ -> assert false
    in
    { t with facts = facts @ t.facts }

  let register uf term kind t =
    if E.Map.mem term t.apps
    then t
    else
      let find = Uf.find uf in
      let args =
        match kind, E.term_view term with
        | Of_bits, { E.xs = [_; _; s; e; m]; _ } ->
          Bits { sign = find s; exp = find e; mant = find m }
        | _, { E.xs = [_; _; mode; arg]; _ } ->
          Rounded { mode = find mode; arg = find arg }
        | _ -> assert false
      in
      let app = { kind; r = find term; args } in
      let watched =
        List.fold_left
          (fun watched (r, _) ->
            let terms =
              Option.value ~default:E.Set.empty (MX.find_opt r watched)
            in
            MX.add r (E.Set.add term terms) watched)
          t.watched (reps app)
      in
      apply_conv_rules term app
        { t with apps = E.Map.add term app t.apps; watched }

  let subst ~ex rr nrr t =
    match MX.find_opt rr t.watched with
    | None -> t
    | Some terms ->
      let update ((r, ex_r) as rep) =
        if X.equal r rr then nrr, Ex.union ex_r ex else rep
      in
      let update_reps app =
        let args =
          match app.args with
          | Bits { sign; exp; mant } ->
            Bits { sign = update sign; exp = update exp; mant = update mant }
          | Rounded { mode; arg } ->
            Rounded { mode = update mode; arg = update arg }
        in
        { app with r = update app.r; args }
      in
      let apps =
        E.Set.fold
          (fun term apps -> E.Map.update term (Option.map update_reps) apps)
          terms t.apps
      in
      let on_nrr =
        match MX.find_opt nrr t.watched with
        | Some s -> E.Set.union terms s
        | None -> terms
      in
      { t with
        apps;
        watched = MX.add nrr on_nrr (MX.remove rr t.watched);
        dirty = E.Set.union terms t.dirty
      }

  (* Reruns the dirty applications and returns the pending facts. *)
  let flush t =
    let t =
      E.Set.fold
        (fun term t ->
          match E.Map.find_opt term t.apps with
          | Some app -> apply_conv_rules term app t
          | None -> t)
        t.dirty
        { t with dirty = E.Set.empty }
    in
    t.facts, { t with facts = [] }
end

(* Registers [term] in [Conv_watch] if it is a conversion. *)
let register_conv uf term ds =
  match conv_kind term with
  | Some kind ->
    let cw = Uf.GlobalDomains.find (module Conv_watch) ds in
    Uf.GlobalDomains.add
      (module Conv_watch)
      (Conv_watch.register uf term kind cw)
      ds
  | None -> ds

type t =
  { seen_types : IntPairSet.t;
        (* formats whose precision facts are sent or pending in this env *)
    pending_types : IntPairSet.t;
    pending_literals : (E.t * E.t) list;
    new_terms : E.Set.t;
    defs : E.Set.t
  }

let empty uf =
  ( { seen_types = IntPairSet.empty;
      pending_types = IntPairSet.empty;
      pending_literals = [];
      new_terms = E.Set.empty;
      defs = E.Set.empty
    },
    Uf.domains uf
    |> Uf.GlobalDomains.add (module AEFloat_arg_watch) AEFloat_arg_watch.empty
    |> Uf.GlobalDomains.add (module Conv_watch) Conv_watch.empty )

let pow2 n = Z.shift_left Z.one n

let mk_eq_fact ~ex lhs rhs =
  Literal.LTerm (E.mk_eq ~iff:false lhs rhs), ex, Th_util.Other

let int_literal_fact eb_t sb_t name literal (terms, facts) =
  let lhs = E.mk_term (Sy.name name) [eb_t; sb_t] Ty.Tint in
  ( E.Set.add lhs terms,
    mk_eq_fact ~ex:Ex.empty lhs (E.Ints.of_Z literal) :: facts )

let real_literal_fact eb_t sb_t name literal (terms, facts) =
  let lhs = E.mk_term (Sy.name name) [eb_t; sb_t] Ty.Treal in
  ( E.Set.add lhs terms,
    mk_eq_fact ~ex:Ex.empty lhs (E.Reals.of_Q literal) :: facts )

let real_literal_fact_z eb_t sb_t name literal =
  real_literal_fact eb_t sb_t name (Q.from_z literal)

let zero_literal_fact eb sb (terms, facts) =
  let ty = Ty.Tfloat (eb, sb) in
  let lhs =
    E.mk_term (Sy.name Names.zeroF) [E.Ints.of_int eb; E.Ints.of_int sb] ty
  in
  ( E.Set.add lhs terms,
    mk_eq_fact ~ex:Ex.empty lhs (E.float Fp_value.Plus_zero eb sb) :: facts )

let compute_emax_min_exp eb sb =
  let bias = (1 lsl (eb - 1)) - 1 in
  let emax = bias + 1 in
  let min_exp = emax + sb - 3 in
  emax, min_exp

(* The constants of the prelude for the format [(eb, sb)], as facts, sent when
   the format is first seen in the current branch of the search. *)
let type_literal_facts eb sb =
  let _, min_exp = compute_emax_min_exp eb sb in
  let max_real_q = Fp_value.max_finite_q ~eb ~sb in
  let eb_t = E.Ints.of_int eb in
  let sb_t = E.Ints.of_int sb in
  (E.Set.empty, [])
  |> int_literal_fact eb_t sb_t E.FP.Names.pow2sb (pow2 sb)
  |> int_literal_fact eb_t sb_t E.FP.Names.max_int (Q.to_z (Q.floor max_real_q))
  |> real_literal_fact eb_t sb_t E.FP.Names.max_real max_real_q
  |> real_literal_fact_z eb_t sb_t E.FP.Names.pow2sb_real (pow2 sb)
  |> real_literal_fact_z eb_t sb_t E.FP.Names.half_pow2sb_real (pow2 (sb - 1))
  |> real_literal_fact_z eb_t sb_t E.FP.Names.abs_err_rne_denom
       (pow2 (min_exp + 1))
  |> real_literal_fact_z eb_t sb_t E.FP.Names.abs_err_denom (pow2 min_exp)
  |> zero_literal_fact eb sb

let mk_fp_literal_facts eb_t sb_t term ?(is_nan = false) ?(is_zero = false)
    ?(is_infinite = false) ?(is_positive = false) ?(is_negative = false) () =
  let mk_fact name b =
    E.mk_term (Sy.name name) [eb_t; sb_t; term] Ty.Tbool, E.Core.bool b
  in
  [ mk_fact Names.is_nan is_nan;
    mk_fact Names.is_finite (not (is_nan || is_infinite));
    mk_fact Names.is_zero is_zero;
    mk_fact Names.is_infinite is_infinite;
    mk_fact Names.is_positive is_positive;
    mk_fact Names.is_negative is_negative ]

let fp_literal_facts eb sb term v =
  let eb_t = E.Ints.of_int eb in
  let sb_t = E.Ints.of_int sb in
  let mk = mk_fp_literal_facts eb_t sb_t term in
  match v with
  | Fp_value.NaN -> mk ~is_nan:true ()
  | Plus_infinity -> mk ~is_infinite:true ~is_positive:true ()
  | Minus_infinity -> mk ~is_infinite:true ~is_negative:true ()
  | Plus_zero -> mk ~is_zero:true ~is_positive:true ()
  | Minus_zero -> mk ~is_zero:true ~is_negative:true ()
  | Finite q ->
    let to_real_term =
      E.mk_term (Sy.name Names.to_real) [eb_t; sb_t; term] Ty.Treal
    in
    (to_real_term, E.Reals.of_Q q)
    :: mk ~is_positive:(Q.sign q > 0) ~is_negative:(Q.sign q < 0) ()

(* [is_normal] and [is_subnormal] of a literal. *)
let normal_literal_facts eb sb term v =
  let mk_fact name b =
    ( E.mk_term (Sy.name name)
        [E.Ints.of_int eb; E.Ints.of_int sb; term]
        Ty.Tbool,
      E.Core.bool b )
  in
  [ mk_fact Names.is_normal (Fp_value.is_normal ~eb v);
    mk_fact Names.is_subnormal (Fp_value.is_subnormal ~eb v) ]

let register_aefloat_arg_watch uf term ds =
  match E.term_view term with
  | { E.f = Sy.Op FloatEbSb; xs = [eb; sb; mode; _x]; _ } -> (
    (* [ae.float] is only built by the prelude, whose precisions are literals.
       Applications built by hand with other precisions are left
       uninterpreted. *)
    match E.int_view eb, E.int_view sb with
    | eb, sb ->
      let r_mode, _ = Uf.find uf mode in
      let args = { AEFloat_arg_watch.eb; sb; mode } in
      let fw = Uf.GlobalDomains.find (module AEFloat_arg_watch) ds in
      let fw = AEFloat_arg_watch.register term args r_mode fw in
      Uf.GlobalDomains.add (module AEFloat_arg_watch) fw ds
    | exception Failure _ -> ds)
  | _ -> ds

let normal_pred term =
  match E.term_view term with
  | { E.f = Sy.Name { hs; _ }; xs = [eb_t; sb_t; x]; ty = Ty.Tbool; _ } -> (
    let name = Hstring.view hs in
    match E.term_view x with
    | { E.f = Sy.Float _; _ } -> None
    | { E.ty = Ty.Tfloat (eb, sb); _ }
      when String.equal name Names.is_normal
           || String.equal name Names.is_subnormal ->
      (* TODO: make sure that users cannot create these terms by hand (or that
         they are well-typed) *)
      assert (E.equal eb_t (E.Ints.of_int eb) && E.equal sb_t (E.Ints.of_int sb));
      Some (String.equal name Names.is_normal, eb, sb, x)
    | _ -> None)
  | _ -> None

(* [is_normal x <-> is_finite x /\ (to_real x <= -c \/ c <= to_real x)] and
   [is_subnormal x <-> is_finite x /\ not is_zero x /\ -c < to_real x < c]. *)
let normal_definition term (normal, eb, sb, x) =
  let c = Fp_value.min_normal_q ~eb in
  let r = E.FP.to_real ~eb ~sb x in
  let is_finite = E.FP.is_finite ~eb ~sb x in
  let minus_c = E.Reals.of_Q (Q.minus c) in
  let c = E.Reals.of_Q c in
  let body =
    if normal
    then
      E.mk_and is_finite
        (E.mk_or E.Reals.(r <= minus_c) E.Reals.(c <= r) false)
        false
    else
      E.mk_and is_finite
        (E.mk_and
           (E.neg (E.FP.is_zero ~eb ~sb x))
           (E.mk_and E.Reals.(minus_c < r) E.Reals.(r < c) false)
           false)
        false
  in
  E.mk_iff term body

let mk_clause = function
  | [] -> assert false
  | l :: ls -> List.fold_left (fun acc l -> E.mk_or acc l false) l ls

let class_clauses x =
  let eb, sb = float_format x in
  let is_nan = E.FP.is_nan ~eb ~sb x in
  let is_infinite = E.FP.is_infinite ~eb ~sb x in
  let is_finite = E.FP.is_finite ~eb ~sb x in
  let is_zero = E.FP.is_zero ~eb ~sb x in
  let is_positive = E.FP.is_positive ~eb ~sb x in
  let is_negative = E.FP.is_negative ~eb ~sb x in
  let is v = E.mk_eq ~iff:false x (E.float v eb sb) in
  let rec at_most_one = function
    | [] -> []
    | a :: l -> List.map (fun b -> [E.neg a; E.neg b]) l @ at_most_one l
  in
  (* [is_normal] and [is_subnormal] are left out for now, they would bring the
     [normal_definition] of every float, and thus its [to_real], into
     arithmetic. *)
  let classes = [is_nan; is_infinite; is_finite] in
  List.map mk_clause
    ((classes :: at_most_one classes)
    @ [ [E.neg is_zero; is_finite];
        [is_nan; is_positive; is_negative];
        [E.neg is_positive; E.neg is_negative];
        [E.neg is_nan; E.neg is_positive];
        [E.neg is_nan; E.neg is_negative];
        [E.neg is_nan; is Fp_value.NaN];
        [E.neg is_zero; E.neg is_positive; is Fp_value.Plus_zero];
        [E.neg is_zero; E.neg is_negative; is Fp_value.Minus_zero];
        [E.neg is_infinite; E.neg is_positive; is Fp_value.Plus_infinity];
        [E.neg is_infinite; E.neg is_negative; is Fp_value.Minus_infinity] ])

let definitions term =
  match normal_pred term with
  | Some p -> "fpa_normal_definition", [normal_definition term p]
  | None -> "fpa_class_clauses", class_clauses term

let add env uf _r term =
  if not (Options.get_smt_lib_fpa ())
  then env, Uf.domains uf, []
  else
    let { E.f; ty; _ } = E.term_view term in
    match ty with
    | Ty.Tfloat (eb, sb) ->
      let env =
        if IntPairSet.mem (eb, sb) env.seen_types
        then env
        else
          { env with
            seen_types = IntPairSet.add (eb, sb) env.seen_types;
            pending_types = IntPairSet.add (eb, sb) env.pending_types
          }
      in
      let env =
        match f with
        | Sy.Float v ->
          if Options.get_debug_fpa () > 0
          then
            Printer.print_dbg ~module_name:"Fpa_rel" ~function_name:"add"
              "queueing literal facts for %a" E.print term;
          { env with
            pending_literals =
              fp_literal_facts eb sb term v
              @ normal_literal_facts eb sb term v
              @ env.pending_literals
          }
        | _ -> { env with defs = E.Set.add term env.defs }
      in
      env, register_conv uf term (Uf.domains uf), []
    | Ty.Treal ->
      (* ae.float applies ae.round on reals *)
      let ds = register_aefloat_arg_watch uf term (Uf.domains uf) in
      env, ds, []
    | _ ->
      let env =
        if Option.is_some (normal_pred term)
        then { env with defs = E.Set.add term env.defs }
        else env
      in
      env, register_conv uf term (Uf.domains uf), []

let mk_aefloat_eq_fact uf term { AEFloat_arg_watch.eb; sb; mode } =
  match E.term_view term with
  | { E.xs = [_; _; _; x]; _ } ->
    let r_mode, ex = Uf.find uf mode in
    (* [mode] is in [ready], so its representative is a literal. *)
    let mode = Option.get (X.to_model_term r_mode) in
    let _, min_exp = compute_emax_min_exp eb sb in
    let repl =
      E.mk_term (Sy.Op Float)
        [E.Ints.of_int sb; E.Ints.of_int min_exp; mode; x]
        Ty.Treal
    in
    repl, mk_eq_fact ~ex term repl
  | _ -> assert false

let assume env uf _la =
  if not (Options.get_smt_lib_fpa ())
  then env, Uf.domains uf, { Sig_rel.assume = []; remove = [] }
  else
    let ds = Uf.domains uf in
    let new_terms, prec_facts =
      IntPairSet.fold
        (fun (eb, sb) (terms_acc, facts_acc) ->
          let terms, facts = type_literal_facts eb sb in
          E.Set.union terms terms_acc, facts @ facts_acc)
        env.pending_types (E.Set.empty, [])
    in
    let eval_facts =
      List.map
        (fun (lhs, rhs) -> mk_eq_fact ~ex:Ex.empty lhs rhs)
        env.pending_literals
    in
    let env =
      { env with
        pending_types = IntPairSet.empty;
        pending_literals = [];
        new_terms = E.Set.union new_terms env.new_terms
      }
    in
    let aefloat_arg_watch =
      Uf.GlobalDomains.find (module AEFloat_arg_watch) ds
    in
    let ready, aefloat_arg_watch =
      AEFloat_arg_watch.flush_ready aefloat_arg_watch
    in
    let aefloat_terms, aefloat_facts =
      List.split
        (E.Map.fold
           (fun term p acc -> mk_aefloat_eq_fact uf term p :: acc)
           ready [])
    in
    let env =
      { env with
        new_terms =
          List.fold_left
            (fun acc t -> E.Set.add t acc)
            env.new_terms aefloat_terms
      }
    in
    let ds =
      Uf.GlobalDomains.add (module AEFloat_arg_watch) aefloat_arg_watch ds
    in
    let conv_facts, conv_watch =
      Conv_watch.flush (Uf.GlobalDomains.find (module Conv_watch) ds)
    in
    let ds = Uf.GlobalDomains.add (module Conv_watch) conv_watch ds in
    (* New terms of the facts, for matching. *)
    let env =
      { env with
        new_terms =
          List.fold_left
            (fun acc (lit, _, _) ->
              match lit with
              | Literal.LTerm f -> E.Set.union (E.max_terms_of_lit f) acc
              | Literal.LSem _ -> acc)
            env.new_terms conv_facts
      }
    in
    ( env,
      ds,
      { Sig_rel.assume = prec_facts @ eval_facts @ aefloat_facts @ conv_facts;
        remove = []
      } )

let query _ _ _ = Th_util.Unknown

let case_split _env _uf ~for_model:_ = []

let optimizing_objective _env _uf _o = None

let new_terms env = env.new_terms

(* Sends the lemmas of [defs] to the SAT solver: the definitions of [is_normal]
   and [is_subnormal], and the class clauses of the floats. *)
let instantiate ~do_syntactic_matching _ env _uf selector =
  (* only send the lemmas once per round, in the syntactic pass, rather than
     again in each of the semantic passes. *)
  if (not (Options.get_smt_lib_fpa ())) || not do_syntactic_matching
  then env, []
  else
    let insts =
      E.Set.fold
        (fun term acc ->
          let origin_name, ffs = definitions term in
          List.fold_left
            (fun acc ff ->
              if selector ff ff
              then
                let gf =
                  { E.ff;
                    origin_name;
                    trigger_depth = 0;
                    gdist = -1;
                    hdist = -1;
                    nb_reductions = 0;
                    age = 0;
                    mf = true;
                    gf = false;
                    lem = None;
                    from_terms = [term];
                    theory_elim = false
                  }
                in
                ([], gf, Ex.empty) :: acc
              else acc)
            acc ffs)
        env.defs []
    in
    env, insts

let assume_th_elt t _ _ = t

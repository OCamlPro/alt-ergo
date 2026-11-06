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
  | Rem  (** [Sy.Float_rem] applied to [x y] *)
  | Eval  (** the float operators of [evaluated] *)
  | To_real  (** [ae.fp.to_real eb sb x] *)
  | Cmp  (** [ae.fp.le], [ae.fp.lt] and [ae.fp.eq] *)

(* The comparisons are not evaluated with the operators: that would make the BV
   case splits enumerate the values of their arguments before the prelude axioms
   conclude. *)
let evaluated =
  Names.[add; sub; mul; div; fma; sqrt; round_to_integral; abs; neg; min; max]

let is_name hs names = List.exists (String.equal (Hstring.view hs)) names

let conv_kind term =
  match E.term_view term with
  | { E.f = Sy.Op Float_of_bits; xs = [_; _; _; _; _]; _ } -> Some Of_bits
  | { E.f = Sy.Op Float_to_fp; xs = [_; _; _; _]; _ } -> Some To_fp
  | { E.f = Sy.Op (Float_to_ubv n); xs = [_; _; _; _]; _ } ->
    Some (To_bv (false, n))
  | { E.f = Sy.Op (Float_to_sbv n); xs = [_; _; _; _]; _ } ->
    Some (To_bv (true, n))
  | { E.f = Sy.Op Float_rem; xs = [_; _]; _ } -> Some Rem
  | { E.f = Sy.Name { hs; _ }; xs = [_; _; _; _]; ty = Ty.Tfloat _; _ }
    when String.equal (Hstring.view hs) Names.of_int ->
    Some Of_int
  | { E.f = Sy.Name { hs; _ }; xs = [_; _; _; _]; ty = Ty.Tfloat _; _ }
    when String.equal (Hstring.view hs) Names.of_real ->
    Some Of_real
  | { E.f = Sy.Name { hs; _ }; xs = [_; _; _; _]; ty = Ty.Tint; _ }
    when String.equal (Hstring.view hs) Names.to_int ->
    Some To_int
  | { E.f = Sy.Name { hs; _ }; xs = _ :: _ :: _; ty = Ty.Tfloat _; _ }
    when is_name hs evaluated ->
    Some Eval
  | { E.f = Sy.Name { hs; _ }; xs = [_; _; _]; ty = Ty.Treal; _ }
    when String.equal (Hstring.view hs) Names.to_real ->
    Some To_real
  | { E.f = Sy.Name { hs; _ }; xs = [_; _; _; _]; ty = Ty.Tbool; _ }
    when is_name hs Names.[le; lt; eq] ->
    Some Cmp
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

let mk_clause = function
  | [] -> assert false
  | l :: ls -> List.fold_left (fun acc l -> E.mk_or acc l false) l ls

let pred_fact ex mk ~eb ~sb t b =
  let f = mk ~eb ~sb t in
  lit_fact ex (if b then f else E.neg f)

let z_to_int z = Option.get (Z.to_machine_int z)

let all_ones n = Z.sub (Z.shift_left Z.one n) Z.one

let real_of_int t = E.mk_term (Sy.Op Sy.Real_of_int) [t] Ty.Treal

(* [to_real term] for a finite [term = fp neg biased_exp m], linear in [bv2nat
   m]. *)
let of_bits_to_real eb sb term ~neg ~biased_exp m =
  let bias = (1 lsl (eb - 1)) - 1 in
  let significand, k =
    if biased_exp > 0
    then
      let hidden_bit = E.Ints.of_Z (Z.shift_left Z.one (sb - 1)) in
      E.Ints.(hidden_bit + E.BV.ubv_to_int m), biased_exp - bias - (sb - 1)
    else E.BV.ubv_to_int m, 1 - bias - (sb - 1)
  in
  let c = if k >= 0 then Q.mult_2exp Q.one k else Q.div_2exp Q.one (-k) in
  let c = if neg then Q.minus c else c in
  E.mk_eq ~iff:false
    (E.FP.to_real ~eb ~sb term)
    E.Reals.(of_Q c * real_of_int significand)

let bv_width bv =
  match E.type_info bv with Ty.Tbitv n -> n | _ -> assert false

(* [Some (bv, signed, exact)] if [i] is the integer of the bit-vector [bv] and
   its conversion to [(eb, sb)] cannot overflow. [exact] if it is not
   rounded. *)
let bv_int_conversion eb sb i =
  match E.FP.of_bv_int_view i with
  | Some (bv, signed) ->
    let bits = if signed then bv_width bv - 1 else bv_width bv in
    let bound = Q.from_z (Z.shift_left Z.one bits) in
    if Q.compare bound (Fp_value.max_finite_q ~eb ~sb) <= 0
    then Some (bv, signed, bits <= sb)
    else None
  | None -> None

(* [term = of_int mode i], where [i] is the integer of a bit-vector: [term] is
   not NaN nor subnormal, and positive if unsigned. It is finite if it cannot
   overflow, or if the mode rounds an overflow to the largest finite value.
   Without overflow, [to_real term] is [i], rounded unless exact. *)
let of_bv_int_facts term =
  match E.term_view term with
  | { E.xs = [eb_t; sb_t; mode; i]; ty = Ty.Tfloat (eb, sb); _ } -> (
    match E.FP.of_bv_int_view i with
    | Some (_, signed) ->
      let pred mk b = if b then mk ~eb ~sb term else E.neg (mk ~eb ~sb term) in
      let conv = bv_int_conversion eb sb i in
      let module RM = Dolmen.Std.Builtin.Float in
      let finite =
        Option.is_some conv
        ||
        match E.rounding_mode_view mode with
        | Some RM.RoundTowardZero -> true
        | Some RM.RoundTowardNegative -> not signed
        | Some
            ( RM.RoundNearestTiesToEven | RoundNearestTiesToAway
            | RoundTowardPositive )
        | None ->
          false
      in
      let value =
        match conv with
        | Some (_, _, exact) ->
          let v =
            if exact
            then real_of_int i
            else
              E.mk_term (Sy.Op FloatEbSb)
                [eb_t; sb_t; mode; real_of_int i]
                Ty.Treal
          in
          [E.mk_eq ~iff:false (E.FP.to_real ~eb ~sb term) v]
        | None -> []
      in
      List.concat
        [ [pred E.FP.is_nan false; pred E.FP.is_subnormal false];
          (if signed then [] else [pred E.FP.is_positive true]);
          (if finite
           then [pred E.FP.is_finite true; pred E.FP.is_infinite false]
           else []);
          value ]
    | None -> [])
  | _ -> []

(* [Some (eb, sb, f)] if [term = of_int mode i], where [i] is the integer of a
   bit-vector whose conversion can overflow, and [f = ae.float(eb, sb, mode, i)]
   is the real value of [term] when it is in range. *)
let of_bv_int_overflow term =
  match E.term_view term with
  | { E.f = Sy.Name { hs; _ };
      xs = [eb_t; sb_t; mode; i];
      ty = Ty.Tfloat (eb, sb);
      _
    }
    when String.equal (Hstring.view hs) Names.of_int -> (
    match E.FP.of_bv_int_view i, bv_int_conversion eb sb i with
    | Some _, None ->
      Some
        ( eb,
          sb,
          E.mk_term (Sy.Op FloatEbSb) [eb_t; sb_t; mode; real_of_int i] Ty.Treal
        )
    | _ -> None)
  | _ -> None

let is_fpa_ty = function Ty.Tfloat _ -> true | _ -> false

let r_true () = fst (X.make E.vrai)

let r_false () = fst (X.make E.faux)

(* The predicates of the FPA prelude, read from the union-find. *)
module Pred = struct
  type t =
    | Nan
    | Zero
    | Infinite
    | Normal
    | Subnormal
    | Positive
    | Negative

  let all = [Nan; Zero; Infinite; Normal; Subnormal; Positive; Negative]

  let to_expr p x =
    let eb, sb = float_format x in
    (match p with
    | Nan -> E.FP.is_nan
    | Zero -> E.FP.is_zero
    | Infinite -> E.FP.is_infinite
    | Normal -> E.FP.is_normal
    | Subnormal -> E.FP.is_subnormal
    | Positive -> E.FP.is_positive
    | Negative -> E.FP.is_negative)
      ~eb ~sb x

  (* Truth value of [p x], if [p x] is a known term equal to [true] or
     [false]. *)
  let status uf x p =
    let a = to_expr p x in
    if not (Uf.mem uf a)
    then None
    else
      let r, ex = Uf.find uf a in
      if X.equal r (r_true ())
      then Some (true, ex)
      else if X.equal r (r_false ())
      then Some (false, ex)
      else None

  let is uf x p b =
    match status uf x p with
    | Some (b', ex) when Bool.equal b b' -> Some ex
    | Some _ | None -> None

  let fact ex p x b =
    let a = to_expr p x in
    lit_fact ex (if b then a else E.neg a)
end

(* Classes of floats, propagated through the operators and the comparisons. In
   the order of the values, [-oo], the negative normal and subnormal values,
   [-0], [+0], the positive subnormal and normal values and [+oo] are [0] to
   [7], and NaN is [8]. A set of classes is a bit mask. *)
module Cls = struct
  let nan = 8

  (* Magnitudes. *)
  let zero = 0

  let sub = 1

  let norm = 2

  let inf = 3

  let neg c = c < 4

  let mag c = if neg c then 3 - c else c - 4

  let mk m neg = if neg then 3 - m else 4 + m

  let bit c = 1 lsl c

  let all = bit 9 - 1

  let some ms neg = List.fold_left (fun acc m -> acc lor bit (mk m neg)) 0 ms

  let both m = some [m] false lor some [m] true

  let elements m = List.filter (fun c -> m land bit c <> 0) (List.init 9 Fun.id)

  (* Order of the values, the zeros being equal. *)
  let key c = if c = mk zero true then mk zero false else c

  let of_pred (p : Pred.t) =
    match p with
    | Nan -> bit nan
    | Zero -> both zero
    | Infinite -> both inf
    | Normal -> both norm
    | Subnormal -> both sub
    | Positive -> 0xF0
    | Negative -> 0x0F

  (* Classes allowed by the predicates known on [x], with their explanation. *)
  let of_preds uf x =
    List.fold_left
      (fun (m, ex) p ->
        match Pred.status uf x p with
        | Some (b, ex') ->
          let pm = of_pred p in
          (if b then m land pm else m land lnot pm), Ex.union ex ex'
        | None -> m, ex)
      (all, Ex.empty) Pred.all

  (* Facts on [x] from its classes [m], for the predicates not known yet. An
     empty [m] is a conflict. *)
  let facts uf ex x m =
    if m = 0
    then [Pred.fact ex Nan x true; Pred.fact ex Nan x false]
    else
      List.filter_map
        (fun p ->
          let pm = of_pred p in
          match Pred.status uf x p with
          | Some _ -> None
          | None when m land pm = m -> Some (Pred.fact ex p x true)
          | None when m land pm = 0 -> Some (Pred.fact ex p x false)
          | None -> None)
        Pred.all

  (* IEEE 754 on non-NaN classes, in any rounding mode. *)
  let add a b =
    let same = Bool.equal (neg a) (neg b) and ma = mag a and mb = mag b in
    if ma = inf && mb = inf
    then bit (if same then a else nan)
    else if ma = inf || (mb = zero && ma <> zero)
    then bit a
    else if mb = inf || (ma = zero && mb <> zero)
    then bit b
    else if ma = zero
    then if same then bit a else both zero
    else if same
    then some [sub; norm; inf] (neg a)
    else both zero lor both sub lor both norm

  let mul s a b =
    let ma = mag a and mb = mag b in
    if (ma = inf && mb = zero) || (ma = zero && mb = inf)
    then bit nan
    else if ma = inf || mb = inf
    then some [inf] s
    else if ma = zero || mb = zero
    then some [zero] s
    else some [zero; sub; norm; inf] s

  let div s a b =
    let ma = mag a and mb = mag b in
    if ma = mb && (ma = inf || ma = zero)
    then bit nan
    else if ma = inf || mb = zero
    then some [inf] s
    else if ma = zero || mb = inf
    then some [zero] s
    else some [zero; sub; norm; inf] s

  (* NaN is ignored, the zeros are unspecified. *)
  let min_max ~is_min a b =
    if a = nan
    then bit b
    else if b = nan || key a = key b
    then bit a lor if b = nan then 0 else bit b
    else bit (if Bool.equal (key a < key b) is_min then a else b)

  (* Classes of [name(args)] for the classes [args] of its float arguments. *)
  let transfer name args =
    let is = String.equal name in
    let xor a b = not (Bool.equal (neg a) (neg b)) in
    match args with
    | [a; b] when is Names.min -> min_max ~is_min:true a b
    | [a; b] when is Names.max -> min_max ~is_min:false a b
    | _ when List.mem nan args -> bit nan
    | [a] when is Names.neg -> bit (7 - a)
    | [a] when is Names.abs -> bit (mk (mag a) false)
    | [a] when is Names.sqrt ->
      if mag a = zero || (mag a = inf && not (neg a))
      then bit a
      else if neg a
      then bit nan
      else some [sub; norm] false
    | [a] when is Names.round_to_integral ->
      if mag a = zero || mag a = inf
      then bit a
      else some [zero; norm; inf] (neg a)
    | [a; b] when is Names.add -> add a b
    | [a; b] when is Names.sub -> add a (7 - b)
    | [a; b] when is Names.mul -> mul (xor a b) a b
    | [a; b] when is Names.div -> div (xor a b) a b
    | _ -> all

  (* Truth values of [name(a, b)], as a mask: [1] for false, [2] for true. *)
  let compare name a b =
    let tf b = if b then 2 else 1 in
    if a = nan || b = nan
    then tf false
    else if key a <> key b
    then tf ((not (String.equal name Names.eq)) && key a < key b)
    else if mag a = zero || mag a = inf
    then tf (not (String.equal name Names.lt))
    else 3

  (* Narrows [res], the results of [op] on [args], and [args] to the
     combinations of classes of [args] whose result is in [res]. *)
  let narrow op res args =
    let sup = Array.make (List.length args) 0 and res' = ref 0 in
    let rec go cs = function
      | [] ->
        let cs = List.rev cs in
        let r = op cs land res in
        if r <> 0
        then (
          res' := !res' lor r;
          List.iteri (fun i c -> sup.(i) <- sup.(i) lor bit c) cs)
      | m :: ms -> List.iter (fun c -> go (c :: cs) ms) (elements m)
    in
    go [] args;
    !res', Array.to_list sup
end

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
    | Ops of (X.r * Ex.t) list
        (** of [Eval], [To_real] and [Cmp], applied to these arguments after
            [eb] and [sb], and of [Rem] *)

  type app =
    { kind : conv_kind;
      r : X.r * Ex.t;  (** the application *)
      args : args
    }

  let reps app =
    match app.args with
    | Bits { sign; exp; mant } -> [app.r; sign; exp; mant]
    | Rounded { mode; arg } -> [app.r; mode; arg]
    | Ops l -> app.r :: l

  type t =
    { apps : app E.Map.t;
      watched : E.Set.t MX.t;  (** representative -> applications using it *)
      dirty : E.Set.t;  (** applications to rerun *)
      facts : X.r Sig_rel.fact list;  (** pending facts *)
      lemmas : E.t list  (** pending lemmas *)
    }

  type _ Uf.id += Id : t Uf.id

  exception Inconsistent of Ex.t

  let empty =
    { apps = E.Map.empty;
      watched = MX.empty;
      dirty = E.Set.empty;
      facts = [];
      lemmas = []
    }

  let pp ppf t =
    Fmt.pf ppf "{conv_watch: %d applications}" (E.Map.cardinal t.apps)

  let filter_ty _ = true

  let init _ t = t

  let watchers r t =
    match MX.find_opt r t.watched with Some s -> s | None -> E.Set.empty

  (* Value, once the bits are known. *)
  let of_bits_eval ~eb ~sb term s e m =
    match s, e, m with
    | Some (zs, ex_s), Some (ze, ex_e), Some (zm, ex_m) ->
      let v =
        Fp_value.mk_fp_literal ~neg:(Z.equal zs Z.one) ~biased_exp:(z_to_int ze)
          ~mantissa:zm ~eb ~sb
      in
      [eq_float_fact (Ex.union ex_s (Ex.union ex_e ex_m)) term v eb sb]
    | _ -> []

  (* Classes, from the exponent and the significand. *)
  let of_bits_classes ~eb ~sb term e m =
    let pred ex mk b = pred_fact ex mk ~eb ~sb term b in
    match e, m with
    | Some (ze, ex_e), _ when Z.equal ze (all_ones eb) -> (
      (* NaN or infinite. Infinite if [m = 0]. *)
      [ pred ex_e E.FP.is_zero false;
        pred ex_e E.FP.is_finite false;
        pred ex_e E.FP.is_normal false;
        pred ex_e E.FP.is_subnormal false ]
      @
      match m with
      | Some (zm, ex_m) ->
        let ex = Ex.union ex_e ex_m in
        let zero_m = Z.equal zm Z.zero in
        pred ex E.FP.is_nan (not zero_m)
        :: (if zero_m then [pred ex E.FP.is_infinite true] else [])
      | None -> [])
    | Some (ze, ex_e), _ -> (
      (* Finite. Normal if [e <> 0], otherwise zero if [m = 0] and subnormal if
         not. *)
      [ pred ex_e E.FP.is_nan false;
        pred ex_e E.FP.is_infinite false;
        pred ex_e E.FP.is_finite true ]
      @
      match m with
      | _ when not (Z.equal ze Z.zero) ->
        [pred ex_e E.FP.is_zero false; pred ex_e E.FP.is_normal true]
      | Some (zm, ex_m) ->
        let ex = Ex.union ex_e ex_m in
        let zero_m = Z.equal zm Z.zero in
        [ pred ex_e E.FP.is_normal false;
          pred ex E.FP.is_zero zero_m;
          pred ex E.FP.is_subnormal (not zero_m) ]
      | None -> [pred ex_e E.FP.is_normal false])
    | None, _ -> []

  (* Explanation that [fp s e m] is not NaN, if the bits show it. *)
  let of_bits_not_nan ~eb e m =
    match e, m with
    | Some (ze, ex_e), _ when not (Z.equal ze (all_ones eb)) -> Some ex_e
    | Some (_, ex_e), Some (zm, ex_m) when Z.equal zm Z.zero ->
      Some (Ex.union ex_e ex_m)
    | _ -> None

  (* Sign, if the bits show that it is not NaN. Otherwise, the clauses of
     [of_bits_clauses] give it. *)
  let of_bits_sign ~eb ~sb term s not_nan =
    match s, not_nan with
    | Some (zs, ex_s), Some ex_nn ->
      let ex = Ex.union ex_s ex_nn in
      let neg = Z.equal zs Z.one in
      [ pred_fact ex E.FP.is_negative ~eb ~sb term neg;
        pred_fact ex E.FP.is_positive ~eb ~sb term (not neg) ]
    | _ -> []

  (* Real value, if finite. *)
  let of_bits_real ~eb ~sb term m_term s e =
    match s, e with
    | Some (zs, ex_s), Some (ze, ex_e) when not (Z.equal ze (all_ones eb)) ->
      [ lit_fact (Ex.union ex_s ex_e)
          (of_bits_to_real eb sb term ~neg:(Z.equal zs Z.one)
             ~biased_exp:(z_to_int ze) m_term) ]
    | _ -> []

  (* Bits, once the value is known. NaN: [e] is all ones and [m <> 0]. *)
  let of_bits_args ~eb ~sb rep_r ~sign:(rs, ex_s) ~exp:(re, ex_e)
      ~mant:(rm, ex_m) =
    let bv sz z = E.BV.of_Z ~size:sz z in
    match get_fp_value rep_r with
    | None -> []
    | Some (v, ex_r) -> (
      match Fp_value.to_bits ~eb ~sb v with
      | Some (neg, biased_exp, mantissa) ->
        [ eq_lit_fact (Ex.union ex_r ex_s) rs
            (bv 1 (if neg then Z.one else Z.zero));
          eq_lit_fact (Ex.union ex_r ex_e) re (bv eb (Z.from_int biased_exp));
          eq_lit_fact (Ex.union ex_r ex_m) rm (bv (sb - 1) mantissa) ]
      | None ->
        let zero_m = fst (X.make (bv (sb - 1) Z.zero)) in
        [ eq_lit_fact (Ex.union ex_r ex_e) re (bv eb (all_ones eb));
          ( Literal.LSem
              (Shostak.L.view (Shostak.L.mk_distinct false [rm; zero_m])),
            Ex.union ex_r ex_m,
            Th_util.Other ) ])

  (* Injectivity on non-NaN values, for each other [fp] application [term'] in
     the class of [term]: facts that the bits are equal if the bits of [term]
     show that it is not NaN, and the lemma [term = term' -> is_nan term \/ same
     bits] otherwise. *)
  let of_bits_injectivity t term (r, ex_r) not_nan ~sign ~exp ~mant =
    match E.term_view term with
    | { E.xs = [_; _; s; e; m]; ty = Ty.Tfloat (eb, sb); _ } ->
      E.Set.fold
        (fun term' (facts, lemmas) ->
          match E.Map.find_opt term' t.apps, E.term_view term' with
          | ( Some { kind = Of_bits; r = r', ex_r'; args = Bits b' },
              { E.xs = [_; _; s'; e'; m']; _ } )
            when (not (E.equal term term')) && X.equal r r' -> (
            match not_nan with
            | Some ex_nn ->
              let ex = Ex.union ex_nn (Ex.union ex_r ex_r') in
              let same (r1, ex1) (r2, ex2) =
                ( Literal.LSem (Shostak.L.view (Shostak.L.mk_eq r1 r2)),
                  Ex.union ex (Ex.union ex1 ex2),
                  Th_util.Other )
              in
              ( same sign b'.sign :: same exp b'.exp :: same mant b'.mant
                :: facts,
                lemmas )
            | None when E.compare term term' < 0 ->
              let ne = E.neg (E.mk_eq ~iff:false term term') in
              let is_nan = E.FP.is_nan ~eb ~sb term in
              ( facts,
                List.map
                  (fun (a, b) -> mk_clause [ne; is_nan; E.mk_eq ~iff:false a b])
                  [s, s'; e, e'; m, m']
                @ lemmas )
            | None -> facts, lemmas)
          | _ -> facts, lemmas)
        (watchers r t) ([], [])
    | _ -> assert false

  (* [term = fp s e m]. *)
  let of_bits t term rep_r ~sign ~exp ~mant =
    match E.term_view term with
    | { E.xs = [_; _; _; _; m_term]; ty = Ty.Tfloat (eb, sb); _ } ->
      let s = get_bv_value sign in
      let e = get_bv_value exp in
      let m = get_bv_value mant in
      let not_nan = of_bits_not_nan ~eb e m in
      let inj_facts, inj_lemmas =
        of_bits_injectivity t term rep_r not_nan ~sign ~exp ~mant
      in
      ( List.concat
          [ of_bits_eval ~eb ~sb term s e m;
            of_bits_classes ~eb ~sb term e m;
            of_bits_sign ~eb ~sb term s not_nan;
            of_bits_real ~eb ~sb term m_term s e;
            of_bits_args ~eb ~sb rep_r ~sign ~exp ~mant;
            inj_facts ],
        inj_lemmas )
    | _ -> assert false

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
  let to_bv t term ~signed n (r, ex_r) ~mode ~arg:((r_x, ex_x) as arg) =
    let lo, hi = bv_range ~signed n in
    let eval =
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
    in
    (* If [x] is an exact conversion [of_int(int(bv))] and [bv] fits in [n]
       bits, [term] is [bv], extended. *)
    let of_exact =
      E.Set.fold
        (fun term' acc ->
          match E.Map.find_opt term' t.apps, E.term_view term' with
          | ( Some { kind = Of_int; r = r_i, ex_i; _ },
              { E.xs = [_; _; _; i]; ty = Ty.Tfloat (eb, sb); _ } )
            when X.equal r_x r_i -> (
            match bv_int_conversion eb sb i with
            | Some (bv, signed', true) ->
              let n' = bv_width bv in
              let lo', hi' = bv_range ~signed:signed' n' in
              if Z.compare lo lo' <= 0 && Z.compare hi' hi <= 0
              then
                let ext =
                  if signed'
                  then E.BV.sign_extend (n - n') bv
                  else E.BV.zero_extend (n - n') bv
                in
                lit_fact (Ex.union ex_x ex_i) (E.mk_eq ~iff:false term ext)
                :: acc
              else acc
            | Some (_, _, false) | None -> acc)
          | _ -> acc)
        (watchers r_x t) []
    in
    eval @ of_exact

  (* [term = rem x y]: the value, once [x] and [y] are literals. *)
  let rem term x y =
    match get_fp_value x, get_fp_value y with
    | Some (vx, ex_x), Some (vy, ex_y) ->
      let eb, sb = float_format term in
      [ eq_float_fact (Ex.union ex_x ex_y) term
          (Fp_value.rem ~eb ~sb vx vy)
          eb sb ]
    | _ -> []

  (* [term = rem(x, y)] with [y] equal to a nonzero finite literal [c]: [term]
     is exactly [x - c * n], with [n = integer_round(NearestTiesToEven, x / c)].
     Guarded by [y = c] so that it holds as a lemma. *)
  let rem_lemmas term rep_y =
    match E.term_view term, get_fp_value rep_y with
    | { E.xs = [x; y]; ty = Ty.Tfloat (eb, sb); _ }, Some ((Finite c as v), _)
      ->
      let rne =
        E.mk_constr
          (Fpa_rounding.term_cst_of_rounding_mode RoundNearestTiesToEven)
          [] Fpa_rounding.fpa_rounding_mode
      in
      let rx = E.FP.to_real ~eb ~sb x in
      let n =
        E.mk_term (Sy.Op Sy.Integer_round)
          [rne; E.Reals.(rx * of_Q (Q.inv c))]
          Ty.Tint
      in
      let value =
        E.mk_eq ~iff:false
          (E.FP.to_real ~eb ~sb term)
          E.Reals.(rx - (of_Q c * real_of_int n))
      in
      [ mk_clause
          [ E.neg (E.mk_eq ~iff:false y (E.float v eb sb));
            E.neg (E.FP.is_finite ~eb ~sb x);
            value ] ]
    | _ -> []

  let ex_of l = List.fold_left (fun acc (_, ex) -> Ex.union acc ex) Ex.empty l

  (* Bits of [term = fp s e m], from the predicates known on [term]. *)
  let of_bits_fields uf term ~sign:(rs, ex_s) ~exp:(re, ex_e) ~mant:(rm, ex_m) =
    let eb, sb = float_format term in
    let bv sz z = fst (X.make (E.BV.of_Z ~size:sz z)) in
    let zero_e = bv eb Z.zero and ones_e = bv eb (all_ones eb) in
    let zero_m = bv (sb - 1) Z.zero in
    let sem ex ex' l =
      Literal.LSem (Shostak.L.view l), Ex.union ex ex', Th_util.Other
    in
    let eq ex ex' r1 r2 = sem ex ex' (Shostak.L.mk_eq r1 r2) in
    let ne ex ex' r1 r2 = sem ex ex' (Shostak.L.mk_distinct false [r1; r2]) in
    let if_true p f =
      match Pred.is uf term p true with Some ex -> f ex | None -> []
    in
    List.concat
      [ if_true Normal (fun ex -> [ne ex ex_e re zero_e; ne ex ex_e re ones_e]);
        if_true Subnormal (fun ex ->
            [eq ex ex_e re zero_e; ne ex ex_m rm zero_m]);
        if_true Zero (fun ex -> [eq ex ex_e re zero_e; eq ex ex_m rm zero_m]);
        if_true Infinite (fun ex ->
            [eq ex ex_e re ones_e; eq ex ex_m rm zero_m]);
        if_true Nan (fun ex -> [eq ex ex_e re ones_e; ne ex ex_m rm zero_m]);
        if_true Positive (fun ex -> [eq ex ex_s rs (bv 1 Z.zero)]);
        if_true Negative (fun ex -> [eq ex ex_s rs (bv 1 Z.one)]) ]

  (* [term = of_int mode i], where [i] is the integer of a bit-vector, once
     [term] is known and [i] is not. If the conversion is exact, [i] is the
     value of [term] (there is none if it is not an integer). If it can overflow
     but [term] is below the largest finite value, [to_real term] is the rounded
     [i]. *)
  let of_int_inverse term rep_r ~arg:((r_arg, ex_arg) as rep_arg) =
    match E.term_view term, get_fp_value rep_r, get_int_value rep_arg with
    | { E.xs = [_; _; _; i]; ty = Ty.Tfloat (eb, sb); _ }, Some (v, ex_v), None
      -> (
      match bv_int_conversion eb sb i, Fp_value.to_q v with
      | Some (_, _, true), Some q ->
        let ex = Ex.union ex_v ex_arg in
        let eq z = eq_lit_fact ex r_arg (E.Ints.of_Z z) in
        let z = Q.to_z (Q.floor q) in
        (* If [q] is not an integer, the two facts conflict. *)
        eq z :: (if Q.is_int q then [] else [eq (Z.add z Z.one)])
      | _, Some q -> (
        match of_bv_int_overflow term with
        | Some (_, _, f)
          when Q.compare (Q.abs q) (Fp_value.max_finite_q ~eb ~sb) < 0 ->
          [lit_fact ex_v (E.mk_eq ~iff:false (E.FP.to_real ~eb ~sb term) f)]
        | Some _ | None -> [])
      | _, None -> [])
    | _ -> []

  (* [term = op(args)], for the operators of kind [Eval]: value, once the
     arguments are known. *)
  let eval_op term args =
    match E.term_view term with
    | { E.f = Sy.Name { hs; _ }; ty = Ty.Tfloat (eb, sb); _ } -> (
      let is = String.equal (Hstring.view hs) in
      let m =
        Option.bind (List.nth_opt args 0) (fun (r, _) -> mode_of_repr r)
      in
      let vs = List.filter_map (fun (r, _) -> fp_value_of_repr r) args in
      let v =
        let open Fp_value in
        match m, vs with
        | Some m, [x; y; z] when is Names.fma -> Some (fma ~eb ~sb m x y z)
        | Some m, [x; y] when is Names.add -> Some (add ~eb ~sb m x y)
        | Some m, [x; y] when is Names.sub -> Some (sub ~eb ~sb m x y)
        | Some m, [x; y] when is Names.mul -> Some (mul ~eb ~sb m x y)
        | Some m, [x; y] when is Names.div -> Some (div ~eb ~sb m x y)
        | Some m, [x] when is Names.sqrt -> Some (sqrt ~eb ~sb m x)
        | Some m, [x] when is Names.round_to_integral ->
          Some (round_to_integral ~eb ~sb m x)
        | None, [x] when is Names.abs -> Some (abs x)
        | None, [x] when is Names.neg -> Some (neg x)
        | None, [x; y] when is Names.min -> min x y
        | None, [x; y] when is Names.max -> max x y
        | _ -> None
      in
      match v with
      | Some v when List.for_all (fun (r, _) -> X.is_constant r) args ->
        [eq_float_fact (ex_of args) term v eb sb]
      | Some _ | None -> [])
    | _ -> assert false

  (* Propagates the classes between [term = op(args)] and its float arguments
     (see [Cls]), for the operators of kind [Eval]. *)
  let op_classes uf term =
    match E.term_view term with
    | { E.f = Sy.Name { hs; _ }; xs = _ :: _ :: xs; _ } ->
      let floats =
        term :: List.filter (fun x -> is_fpa_ty (E.type_info x)) xs
      in
      let ms, exs = List.split (List.map (Cls.of_preds uf) floats) in
      let ex = List.fold_left Ex.union Ex.empty exs in
      let res, ms' =
        Cls.narrow (Cls.transfer (Hstring.view hs)) (List.hd ms) (List.tl ms)
      in
      List.concat (List.map2 (Cls.facts uf ex) floats (res :: ms'))
    | _ -> []

  (* [term = to_real x]: the real value of a known [x], none for NaN and the
     infinities. *)
  let to_real_value (r, ex_r) rep_x =
    match get_fp_value rep_x with
    | Some (v, ex_x) -> (
      match Fp_value.to_q v with
      | Some q -> [eq_lit_fact (Ex.union ex_r ex_x) r (E.Reals.of_Q q)]
      | None -> [])
    | None -> []

  (* Extensionality on [term = to_real x], for a finite [x]: floats with the
     same real value are equal unless they are zeros. *)
  let to_real_extensionality uf t term (r, ex_r) (rx, _) =
    match E.term_view term with
    | { E.xs = [_; _; x]; _ } -> (
      let finite y =
        match Pred.is uf y Nan false, Pred.is uf y Infinite false with
        | Some ex1, Some ex2 -> Some (Ex.union ex1 ex2)
        | _ -> None
      in
      match finite x with
      | None -> []
      | Some ex_fin ->
        E.Set.fold
          (fun term' acc ->
            match E.Map.find_opt term' t.apps, E.term_view term' with
            | ( Some { kind = To_real; r = r', ex_r'; args = Ops [(ry, _)] },
                { E.xs = [_; _; y]; _ } )
              when (not (E.equal term term'))
                   && X.equal r r'
                   && Ty.equal (E.type_info y) (E.type_info x)
                   && not (X.equal rx ry) -> (
              let nonzero =
                match Pred.is uf x Zero false with
                | Some _ as ex -> ex
                | None -> Pred.is uf y Zero false
              in
              match finite y, nonzero with
              | Some ex_fin', Some ex_nz ->
                let ex =
                  Ex.union (Ex.union ex_r ex_r')
                    (Ex.union ex_fin (Ex.union ex_fin' ex_nz))
                in
                lit_fact ex (E.mk_eq ~iff:false x y) :: acc
              | _ -> acc)
            | _ -> acc)
          (watchers r t) [])
    | _ -> assert false

  (* Decides [term = cmp(x, y)] from the classes of [x] and [y] (see [Cls]) or
     by evaluation on literals, and narrows the classes of [x] and [y] from a
     known comparison. *)
  let compare_rules uf term rep_r rep_x rep_y =
    (* A bit-vector conversion whose value is known was usually reached by the
       BV case splits: deciding the comparison then makes them enumerate the
       bit-vectors instead of letting the prelude axioms conclude. Not when the
       bit-vector is a literal. *)
    let bv_conv e =
      match conv_kind e, E.term_view e with
      | Some Of_bits, _ -> true
      | Some Of_int, { E.xs = [_; _; _; n]; _ } ->
        Option.is_some (E.FP.of_bv_int_view n)
      | _ -> false
    in
    let literal_conv e =
      E.Set.for_all
        (fun s ->
          match (E.term_view s).xs with
          | [] -> X.is_constant (fst (X.make s))
          | _ -> true)
        (E.sub_terms E.Set.empty e)
    in
    let enumerated (r, _) e =
      X.is_constant r && bv_conv e && not (literal_conv e)
    in
    match E.term_view term with
    | { E.f = Sy.Name { hs; _ }; xs = [_; _; x; y]; _ }
      when not (enumerated rep_x x || enumerated rep_y y) ->
      let name = Hstring.view hs in
      let r, ex_r = rep_r in
      (* Known truth value, as a mask of [Cls.compare]. *)
      let truth, ex_t =
        if X.equal r (r_true ())
        then 2, ex_r
        else if X.equal r (r_false ())
        then 1, ex_r
        else 3, Ex.empty
      in
      let (mx, ex_x), (my, ex_y) = Cls.of_preds uf x, Cls.of_preds uf y in
      let ex = Ex.union ex_t (Ex.union ex_x ex_y) in
      let decide ex b = lit_fact ex (if b then term else E.neg term) in
      let op = function [a; b] -> Cls.compare name a b | _ -> assert false in
      (* A contradicted [truth] leaves no classes to [x] and [y]: conflict. *)
      let res, mx', my' =
        match Cls.narrow op truth [mx; my] with
        | res, [mx'; my'] -> res, mx', my'
        | _ -> assert false
      in
      let decided =
        if truth = 3 && (res = 1 || res = 2) then [decide ex (res = 2)] else []
      in
      (* Nonzero values are equal when [eq] holds. Not for BV conversions: the
         equality makes each enumerated value conflict. *)
      let equal =
        if
          String.equal name Names.eq && truth = 2
          && mx' land Cls.both Cls.zero = 0
          && (not (X.equal (fst rep_x) (fst rep_y)))
          && not (bv_conv x || bv_conv y)
        then [lit_fact ex (E.mk_eq ~iff:false x y)]
        else []
      in
      (* Evaluation on literals. *)
      let evaluated =
        match get_fp_value rep_x, get_fp_value rep_y with
        | Some (vx, ex_x), Some (vy, ex_y) ->
          let f =
            if String.equal name Names.le
            then Fp_value.le
            else if String.equal name Names.lt
            then Fp_value.lt
            else Fp_value.eq
          in
          let b = f vx vy in
          if truth = if b then 2 else 1
          then []
          else [decide (Ex.union ex_x ex_y) b]
        | _ -> []
      in
      List.concat
        [decided; Cls.facts uf ex x mx'; Cls.facts uf ex y my'; equal; evaluated]
    | _ -> []

  (* The float terms of [term] whose predicates the rules read. *)
  let pred_terms term kind =
    match kind, E.term_view term with
    | Of_bits, _ -> [term]
    | (Eval | Cmp | To_real), { E.xs; _ } ->
      List.filter (fun x -> is_fpa_ty (E.type_info x)) (term :: xs)
    | (Of_int | Of_real | To_int | To_fp | To_bv _ | Rem), _ -> []

  (* Watches the known predicate terms of [pred_terms], so that [term] reruns
     when they get a truth value. *)
  let watch_preds uf term kind t =
    let watched =
      List.fold_left
        (fun watched x ->
          List.fold_left
            (fun watched p ->
              let a = Pred.to_expr p x in
              if Uf.mem uf a
              then
                let r = fst (Uf.find uf a) in
                if X.is_constant r
                then watched
                else
                  let s =
                    Option.value ~default:E.Set.empty (MX.find_opt r watched)
                  in
                  MX.add r (E.Set.add term s) watched
              else watched)
            watched Pred.all)
        t.watched (pred_terms term kind)
    in
    { t with watched }

  (* Runs the rules of [term] and queues their facts. *)
  let apply_conv_rules uf term app t =
    let facts, lemmas =
      match app.kind, app.args with
      | Of_bits, Bits { sign; exp; mant } ->
        let facts, lemmas = of_bits t term app.r ~sign ~exp ~mant in
        of_bits_fields uf term ~sign ~exp ~mant @ facts, lemmas
      | Of_int, Rounded { mode; arg } ->
        of_int term ~mode ~arg @ of_int_inverse term app.r ~arg, []
      | Of_real, Rounded { mode; arg } -> of_real term ~mode ~arg, []
      | To_int, Rounded { mode; arg } -> to_int app.r ~mode ~arg, []
      | To_fp, Rounded { mode; arg } -> to_fp term ~mode ~arg, []
      | To_bv (signed, n), Rounded { mode; arg } ->
        to_bv t term ~signed n app.r ~mode ~arg, []
      | Eval, Ops args -> eval_op term args @ op_classes uf term, []
      | To_real, Ops [x] ->
        to_real_value app.r x @ to_real_extensionality uf t term app.r x, []
      | Cmp, Ops [x; y] -> compare_rules uf term app.r x y, []
      | Rem, Ops [x; y] -> rem term x y, rem_lemmas term y
      | _ -> assert false
    in
    let t = watch_preds uf term app.kind t in
    { t with facts = facts @ t.facts; lemmas = lemmas @ t.lemmas }

  (* [a = p x] is a new predicate term: the applications on [x] rerun. *)
  let notify_pred uf x t =
    { t with dirty = E.Set.union (watchers (fst (Uf.find uf x)) t) t.dirty }

  let register uf term kind t =
    if E.Map.mem term t.apps
    then t
    else
      let find = Uf.find uf in
      let args =
        match kind, E.term_view term with
        | Of_bits, { E.xs = [_; _; s; e; m]; _ } ->
          Bits { sign = find s; exp = find e; mant = find m }
        | (Eval | To_real | Cmp), { E.xs = _ :: _ :: xs; _ } ->
          Ops (List.map find xs)
        | Rem, { E.xs; _ } -> Ops (List.map find xs)
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
      let t = { t with apps = E.Map.add term app t.apps; watched } in
      (* Facts from the arguments alone. *)
      let t =
        match kind with
        | Of_int ->
          let facts = List.map (lit_fact Ex.empty) (of_bv_int_facts term) in
          { t with facts = facts @ t.facts }
        | Of_bits | Of_real | To_int | To_fp | To_bv _ | Eval | To_real | Cmp
        | Rem ->
          t
      in
      apply_conv_rules uf term app t

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
          | Ops l -> Ops (List.map update l)
        in
        { app with r = update app.r; args }
      in
      let apps =
        E.Set.fold
          (fun term apps -> E.Map.update term (Option.map update_reps) apps)
          terms t.apps
      in
      (* All the applications on [nrr] rerun, for the rules that relate two
         applications. *)
      let on_nrr = E.Set.union terms (watchers nrr t) in
      { t with
        apps;
        watched = MX.add nrr on_nrr (MX.remove rr t.watched);
        dirty = E.Set.union on_nrr t.dirty
      }

  (* Reruns the dirty applications and returns the pending facts and lemmas. *)
  let flush uf t =
    let t =
      E.Set.fold
        (fun term t ->
          match E.Map.find_opt term t.apps with
          | Some app -> apply_conv_rules uf term app t
          | None -> t)
        t.dirty
        { t with dirty = E.Set.empty }
    in
    t.facts, t.lemmas, { t with facts = []; lemmas = [] }
end

(* The argument [x] of [term = p x], for the predicates of [Pred]. *)
let pred_arg term =
  match E.term_view term with
  | { E.f = Sy.Name { hs; _ }; xs = [_; _; x]; ty = Ty.Tbool; _ }
    when is_name hs
           Names.
             [ is_nan;
               is_zero;
               is_infinite;
               is_normal;
               is_subnormal;
               is_positive;
               is_negative ] ->
    Some x
  | _ -> None

(* Registers [term] in [Conv_watch] if it has rules, and reruns the rules on [x]
   if [term] is a predicate [p x]. *)
let register_conv uf term ds =
  let cw = Uf.GlobalDomains.find (module Conv_watch) ds in
  let cw =
    match conv_kind term with
    | Some kind -> Conv_watch.register uf term kind cw
    | None -> cw
  in
  let cw =
    match pred_arg term with
    | Some x -> Conv_watch.notify_pred uf x cw
    | None -> cw
  in
  Uf.GlobalDomains.add (module Conv_watch) cw ds

type t =
  { seen_types : IntPairSet.t;
        (* formats whose precision facts are sent or pending in this env *)
    pending_types : IntPairSet.t;
    pending_literals : (E.t * E.t) list;
    new_terms : E.Set.t;
    defs : E.Set.t;
    lemmas : E.Set.t  (** lemmas of [Conv_watch] *)
  }

let empty uf =
  ( { seen_types = IntPairSet.empty;
      pending_types = IntPairSet.empty;
      pending_literals = [];
      new_terms = E.Set.empty;
      defs = E.Set.empty;
      lemmas = E.Set.empty
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

let mk_rounding m =
  E.mk_constr
    (Fpa_rounding.term_cst_of_rounding_mode m)
    [] Fpa_rounding.fpa_rounding_mode

(* [term = fp s e m]: if [term] is not NaN, its sign is [s]. *)
let of_bits_clauses term =
  match E.term_view term with
  | { E.xs = [_; _; s; _; _]; ty = Ty.Tfloat (eb, sb); _ } ->
    let is_nan = E.FP.is_nan ~eb ~sb term in
    let sign_is z = E.mk_eq ~iff:false s (E.BV.of_Z ~size:1 z) in
    [ mk_clause [is_nan; E.neg (sign_is Z.one); E.FP.is_negative ~eb ~sb term];
      mk_clause [is_nan; E.neg (sign_is Z.zero); E.FP.is_positive ~eb ~sb term]
    ]
  | _ -> assert false

(* [term = to_fp mode x], from [(eb1, sb1)] to [(eb2, sb2)]. *)
let to_fp_clauses term =
  match E.term_view term with
  | { E.xs = [eb_t; sb_t; mode; x]; ty = Ty.Tfloat (eb2, sb2); _ } ->
    let eb1, sb1 = float_format x in
    (* Widening is exact. *)
    let exact = eb1 <= eb2 && sb1 <= sb2 in
    let px p = p ~eb:eb1 ~sb:sb1 x in
    let pt p = p ~eb:eb2 ~sb:sb2 term in
    let iff p = [[E.neg (px p); pt p]; [px p; E.neg (pt p)]] in
    (* [p x -> p term], and the converse if exact. Narrowing can overflow or
       underflow, so infinite and zero are only kept forward. *)
    let forward p =
      [E.neg (px p); pt p] :: (if exact then [[px p; E.neg (pt p)]] else [])
    in
    (* The clauses [conds m @ tail] for the modes [m] where [conds m] is
       defined, guarded by [mode = m] if [mode] is not a literal. *)
    let by_mode conds tail =
      match E.rounding_mode_view mode with
      | Some m -> ( match conds m with Some l -> [l @ tail] | None -> [])
      | None ->
        List.filter_map
          (fun m ->
            Option.map
              (fun l ->
                (E.neg (E.mk_eq ~iff:false mode (mk_rounding m)) :: l) @ tail)
              (conds m))
          Dolmen.Std.Builtin.Float.
            [ RoundNearestTiesToEven;
              RoundNearestTiesToAway;
              RoundTowardPositive;
              RoundTowardNegative;
              RoundTowardZero ]
    in
    (* [x] and [term] finite: [to_real term] is [to_real x], rounded unless
       exact. Narrowing must also not overflow: an overflow gives an infinity
       only when rounding away from zero, and the largest finite value
       otherwise. *)
    let real =
      let real_x = E.FP.to_real ~eb:eb1 ~sb:sb1 x in
      let value =
        if exact
        then real_x
        else E.mk_term (Sy.Op FloatEbSb) [eb_t; sb_t; mode; real_x] Ty.Treal
      in
      let finite =
        [ px E.FP.is_nan;
          px E.FP.is_infinite;
          pt E.FP.is_infinite;
          E.mk_eq ~iff:false (pt E.FP.to_real) value ]
      in
      let module RM = Dolmen.Std.Builtin.Float in
      (* Conditions, other than the mode, for no overflow in mode [m]. *)
      let no_overflow (m : Fpa_rounding.rounding_mode) =
        match m with
        | RM.RoundNearestTiesToEven | RoundNearestTiesToAway -> Some []
        | RoundTowardPositive -> Some [E.neg (px E.FP.is_positive)]
        | RoundTowardNegative -> Some [E.neg (px E.FP.is_negative)]
        | RoundTowardZero -> None
      in
      if exact then [finite] else by_mode no_overflow finite
    in
    (* Narrowing a finite [x] overflows to the largest finite value, not to an
       infinity, when rounding toward zero. *)
    let not_infinite =
      let module RM = Dolmen.Std.Builtin.Float in
      let to_max (m : Fpa_rounding.rounding_mode) =
        match m with
        | RM.RoundTowardZero -> Some []
        | RoundTowardPositive -> Some [E.neg (px E.FP.is_negative)]
        | RoundTowardNegative -> Some [E.neg (px E.FP.is_positive)]
        | RoundNearestTiesToEven | RoundNearestTiesToAway -> None
      in
      if exact
      then []
      else by_mode to_max [px E.FP.is_infinite; E.neg (pt E.FP.is_infinite)]
    in
    List.map mk_clause
      (List.concat
         [ (* NaN and the sign are kept. *)
           iff E.FP.is_nan;
           iff E.FP.is_positive;
           iff E.FP.is_negative;
           forward E.FP.is_infinite;
           forward E.FP.is_zero;
           not_infinite;
           real ])
  | _ -> assert false

(* [term = rem x y]. NaN if [x] is NaN or infinite, or if [y] is NaN or zero.
   [x] if [x] is finite and [y] infinite, or if [x] is zero and [y] finite and
   nonzero. Otherwise, for [x] finite and [y] finite and nonzero, [term] is
   finite, [|term| <= |y| / 2] and [|term| <= |x|]. *)
let rem_clauses term =
  match E.term_view term with
  | { E.xs = [x; y]; ty = Ty.Tfloat (eb, sb); _ } ->
    let p mk t = mk ~eb ~sb t in
    let not_ mk t = E.neg (p mk t) in
    let nan_r = p E.FP.is_nan term in
    let eq_x = E.mk_eq ~iff:false term x in
    let abs t = E.mk_term (Sy.Op Abs_real) [t] Ty.Treal in
    let real t = abs (E.FP.to_real ~eb ~sb t) in
    let finite t = [p E.FP.is_nan t; p E.FP.is_infinite t] in
    let finite_nonzero t = p E.FP.is_zero t :: finite t in
    let bounds =
      let open E.Reals in
      [p E.FP.is_finite term; real term <= real y / ~$2; real term <= real x]
    in
    List.map mk_clause
      ([ [not_ E.FP.is_nan x; nan_r];
         [not_ E.FP.is_infinite x; nan_r];
         [not_ E.FP.is_nan y; nan_r];
         [not_ E.FP.is_zero y; nan_r];
         finite x @ [not_ E.FP.is_infinite y; eq_x];
         (not_ E.FP.is_zero x :: finite_nonzero y) @ [eq_x] ]
      @ List.map (fun b -> finite x @ finite_nonzero y @ [b]) bounds)
  | _ -> assert false

(* [term = of_int mode i], where the conversion of [i] can overflow: the rounded
   value is the result when it is in range. With a known mode, an overflow is
   the largest finite value of its sign or an infinity. *)
let overflow_definition term (eb, sb, f) =
  let m = Fp_value.max_finite_q ~eb ~sb in
  let value = E.mk_eq ~iff:false (E.FP.to_real ~eb ~sb term) in
  let in_range =
    E.mk_and E.Reals.(of_Q (Q.minus m) <= f) E.Reals.(f <= of_Q m) false
  in
  let overflow neg =
    let max_fin = E.Reals.of_Q (if neg then Q.minus m else m) in
    let out = if neg then E.Reals.(f < max_fin) else E.Reals.(max_fin < f) in
    let module RM = Dolmen.Std.Builtin.Float in
    let to_max =
      match E.rounding_mode_view (List.nth (E.term_view term).xs 2) with
      | Some RM.RoundTowardZero -> Some true
      | Some RM.RoundTowardNegative -> Some (not neg)
      | Some RM.RoundTowardPositive -> Some neg
      | Some (RM.RoundNearestTiesToEven | RoundNearestTiesToAway) -> Some false
      | None -> None
    in
    let sign = if neg then E.FP.is_negative else E.FP.is_positive in
    let infinite =
      E.mk_and (E.FP.is_infinite ~eb ~sb term) (sign ~eb ~sb term) false
    in
    Option.map
      (fun to_max -> E.mk_imp out (if to_max then value max_fin else infinite))
      to_max
  in
  E.mk_imp in_range (value f) :: List.filter_map overflow [false; true]

(* [term = to_bv n mode x] and [i = to_int mode x]: [is_finite x /\ lo <= i < hi
   -> term = int2bv n i]. Unspecified otherwise. *)
let to_bv_definition term ~signed n =
  match E.term_view term with
  | { E.xs = [_; _; mode; x]; _ } ->
    let eb, sb = float_format x in
    let lo, hi = bv_range ~signed n in
    let i = E.FP.to_int ~eb ~sb ~mode x in
    let guard =
      E.mk_and (E.FP.is_finite ~eb ~sb x)
        (E.mk_and E.Ints.(~$$lo <= i) E.Ints.(i < ~$$hi) false)
        false
    in
    E.mk_imp guard (E.mk_eq ~iff:false term (E.BV.int2bv n i))
  | _ -> assert false

let overflow_name = "fpa_overflow_definition"

let definitions term =
  match normal_pred term, conv_kind term with
  | Some p, _ -> ["fpa_normal_definition", [normal_definition term p]]
  | None, Some (To_bv (signed, n)) ->
    ["fpa_to_bv_definition", [to_bv_definition term ~signed n]]
  | None, kind ->
    List.concat
      [ ["fpa_class_clauses", class_clauses term];
        (match kind with
        | Some Of_bits -> ["fpa_of_bits_clauses", of_bits_clauses term]
        | Some To_fp -> ["fpa_to_fp_clauses", to_fp_clauses term]
        | Some Rem -> ["fpa_rem_clauses", rem_clauses term]
        | Some (Of_int | Of_real | To_int | To_bv _ | Eval | To_real | Cmp)
        | None ->
          []);
        (match of_bv_int_overflow term with
        | Some o -> [overflow_name, overflow_definition term o]
        | None -> []) ]

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
      env, register_conv uf term ds, []
    | _ ->
      let env =
        match normal_pred term, conv_kind term with
        | Some _, _ | None, Some (To_bv _) ->
          { env with defs = E.Set.add term env.defs }
        | None, _ -> env
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
    let conv_facts, conv_lemmas, conv_watch =
      Conv_watch.flush uf (Uf.GlobalDomains.find (module Conv_watch) ds)
    in
    let env =
      { env with
        lemmas =
          List.fold_left (fun acc l -> E.Set.add l acc) env.lemmas conv_lemmas
      }
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
let instantiate ~do_syntactic_matching _ env uf selector =
  (* only send the lemmas once per round, in the syntactic pass, rather than
     again in each of the semantic passes. *)
  if (not (Options.get_smt_lib_fpa ())) || not do_syntactic_matching
  then env, []
  else
    let add_inst origin_name from_terms acc ff =
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
            from_terms;
            theory_elim = false
          }
        in
        ([], gf, Ex.empty) :: acc
      else acc
    in
    let insts =
      E.Set.fold
        (fun term acc ->
          List.fold_left
            (fun acc (origin_name, ffs) ->
              (* The overflow lemma only slows down the search once the integer
                 is known: [Conv_watch] then evaluates the conversion. *)
              let known () =
                match E.term_view term with
                | { E.xs = [_; _; _; i]; _ } ->
                  X.is_constant (fst (Uf.find uf i))
                | _ -> false
              in
              if String.equal origin_name overflow_name && known ()
              then acc
              else List.fold_left (add_inst origin_name [term]) acc ffs)
            acc (definitions term))
        env.defs []
    in
    let insts =
      E.Set.fold
        (fun l acc -> add_inst "fpa_conv_lemma" [] acc l)
        env.lemmas insts
    in
    env, insts

let assume_th_elt t _ _ = t

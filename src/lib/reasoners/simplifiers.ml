(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2021 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

module SRE = Simple_reasoner_expr
module E = Expr
module Q = Numbers.Q
module R = Shostak.Combine
module A = Shostak.Arith
module P = Shostak.Polynome
module M = P.M

exception EmptyInterval

let verb = Options.get_debug_simplify

let silent (msg : ('a, Format.formatter, unit) format) =
  Format.ifprintf Format.std_formatter msg

let talk (msg : ('a, Format.formatter, unit) format) =
  Format.printf "[Simplifiers] ";
  Format.printf msg

let debug (msg : ('a, Format.formatter, unit) format) =
  if verb ()
  then talk msg
  else silent msg

module DummySimp =
  SRE.SimpleReasoner
    (struct
      type v = unit
      type state = unit
      let top = ()
      let bottom = ()
      let compare _ _ = Some 0
      let join _ _ = ()
      let add_constraint _ _ _ = SRE.NewConstraint ()
      let pp fmt _ = Format.fprintf fmt "()"
      let unknown = ()
      let _false = ()
      let _true = ()
      let const_int _ = ()
      let to_bool _ = None
      let to_int _ = None
      let pp_v fmt _ = Format.fprintf fmt "()"
      let eval_expr _ _ = ()
      let v_join _ _ = ()
      let add_raw_value _ _ _ = ()
    end
    )

type 'a abstract_value =
  | Bottom
  | Top
  | Value of 'a

let pp_abs_val pp fmt = function
  | Bottom -> Format.fprintf fmt "⊥"
  | Top -> Format.fprintf fmt "T"
  | Value v -> pp fmt v

let compare_abs_val cmp v1 v2 =
  match v1, v2 with
  | Bottom, Bottom
  | Top, Top -> Some 0
  | Bottom, _
  | _, Top -> Some (-1)
  | Top, _
  | _, Bottom -> Some 1
  | Value v1, Value v2 -> cmp v1 v2

type abstract_bool =
  | True
  | False
  | TrueOrFalse

let pp_abstract_bool fmt = function
  | True -> Format.fprintf fmt "{t}"
  | False -> Format.fprintf fmt "{f}"
  | TrueOrFalse -> Format.fprintf fmt "{t;f}"


type interval =
  | Bool of bool
  | Interval of Intervals.t

let pp_interval fmt = function
  | Interval i -> Intervals.print fmt i
  | Bool b -> Format.fprintf fmt "%b" b

module IntervalsDomain :
  SRE.Dom
  with type v = interval abstract_value
   and type state = interval abstract_value M.t abstract_value = struct
  type v = interval abstract_value
  type state = v M.t abstract_value

  let top = Top
  let bottom = Bottom

  let _false = Value (Bool false)
  let _true = Value (Bool true)
  let const_int i = Value (Interval (Intervals.point i Ty.Tint Explanation.empty))
  let unknown = Top

  let to_bool =
    function
    | Top
    | Bottom
    | Value (Interval _) -> None
    | Value (Bool b) -> Some b

  let to_int = function
    | Value (Interval i) -> begin
        match Intervals.is_point i with
        | Some (i, _) -> Some i
        | None -> None
      end
    | Top
    | Bottom
    | Value (Bool _) -> None

  let pp_v = pp_abs_val pp_interval

  let pp fmt v =
    pp_abs_val
      (fun fmt -> M.iter
          (fun r i -> Format.fprintf fmt "\n%a = %a"
              R.print r
              pp_v i
          ))
      fmt
      v

  let compare_intervals_t i1 i2 =
    if Intervals.contained_in i1 i2
    then if Intervals.equal i1 i2
         then Some 0
         else Some (-1)
    else if Intervals.contained_in i2 i1 then Some 1
    else None

  let compare_bool b1 b2 = Some (Bool.compare b1 b2)

  let compare_intervals i1 i2 =
    match i1, i2 with
      | Interval i1, Interval i2 -> compare_intervals_t i1 i2
      | Bool b1, Bool b2 -> compare_bool b1 b2
      | Bool _, Interval _ -> Some 1
      | Interval _, Bool _ -> Some (-1)

  let compare =
    let compare_intervals = compare_abs_val compare_intervals in
    fun m1 m2 ->
      (* Compares two maps.
         Maps are compared itetatively ; the result is saved on a reference
         checked through the main loop. *)
      let res : int option option ref = ref None in
      (* !res = None => comparison not started *)
      (* !res = Some None => Non comparable *)
      (* !res = Some (-1) => m1 < m2 *)
      (* !res = Some   1  => m1 > m2 *)
      (* !res = Some   0  => m1 = m2 *)
      let exception Stop in
      let set_res r =
        (* Sets res to the value in argument if it is consistent *)
        match !res with
        | None -> (* First time comparing *)
          res := Some (Some r)
        | Some None -> (* Comparison should have beed ended before *)
          assert false
        | Some (Some 0) -> (* Up to this point, comparison has shown both
                              maps are equal *)
          if r <> 0 then res := Some (Some r)
        | Some (Some r') ->
          if r <> r' then begin res := Some None; raise Stop end in
      let get_res () =
        match !res with
        | None -> Some 0 (* Comparison did not even started ;
                            maps are both empty *)
        | Some v -> v in
      try
        let () = ignore @@
          (* The result of this merge is ignored : it is only here to compare *)
          M.merge
            (fun _k v1 v2 ->
               match v1, v2 with
               | None, None -> assert false
               | None, _ -> set_res 1   ; None
               | _, None -> set_res (-1); None
               | Some v1, Some v2 ->
                 match compare_intervals v1 v2 with
                 | None -> res := Some None; raise Stop
                 | Some v -> set_res v; None
            )
            m1
            m2 in get_res () with
      | Stop -> get_res ()

  let compare = compare_abs_val compare

  let v_join v1 v2 =
    match v1, v2 with
    | Top, _
    | _, Top -> Top
    | v, Bottom
    | Bottom, v -> v
    | Value (Interval v1), Value (Interval v2) -> Value (Interval (Intervals.merge v1 v2))
    | Value (Bool b1), Value (Bool b2) ->
      if b1 = b2 then v1 else Top
    | Value (Bool _), Value (Interval _)
    | Value (Interval _), Value (Bool _) -> failwith "Cannot v_join boolean & integer"

  let join =
    M.merge
      (fun _k v1 v2 ->
         match v1, v2 with
         | None, ((Some _) as v)
         | ((Some _) as v), None -> v

         | None, None -> assert false
         | Some i1, Some i2 -> Some (v_join i1 i2))

  let join v1 v2 =
    match v1, v2 with
    | Top, _
    | _, Top -> Top
    | Bottom, v
    | v, Bottom -> v
    | Value i1, Value i2 -> Value (join i1 i2)

  let eval_constraint
      (ty : Ty.t)
      (s : state)
      (p : P.t) : interval abstract_value =
    match s with
    | Top -> begin
        match P.to_list p with
        | [], q -> Value (Interval (Intervals.point q ty Explanation.empty))
        | _ -> Top
      end
    | Bottom -> Bottom
    | Value v ->
      let ty = P.type_info p in
      let module Ev = P.Eval (struct
          type t = interval abstract_value
          let one = Value (Interval (Intervals.point Q.one ty Explanation.empty))
          let add i1 i2 =
            match i1, i2 with
            | Top, _
            | _, Top ->  Top
            | Bottom, _
            | _, Bottom -> Bottom
            | Value (Bool _), _
            | _, Value (Bool _) -> failwith "[add] Cannot evaluate polynomial with boolean values"
            | Value (Interval i1), Value (Interval i2) -> Value (Interval (Intervals.add i1 i2))
          let mul coef i =
            match i with
            | Top ->
              if Q.equal coef Q.zero then
                Value (Interval (Intervals.point Q.zero ty Explanation.empty))
              else Top
            | Bottom -> Bottom
            | Value (Bool _) -> failwith "[mul] Cannot evaluate polynomial with boolean values"
            | Value (Interval i) ->
              Value (Interval (
                Intervals.mult
                  (Intervals.point coef ty Explanation.empty)
                  i
              ))
        end) in (* todo: apply functor statically for each possible interval type *)
      let map r =
        match M.find_opt r v with
        | None -> Top
        | Some v -> v in
      Ev.eval map p

  let rfind ty k (s : state) = match s with
    | Bottom -> failwith "Value is bottom: Should have been checked beforehand"
    | Top -> Intervals.undefined ty
    | Value m ->
      match M.find_opt k m with
      | None | Some Top -> Intervals.undefined ty
      | Some Bottom ->
        failwith "Internal value is bottom: Should have been checked beforehand"
      | Some ((Value (Interval i)) as v) ->
        debug "[rfind] Found %a in state %a, associated to %a@."
          R.print k pp s pp_v v;
        i
      | Some (Value (Bool _)) -> failwith "[rfind] Cannot return interval associated to boolean"

  let radd k b s =
    match b with
    | Top -> s
    | _ -> match s with
      | Top -> Value (M.add k b M.empty)
      | Value m -> Value (M.add k b m)
      | Bottom -> s

  type narrow =
    rinter:Intervals.t -> prev_inter:Intervals.t -> Intervals.t * bool

  let fix_point
      (narrow : narrow)
      (ty : Ty.t)
      (constraints : (Q.t * R.r * P.t) list)
      (s : state) =
    let rec aux s =
      let new_vars, keep_iterating =
        List.fold_left
          (fun ((s : state), keep_iterating) (q,r,p) ->
             (* Calculates the interval of `p` given the value of `vars` *)
             debug "[fix_point] Constraint %a%a R %a@."
               Q.print q R.print r P.print p;
             debug "[fix_point] Evaluating with state %a@." pp s;
             match eval_constraint ty s p with
             | Top
             | Bottom  -> s, false
             | Value (Bool _) -> assert false
             | Value (Interval i) ->
               (* Deducing the value of `r` *)
               debug "[fix_point] %a R %a@." P.print p Intervals.print i;

               if Intervals.is_undefined i then begin
                 debug "[fix_point] No information, continuing@.";
                 s, keep_iterating
               end else begin
                 debug "[fix_point] Narrowing@.";
                 debug "[fix_point] Dividing %a by %a@."
                   Intervals.print i Q.print q;
                 let rinter =
                   Intervals.div i (Intervals.point q ty Explanation.empty)
                 in
                 debug "[fix_point] Interval of %a by the constraint : %a@."
                   R.print r
                   Intervals.print rinter;
                 let prev_inter = rfind ty r s in
                 debug "[fix_point] Interval of %a in %a: %a@."
                   R.print r pp s Intervals.print prev_inter;
                 let ri, change = narrow ~rinter ~prev_inter in
                 debug "[fix_point] Old interval of %a : %a@."
                   R.print r Intervals.print prev_inter;
                 debug "[fix_point] New interval of %a : %a@."
                   R.print r Intervals.print ri;
                 if change then
                   radd r (Value (Interval ri)) s, change
                 else
                   s, keep_iterating
               end
          )
          (s, false)
          constraints in
      if keep_iterating then aux new_vars else s in
    aux s

  let narrow_neq ~rinter ~prev_inter =
    (* If r <> p and p \in rinter, then if rinter is a point,
       then we can deduce informations, else we can't *)
    debug "[fix_point] Narrow NEQ@.";
    match Intervals.is_point rinter with
    | None -> prev_inter, false
    | Some (q, _) ->
      try
        if Intervals.contains prev_inter q then begin
          let () = debug "Excluding %a from %a@."
              Q.print q Intervals.print prev_inter in
          Intervals.exclude rinter prev_inter, true
        end else prev_inter, false
      with
      | Intervals.NotConsistent _ -> raise EmptyInterval

  let narrow_le ~rinter ~prev_inter =
    debug "[fix_point] Narrow LE ; r_inter = %a -- previous_inter = %a@."
      Intervals.print rinter Intervals.print prev_inter
    ;
    try
      let bound   , _, is_le = Intervals.borne_sup rinter in
      let prev_sup =
        try
          let s, _, _ = Intervals.borne_sup prev_inter in Some s
        with
          Intervals.No_finite_bound -> None in
      match prev_sup with
      | None ->
        debug "[fix_point] New constraint upper bound: %a@." Q.print bound;
        Intervals.new_borne_sup
          Explanation.empty
          bound
          ~is_le
          prev_inter, true
      | Some prev_sup ->
        if Q.compare bound prev_sup >= 0 then begin
          debug
            "[fix_point] Constraint upper bound %a >= %a previous upper bound@."
            Q.print bound Q.print prev_sup;
          debug "[fix_point] No need for more narrowing@.";
          prev_inter, false
        end else begin
          (* The new upper bound is lower than then previous one,
             replacing it *)
          debug
            "[fix_point] Constraint upper bound %a < %a previous upper bound@."
            Q.print bound Q.print prev_sup;
          debug "[fix_point] Narrowing@.";
          Intervals.new_borne_sup
            Explanation.empty
            bound
            ~is_le
            prev_inter, true
        end
    with
    | Intervals.No_finite_bound -> prev_inter, false
    | Intervals.NotConsistent _ -> raise EmptyInterval

  let narrow_lt ~rinter ~prev_inter =
    debug "[fix_point] Narrow LT@.";
    try
      let bound   , _, _ = Intervals.borne_sup rinter in
      let prev_sup =
        try
          let s, _, _ = Intervals.borne_sup prev_inter in Some s
        with
          Intervals.No_finite_bound -> None in
      match prev_sup with
      | None ->
        debug "[fix_point] New constraint upper bound: %a" Q.print bound;
        Intervals.new_borne_sup
          Explanation.empty
          bound
          ~is_le:false
          prev_inter, true
      | Some prev_sup ->
        if Q.compare bound prev_sup >= 0 then begin
          (* The new upper bound is higher then the previous one,
             keeping it *)
          debug
            "[fix_point] Constraint upper bound %a >= %a previous upper bound@."
            Q.print bound Q.print prev_sup;
          debug "[fix_point] No need for more narrowing";
          prev_inter, false
        end else begin
          (* The new upper bound is lower than then previous one,
             replacing it *)
          debug
            "[fix_point] Constraint upper bound %a < %a previous upper bound@."
            Q.print bound Q.print prev_sup;
          debug "[fix_point] Narrowing@.";
          Intervals.new_borne_sup
            Explanation.empty
            bound
            ~is_le:false
            prev_inter, true
        end
    with
    | Intervals.No_finite_bound -> prev_inter, false
    | Intervals.NotConsistent _ -> raise EmptyInterval


  let narrow_gt ~rinter ~prev_inter =
    debug "[fix_point] Narrow GT@.";
    try
      let bound   , _, _ = Intervals.borne_inf rinter in
      let prev_inf =
        try
          let s , _, _ = Intervals.borne_inf prev_inter in Some s
        with
        | Intervals.No_finite_bound ->
          None
      in
      match prev_inf with
      | None ->
        Intervals.new_borne_inf
          Explanation.empty bound
          ~is_le:false
          prev_inter,
        true
      | Some prev_inf ->
        if Q.compare prev_inf bound >= 0 then
          prev_inter, false
        else
          Intervals.new_borne_inf
            Explanation.empty bound
            ~is_le:false
            prev_inter,
          true
    with
    | Intervals.No_finite_bound -> prev_inter, false
    | Intervals.NotConsistent _ -> raise EmptyInterval

  let narrow_ge ~rinter ~prev_inter =
    debug "[fix_point] Narrow GE@.";
    try
      let bound   , _, is_le = Intervals.borne_inf rinter in
      let prev_inf =
        try let s , _, _ = Intervals.borne_inf prev_inter in Some s with
        | Intervals.No_finite_bound -> None
      in
      match prev_inf with
      | None ->
        Intervals.new_borne_inf Explanation.empty bound ~is_le prev_inter,
        true
      | Some prev_inf ->
        if Q.compare prev_inf bound >= 0 then
          prev_inter, false
        else
          Intervals.new_borne_inf Explanation.empty bound ~is_le prev_inter,
          true
    with
    | Intervals.No_finite_bound -> prev_inter, false
    | Intervals.NotConsistent _ -> raise EmptyInterval

  let narrow_eq ~rinter ~prev_inter =
    debug "[fix_point] Narrow EQ@.";
    let rinter', change1 = narrow_le ~rinter ~prev_inter in
    debug "[fix_point] After LE: %a@." Intervals.print rinter;
    let rinter, change2 = narrow_ge ~rinter ~prev_inter:rinter' in
    debug "[fix_point] After GE: %a@." Intervals.print rinter;
    rinter, change1 || change2

  let fix_point_eq  = fix_point narrow_eq
  let fix_point_neq = fix_point narrow_neq
  let fix_point_le  = fix_point narrow_le
  let fix_point_lt  = fix_point narrow_lt
  let fix_point_gt  = fix_point narrow_gt
  let fix_point_ge  = fix_point narrow_ge

  (* Adds the constraints in argument to the abstract value, then repeats of the
     abstract value has been refined thanks to the constraints. *)
  let fix_point (lit : Symbols.lit) =
    match lit with
    | Symbols.L_eq -> fix_point_eq
    | L_neg_eq -> fix_point_neq
    | L_built LE -> fix_point_le
    | L_built LT -> fix_point_lt
    | L_neg_built LE -> fix_point_gt
    | L_neg_built LT -> fix_point_ge
    | L_built (IsConstr _)
    | L_neg_built (IsConstr _) ->
      (* Should be handled (at least doing nothing) *)
      failwith "Arith Simplifier does not handle IsConstr"
    | L_neg_pred ->
      failwith "Arith Simplifier does not handle L_neg_pred"

  (* todo: take into account types, open bounds & le/lt *)
  let check_constraint ty lit p c v =
    let interval = eval_constraint ty v p in
    match interval with
    | Top | Bottom -> None
    | Value (Bool _) -> assert false
    | Value (Interval i) -> begin
        let inf =
          try let (inf, _, _) = Intervals.borne_inf i in inf with
          | Intervals.No_finite_bound -> Q.sub c Q.one in
        let sup =
          try let (sup, _, _) = Intervals.borne_sup i in sup with
          | Intervals.No_finite_bound -> Q.add c Q.one in
        match lit with
        | Symbols.L_eq ->
          if Q.compare c inf < 0 || Q.compare sup c < 0 then
            Some false
          else
            None
        | L_neg_eq ->
          if Q.compare c inf < 0 || Q.compare sup c < 0 then
            Some true
          else
            None
        | L_built (LE | LT) ->
          if Q.compare sup c < 0 then
            Some true
          else if Q.compare c inf < 0 then
            Some false
          else None

        | L_neg_built (LE | LT) ->
          if Q.compare sup c < 0 then
            Some false
          else if Q.compare c inf < 0 then
            Some true
          else None

        | L_built (IsConstr _)
        | L_neg_built (IsConstr _) ->
          (* Should be handled (at least doing nothing) *)
          failwith "Check constraint does not handle IsConstr"
        | L_neg_pred ->
          failwith "Check constraint does not handle L_neg_pred"
      end

  let to_arith e = A.embed @@ fst @@ R.make e

  (* Adding constraint l1 R l2, with R = (lit). *)
  let add_constraint l1 l2 lit v =
      let l = Symbols.Lit lit in (* Only for debug *)
      debug "[add_constraint] Adding constraint  %a %a %a to environment@."
        E.print l1 Symbols.print l E.print l2;
      let p1 = to_arith l1  in
      let p2 = to_arith l2 in
      let p = P.sub p1 p2 in
      debug "[add_constraint] Constraint : %a %a 0@." P.print p Symbols.print l;
      let ty = P.type_info p1 in

      (* l1 R l2 <=> p + c R 0 *)
      let (p, c, cst) = P.normal_form_pos p in

      let p, c =
        let den = Q.from_z @@ Q.den c in
        P.mult_const den p, Q.from_z @@ Q.num c in

      let lit =
        if Q.compare cst Q.zero < 0 then
          match lit with
          | L_built LE -> Symbols.L_neg_built LT
          | L_built LT -> L_neg_built LE
          | L_neg_built LE -> L_built LT
          | L_neg_built LT -> L_built LE
          | l -> l
        else lit
      in

      debug "[add_constraint] Normalized constraint : %a + %a %a 0@."
        P.print p Q.print c Symbols.print (Lit lit);
      debug "[add_constraint] Known information: %a@." pp v;

      (* Checking if p R -c *)
      let mc = Q.minus c in
      match check_constraint ty lit p mc v with
      | Some true  -> SRE.AlreadyTrue
      | Some false -> AlreadyFalse
      | None ->
        (* p R -c cannot be deduced from state : adding constraint *)
        (* p = \Sum (q_i * r_i)
           p R -c <=> \A i. q_i * r_i R (q_i * r_i) - p - c *)
        let constraints =
          P.fold_on_vars
            (fun r q acc_cstr ->
               let p' = P.sub (P.create [q,r] mc ty) p in
               debug "[add_constraint] Partial constraint for %a*%a: %a@."
                 Q.print q R.print r P.print p';
               ((q, r, p') :: acc_cstr))
            p
            [] in
        try
          let new_constraint = fix_point lit ty constraints v in
          debug "[add_constraint] New constraint: %a@." pp new_constraint;
          NewConstraint new_constraint
        with
        | EmptyInterval ->
          (* fix_point calculation reduced a variable to the empty interval *)
          debug "[add_constraint] Inconsistent interval, returning `false`@.";
          AlreadyFalse

  let add_constraint elist lit v =
    match v with
    | Bottom -> failwith "Add constraint with bottom is forbidden"
    | _ ->
      match elist with
      | [l1; l2] -> add_constraint l1 l2 lit v
      | _ ->
        debug "[add_constraint] Bad number of litterals, ending";
        NewConstraint v

  let eval_expr e s =
    match E.term_view e with
    | Not_a_term _ -> unknown
    | Term _ ->
      eval_constraint (E.type_info e) s (A.embed @@ fst @@ R.make e)

  let add_raw_value e v (s : state) =
    let r = fst @@ R.make e in
    debug "[add_raw_value] Adding %a = %a in %a@." R.print r pp_v v pp s ;
    radd r v s
end

module IntervalsSimp =
  SRE.SimpleReasoner(IntervalsDomain)

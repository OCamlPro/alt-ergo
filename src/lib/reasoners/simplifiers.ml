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

let verb = Options.get_simplify_verbose

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
      let top = ()
      let bottom = ()
      let compare _ _ = Some 0
      let join _ _ = ()
      let add_constraint _ _ _ _ = SRE.NewConstraint ()
      let pp fmt _ = Format.fprintf fmt "()"
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

module IntervalsDomain :
  SRE.Dom with type v = Intervals.t abstract_value M.t abstract_value = struct
  type v = Intervals.t abstract_value M.t abstract_value

  let top = Top
  let bottom : v = Bottom

  let pp fmt v =
    pp_abs_val
      (fun fmt -> M.iter
          (fun r i -> Format.fprintf fmt "%a = %a"
              R.print r
              (pp_abs_val Intervals.print) i))
      fmt
      v

  let compare =
    let compare_intervals =
      compare_abs_val (fun i1 i2 ->
          if Intervals.contained_in i1 i2 then
            if Intervals.equal i1 i2 then Some 0 else Some (-1)
          else if Intervals.contained_in i2 i1 then Some 1
          else None
        ) in
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
        (* Sets the res reference to the value in argument if it is consistent *)
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
          M.merge (* The result of this merge is ignored : it is only here to compare *)
            (fun _k v1 v2 ->
               match v1, v2 with
               | None, None -> assert false
               | None, _ ->
                 (* Could be 'assert false', but assuming variable absent <=> equal to top *)
                 set_res 1; None
               | _, None ->
                 (* Could be 'assert false', but assuming variable absent <=> equal to top *)
                 set_res (-1); None
               | Some v1, Some v2 ->
                 match compare_intervals v1 v2 with
                 | None -> res := Some None; raise Stop
                 | Some v -> set_res v; None
            )
            m1
            m2 in get_res () with
      | Stop -> get_res ()

  let compare = compare_abs_val compare

  let join =
    M.merge
      (fun _k v1 v2 ->
         match v1, v2 with
         | None, ((Some _) as v)
         | ((Some _) as v), None -> v

         | None, None -> assert false

         | Some Top, Some _
         | Some _, Some Top -> Some Top

         | ((Some _) as v), Some Bottom
         | Some Bottom, ((Some _) as v) -> v

         | Some (Value v1), Some (Value v2) -> Some (Value (Intervals.merge v1 v2)))

  let join v1 v2 =
    match v1, v2 with
    | Top, _
    | _, Top -> Top
    | Bottom, v
    | v, Bottom -> v
    | Value i1, Value i2 -> Value (join i1 i2)

  let eval_constraint (ty : Ty.t) (v : v) (p : P.t) : Intervals.t abstract_value =
    match v with
    | Top -> begin
      match P.to_list p with
        | [], q -> Value (Intervals.point q ty Explanation.empty)
        | _ -> Top
    end
    | Bottom -> Bottom
    | Value v ->
      let ty = P.type_info p in
      let module E = P.Eval (struct
          type t = Intervals.t abstract_value
          let one = Value (Intervals.point Q.one ty Explanation.empty)
          let add i1 i2 =
            match i1, i2 with
            | Top, _
            | _, Top ->  Top
            | Bottom, _
            | _, Bottom -> Bottom
            | Value i1, Value i2 -> Value (Intervals.add i1 i2)
          let mul coef i =
            match i with
            | Top ->
              if Q.equal coef Q.zero then
                Value (Intervals.point Q.zero ty Explanation.empty)
              else Top
            | Bottom -> Bottom
            | Value i ->
              Value (Intervals.affine_scale ~const:Q.zero ~coef i)
        end) in (* todo: apply functor statically for each type *)
      E.eval v p

  let rfind ty k (v : v) = match v with
    | Bottom -> failwith "Value is bottom: Should have been checked beforehand"
    | Top -> Intervals.undefined ty
    | Value m -> match M.find_opt k m with
      | None | Some Top -> Intervals.undefined ty
      | Some Bottom -> failwith "Internal value is bottom: Should have been checked beforehand"
      | Some (Value i) -> i

  let radd k b v = match v with
    | Top -> Value (M.add k b M.empty)
    | Value m -> Value (M.add k b m)
    | Bottom -> v

  let fix_point
      (narrow : rinter:Intervals.t -> prev_inter:Intervals.t -> Intervals.t * bool)
      (ty : Ty.t)
      (constraints : (Q.t * R.r * P.t) list)
      (v : v) =
    let rec aux v =
      let new_vars, keep_iterating =
        List.fold_left
          (fun ((v : v), keep_iterating) (q,r,p) ->
             (* Calculates the interval of `p` given the value of `vars` *)
             debug "[fix_point] Constraint %a%a R %a@." Q.print q R.print r P.print p;
             match eval_constraint ty v p with
             | Top
             | Bottom  -> v, false
             | Value i ->
               (* Deducing the value of `r` *)
               debug "[fix_point] %a = %a@." P.print p Intervals.print i;

               if Intervals.is_undefined i then begin
                 debug "[fix_point] No information, continuing@.";
                 v, keep_iterating
               end else begin
                 debug "[fix_point] Narrowing@.";
                 let rinter = Intervals.scale (Q.div Q.one q) i in
                 let prev_inter = rfind ty r v in
                 let ri, change = narrow ~rinter ~prev_inter in
                 debug "[fix_point] %a ~~> %a@." Intervals.print rinter Intervals.print prev_inter;
                 if change then
                   radd r (Value ri) v, change
                 else
                   v, keep_iterating
               end
          )
          (v, false)
          constraints in
      if keep_iterating then aux new_vars else v in
    aux v

  let narrow_eq ~rinter ~prev_inter =
    debug "[fix_point] Narrow EQ@.";
    if Intervals.contained_in rinter prev_inter
    then rinter, true
    else prev_inter, false

  let narrow_neq ~rinter ~prev_inter =
    (* If r <> p and p \in rinter, then if rinter is a point we can deduce informations,
       otherwise we can't *)
    debug "[fix_point] Narrow NEQ@.";
    match Intervals.is_point rinter with
    | None -> prev_inter, false
    | Some (q, _) ->
      if Intervals.contains prev_inter q then
        Intervals.exclude rinter prev_inter, true
      else prev_inter, false

  let narrow_le ~rinter ~prev_inter =
    debug "[fix_point] Narrow LE@.";
    try
      let bound   , _, is_le = Intervals.borne_sup rinter in
      let prev_sup =
        try
          let s, _, _ = Intervals.borne_sup prev_inter in s
        with
          Intervals.No_finite_bound -> (* A value satisfying the next condition *)
          Q.sub bound Q.one in
      if Q.compare bound prev_sup <= 0 then begin
        debug "[fix_point] %a <= %a@." Q.print bound Q.print prev_sup;
        prev_inter, false
      end else
        (* The new upper bound is lower than then previous one,
           replacing it *)
        Intervals.new_borne_sup
          Explanation.empty
          bound
          ~is_le
          prev_inter, true
    with
    | Intervals.No_finite_bound -> prev_inter, false

  let narrow_lt ~rinter ~prev_inter =
    debug "[fix_point] Narrow LT@.";
    try
      let bound   , _, _ = Intervals.borne_sup rinter in
      let prev_sup =
        try
          let s, _, _ = Intervals.borne_sup prev_inter in s
        with
          Intervals.No_finite_bound -> (* A value satisfying the next condition *)
          Q.sub bound Q.one in
      if Q.compare bound prev_sup <= 0 then
        (* The new upper bound is higher then the previous one,
           keeping it *)
        prev_inter, false
      else
        (* The new upper bound is lower than then previous one,
           replacing it *)
        Intervals.new_borne_sup
          Explanation.empty
          bound
          ~is_le:false
          prev_inter, true
    with
    | Intervals.No_finite_bound -> prev_inter, false

  let narrow_gt ~rinter ~prev_inter =
    debug "[fix_point] Narrow GT@.";
    try
      let bound   , _, _ = Intervals.borne_inf rinter in
      let prev_inf =
        try let s , _, _ = Intervals.borne_inf prev_inter in s with
        | Intervals.No_finite_bound -> (* A value satisfying the next condition *)
          Q.add bound Q.one
      in
      if Q.compare prev_inf bound > 0 then
        prev_inter, false
      else
        Intervals.new_borne_inf Explanation.empty bound ~is_le:false prev_inter, true
    with
    | Intervals.No_finite_bound -> prev_inter, false

  let narrow_ge ~rinter ~prev_inter =
    debug "[fix_point] Narrow GE@.";
    try
      let bound   , _, is_le = Intervals.borne_inf rinter in
      let prev_inf =
        try let s , _, _ = Intervals.borne_inf prev_inter in s with
        | Intervals.No_finite_bound -> (* A value satisfying the next condition *)
          Q.add bound Q.one
      in
      if Q.compare prev_inf bound > 0 then
        prev_inter, false
      else
        Intervals.new_borne_inf Explanation.empty bound ~is_le prev_inter, true
    with
    | Intervals.No_finite_bound -> prev_inter, false

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
    | L_neg_built (IsConstr _) -> (* Should be handled (at least doing nothing) *)
      failwith "Arith Simplifier: do not handle IsConstr"
    | L_neg_pred ->
      failwith "todo (even a better error message would be nice)"

  (* todo: take into account types, open bounds & le/lt *)
  let check_constraint ty lit p c v =
    let interval = eval_constraint ty v p in
    match interval with
    | Top | Bottom -> None
    | Value i -> begin
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
        | L_neg_built (IsConstr _) -> (* Should be handled (at least doing nothing) *)
          failwith "Check constraint: do not handle IsConstr"
        | L_neg_pred ->
          failwith "Check constraint : todo (even a better error message would be nice)"
    end

  (* Adding constraint l1 R l2, with R = (lit). *)
  let add_constraint l1 l2 lit v =
    match v with
    | Bottom -> failwith "Add constraint with bottom is forbidden"
    | _ ->

      let p1 = A.embed @@ fst (R.make l1) in
      let p2 = A.embed @@ fst (R.make l2) in
      let ty = P.type_info p1 in

      (* l1 R l2 <=> p + c R 0 *)
      let (p, c, _cst) = P.normal_form_pos (P.sub p1 p2) in

      debug "Constraint : %a + %a R 0@." P.print p Q.print c;

      let mc = Q.minus c in

      match check_constraint ty lit p mc v with
      | Some true  -> SRE.AlreadyTrue
      | Some false -> AlreadyFalse
      | None ->
      (* p = \Sum (q_i * r_i)
         p R c <=> \A i. q_i * r_i = p - (q_i * r_i) - c *)
      let constraints =
        P.fold_on_vars
          (fun r q acc_cstr -> ((q, r, P.sub p (P.create [q,r] c ty)) :: acc_cstr))
          p
          [] in
      NewConstraint (fix_point lit ty constraints v)
end

module IntervalsSimp =
  SRE.SimpleReasoner(IntervalsDomain)

(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

module E = Expr
module Sy = Symbols

let verb = Options.get_debug_simplify

let silent (msg : ('a, Format.formatter, unit) format) =
  Format.ifprintf Format.std_formatter msg

let talk (msg : ('a, Format.formatter, unit) format) =
  Format.printf "[Preprocess] ";
  Format.printf msg

let debug (msg : ('a, Format.formatter, unit) format) =
  if verb ()
  then talk msg
  else silent msg

(** 1. Utils *)

(** Same as List.fold_left, but f returns
    a tuple (acc, stop) where stop is a boolean
    stating that the loop has to stop. *)
let fold_left_stop
    (f : 'a -> 'b -> ('a * bool))
    (acc : 'a)
    (l : 'b list) : 'a
  =
  let rec __fold acc l =
    match l with
      [] -> acc
    | hd :: tl ->
      let acc, stop = f acc hd in
      if stop then acc
      else __fold acc tl
  in __fold acc l

type ('expr, 'abs_val) simp = {
  exp : 'expr;
  diff : bool;
  v : 'abs_val
}

let pp_simp pp_abs_val fmt s =
  Format.fprintf fmt "%a:%a"
    E.print s.exp
    pp_abs_val s.v

let get_expr e = e.exp
let get_abs_val e = e.v
let has_changed e = e.diff

type 'abs_val add_constraint_res =
  | AlreadyTrue (* The constraint is already true *)
  | AlreadyFalse (* The constraint is already false*)
  | NewConstraint of 'abs_val (* The new abstract value *)

(** 2. Simplifyer *)

(** As the simplifyer interacts with different components of alt-ergo,
    it is written to be as generic as possible.
    The simplifyer is then a functor of different modules which type is
    defined below. *)

(** Dom is the signature of the abstact domain. *)
module type Dom = sig
  type v (* The raw abstract value. For the interval domain, an interval *)
  type state (* The global state representation. Usually a map of 'v's *)

  (** Top/Bottom value *)
  val top : state
  val bottom : state

  val _true : v
  val _false : v
  val unknown : v

  (** (Partial) Compare function *)
  val compare : state -> state -> int option

  (** Join operator *)
  val join : state -> state -> state
  val v_join : v -> v -> v

  (** Add constraint *)
  val add_constraint :
    Expr.t ->
    Expr.t ->
    Symbols.lit ->
    state ->
    state add_constraint_res

  (** If possible, adds `expr` to `state` with the value `v` *)
  val add_raw_value : Expr.t -> v -> state -> state

  (** Evaluates an expression in the given state *)
  val eval_expr : Expr.t -> state -> v

  val pp : Format.formatter -> state -> unit
  val pp_v : Format.formatter -> v -> unit
end

(** This is the signature of the simplifyer. *)
module type S =
sig
  type v

  (** Empties the simplifier caches *)
  val empty_caches : unit -> unit

  (** Simplifies an expression. *)
  val simp_expr : Expr.t -> (Expr.t, v) simp
end

module SimpleReasoner
    (D : Dom)
  : S with type v = D.v = struct
  type state = D.state
  type v = D.v

  let (simp_cache : (state * (Expr.t, v) simp) list Expr.Map.t ref) =
    ref E.Map.empty

  let constraint_cache : (state * state add_constraint_res) list E.Map.t ref =
    ref E.Map.empty


  let empty_caches () =
    simp_cache := E.Map.empty;
    constraint_cache := E.Map.empty

  let add_cache cache exp state smp =
    let c = !cache in
    cache :=
      E.Map.add
        exp
        (match E.Map.find_opt exp c with
         | None ->  [state, smp]
         | Some l -> (state, smp) :: l)
        c

  let find_cache cache exp state =
    match E.Map.find_opt exp !cache with
    | Some l -> List.find_opt (
        fun (s,_) ->
          match D.compare s state with
          | Some 0 -> true
          | _ -> false)
        l
    | None -> None

  let pp_simp = pp_simp D.pp_v

  let identity v exp = {exp; diff = false; v = D.eval_expr exp v}

  let simp_true = {exp = E.vrai; diff = true; v = D._true}
  let simp_false = {exp = E.faux; diff = true; v = D._false}

  let is_true e = E.equal e.exp E.vrai
  let is_false e = E.equal e.exp E.faux

  let rec add_lit_constraint_no_cache (state : state) (e : Expr.t) =
    let exception Stop of state add_constraint_res in
    match E.lit_view e with
    | Eq (e1, e2) ->
      debug "[add_lit_constraint] Eq@.";
      D.add_constraint e1 e2 Sy.L_eq state

    | Eql [] -> assert false
    | Eql (hd :: tl) -> begin try
          debug "[add_lit_constraint] Eql@.";
          NewConstraint (
            List.fold_left
              (fun s e ->
                 match D.add_constraint hd e Sy.L_eq s with
                 | AlreadyTrue -> s
                 | AlreadyFalse -> raise (Stop AlreadyFalse)
                 | NewConstraint s' -> s'
              ) state tl
          )
        with Stop res -> res
      end
    | Distinct [] -> assert false
    | Distinct (hd :: tl) -> begin try
          debug "[add_lit_constraint] Distinct@.";
          NewConstraint (
            List.fold_left
              (fun s e ->
                 match D.add_constraint hd e Sy.L_neg_eq s with
                 | AlreadyTrue -> s
                 | AlreadyFalse -> raise (Stop AlreadyFalse)
                 | NewConstraint s' -> s') state tl)
        with Stop res -> res
      end
    | Builtin (_, btin, [e1; e2]) -> begin
        debug "[add_lit_constraint] Builtin@.";
        match D.add_constraint e1 e2 (Sy.L_built btin) state with
        | AlreadyTrue ->
          debug "[add_lit_constraint] Already true@.";
          AlreadyTrue
        | AlreadyFalse ->
          debug "[add_lit_constraint] Already false@.";
          AlreadyFalse
        | NewConstraint s' ->
          debug "[add_lit_constraint] New constraint: %a@."
            D.pp s';
          NewConstraint s'
      end
    | Builtin (_, _, _) -> failwith "Unhandled builtin"
    | Pred _ ->
      debug "[add_lit_constraint] Pred@.";
      NewConstraint state
    | Not_a_lit {is_form} ->
      debug "[add_lit_constraint] Not a lit@.";
      if is_form then
        add_form_constraint state e
      else
        failwith
          "add_lit_constraint should be only called on litterals or formulas"

  and add_lit_constraint (state : state) (e : Expr.t) =
    match find_cache constraint_cache e state with
    | None ->
      let res = add_lit_constraint_no_cache state e in
      add_cache constraint_cache e state res;
      res
    | Some (_, res) -> res

  and (&&&) v e =
    add_form_constraint v e

  and add_form_view_constraint state = function
    | E.Unit (e1, e2) -> begin
        debug "[add_form_constraint] Unit@.";
        match state &&& e1 with
        | AlreadyTrue -> state &&& e2
        | AlreadyFalse -> AlreadyFalse
        | NewConstraint state -> state &&& e2
      end
    | Clause (e1, e2, _) -> begin
        debug "[add_form_constraint] Clause@.";
        match state &&& e1 with
        | AlreadyTrue -> AlreadyTrue
        | AlreadyFalse -> state &&& e2
        | NewConstraint state1 -> begin
            match state &&& e2 with
            | AlreadyTrue -> AlreadyTrue
            | AlreadyFalse -> AlreadyFalse
            | NewConstraint state2 ->
              NewConstraint (D.join state1 state2)
          end
      end
    | Iff (e1, e2) -> begin (* = (e1 /\ e2) \/ (~e1 /\ ~e2) *)
        debug "[add_form_constraint] Iff@.";
        let c1 = state &&& e1 in (* Constraint on e1 *)
        match c1 with
        | AlreadyTrue -> (* e1 is true *) state &&& e2
        | AlreadyFalse -> (* e1 is false *) state &&& E.neg e2
        | NewConstraint s1 -> begin
            let nc1 = state &&& E.neg e1 in (* Constraint on ~e1 *)
            match nc1 with
            | AlreadyTrue -> (* e1 is false *)
              state &&& E.neg e2
            | AlreadyFalse -> (* e1 is true *)
              state &&& e2
            | NewConstraint ns1 ->
              let c2 = s1 &&& e2 in (* Constraint on (e1 /\ e2) *)
              match c2 with
              | AlreadyTrue -> (* (e1 /\ e2) is true *)
                AlreadyTrue
              | AlreadyFalse -> (* (e1 /\ e2) is false *)
                ns1 &&& E.neg e2
              | NewConstraint s2 ->
                let nc2 = ns1 &&& E.neg e2 in (* Constraint on (~e1 /\ ~e2) *)
                match nc2 with
                | AlreadyTrue -> (* (~e1 /\ ~e2) is true *)
                  AlreadyTrue
                | AlreadyFalse -> (* (~e1 /\ ~e2) is false *)
                  c2
                | NewConstraint ns2 ->
                  NewConstraint (D.join s2 ns2)
          end
      end
    | Xor (e1, e2) -> begin (* (e1 /\ ~e2) \/ (~e1 /\ e2) *)
        debug "[add_form_constraint] Xor@.";
        let c1 = state &&& e1 in (* Constraint on e1 *)
        match c1 with
        | AlreadyTrue -> (* e1 is true *)
          state &&& E.neg e2
        | AlreadyFalse -> (* e1 is false *)
          state &&& e2
        | (NewConstraint s1) as c1 ->
          let c2 = state &&& e2 in (* Constraint on e2 *)
          match c2 with
          | AlreadyTrue -> (* e2 is true *)
            state &&& E.neg e1
          | AlreadyFalse -> (* e2 is false *)
            c1
          | NewConstraint s2 -> (* State for e2 *)
            let nc1 = s1 &&& E.neg e2 in (* Constraint on (e1 /\ ~e2) *)
            match nc1 with
            | AlreadyTrue -> (* (e1 /\ ~e2) is true *)
              AlreadyTrue
            | AlreadyFalse -> (* (e1 /\ ~e2) is false *)
              s2 &&& E.neg e1
            | NewConstraint ns1 ->
              let nc2 = s2 &&& E.neg e1 in (* Constraint on (e2 /\ ~e1) *)
              match nc2 with
              | AlreadyTrue -> (* (e2 /\ ~e1) is true *)
                AlreadyTrue
              | AlreadyFalse -> (* (e2 /\ ~e1) is false *)
                nc1
              | NewConstraint ns2 -> NewConstraint (D.join ns1 ns2)
      end
    | Literal e ->
      debug "[add_form_constraint] Litteral@.";
      add_lit_constraint state e
    | Let _ ->
      debug "[add_form_constraint] Let binding: TODO@.";
      NewConstraint state

    | Lemma _
    | Skolem _ ->
      debug "[add_form_constraint] Lemma/Skolem: not using it@.";
      NewConstraint state

    | Not_a_form ->
      failwith
        "add_form_constraint should be only called on litterals or formulas"

  and add_form_constraint state e =
    match find_cache constraint_cache e state with
    | None ->
      let res = add_form_view_constraint state (E.form_view e) in
      add_cache constraint_cache e state res;
      res
    | Some (_, res) -> res

  and simp_ite
      (state : state)
      (cond : E.t)
      (th : E.t)
      (el : E.t) :
    (E.t, v) simp list =
    debug "[simp_ite] Simplifying condition %a with %a@."
      E.print cond
      D.pp state;
    let scond = simp_expr state cond in
    debug "[simp_ite] New condition %a ~~> %a@." E.print cond E.print scond.exp;
    if is_true scond then begin
      debug "[simp_ite] It is true, ending@.";
      let th : (E.t, v) simp = simp_expr state th in
      [{th with diff = true}]
    end else if is_false scond then begin
      debug "[simp_ite] It is false, ending@.";
      let el : (E.t, v) simp = simp_expr state el in
      [{el with diff = true}]
    end else begin
      (* Evaluating the condition *)
      let neg_cond = E.neg scond.exp in
      (* todo: split add constraint *)
      match state &&& scond.exp, state &&& neg_cond with
      | AlreadyTrue, AlreadyTrue
      | AlreadyFalse, AlreadyFalse ->
        failwith "Both the condition and its negation are true/false"
      | AlreadyFalse, _
      | _, AlreadyTrue ->
        debug "[simp_ite] Negation is true, ending@.";
        let el : (E.t, v) simp = simp_expr state el in
        [{el with diff = true}]
      | _, AlreadyFalse
      | AlreadyTrue, _ ->
        debug "[simp_ite] Negation is false, ending@.";
        let th : (E.t, v) simp = simp_expr state th in
        [{th with diff = true}]
      | NewConstraint cth, NewConstraint cel ->
        debug "[simp_ite] Cannot conclude, simplifying branches@.";
        let sth : (E.t, v) simp = simp_expr cth th in
        let sel : (E.t, v) simp = simp_expr cel el in
        [scond; sth; sel]
    end

  and simp_form
      (state : state)
      (f : Symbols.form)
      (elist : E.t list)
    : (E.t, v) simp list =
    match f with
    | Symbols.F_Unit _ -> begin (* <=> AND *)
        let () = debug "[simp_form] F_Unit@." in
        let _state,rev_res =
          fold_left_stop
            (fun (state, simp_exps) e ->
               debug "[simp_form] Simplifying %a in F_Unit@."
                 E.print e;
               let esimp : (E.t, v) simp = simp_expr state e in
               debug "[simp_form] Simplified %a into %a in F_Unit@."
                 E.print e pp_simp esimp;
               if is_false esimp then (
                 debug "[simp_form] %a = false@." E.print e;
                 (state, [simp_false]), true
               )
               else if is_true esimp then (
                 debug "[simp_form] %a = true@." E.print e;
                 (state, simp_exps), false
               )
               else (
                 debug "[simp_form] Keeping %a@." E.print e;
                 match state &&& esimp.exp with
                 | AlreadyTrue
                 | AlreadyFalse -> failwith "Should have simplify beforehand"
                 | NewConstraint state ->
                   (state, (esimp :: simp_exps)))
               , false
            )
            (state, [])
            elist
        in
        match rev_res with
        | [] ->
          debug "[simp_form] No more litteral in form: must be true@.";
          [simp_true]
        | _ -> List.rev rev_res
      end

    | F_Clause _ -> begin (* <=> OR *)
        let () = debug "[simp_form] F_Clause@." in
        let _state, rev_res =
          fold_left_stop
            (fun (state, simp_exps) e ->
               debug "[simp_form] Simplifying %a in clause@."
                 E.print e;
               let (esimp : (E.t, v) simp) = simp_expr state e in
               debug "[simp_form] Simplified %a into %a in clause@."
                 E.print e pp_simp esimp;
               if is_false esimp then (
                 debug "[simp_form] %a = false@." E.print e;
                 (state, simp_exps), false
               )
               else if is_true esimp then (
                 debug "[simp_form] %a = true@." E.print e;
                 (state, [simp_true]), true
               )
               else (
                 debug "[simp_form] Keeping %a@." E.print e;
                 (state, (esimp :: simp_exps)))
               , false)
            (state, [])
            elist
        in
        match rev_res with
        | [] ->
          debug "[simp_form] No more litteral in form: must be false@.";
          [simp_false]
        | _ -> List.rev rev_res
      end
    | _ ->
      let () = debug "[simp_form] No additional simplification@." in
      List.map (identity state) elist

  and simp_expr_no_cache state (e : E.t) : (E.t, v) simp =
    debug "[simp_expr] Simplifying expression %a with %a@."
      E.print e D.pp state;
    let res =
      let ty = E.type_info e in
      let elist = E.get_sub_expr e in
      let symb = E.get_symb e in
      match symb, elist with
      | Op Tite, [cond; th; el] -> begin
          debug "[simp_expr] Ite@.";
          let simp = simp_ite state cond th el in
          debug "[simp_expr] Ite treated@.";
          match simp with
          | [branch] ->
            debug "[simp_expr] Simplification cut a branch, yielding %a@."
              Expr.print branch.exp;
            branch
          | [cond; th; el] ->
            if cond.diff || th.diff || el.diff then
              (* If by any luck, th == el... *)
              if Expr.equal th.exp el.exp then begin (* bingo *)
                debug "[simp_expr] Both branches are equal @.";
                {th with diff = true}
              end else begin
                (* A simplification has been made *)
                debug "[simp_expr] Simplification worked on a branch@."; {
                  exp = E.mk_term (Op Tite) [cond.exp; th.exp; el.exp] ty;
                  diff = true;
                  v = D.v_join th.v el.v
                }
              end else begin
              debug "[simp_expr] Simplification failed@.";
              { (* Simplification failed *)
                exp = e;
                diff = false;
                v = D.v_join th.v el.v
              } end
          | _ -> assert false
        end
      | Op Tite, _ -> assert false
      | Symbols.Form (F_Skolem | F_Lemma), _ ->
        debug "[simp_expr] Skolem/Lemmas not simplified";
        {
          exp = e;
          diff = false;
          v = D.unknown
        }
      | Symbols.Form f, _ -> begin
          debug "[simp_expr] Formula: %a@." Symbols.print symb;
          let l = simp_form state f elist in
          match l with
          | [] -> assert false
          | hd :: tl ->
            if hd.diff || List.exists (fun e -> e.diff) tl then
              begin
                let make =
                  (match f with
                   | F_Unit b   -> (fun e e' -> E.mk_and e e' b)
                   | F_Clause b -> (fun e e' -> E.mk_or e e' b)
                   | F_Iff      -> E.mk_iff
                   | F_Xor      -> E.mk_xor
                   | F_Skolem | F_Lemma -> assert false) in
                List.fold_left
                  (fun sexp term ->
                     {sexp with exp = make sexp.exp term.exp (-44)})
                  hd tl
              end
            else {
              exp = e;
              diff = false;
              v = D.unknown
            }
        end
      | Symbols.Lit _, _ -> begin
          debug
            "[simp_expr] Litteral : %a@."
            Symbols.print symb;
          match add_lit_constraint state e with
          | AlreadyTrue  ->
            debug "[simp_expr] Litteral %a is true@." E.print e;
            simp_true
          | AlreadyFalse ->
            debug "[simp_expr] Litteral %a is false@." E.print e;
            simp_false
          | NewConstraint state -> {
              exp = e;
              diff = false;
              v = D.eval_expr e state
            }
        end
      | Symbols.Let, [] -> begin
          match Expr.form_view e with
          | E.Let {let_v; let_e; in_e; let_sko = _; is_bool = _} ->
            debug "[simp_expr] Let@.";
            let v_exp = E.mk_term let_v [] (E.type_info let_e) in
            let simp_let = simp_expr state let_e in
            let state = D.add_raw_value v_exp simp_let.v state in
            let simp_in = simp_expr state in_e in
            let diff = simp_let.diff || simp_in.diff in
            let exp =
              if diff then E.mk_let let_v simp_let.exp simp_in.exp (-43)
              else e
            in {exp; diff; v = simp_in.v}
          | _ -> assert false
        end

      | Symbols.Let, _ -> assert false
      | _ ->
        debug
          "[simp_expr] Other: %a@."
          Symbols.print symb;
        let (l : (E.t, v) simp list) = List.map (simp_expr state) elist in
        if List.exists (fun e -> e.diff) l then {
          exp = E.mk_term symb (List.map (fun e -> e.exp) l) ty;
          diff = true;
          v = D.eval_expr e state
        }
        else {exp = e; diff = false; v = D.eval_expr e state}
    in
    debug "[simp_expr] Simplification ENDED.@.";
    debug "[simp_expr] Old : %a@." E.print e;
    debug "[simp_expr] Result : %a@." pp_simp res;
    res

  and simp_expr state (e : E.t) : (E.t, v) simp =
    match find_cache simp_cache e state with
    | None ->
      debug "[simp_expr] Expression %a never simplified@."
        E.print e;
      let res = simp_expr_no_cache state e in
      add_cache simp_cache e state res;
      res
    | Some (_, se) ->
      debug "[simp_expr] Expression %a already simplified by %a@."
        E.print e pp_simp se;
      se

  (** Wrapper of simp_expr for verbose *)
  let simp_expr e =
    try
      debug "START Simplifying %a@." E.print e;
      let res = simp_expr D.top e in
      if res.diff
      then
        let () =
          debug
            "Old expression = %a@."
            E.print e;
          debug
            "New expression = %a@."
            E.print res.exp in
        res
      else
        let () =
          debug
            "No change on %a@."
            E.print e in
        identity D.top e
    with
      Failure s ->
      debug
        "Error while simplifying %a\n%s\n\
         I will continue with the initial expression@."
        E.print e
        s;
      identity D.top e
end

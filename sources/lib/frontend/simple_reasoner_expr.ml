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

(** 1. Utils *)
type value =
    Bool of bool
  | Num of float

let (++) v1 v2 =
  match v1, v2 with
    Bool b1, Bool b2 -> Bool (b1 || b2)
  | Num n1, Num n2 -> Num (n1 +. n2)
  | _,_ -> assert false

let (--) v1 v2 =
  match v1, v2 with
  | Num n1, Num n2 -> Num (n1 -. n2)
  | _,_ -> assert false

let ( ** ) v1 v2 =
  match v1, v2 with
    Bool b1, Bool b2 -> Bool (b1 && b2)
  | Num n1, Num n2 -> Num (n1 *. n2)
  | _,_ -> assert false

let (|=) v1 v2 =
  match v1, v2 with
    Bool b1, Bool b2 -> b1 == b2
  | Num n1, Num n2 -> Float.equal n1 n2
  | _,_ -> false

(*let (|<>) v1 v2 = not (v1 |= v2) *)

let (|<) v1 v2 =
  match v1, v2 with
  | Num n1, Num n2 -> n1 < n2
  | _,_ -> assert false

let (|<=) v1 v2 =
  match v1, v2 with
  | Num n1, Num n2 -> n1 <= n2
  | _,_ -> assert false

let fold_left_stop f acc l =
  let rec __fold acc l =
    match l with
      [] -> acc
    | hd :: tl ->
      let acc, stop = f acc hd in
      if stop then acc else
        __fold acc tl
  in __fold acc l

(** A simplified formula/expr/... type.
   the diff field is set to false if the operation did not change the
   input.
 *)
type 'a simp =
  {
    v : 'a;
    diff : bool
  }

let get_expr (e : 'a simp) : 'a = e.v
let has_changed (e : 'a simp) : bool = e.diff

(** 2. Simplifyer *)

module type S =
sig
  type expr

  (** Adds/replaces the value of an expression. This expression will be replaced by a
      constant if possible *)
  val bind_expr_val : expr -> float -> unit

  (** Adds/replaces the value of an expression. This expression will be replaced by a
      constant if possible *)
  val bind_expr_bool : expr -> bool -> unit

  (** Simplifies an expression *)
  val simp_expr : expr -> expr simp
end

module SimpleReasoner
    (E :
     sig
       (** Expressions are generally defined by 3 elements:
           - a type
           - a set of sub expressions
           - a composition operator *)
       type t
       val hash : t -> int
       val equal : t -> t -> bool
       val mk_expr : Symbols.t -> t list -> Ty.t -> t

       val get_comp : t -> Symbols.t
       val get_sub_expr : t -> t list
       val get_type : t -> Ty.t

       val vrai : t
       val faux : t

       val real : string -> t
       val int : string -> t

       val pretty : Format.formatter -> t -> unit

     end) : S with type expr = E.t
=
struct
  let verb = Options.simplify_verbose
  type expr = E.t

  module ExprTbl =
  struct
    include Hashtbl.Make (E)
    let find_opt (tbl : 'a t) (k : key) =
      try Some (find tbl k) with _ -> None
  end

  let binder : value ExprTbl.t = ExprTbl.create 17
  let bind_expr_val (e : expr) v =
    if verb () then
      Format.printf
        "%a = %f@."
        E.pretty e
        v;
    ExprTbl.add binder e (Num v)

  let bind_expr_bool (e : expr) b =
    if verb () then
      Format.printf
        "%a = %b@."
        E.pretty e
        b;
    ExprTbl.add binder e (Bool b)

  let identity v = {v; diff = false}
  let diff_list (l : 'a simp list) : 'a list simp =
    let rev =
      List.fold_left
        (fun acc s ->
           {v = s.v :: acc.v; diff = acc.diff || s.diff}
        )
        {v = []; diff = false}
        l
    in
    {rev with v = List.rev rev.v}

  let expr_to_value (e : expr) : value option =
    match E.get_comp e with
      True -> Some (Bool true)
    | False -> Some (Bool false)
    | Int s
    | Real s -> Some (Num (Float.of_string (Hstring.view s)))
    | _ -> ExprTbl.find_opt binder e

  let value_to_expr (ty : Ty.t) (v : value) : expr =
    match v with
      Bool true -> E.vrai
    | Bool false -> E.faux
    | Num i ->
      if ty == Ty.Treal then E.real (string_of_float i)
      else E.int (string_of_float i)

  let arith
      (ty : Ty.t)
      (op : value -> value -> value)
      (e_list : expr list): expr list simp =
    let vals,exprs =
      List.fold_left
        (fun (acc_solved,acc_remain) v ->
           match expr_to_value v with
             None -> (acc_solved, v :: acc_remain)
           | Some v ->
             match acc_solved with
               None -> (Some v, acc_remain)
             | Some old_v -> (Some (op old_v v), acc_remain)
        )
        (None, [])
        e_list
    in
    match vals with
      None -> {v = e_list; diff = false}
    | Some v -> {v = (value_to_expr ty v) :: List.rev exprs; diff = true}

  let oper (op : value -> value -> bool) (l : expr list) : bool * bool =
    (* all_true is a boolean stating that every operation succeded.
       set to true at the beginning, it is set to false if one of the
       list term.
       last_val is the last value that has been accepted by the test.
       Set to None at the beginning. *)
    let rec _oper
        (all_true : bool)
        (last_val : value option)
        (l : expr list) : bool * bool =
      match l with
        [] -> (* No more elements, and none failed the test. *)
        false, all_true
      | hd :: tl ->
        let hd_val = expr_to_value hd in
        match hd_val, last_val with
        | None, None ->
          _oper false None tl

        | Some v, None ->
          _oper all_true (Some v) tl

        | None, Some v ->
          _oper all_true (Some v) tl

        | Some v, Some v' ->
          if op v v'
          then (
            _oper all_true (Some v') tl
          )
          else (
            true,false (* The operation is not respected *)
          )
    in
    _oper true None l

  let apply_op (op : value -> value -> bool) (l : expr list) : expr list simp =
    let falsify,all_true = oper op l in
    if falsify
    then {v = [E.faux]; diff = true}
    else if all_true
    then {v = [E.vrai]; diff = true}
    else {v = l; diff = false}

  let rec simp_expr (e : expr) : expr simp =

    let ty = E.get_type e in (*
    let elist = (List.map (fun e -> simp_expr e))  (E.get_sub_expr e) in *)
    let by_operator (op : Symbols.operator) (elist : expr list) : expr list simp =
      match op with
      | Symbols.Plus  -> arith ty (++) elist
      | Symbols.Minus -> arith ty (--) elist
      | Symbols.Mult  -> arith ty ( ** ) elist
      | Symbols.Tite -> (
          match elist with
            cond :: th :: el :: [] ->
            if E.(equal cond vrai) then {v = [th]; diff = true}
            else if E.(equal cond faux) then {v = [el]; diff = true}
            else if E.equal th el then {v = [th]; diff = true}
            else identity elist
          | _ -> assert false
        )
      | _ -> identity elist in

    let by_form (f : Symbols.form) (elist : expr list) : expr list simp =
      match f with
      | Symbols.F_Unit _ -> (* <=> AND *) (
          let res =
            fold_left_stop
              (fun acc e ->
                 if E.(equal e vrai) then {v = acc.v; diff = true}, false
                 else if E.(equal e faux) then {v = [E.faux]; diff = true}, true
                 else {v = (e :: acc.v); diff = acc.diff}, false
              )
              {v = []; diff= false}
              elist
          in
          match res.v with
            [] -> {v = [E.vrai]; diff = true}
          | _ -> {res with v = List.rev res.v}
        )
      | F_Clause _ -> (* <=> OR *) (
          let res =
            fold_left_stop
              (fun acc e ->
                 if E.(equal e faux) then {v = acc.v; diff = true}, false
                 else if E.(equal e vrai) then {v = [E.vrai]; diff = true}, true
                 else {v = (e :: acc.v); diff = acc.diff}, false
              )
              {v = []; diff= false}
              elist
          in
          match res.v with
            [] -> {v = [E.faux]; diff = true}
          | _ ->  {res with v = List.rev res.v}
        )
      | _ -> identity elist

    and by_lit (l : Symbols.lit) (elist : expr list) : expr list simp =
      let is_constr (constr : Hstring.t) (e : expr) : bool option =
        match E.get_comp e with
          Op (Constr s') -> Some (Hstring.equal constr s')
        | _ -> None
      in
      match l with
        L_eq -> (
          let res = apply_op (|=) elist in
          match res.v with
            [] | _ :: [] -> res
          | _ -> (* structural equality check *)
            if
              List.for_all
                (fun elt -> E.equal elt @@ List.hd res.v) (List.tl res.v)
            then
              {v = [E.vrai]; diff = true}
            else res
        )
      | L_built LE -> apply_op (|<=) elist
      | L_built LT -> apply_op (|<) elist
      | L_neg_built _
      | L_neg_pred
      | L_neg_eq -> identity elist

      | L_built (IsConstr s) -> (
        match elist with
          e :: [] -> (
            match is_constr s e with
              None ->
              if verb ()
              then
                Format.printf
                  "%a is not explicitely the constructor %a, leaving as is@."
                  E.pretty e
                  Hstring.print s
              ;
              identity elist
            | Some true  ->
              if verb ()
              then
                Format.printf
                  "%a is explicitely the constructor %a, this is TRUE@."
                  E.pretty e
                  Hstring.print s;
              {v = [E.vrai]; diff = true}
            | Some false ->
              if verb ()
              then
                Format.printf
                  "%a is explicitely NOT the constructor %a, this is FALSE@."
                  E.pretty e
                  Hstring.print s;
              {v = [E.faux]; diff = true}
          )
          | _ -> assert false
      )
    in
    let elist = (List.map (fun e -> simp_expr e))  (E.get_sub_expr e) |> diff_list in
    let xs =
      let symb = E.get_comp e in
      match symb with
        Op o ->
        if verb () then
          Format.printf
            "Operator: %a@."
            Symbols.print symb;
        by_operator o elist.v
      | Form f ->
        if verb () then
          Format.printf
            "Formula: %a@."
            Symbols.print symb;
        by_form f elist.v
      | Lit l ->
        if verb () then
          Format.printf
            "Literal: %a@."
            Symbols.print symb;
        by_lit l elist.v
      | _ ->
        if verb () then
          Format.printf
            "Other: %a@."
            Symbols.print symb;
        elist
    in
    let diff = elist.diff || xs.diff in
    let v =
      if not diff then e
      else
      match xs.v with
        [] -> e
      | elt :: [] -> elt
      | l -> E.mk_expr (E.get_comp e) l (E.get_type e)
    in
    if verb ()
    then
      Format.printf
        "Old expression = %a\n\
         New expression = %a@."
        E.pretty e
        E.pretty v;
    {v; diff}

  (** Wrapper of simp_expr for option *)
  let simp_expr e =
    if Options.simplify ()
    then simp_expr e
    else identity e
end

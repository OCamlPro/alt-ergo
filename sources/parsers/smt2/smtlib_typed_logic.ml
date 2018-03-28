open Smtlib_typed_env
open Smtlib_error

type th_def = {
  sorts : (string * ((int * int) * (string -> (Smtlib_ty.ty list * int list)  -> Smtlib_ty.desc))) list;
  funs : (string * (Smtlib_ty.ty list) * Smtlib_ty.ty * assoc option) list
}

type theory =
  | Core
  | Ints
  | Reals
  | Reals_Ints
  | FloatingPoint
  | Arrays
  | BitVectors

let new_fun name  params return assoc =
  name, params, return, assoc

let core = {
  sorts = [ "Bool",((0,0),(fun s (l1,l2) -> assert (l1 == [] && l2 == []); Smtlib_ty.TBool))];
  funs = [
    new_fun "true" [] (Smtlib_ty.new_type Smtlib_ty.TBool) None;
    new_fun "false" [] (Smtlib_ty.new_type Smtlib_ty.TBool) None;
    new_fun "not" [(Smtlib_ty.new_type Smtlib_ty.TBool)] (Smtlib_ty.new_type Smtlib_ty.TBool) None;
    new_fun  "=>" [(Smtlib_ty.new_type Smtlib_ty.TBool); (Smtlib_ty.new_type Smtlib_ty.TBool)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Right);
    new_fun "and" [(Smtlib_ty.new_type Smtlib_ty.TBool); (Smtlib_ty.new_type Smtlib_ty.TBool)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Left);
    new_fun "or" [(Smtlib_ty.new_type Smtlib_ty.TBool); (Smtlib_ty.new_type Smtlib_ty.TBool)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Left);
    new_fun "xor" [(Smtlib_ty.new_type Smtlib_ty.TBool); (Smtlib_ty.new_type Smtlib_ty.TBool)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Left);
    (let a = Smtlib_ty.new_type(TVar("A")) in new_fun "=" [a;a]
      (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Chainable));
    (let a = Smtlib_ty.new_type(TVar("A")) in new_fun "distinct" [a;a]
       (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Pairwise));
    (let a = Smtlib_ty.new_type(TVar("A")) in new_fun "ite" [(Smtlib_ty.new_type Smtlib_ty.TBool); a; a] a None);
  ]
}

let ints = {
  sorts = ["Int",((0,0),(fun s (l1,l2) -> assert (l1 == [] && l2 == []); Smtlib_ty.TInt))];
  funs = [
    new_fun "-" [(Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TInt) None;
    new_fun "-" [(Smtlib_ty.new_type Smtlib_ty.TInt); (Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TInt) (Some Left);
    new_fun "+" [(Smtlib_ty.new_type Smtlib_ty.TInt); (Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TInt) (Some Left);
    new_fun "*" [(Smtlib_ty.new_type Smtlib_ty.TInt); (Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TInt) (Some Left);
    new_fun "div" [(Smtlib_ty.new_type Smtlib_ty.TInt); (Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TInt) (Some Left);
    new_fun "mod" [(Smtlib_ty.new_type Smtlib_ty.TInt); (Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TInt) None;
    new_fun "abs" [(Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TInt) None;
    new_fun "<=" [(Smtlib_ty.new_type Smtlib_ty.TInt); (Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Chainable);
    new_fun "<" [(Smtlib_ty.new_type Smtlib_ty.TInt); (Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Chainable);
    new_fun ">=" [(Smtlib_ty.new_type Smtlib_ty.TInt); (Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Chainable);
    new_fun ">" [(Smtlib_ty.new_type Smtlib_ty.TInt); (Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Chainable);
  ]
}

let reals = {
  sorts = ["Real",((0,0),(fun s (l1,l2) -> assert (l1 == [] && l2 == []); Smtlib_ty.TReal))];
  funs = [
    new_fun "-" [(Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TReal) None;
    new_fun "-" [(Smtlib_ty.new_type Smtlib_ty.TReal); (Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TReal) (Some Left);
    new_fun "+" [(Smtlib_ty.new_type Smtlib_ty.TReal); (Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TReal) (Some Left);
    new_fun "*" [(Smtlib_ty.new_type Smtlib_ty.TReal); (Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TReal) (Some Left);
    new_fun "/" [(Smtlib_ty.new_type Smtlib_ty.TReal); (Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TReal) (Some Left);
    new_fun "<=" [(Smtlib_ty.new_type Smtlib_ty.TReal); (Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Chainable);
    new_fun "<" [(Smtlib_ty.new_type Smtlib_ty.TReal); (Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Chainable);
    new_fun ">=" [(Smtlib_ty.new_type Smtlib_ty.TReal); (Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Chainable);
    new_fun ">" [(Smtlib_ty.new_type Smtlib_ty.TReal); (Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TBool) (Some Chainable);
  ]
}
let reals_ints = {
  sorts = List.rev_append ints.sorts reals.sorts;
  funs = List.rev_append (List.rev_append ints.funs reals.funs) [
    new_fun "to_real" [(Smtlib_ty.new_type Smtlib_ty.TInt)] (Smtlib_ty.new_type Smtlib_ty.TReal) None;
    new_fun "to_int" [(Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TInt) None;
    new_fun "is_int" [(Smtlib_ty.new_type Smtlib_ty.TReal)] (Smtlib_ty.new_type Smtlib_ty.TBool) None;
  ] }

let arrays =
  {
    sorts = ["Array",((2,0),
                      (fun s (l1,l2) ->
                         let t1,t2 = List.hd l1, List.hd (List.tl l1) in
                         assert (List.length l1 = 2 && l2 == []);
                         Smtlib_ty.TArray (t1,t2)))];
    funs = [
      (let x = Smtlib_ty.new_type(TVar("X")) in
       let y = Smtlib_ty.new_type(TVar("Y")) in
       new_fun "select" [Smtlib_ty.new_type (Smtlib_ty.TArray (x,y));x] y None);
      (let x = Smtlib_ty.new_type(TVar("X")) in
       let y = Smtlib_ty.new_type(TVar("Y")) in
       new_fun "store" [Smtlib_ty.new_type (Smtlib_ty.TArray (x,y));x;y] (Smtlib_ty.new_type (Smtlib_ty.TArray (x,y))) None);
    ] }


let floating_point = {
  sorts = List.rev_append reals.sorts [];
  funs = [] }

let bit_vectors = {
    sorts = ["BitVec",((0,1),
                       (fun s (l1,l2) ->
                          assert (List.length l2 = 1 && l1 == []);
                          Smtlib_ty.TBitVec(List.hd l2)
                       ))];
  funs = [ ] }


let add_theories env ths c =
  let aux env th =
    let sorts, funs =
      match th with
      | Core -> core.sorts,core.funs
      | Ints -> ints.sorts,ints.funs
      | Reals ->
        let sorts = if get_is_real () then
            ("Int",((0,0),(fun s (l1,l2) -> assert (l1 == [] && l2 == []); Smtlib_ty.TReal)))
            :: reals.sorts
          else reals.sorts
        in
          sorts ,reals.funs
      | Reals_Ints -> reals_ints.sorts,reals_ints.funs
      | FloatingPoint -> floating_point.sorts,floating_point.funs
      | Arrays -> arrays.sorts,arrays.funs
      | BitVectors -> bit_vectors.sorts,bit_vectors.funs
    in
    let env = Smtlib_typed_env.add_sorts env sorts in
    Smtlib_typed_env.add_funs env funs c
  in
  List.fold_left (fun env th -> aux env th) env ths


let contains s1 s2 =
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.sub s1 i len = s2 then raise Exit
    done;
    false
  with Exit -> true

let set_logic env s =
  let logic = s.Smtlib_syntax.c in
  let theories = ref [Core] in
  let all = contains logic "ALL" in
  if contains logic "QF" then
    set_is_qf true;
  if all || contains logic "UF" then
    set_is_uf true;

  if contains logic "BV" then
    Printf.eprintf "[Warning] Bitvector not yet implemented\n%!";
  if contains logic "FP" then
    Printf.eprintf "[Warning] Floating point not yet implemented\n%!";

  if all || contains logic "AX" || contains logic "A" then
      theories := Arrays :: !theories;

  if contains logic "IRA" then
    theories := Reals_Ints :: !theories
  else if contains logic "IA" || contains logic "IDL" then
    theories := Ints :: !theories
  else if all || contains logic "RA" || contains logic "RDL" then
    set_is_real true;
    theories := Reals :: !theories;

  if all || contains logic "LIRA" || contains logic "LIA" || contains logic "LRA" then
    set_is_linear true;
  if contains logic "NIRA" || contains logic "NIA" || contains logic "NRA" then
    set_is_non_linear true;

  if contains logic "DT" then
    set_is_dt true;

  add_theories env !theories s

(* This function is present in the stdlib since Ocaml 4.12. *)
let rec compare_list cmp l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | [], _ -> 1
  | _, [] -> -1
  | (_, x1)::l1, (_, x2)::l2 -> (
      let c = cmp x1 x2 in
      if c <> 0 then c else compare_list cmp l1 l2)

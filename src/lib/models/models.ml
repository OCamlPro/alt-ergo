module Sorts = Map.Make(String)

let h = ref Sorts.empty

let sorts parsed =
  let open Parsed in
  Format.eprintf "@[<v 2>";
  Seq.iter (fun d -> match d with
      | Parsed.Axiom (_, _, _, le) -> begin
          match le.pp_desc with
          | PPapp("sort", f)
          | PPforall_named (_, _, _, {pp_desc = PPapp("sort", f); _}) ->
            begin
              match f with
              | [{pp_desc = PPapp(t, _); _}; {pp_desc = PPapp(f, args); _}] ->
                h := Sorts.add f (List.length args, t) !h
              | _ -> ()
            end
          | _ -> ()
        end
      | _ -> ()
    ) parsed

let get_type s =
  try let (_, t) = Sorts.find s !h in Some t
  with Not_found -> None

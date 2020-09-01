module Sorts = Map.Make(String)

let sorts parsed =
  let open Parsed in
  Seq.iter (fun d -> match d with
      | Axiom (_, _, _, {
          pp_desc =
            PPapp("sort", [
                {pp_desc = PPapp(t, []); _};
                {pp_desc=PPapp(f, []); _}
              ]); _
        }) ->
        Format.eprintf "@{<fg_blue>sort: %s : %s@}@ " f t
      | _ -> ()
      (* Format.eprintf "blah@." *)
    ) parsed;
  Format.eprintf "@]@.";

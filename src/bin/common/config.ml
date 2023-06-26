let plugins_locations = AltErgoSites.Sites.plugins

let preludes_locations = AltErgoSites.Sites.preludes

(* {!List.find_map} from OCaml >= 4.10 *)
let rec find_map f = function
  | [] -> None
  | x :: xs ->
    match f x with
    | Some _ as y -> y
    | None -> find_map f xs

let lookup_file locations filename =
  find_map
    (fun location ->
       let filename = Filename.concat location filename in
       if Sys.file_exists filename then Some filename else None)
    locations

let lookup_prelude = lookup_file preludes_locations

let lookup_plugin = lookup_file plugins_locations

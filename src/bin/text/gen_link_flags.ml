let pkgconfig lib archive =
  let cmd = Fmt.str "pkg-config %s --variable libdir" lib in
  let output = Unix.open_process_in cmd |> input_line in
  Fmt.str "%s/%s" output archive

let pp_lib ppf s = Fmt.pf ppf "-cclib %s" s

let starts_with ~prefix s =
  let open String in
  let len_s = length s
  and len_pre = length prefix in
  let rec aux i =
    if i = len_pre then true
    else if unsafe_get s i <> unsafe_get prefix i then false
    else aux (i + 1)
  in len_s >= len_pre && aux 0

let () =
  let mixed_flags = ["-noautolink"] in
  (* Note: for OCaml 5, use -lcamlstrnat and -lunixnat and mind zlib
     https://github.com/ocaml/ocaml/issues/12562 *)
  let mixed_cclib = [
    "-lcamlzip";
    "-lzarith";
    "-lcamlstr";
    "-lunix";
    "-lz"
  ]
  in
  let libs = ["gmp"] in
  let link_mode = Sys.argv.(1) and os = Sys.argv.(2) in
  let flags, cclib =
    match link_mode, os with
    | "dynamic", _ -> [], []
    | "static", "linux" -> [], ["-static"; "-no-pie"]
    | "mixed", "linux" ->
      let cclib = mixed_cclib @ List.map (fun s -> "-l" ^ s) libs in
      mixed_flags, "-Wl,-Bdynamic" :: "-Wl,-Bstatic" :: cclib
    | "mixed", "macosx" ->
      let cclib = mixed_cclib @
                  List.map
                    (fun lib ->
                       let archive =
                         if starts_with
                             ~prefix:"lib" lib then
                           Fmt.str "%s.a" lib
                         else
                           Fmt.str "lib%s.a" lib
                       in
                       pkgconfig lib archive
                    ) libs
      in
      mixed_flags, cclib
    | _ -> Fmt.invalid_arg "unsupported mode %s and OS %s" link_mode os
  in
  Fmt.pr "@[(-linkall %a %a)@]"
    Fmt.(list ~sep:sp string) flags
    Fmt.(list ~sep:sp pp_lib) cclib;

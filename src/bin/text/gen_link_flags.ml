let pkgconfig lib archive =
  let cmd = Fmt.str "pkg-config %s --variable libdir" lib in
  let output =
    Unix.open_process_in cmd
    |> In_channel.input_line
    |> Option.get
  in
  Fmt.str "%s/%s" output archive

let pp_lib ppf s = Fmt.pf ppf "-cclib %s" s

let () =
  let link_mode = Sys.argv.(1) in
  let os = Sys.argv.(2) in
  let flags, cclib =
    match link_mode with
    | "dynamic" -> [], []
    | "static" ->
      begin
        match os with
        | "linux" -> ["-static"; "-no-pie"], []
        | _ ->
          Fmt.epr "No known static compilation flags for %s" os;
          exit 1
      end
    | "mixed" ->
      begin
        let flags = ["-noautolink"] in
        let cclib = [
          "-lstdcompat_stubs";
          "-lcamlzip";
          "-lzarith";
          "-lcamlstr";
          "-lunix";
          "-lz"
        ]
        in
        let libs = ["gmp"] in
        match os with
        | "linux" ->
          let cclib = cclib @ List.map (fun s -> "-l" ^ s) libs in
          flags,
          "-Wl,-Bstatic" :: cclib @ ["-Wl,-Bdynamic"]
        | "macosx" ->
          let cclib = cclib @
                      List.map
                        (fun lib ->
                           let archive =
                             if Stdcompat.String.starts_with ~prefix:"lib" lib then
                               Fmt.str "%s.a" lib
                             else
                               Fmt.str "lib%s.a" lib
                           in
                           pkgconfig lib archive
                        ) libs
          in
          flags,
          cclib
        | _ ->
          Fmt.epr "No known mixed compilation flags for %s" os;
          exit 1
      end
    | _ ->
      Fmt.epr "Invalid link mode %s" link_mode;
      exit 1
  in
  Fmt.pr "@[(-linkall %a %a)@]"
    Fmt.(list ~sep:sp string) flags
    Fmt.(list ~sep:sp pp_lib) cclib

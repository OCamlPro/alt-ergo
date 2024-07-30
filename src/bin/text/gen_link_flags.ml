type os = Linux | Macos
type link_mode = Dynamic | Static | Mixed

module Cmd = struct
  open Cmdliner

  let show l = List.map (fun (s, _) -> s) l

  let os_term =
    let all = [
      ("linux", Linux);
      ("macosx", Macos)
    ]
    in
    let doc =
      Fmt.str "Choose the operating system, $(docv) must be %s."
        (Arg.doc_alts @@ show all)
    in
    Arg.(value & opt (enum all) Linux & info ["os"] ~docv:"OS" ~doc)

  let link_mode_term =
    let all = [
      ("dynamic", Dynamic);
      ("static", Static);
      ("mixed", Mixed)
    ]
    in
    let doc =
      Fmt.str "Choose the operating system, $(docv) must be %s."
        (Arg.doc_alts @@ show all)
    in
    Arg.(value & opt (enum all) Dynamic &
         info ["link-mode"] ~docv:"MODE" ~doc)

  let parse k =
    let info = Cmd.info "rewrite-gen-link-flags" in
    Cmd.v info Term.(ret (const k $ link_mode_term $ os_term))
    |> Cmd.eval
end

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
  let mixed_flags = ["-noautolink"] in
  let mixed_cclib = [
    "-lstdcompat_stubs";
    "-lcamlzip";
    "-lzarith";
    "-lcamlstr";
    "-lunix";
    "-lz"
  ]
  in
  let libs = ["gmp"] in
  let rc =
    Cmd.parse @@ fun link_mode os ->
    let flags, cclib =
      match link_mode, os with
      | Dynamic, _ -> [], []
      | Static, Linux -> [], ["-static"; "-no-pie"]
      | Mixed, Linux ->
        let cclib = mixed_cclib @ List.map (fun s -> "-l" ^ s) libs in
        mixed_flags, "-Wl,-Bdynamic" :: "-Wl,-Bstatic" :: cclib
      | Mixed, Macos ->
        let cclib = mixed_cclib @
                    List.map
                      (fun lib ->
                         let archive =
                           if Stdcompat.String.starts_with
                               ~prefix:"lib" lib then
                             Fmt.str "%s.a" lib
                           else
                             Fmt.str "lib%s.a" lib
                         in
                         pkgconfig lib archive
                      ) libs
        in
        mixed_flags, cclib
      | _ -> Fmt.invalid_arg "unsupported mode and OS"
    in
    Fmt.pr "@[(-linkall %a %a)@]"
      Fmt.(list ~sep:sp string) flags
      Fmt.(list ~sep:sp pp_lib) cclib;
    `Ok ()
  in
  exit rc

{ pkgs ? import ./nix { } }:

let
  inherit (pkgs) lib python3Packages;
  ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
in

pkgs.mkShell {
  # Required for correct locales on non-NixOS,
  # see https://nixos.wiki/wiki/Locales
  LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
  nativeBuildInputs = with ocamlPackages; [
    pkgs.ocamlformat_0_28_1
    pkgs.sphinx
    python3Packages.myst-parser
    python3Packages.sphinx-rtd-theme
    ocaml
    dune_3
    ocaml-lsp
    ocp-indent
    dune-site
    crunch
    # The version in NixOS 26.05 is insecure (CVE-2026-87732)
    # dune-release
  ];

  buildInputs = [ pkgs.nodejs ] ++ (with ocamlPackages; [
    ocplib-simplex
    bos
    dolmen_loop
    camlzip
    psmt2-frontend
    stdlib-shims
    menhir
    dune-build-info
    js_of_ocaml-ppx
    js_of_ocaml-lwt
    lwt_ppx
    data-encoding
    zarith_stubs_js
    cmdliner_2
    odoc
    qcheck
    utop
    opam-ed
  ]);
}

{ pkgs ? import ./nix { } }:

let
  inherit (pkgs) lib python3Packages ocamlPackages;
in

pkgs.mkShell {
  nativeBuildInputs = with ocamlPackages; [
    pkgs.ocamlformat
    pkgs.sphinx
    python3Packages.myst-parser
    python3Packages.sphinx-markdown-tables
    python3Packages.sphinx-rtd-theme
    ocaml
    dune_3
    ocaml-lsp
    ocp-indent
    dune-release
    dune-site
  ];

  buildInputs = with ocamlPackages; [
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
    cmdliner
    ppx_blob
    odoc
  ];
}

{ sources ? import ./nix/sources.nix
, pkgs ? import ./nix { inherit sources; }
}:

let
  inherit (pkgs) lib ocamlPackages;
  version = "dev";
  src = lib.cleanSource ./.;
  alt-ergo-lib = ocamlPackages.buildDunePackage rec {
    pname = "alt-ergo-lib";
    inherit version src;

    minimalOCamlVersion = "4.08";
    duneVersion = "3";

    propagatedBuildInputs = with ocamlPackages; [
      dune-build-info
      zarith
      ocplib-simplex
      seq
      stdlib-shims
      fmt
      ppx_blob
      dolmen_loop
      camlzip
      ppx_deriving
    ];
  };

  alt-ergo-parsers = ocamlPackages.buildDunePackage rec {
    pname = "alt-ergo-parsers";
    inherit version src;

    minimalOCamlVersion = "4.08";
    duneVersion = "3";

    nativeBuildInputs = [ ocamlPackages.menhir ];
    propagatedBuildInputs = [ alt-ergo-lib ] ++ (with ocamlPackages; [
      psmt2-frontend
    ]);
  };

  alt-ergo = ocamlPackages.buildDunePackage {
    pname = "alt-ergo";
    inherit version src;

    minimalOCamlVersion = "4.08";
    duneVersion = "3";

    buildInputs = [ alt-ergo-parsers ] ++ (with ocamlPackages; [
      cmdliner
      dune-site
    ]);
  };

in

{
  alt-ergo = alt-ergo;
}

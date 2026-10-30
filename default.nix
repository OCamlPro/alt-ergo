{ sources ? import ./nix/sources.nix
, useFlambda ? false
, pkgs ? import ./nix { inherit sources; }
}:

let
  inherit (pkgs) lib;
  ocamlPackages =
    if useFlambda
    then pkgs.ocamlPackages.overrideScope (self: super: {
      ocaml = super.ocaml.override { flambdaSupport = true; };
    })
    else pkgs.ocamlPackages;
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
      dolmen_loop
      camlzip
    ];
  };

  alt-ergo = ocamlPackages.buildDunePackage {
    pname = "alt-ergo";
    inherit version src;

    minimalOCamlVersion = "4.08";
    duneVersion = "3";

    buildInputs = (with ocamlPackages; [
      alt-ergo-lib
      cmdliner
      dune-site
    ]);
  };

in

{
  alt-ergo = alt-ergo;
}

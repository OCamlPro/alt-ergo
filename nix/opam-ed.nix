{ sources, lib, ocamlPackages, cmdliner_2, opam-file-format }:

let
  opam-ed = sources.opam-ed;
in

ocamlPackages.buildDunePackage {
  strictDeps = true;
  pname = "opam-ed";
  inherit (opam-ed) version;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  propagatedBuildInputs = with ocamlPackages; [
    cmdliner_2
    opam-file-format
  ];

  src = opam-ed;

  meta = with lib; {
    inherit (opam-ed) homepage description;
  };
}

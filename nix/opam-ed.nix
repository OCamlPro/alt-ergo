{ sources, lib, buildDunePackage, cmdliner, opam-file-format }:

let
  opam-ed = sources.opam-ed;
in

buildDunePackage {
  strictDeps = true;
  pname = "opam-ed";
  inherit (opam-ed) version;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  propagatedBuildInputs = [
    cmdliner
    opam-file-format
  ];

  src = opam-ed;

  meta = with lib; {
    inherit (opam-ed) homepage description;
  };
}

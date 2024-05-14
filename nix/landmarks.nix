{ sources, lib, ocamlPackages }:

let
  landmarks = sources.landmarks;
in

ocamlPackages.buildDunePackage {
  strictDeps = true;
  pname = "landmarks";
  inherit (landmarks) version;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  src = landmarks;

  meta = with lib; {
    inherit (landmarks) homepage description;
  };
}

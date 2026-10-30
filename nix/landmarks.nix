{ sources, lib, buildDunePackage }:

let
  landmarks = sources.landmarks;
in

buildDunePackage {
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

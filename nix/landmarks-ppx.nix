{ sources, lib, buildDunePackage, landmarks, ppxlib }:

buildDunePackage {
  pname = "landmarks-ppx";
  inherit (landmarks) version src strictDeps;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  propagatedBuildInputs = [
    landmarks
    ppxlib
  ];

  meta = landmarks.meta;
}

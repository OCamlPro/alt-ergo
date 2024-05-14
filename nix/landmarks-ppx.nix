{ sources, lib, ocamlPackages }:

ocamlPackages.buildDunePackage {
  pname = "landmarks-ppx";
  inherit (ocamlPackages.landmarks) version src strictDeps;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  propagatedBuildInputs = [
    ocamlPackages.landmarks
    ocamlPackages.ppxlib
  ];

  meta = ocamlPackages.landmarks.meta;
}

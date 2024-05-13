{ sources, lib, ocamlPackages }:

ocamlPackages.buildDunePackage {
  pname = "dolmen_type";
  inherit (ocamlPackages.dolmen) version src strictDeps;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  propagatedBuildInputs = [
    ocamlPackages.dolmen
    ocamlPackages.pp_loc
    ocamlPackages.spelll
    ocamlPackages.uutf
  ];

  meta = ocamlPackages.dolmen.meta;
}

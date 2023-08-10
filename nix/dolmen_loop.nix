{ sources, lib, ocamlPackages }:

ocamlPackages.buildDunePackage {
  pname = "dolmen_loop";
  inherit (ocamlPackages.dolmen) version src strictDeps;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  propagatedBuildInputs = [ ocamlPackages.gen ocamlPackages.dolmen_type ];

  meta = ocamlPackages.dolmen.meta;
}

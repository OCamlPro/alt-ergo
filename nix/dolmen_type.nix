{ sources, lib, buildDunePackage, dolmen
, pp_loc, spelll, uutf }:

buildDunePackage {
  pname = "dolmen_type";
  inherit (dolmen) version src strictDeps;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  propagatedBuildInputs = [
    dolmen
    pp_loc
    spelll
    uutf
  ];

  meta = dolmen.meta;
}

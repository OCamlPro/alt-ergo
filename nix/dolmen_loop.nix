{ sources, lib, buildDunePackage
, gen, zarith, dolmen, dolmen_type }:

buildDunePackage {
  pname = "dolmen_loop";
  inherit (dolmen) version src strictDeps;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  propagatedBuildInputs = [ gen dolmen_type zarith ];

  meta = dolmen.meta;
}

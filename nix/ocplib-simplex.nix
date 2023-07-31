{ sources, lib, ocamlPackages }:

ocamlPackages.buildDunePackage {
  strictDeps = true;
  pname = "ocplib-simplex";
  inherit (sources.ocplib-simplex) version;

  minimalOCamlVersion = "4.02";
  duneVersion = "3";

  src = sources.ocplib-simplex;

  propagatedBuildInputs = [ ocamlPackages.num ocamlPackages.logs ];

  meta = with lib; {
    inherit (sources.ocplib-simplex) homepage description;
  };
}

{ sources, lib, buildDunePackage, num, logs }:

buildDunePackage {
  strictDeps = true;
  pname = "ocplib-simplex";
  inherit (sources.ocplib-simplex) version;

  minimalOCamlVersion = "4.02";
  duneVersion = "3";

  src = sources.ocplib-simplex;

  propagatedBuildInputs = [ num logs ];

  meta = with lib; {
    inherit (sources.ocplib-simplex) homepage description;
  };
}

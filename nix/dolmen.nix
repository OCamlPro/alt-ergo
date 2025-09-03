{ sources, lib, buildDunePackage
, menhir, hmap, menhirLib, fmt, uutf, dune-site }:

buildDunePackage {
  strictDeps = true;
  pname = "dolmen";
  inherit (sources.dolmen) version;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  src = sources.dolmen;

  nativeBuildInputs = [ menhir ];
  propagatedBuildInputs = [ hmap menhirLib fmt uutf dune-site ];

  meta = with lib; {
    inherit (sources.dolmen) homepage description;
  };
}

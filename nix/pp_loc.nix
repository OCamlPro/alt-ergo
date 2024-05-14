{ sources, lib, ocamlPackages }:

ocamlPackages.buildDunePackage {
  strictDeps = true;
  pname = "pp_loc";
  inherit (sources.pp_loc) version;

  src = sources.pp_loc;

  meta = with lib; {
    inherit (sources.pp_loc) homepage description;
  };
}

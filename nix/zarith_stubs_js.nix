{ sources, lib, buildDunePackage }:

let
  zarith_stubs_js = sources.zarith_stubs_js;
in

buildDunePackage {
  strictDeps = true;
  pname = "zarith_stubs_js";
  inherit (zarith_stubs_js) version;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  src = zarith_stubs_js;
}

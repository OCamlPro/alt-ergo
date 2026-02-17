{ buildDunePackage,
  dolmen,
  dolmen_loop,
  zarith,
  farith
}:

buildDunePackage {
  pname = "dolmen_model";
  inherit (dolmen) version src strictDeps;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  propagatedBuildInputs = [
    dolmen
    dolmen_loop
    zarith
    farith
  ];

  meta = dolmen.meta;
}

{ buildDunePackage,
  dolmen,
  dolmen_type,
  dolmen_loop,
  dolmen_model,
  fmt,
  cmdliner
}:

buildDunePackage {
  pname = "dolmen_bin";
  inherit (dolmen) version src strictDeps;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  propagatedBuildInputs = [
    dolmen
    dolmen_type
    dolmen_loop
    dolmen_model
    fmt
    cmdliner
  ];

  meta = dolmen.meta;
}

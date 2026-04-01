{ sources ? import ./sources.nix }:

import sources.nixpkgs {
  overlays = [
    (_: pkgs: { inherit sources; })
    (_: pkgs: {
      ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14.overrideScope (self: super: {
        pp_loc = pkgs.callPackage ./pp_loc.nix { };
        ocplib-simplex = pkgs.callPackage ./ocplib-simplex.nix { };
        dolmen = pkgs.callPackage ./dolmen.nix { };
        dolmen_type = pkgs.callPackage ./dolmen_type.nix { };
        dolmen_loop = pkgs.callPackage ./dolmen_loop.nix { };
        landmarks = pkgs.callPackage ./landmarks.nix { };
        landmarks-ppx = pkgs.callPackage ./landmarks-ppx.nix { };
        cmdliner_2 = super.cmdliner.overrideAttrs (_: rec {
          version = "2.1.0";
          src = pkgs.fetchurl {
            url = "https://erratique.ch/software/cmdliner/releases/cmdliner-${version}.tbz";
            hash = "sha256-iBTGFM1D1S/R68ivWjHZElwhTEmPpgVmDk7Rlf+ENOk=";
          };
        });
      });
    })
  ];
}

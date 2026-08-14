{ sources ? import ./sources.nix }:

import sources.nixpkgs {
  overlays = [
    (_: pkgs: { inherit sources; })
    (_: pkgs: {
      ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14.overrideScope (self: super: {
        pp_loc = self.callPackage ./pp_loc.nix { };
        ocplib-simplex = self.callPackage ./ocplib-simplex.nix { };
        dolmen = self.callPackage ./dolmen.nix { };
        dolmen_type = self.callPackage ./dolmen_type.nix { };
        dolmen_loop = self.callPackage ./dolmen_loop.nix { };
        landmarks = self.callPackage ./landmarks.nix { };
        landmarks-ppx = self.callPackage ./landmarks-ppx.nix { };
        cmdliner_2 = self.cmdliner.overrideAttrs (_: rec {
          version = "2.1.0";
          src = pkgs.fetchurl {
            url = "https://erratique.ch/software/cmdliner/releases/cmdliner-${version}.tbz";
            hash = "sha256-iBTGFM1D1S/R68ivWjHZElwhTEmPpgVmDk7Rlf+ENOk=";
          };
        });
        zarith_stubs_js = self.callPackage ./zarith_stubs_js.nix { };
        opam-ed = self.callPackage ./opam-ed.nix { };
      });
    })
  ];
}

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
        dolmen_model = self.callPackage ./dolmen_model.nix { };
        dolmen_bin = self.callPackage ./dolmen_bin.nix { };
        landmarks = self.callPackage ./landmarks.nix { };
        landmarks-ppx = self.callPackage ./landmarks-ppx.nix { };
        zarith_stubs_js = self.callPackage ./zarith_stubs_js.nix { };
      });
    })
  ];
}

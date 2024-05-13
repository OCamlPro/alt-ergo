{ sources ? import ./sources.nix }:

import sources.nixpkgs {
  overlays = [
    (_: pkgs: { inherit sources; })
    (_: pkgs: {
      ocamlPackages = pkgs.ocamlPackages.overrideScope' (self: super: {
        pp_loc = pkgs.callPackage ./pp_loc.nix { };
        ocplib-simplex = pkgs.callPackage ./ocplib-simplex.nix { };
        dolmen = pkgs.callPackage ./dolmen.nix { };
        dolmen_type = pkgs.callPackage ./dolmen_type.nix { };
        dolmen_loop = pkgs.callPackage ./dolmen_loop.nix { };
      });
    })
  ];
}

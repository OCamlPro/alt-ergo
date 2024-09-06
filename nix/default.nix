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
        zarith_stubs_js = pkgs.callPackage ./zarith_stubs_js.nix { };
      });
    })
  ];
}

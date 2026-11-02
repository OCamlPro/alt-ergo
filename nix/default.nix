{ sources ? import ./sources.nix }:

import sources.nixpkgs {
  overlays = [
    (_: pkgs: { inherit sources; })
    (final: pkgs:
      let
        # Additional packages we need, for all OCaml versions.
        ocamlOverrides = self: super: {
          pp_loc = self.callPackage ./pp_loc.nix { };
          ocplib-simplex = self.callPackage ./ocplib-simplex.nix { };
          dolmen = self.callPackage ./dolmen.nix { };
          dolmen_type = self.callPackage ./dolmen_type.nix { };
          dolmen_loop = self.callPackage ./dolmen_loop.nix { };
          landmarks = self.callPackage ./landmarks.nix { };
          landmarks-ppx = self.callPackage ./landmarks-ppx.nix { };
          zarith_stubs_js = self.callPackage ./zarith_stubs_js.nix { };
          opam-ed = self.callPackage ./opam-ed.nix { };
        };
      in
      {
        ocaml-ng = pkgs.lib.mapAttrs
          (name: ocamlPackages:
            if pkgs.lib.hasPrefix "ocamlPackages_" name
            then ocamlPackages.overrideScope ocamlOverrides
            else ocamlPackages)
          pkgs.ocaml-ng;
      })
  ];
}

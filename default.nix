{ sources ? import ./nix/sources.nix
, linkMode ? "dynamic"
, useFlambda ? false
, ocamlVersion ? "4.14"
, pkgs ? import ./nix { inherit sources; }
}:

assert builtins.elem linkMode [ "dynamic" "static" "mixed" ];

let
  inherit (pkgs) lib;
  ocamlPackages =
    let
      ocamlPackages = pkgs.ocaml-ng."ocamlPackages_${
        builtins.replaceStrings [ "." ] [ "_" ] ocamlVersion}";
    in
    if useFlambda
    then ocamlPackages.overrideScope (self: super: {
      ocaml = super.ocaml.override { flambdaSupport = true; };
    })
    else ocamlPackages;
  version = "dev";
  src = lib.cleanSource ./.;
  alt-ergo-lib = ocamlPackages.buildDunePackage rec {
    pname = "alt-ergo-lib";
    inherit version src;

    minimalOCamlVersion = "4.08";
    duneVersion = "3";

    nativeBuildInputs = [ ocamlPackages.crunch ];

    propagatedBuildInputs = with ocamlPackages; [
      dune-build-info
      zarith
      ocplib-simplex
      seq
      stdlib-shims
      fmt
      dolmen_loop
      camlzip
    ];
  };

  alt-ergo = ocamlPackages.buildDunePackage ({
    pname = "alt-ergo";
    inherit version src;

    minimalOCamlVersion = "4.08";
    duneVersion = "3";

    LINK_MODE = linkMode;

    buildInputs = (with ocamlPackages; [
      alt-ergo-lib
      cmdliner
      dune-site
    ]) ++ lib.optionals (linkMode != "dynamic") [
      # Static versions of the C libraries.
      (pkgs.gmp.override { withStatic = true; })
      pkgs.zlib.static
    ] ++ lib.optionals (linkMode == "static") [
      # The regular glibc must come first, so that only the -static link of
      # alt-ergo picks libc.a (build tools are linked dynamically).
      pkgs.stdenv.cc.libc
      pkgs.glibc.static
    ];
  } // lib.optionalAttrs (linkMode != "dynamic") {
    # Distributed executables must look for plugins as a relative path (note
    # that dune install --relocatable needs a relative prefix to work)
    installPhase = ''
      runHook preInstall
      dune install --prefix _install --relocatable alt-ergo
      mv _install $out
      runHook postInstall
    '';

    postInstall = ''
      find $out/lib -name '*.cmt' -delete -o -name '*.cmti' -delete
    '';

    # Use the system's dynamic loader and libc in mixed mode. Also remove all
    # references to the nix store.
    nativeBuildInputs = [ pkgs.nukeReferences ];
    postFixup = lib.optionalString (linkMode == "mixed") ''
      patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 --remove-rpath \
        $out/bin/alt-ergo
    '' + ''
      find $out/lib -name '*.cmxs' -exec patchelf --remove-rpath {} +
      find $out -type f -exec nuke-refs {} +
    '';

    # Make sure no references to the nix store remain
    allowedReferences = [ ];
  } // lib.optionalAttrs (linkMode == "static") {
    # Statically linked alt-ergo can't load these
    postPatch = ''
      rm -r src/plugins/fm-simplex
    '';
  });

in

{
  alt-ergo = alt-ergo;
}

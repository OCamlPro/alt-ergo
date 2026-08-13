#!/usr/bin/env bash
set -e

forbidden_fields=(
  "\"ocaml\""
  "\"ocaml-base-compiler\""
  "\"ocaml-system\""
  "\"ocaml-config\""
  "\"ocaml-variants\""
  "\"ocaml-compiler\""
  "\"ocaml-compiler-libs\""
  "\"ocaml-options-vanilla\""
  "\"base-domains\""
  "\"base-effects\""
  "\"base-nnp\""
  "\"ocamlfind\""
  "\"host"
)

read input || true

for key in "${forbidden_fields[@]}"
do
  if [[ "$input" =~ "$key" ]] then
    exit 1
  fi
done

exit 0

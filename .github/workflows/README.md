# Github Actions Workflows

## Linter workflow (On push)

- check-indentation
- check-style

## Documentation workflow

- build ocaml documentation (push,blocking)
  upload the builded documentation as artifact
  - build sphinx documentation (pr, blocking)
    upload the builded documentation as artifact
    - deploy doc on gh-pages (pushed on `next`)

## Make workflow

- build the project using `make` (push,blocking)
  check diff in opam files (can change after `make` if dune-project changed)
  - build opam packages using dune release profile (pr)
  - install opam packages using `make install*` rules (pr)

## Ubuntu workflow

- install with opam (push,blocking)
  - run non-regression tests (push,blocking)
    - install all supported ocaml versions (pr,blocking)
      - run non-regression tests on all supported ocaml versions (pr)
    - upload the alt-ergo binary (pushed on `next`/`main`)

## MacOS workflow (pushed on `next`/`main`)

- install with opam
  - run non-regression tests
  - upload the alt-ergo binary

## Windows workflow (pushed on `next`/`main`)

- install with opam
  - run non-regression tests
  - upload the alt-ergo binary

## Docker workflow (pushed on `next`/`main`)
- use specific ocp docker container
- install with opam

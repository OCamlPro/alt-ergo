FROM ocamlpro/ocaml:4.14

USER ocaml

RUN sudo apk add zlib-static

COPY . .

RUN sudo chmod a+wx .

RUN opam switch create . ocaml-system --locked --deps-only --ignore-constraints-on alt-ergo-lib,alt-ergo-parsers

RUN opam exec -- dune subst

RUN LINK_MODE=static opam exec -- dune build --release src/bin/text/Main_text.exe

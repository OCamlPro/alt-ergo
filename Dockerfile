FROM quay.io/pypa/manylinux_2_28_x86_64 AS compilation

# Enable Devel repo (for gmp-static)
RUN dnf -y install almalinux-release-devel

# Install config-manager command (for enabling PowerTools repo)
RUN dnf -y install 'dnf-command(config-manager)'

# Enable PowerTools repo (for zlib-static)
RUN dnf config-manager --set-enabled powertools

RUN dnf -y install gmp-static zlib-static make patch unzip

ADD https://github.com/ocaml/opam/releases/download/2.2.0-beta1/opam-2.2.0-beta1-x86_64-linux /bin/opam

RUN chmod +x /bin/opam

RUN opam init -a --bare --disable-sandboxing

COPY . /src/alt-ergo

WORKDIR /src/alt-ergo

ENV OPAMYES 1
ENV OPAMDEPEXTYES 1
ENV OPAMCONFIRMLEVEL unsafe-yes
ENV OPAMERRLOGLEN 0

RUN opam switch create . 4.14.1 --locked --deps-only --ignore-constraints-on alt-ergo-lib,alt-ergo-parsers

RUN opam exec -- dune subst

RUN LINK_MODE=mixed opam exec -- dune build --release src/bin/text/Main_text.exe

FROM scratch AS alt-ergo
COPY --from=compilation /src/alt-ergo/src/bin/text/Main_text.exe /bin/alt-ergo
ENTRYPOINT [ "/bin/alt-ergo" ]

# FROM ocamlpro/ocaml:4.14 AS compilation
#
# USER ocaml
#
# RUN sudo apk add zlib-static
#
# COPY --chown=ocaml:ocaml . /src/alt-ergo
#
# WORKDIR /src/alt-ergo
#
# RUN opam switch create . ocaml-system --locked --deps-only --ignore-constraints-on alt-ergo-lib,alt-ergo-parsers
#
# RUN opam exec -- dune subst
#
# RUN LINK_MODE=static opam exec -- dune build --release src/bin/text/Main_text.exe
#
# FROM scratch AS alt-ergo
# COPY --from=compilation /src/alt-ergo/src/bin/text/Main_text.exe /bin/alt-ergo
# ENTRYPOINT [ "/bin/alt-ergo" ]

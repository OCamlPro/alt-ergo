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

RUN LINK_MODE=mixed opam exec -- dune build --release @install

RUN opam exec -- dune install --relocatable --prefix /opt/alt-ergo/

FROM scratch AS alt-ergo
COPY --from=compilation /opt/alt-ergo/ /opt/alt-ergo/
ENTRYPOINT [ "/opt/alt-ergo/bin/alt-ergo" ]

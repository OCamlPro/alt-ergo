# Licensing

The files of this directory are derived from Why3 and are distributed under
the terms of the GNU Lesser General Public License version 2.1, with the
special exception on linking described in `WHY3-LICENSE`, not under the license
of Alt-Ergo.

- `smt-lib-fpa.ae` is a translation of the `GenericFloat` module of Why3's
  standard library (`stdlib/ieee_float.mlw`, at commit
  [d0a8072e](https://gitlab.inria.fr/why3/why3/-/blob/d0a8072e157935d0d80a7a2156ecf5a98a2aae3e/stdlib/ieee_float.mlw#L34-826)),
  modified by OCamlPro in 2026 (the changes are listed in its header).

`WHY3-LICENSE` is the `LICENSE` file of Why3, which the Why3 headers refer to.

For this reason, `smt-lib-fpa.ae` is not embedded in the Alt-Ergo binary, but
installed separately along with `WHY3-LICENSE` by the opam package
`alt-ergo-smt-float-plugin` (an optional dependency of `alt-ergo`), to be
loaded by `--enable-theory smt.float`.

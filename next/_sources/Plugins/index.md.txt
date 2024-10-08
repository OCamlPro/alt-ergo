# Plugins

Alt-Ergo releases on OPAM support dynamically loading plugins. The command
`alt-ergo --where plugins` can be used to get the absolute path that is
searched by default when looking for plugins.

Binary releases on GitHub use static linking for portability, and hence do not
support plugins.

## Inequality plugins

The `fm-simplex` inequality plugin comes built-in with Alt-Ergo and no further
installation is required. It is distributed under the same licensing conditions
as Alt-Ergo. It can be used as follows:

```console
$ alt-ergo --inequalities-plugin fm-simplex [other-options] file.<ext>
```

```{note}
If you are a developer of an external inequality plugin, your plugin needs to
be registered in the `(alt-ergo plugins)` site using
[dune-site](https://dune.readthedocs.io/en/stable/reference/dune/plugin.html)
to be available as an option to `--inequalities-plugin`.
```

```{toctree}
:maxdepth: 2

AB why3 <ab_why3>
```

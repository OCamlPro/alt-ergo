% Alt-Ergo documentation master file

# Welcome to Alt-Ergo's documentation!

[Alt-Ergo](https://alt-ergo.ocamlpro.com) is an open-source automatic solver of mathematical formulas designed for program verification. It is based on [Satisfiability Modulo Theories](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) (SMT). Solvers of this family have made impressive advances and became very popular during the last decade. They are now used is various domains such as hardware design, software verification and formal testing.

It was developed at [LRI](https://www.lri.fr), and is now improved and maintained at [OCamlPro](https://www.ocamlpro.com), and friendly collaboration is maintained with the [Why3](http://why3.lri.fr/) development team.

You can [try Alt-Ergo](https://alt-ergo.ocamlpro.com/try.html) online.
You can also learn more about our partners with the [Alt-Ergo Users' Club](https://alt-ergo.ocamlpro.com/#club).

If you are using Alt-Ergo as a library, see the [API documentation](API/index) (also available [on ocaml.org](https://ocaml.org/p/alt-ergo-lib/latest/doc/index.html)).

## Input file formats

Alt-ergo supports different input languages:

- Alt-ergo supports the SMT-LIB language v2.6. **This is Alt-Ergo's preferred
  and recommended input format.**
- The original input language is its native language, based on the language of the Why3 platform. Since the version 2.6.0, this language is deprecated.
- It also (partially) supports the input language of Why3 through the [AB-Why3 plugin](../Plugins/ab_why3).

```{toctree}
:caption: Contents
:maxdepth: 2

Install                    <Install/index>
Usage                      <Usage/index>
SMT-LIB language           <SMT-LIB_language/index>
Alt-Ergo's native language <Alt_ergo_native/index>
Model generation           <Model_generation>
Optimization               <Optimization>
API documentation          <API/index>
Plugins                    <Plugins/index>
Developer's documentation  <Dev/index>
About                      <About/index>
```

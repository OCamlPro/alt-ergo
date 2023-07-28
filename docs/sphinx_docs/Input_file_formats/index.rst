
******************
Input file formats
******************

Alt-ergo supports different input languages:

- The original input language is its native language, based on the language of the Why3 platform and
  detailed below.
- Alt-ergo supports the SMT-LIB language v2.6. Since version 2.5.0, improved support
  is provided by the `Dolmen <https://github.com/Gbury/dolmen>`_ frontend, available with
  the ``--frontend dolmen`` option.
- It also (partially) supports the input language of Why3 through the :doc:`AB-Why3 plugin <../Plugins/ab_why3>`.

.. toctree::
   :maxdepth: 2
   :caption: Contents

   Alt-Ergo's native language  <Native/index>
   SMT-LIB 2                   <SMT-LIB2/index>

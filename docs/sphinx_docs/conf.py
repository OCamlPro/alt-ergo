# Configuration file for the Sphinx documentation builder.
#
# This file only contains a selection of the most common options. For a full
# list see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.

import os
import sys
sys.path.insert(0, os.path.abspath('.'))


# -- Project information -----------------------------------------------------

project = 'Alt-Ergo'
copyright = '2020 - 2023, Alt-Ergo developers'
author = 'Alt-Ergo developers'

# -- Custom lexer ------------------------------------------------------------

# Import our custom lexer
from alt_ergo_lexer import AltErgoLexer
from smt_lib_lexer import Smt2Lexer
from sphinx.highlighting import lexers
lexers['alt-ergo'] = AltErgoLexer()
lexers['smt-lib'] = Smt2Lexer()

# Use alt-ergo as the default language
highlight_language = 'alt-ergo'

# -- Entry point -------------------------------------------------------------

master_doc = 'index'

# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = ['myst_parser']

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = ['Alt_ergo_native/TODOs.md']

# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = 'furo'

# -- Options for MyST markdown parser ----------------------------------------

myst_heading_anchors = 3

html_show_sourcelink = False

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static']

# -- Context population (version management and more) ------------------------

html_css_files = ['css/versions.css']
html_js_files = ['js/versions.js']

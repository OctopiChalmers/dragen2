#!/bin/sh

#https://facebook.github.io/watchman/docs/watchman-make.html
watchman-make --make 'make' -p 'main.lhs.tex' 'notation.fmt' 'sections/[^.]*.tex' 'tikz/[^.]*.tex' '**/[^.]*.bib' '**/GNUmakefile' -t all

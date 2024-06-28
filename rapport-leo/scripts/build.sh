#!/usr/bin/env sh

set -eu

( cd "$(dirname "$0")"/../src

  c="texfot xelatex -shell-escape -halt-on-error"

  $c main.tex | sed '/Output written/d' | sed '/Rerun to get \/Page/d' | sed '/Warning: Citation/d' | sed '/Warning: Empty bib/d' | sed '/has changed/d' | sed '/Warning: There were/d' | sed '/biblatex Warning/d'
  biber -quiet main
  $c main.tex | sed '/Output written/d' | sed '/Warning: There were/d' | sed '/biblatex Warning/d'
  $c main.tex
  mv main.pdf ../main.pdf
) | sed '/This is/d' | sed '/texfot: invoking/d'

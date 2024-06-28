#!/usr/bin/env sh

set -eu

( cd "$(dirname "$0")"/../src/

  rm -f ./*.log ./*.tuc ./*.out ./*.aux ./*.toc ./*.pyg ./*.bbl ./*.bcf ./*.blg ./*.run.xml
  rm -rf ./svg-inkscape/

)

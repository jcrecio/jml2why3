#!/usr/bin/env sh

set -eu

(
  cd "$(dirname "$0")"/../

  # Testing scripts
  # shellcheck disable=SC2185
  find -O3 . -type f -name '*.sh' -exec shellcheck {} \;
  cd src/
  # shellcheck disable=SC2185
  find -O3 . -type f -name '*.tex' -exec chktex -q --nowarn 26 --nowarn 15 --nowarn 17 {} \;
  # shellcheck disable=SC2185
  find -O3 . -type f -name '*.tex' -exec lacheck {} \; # TODO: fix lacheck so it's possible to disable some warnings which are incorrects...
)

#!/bin/sh

set -eu

_build/default/get_oa.exe $1 > oa_orig.csv
cat oa_orig.csv | _build/default/given_input.exe $(_build/default/get_taux.exe $1) > oa_res.csv
cmp oa_orig.csv oa_res.csv

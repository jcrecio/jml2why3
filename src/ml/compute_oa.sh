#!/bin/sh

set -eu

_build/default/get_oa.exe $1 | _build/default/given_input.exe $( _build/default/get_taux.exe $1 )

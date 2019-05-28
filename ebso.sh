#!/bin/bash
Z3DIR=$(ocamlfind query z3)

EBSODIR=$(dirname "$(realpath "$0")")
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$Z3DIR "$EBSODIR"/_build/default/main.exe "$@"

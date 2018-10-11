#!/bin/bash
Z3DIR=$(ocamlfind query z3)

LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$Z3DIR _build/default/ebso.exe "$@"

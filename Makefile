Z3DIR := $(shell ocamlfind query z3)

build :
	dune build @install

run : build
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./main.exe

test : build
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune runtest

test_% : build
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./test/$@.exe

clean :
	dune clean

.PHONY : build run test test_% utop clean

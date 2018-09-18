build :
	dune build ebso.exe

run : build
	_build/default/ebso.exe

test : build
	dune runtest

test_% : build
	dune exec ./test/$@.exe

clean :
	dune clean

.PHONY : build run test test_% utop clean

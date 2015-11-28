all:
	cabal configure
	cabal build
	gcc -m32 -g -c lib/runtime.c -o lib/runtime.o

clean:
	rm -rf dist
	rm lib/runtime.o

.PHONY: all clean

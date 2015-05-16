
.PHONY: all clean
all:
	ocamlopt -o main.native  nums.cmxa  unix.cmxa  big.ml test.mli test.ml main.ml
clean:
	rm  big.cmx big.o  main.cmx main.o test.cmi test.o big.cmi main.native main.cmi  test.cmx  

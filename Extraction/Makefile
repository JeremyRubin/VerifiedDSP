
MODULES := Extraction
# DFACorrectness FastVerifier i8051Lemmas VerifierCorrectness
VS 	:= $(MODULES:%=%.v)
.PHONY: all clean
all: main
	echo "Done Compiling"

Extraction.v: 
	echo "Add LoadPath \"../Connect\". Add LoadPath \"../Model\". Require Import Breadboard. Import BB. Extraction Language Ocaml. Extraction \"extracted.ml\"  BB." > Extraction.v



extracted.ml: Extraction.v Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS:%=%) 
	coq_makefile $(VS) -o Makefile.coq



extracted.mli: extracted.ml
	echo "Extraction Done"
extracted: extracted.mli extracted.ml
	echo ""

main: extracted.ml extracted.mli
	corebuild -lib nums main.native
	# ocamlopt -o main.native  nums.cmxa  unix.cmxa  big.ml extracted.mli extracted.ml main.ml

clean:
	rm Makefile.coq
	rm Extraction.{v,glob,v.d,vo}
	rm extracted.ml extracted.mli
	rm  -r _build
	rm main.native

MODULES := Coqlib Tacs Maps Bits i8051Syntax Monad Parser Decode RTL i8051Semantics CheckDeterministic Hex
# DFACorrectness FastVerifier i8051Lemmas VerifierCorrectness
VS 	:= $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

hex:
	python HexGen.py > Hex.v
Makefile.coq: Makefile $(VS:%=%) 
	echo $(VS)
	coq_makefile $(VS) -o Makefile.coq



clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

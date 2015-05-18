
#(**
    #VerifiedDSP
    #Copyright (C) {2015}  {Jeremy L Rubin}

    #This program is free software; you can redistribute it and/or modify
    #it under the terms of the GNU General Public License as published by
    #the Free Software Foundation; either version 2 of the License, or
    #(at your option) any later version.

    #This program is distributed in the hope that it will be useful,
    #but WITHOUT ANY WARRANTY; without even the implied warranty of
    #MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    #GNU General Public License for more details.

    #You should have received a copy of the GNU General Public License along
    #with this program; if not, write to the Free Software Foundation, Inc.,
    #51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

#**)
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

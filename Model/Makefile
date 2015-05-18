
#(**
#    VerifiedDSP
#    Copyright (C) {2015}  {Jeremy L Rubin}
#
#    This program is free software; you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation; either version 2 of the License, or
#    (at your option) any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License along
#    with this program; if not, write to the Free Software Foundation, Inc.,
#    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
#
#**)
MODULES := Coqlib Tacs Maps Bits i8051Syntax Monad Parser Decode RTL i8051Semantics CheckDeterministic Hex
# DFACorrectness FastVerifier i8051Lemmas VerifierCorrectness
VS 	:= $(MODULES:%=%.v)

.PHONY: coq clean 


coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Hex.v: HexGen.py
	python HexGen.py > Hex.v
Makefile.coq: Makefile $(VS:%=%) 
	coq_makefile $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend Hex.v

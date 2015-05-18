
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
.PHONY: model connect ctest extraction

all: model connect extraction ctest
	echo "Done Building"

model:
	cd Model && $(MAKE);


connect: model
	cd Connect && $(MAKE);



ctest:
	cd ctest && $(MAKE);

extraction: ctest connect model
	cd Extraction && $(MAKE);

clean:
	cd Connect && $(MAKE) clean
	cd Model && $(MAKE) clean
	cd Extraction && $(MAKE) clean
	cd ctest && $(MAKE) clean

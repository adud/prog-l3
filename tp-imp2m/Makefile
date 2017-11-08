#
#  This file is part of Imp2ML
#  Copyright (c) 2017 ENS Lyon / Département Informatique
#  Philippe Audebaud <paudebau at gmail dot com>
#
# This software falls under the GNU general public license version 3 or later.
# It comes WITHOUT ANY WARRANTY WHATSOEVER. For details, see the file LICENSE
# in the root directory or <http://www.gnu.org/licenses/gpl-3.0.html>.

NAME    = imp2ml
VERSION = 1
PACKS   = str

ROOT     = $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
TMPDIR  = $(HOME)/.cache/ocaml/$(NAME)
BUILDD  = -build-dir "$(TMPDIR)"               # implies -no-links
MENHIRC = menhir --comment --explain --infer   # menhir is Ocaml best friend
MENHIR  = -use-menhir -menhir "$(MENHIRC)"
OCFIND  = -use-ocamlfind -package "$(PACKS)"
TARGET  = src/main.byte
EXEC    = $(ROOT)$(NAME)
VERBOSE = -quiet                               # -classic-display # -verbose 7

all: main

main: tmpdir script
	@ocamlbuild $(VERBOSE) $(OCFIND) $(BUILDD) $(MENHIR) $(TARGET)
	@/bin/echo "command " $(EXEC) " ready!"

script:
	@/bin/echo -e "#!/bin/sh\n"$(TMPDIR)/$(TARGET)' $$@' > $(EXEC)
	@/bin/chmod 755 $(EXEC)

samples/%.ml: samples/%.imp all
	$(EXEC) -standalone $<

tmpdir:
	@/bin/mkdir -p "$(TMPDIR)"

clean:
	@ocamlbuild $(BUILDD) -clean
	@/bin/rm -f $(EXEC)

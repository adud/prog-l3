#
#  This file is part of Imp2ML
#  Copyright (c) 2017 ENS Lyon / Département Informatique
#  Philippe Audebaud <paudebau at gmail dot com>
#
# This software falls under the GNU general public license version 3 or later.
# It comes WITHOUT ANY WARRANTY WHATSOEVER. For details, see the file LICENSE
# in the root directory or <http://www.gnu.org/licenses/gpl-3.0.html>.

ROOT     = $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
LIBPATH  =
LIBS     = str
OCAMLOPT = /usr/bin/ocamlopt -dtypes $(LIBPATH)
OCAMLC   = /usr/bin/ocamlc -g -dtypes $(LIBPATH)

TARGET   = $(ROOT)../imp2ml
SRCML    = syntax.ml parser.ml lexer.ml interpretation.ml print.ml standalone.ml main.ml
SRCMLI   = syntax.mli interpretation.mli standalone.mli print.mli main.mli

$(TARGET): all
	$(OCAMLC) -o $(TARGET) $(LIBS:=.cma) $(SRCML:.ml=.cmo)

all: $(SRCMLI:.mli=.cmi) $(SRCML:.ml=.cmo)

lexer.ml: lexer.mll parser.cmi
	/usr/bin/ocamllex -q $<

parser.ml parser.mli: parser.mly
	/usr/bin/ocamlyacc $<

parser.cmo: parser.cmi
parser.cmi: parser.mli syntax.cmo

.PHONY: depend

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) -c $<

.mli.cmi:
	$(OCAMLC) -c $<

.ml.cmx:
	@$(OCAMLOPT) -c $<

clean::
	/bin/rm -f *.cm[iox] *.o *~ *.annot lexer.ml parser.ml parser.mli
	/bin/rm -f $(TARGET)

depend:
	/usr/bin/ocamldep $(LIBPATH) $(SRCML) parser.mli $(SRCMLI) > .depend

-include .depend

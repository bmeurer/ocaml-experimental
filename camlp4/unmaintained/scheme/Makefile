#########################################################################
#                                                                       #
#                            Objective Caml                             #
#                                                                       #
#                                Camlp4                                 #
#                                                                       #
#   Copyright 2004 Institut National de Recherche en Informatique et    #
#   en Automatique.  All rights reserved.  This file is distributed     #
#   under the terms of the Q Public License version 1.0.                #
#                                                                       #
#########################################################################
#
# Makefile for pa_lefteval
# M.Mauny
#

include ../../config/Makefile.cnf

OCAMLTOP=../../..
CAMLP4=../../camlp4/camlp4$(EXE)

OCAMLC=$(OCAMLTOP)/ocamlc$(EXE)
OCAMLOPT=$(OCAMLTOP)/ocamlopt$(EXE)

P4INCLUDES= -nolib -I ../../meta -I ../../etc
OCAMLINCLUDES= -nostdlib -I $(OCAMLTOP)/stdlib -I ../../camlp4 -I ../../lib -I ../../etc
OCAMLCFLAGS=-warn-error A $(OCAMLINCLUDES)

SCHSRC=pa_scheme.sc
SRC=pa_scheme.ml  pr_scheme.ml  pr_schp_main.ml
OBJS=$(SRC:.ml=.cmo)
OBJSX=$(OCAMLSRC:.ml=.cmx)

all: $(OBJS) pr_schemep.cmo camlp4sch$(EXE)

opt: all

bootstrap: camlp4sch$(EXE) save
	./camlp4sch$(EXE) ../../etc/q_phony.cmo ../../meta/pa_extend.cmo ../../etc/pr_r.cmo ../../etc/pr_extend.cmo ../../etc/pr_rp.cmo -impl pa_scheme.sc \
	  | sed -e 's/^;; \(.*\)$$/(* \1 *)/' -e 's/^; \(.*\)$$/(* \1 *)/' \
		-e 's/$$Id.*\$$/File generated by pretty print; do not edit!/' > pa_scheme.ml
	@if cmp -s pa_scheme.ml SAVED/pa_scheme.ml; then \
		echo 'pa_scheme.ml and SAVED/pa_scheme.ml are identical' ; \
	 else \
		echo '**** Note: pa_scheme.ml differs from SAVED/pa_scheme.ml'; \
	 fi

save:
	test -d SAVED || mkdir SAVED
	mkdir SAVED.$$$$ && mv SAVED pa_scheme.ml SAVED.$$$$ && mv SAVED.$$$$ SAVED

restore:
	mv SAVED SAVED.$$$$ && mv SAVED.$$$$/* . && rmdir SAVED.$$$$

depend:
	cp .depend .depend.bak
	> .depend
	for file in $(SRC); do \
	  $(CAMLP4) $(P4INCLUDES) `awk 'NR == 1 { ORS=" "; for (i=2; i < NF; i++) print $$i; } ' $$file` pr_depend.cmo $$i | \
	  sed -e 's| \.\./\.\./\.\.| $$(OCAMLTOP)|g' >> .depend; \
	done

clean:
	rm -f camlp4sch$(EXE) *.cm* *.$(O) *.bak .*.bak

camlp4sch: pa_scheme.cmo
	rm -f camlp4sch
	DIR=`pwd` && cd ../../camlp4 && $(MAKE) CAMLP4=$$DIR/camlp4sch CAMLP4M="-I $$DIR pa_scheme.cmo ../meta/pr_dump.cmo"

pr_schemep.cmo: pr_schp_main.cmo
	$(OCAMLC) ../../etc/parserify.cmo pr_schp_main.cmo -a -o $@

.SUFFIXES: .cmx .cmo .cmi .ml .mli

.mli.cmi:
	$(OCAMLC) $(OCAMLCFLAGS) -c $<


.ml.cmo:
	$(OCAMLC) $(OCAMLCFLAGS) -pp "$(CAMLP4) $(P4INCLUDES) `awk 'NR == 1 { ORS=" "; for (i=2; i < NF; i++) print $$i; } ' $<` -loc loc" -c $< 

.ml.cmx:
	$(OCAMLOPT) $(OCAMLCFLAGS) -pp "$(CAMLP4) $(P4INCLUDES)  `awk 'NR == 1 { ORS=" "; for (i=2; i < NF; i++) print $$i; } ' $<` -loc loc" -c $<

include .depend

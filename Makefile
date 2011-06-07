.PHONY: all clean allcoq coq.html coq.pdf

CoqMakeVars := COQDOC = "~/bin/coqdoc -s"

CLASSES := Functor Pointed
Vm := $(CLASSES:%=Classes/%)
Vs := $(Vm:%=%.v)

all: allcoq

Makefile.coq: Makefile $(Vs)
	coq_makefile $(CoqMakeVars) -R Classes Classes $(Vs) -o Makefile.coq

allcoq: Makefile.coq $(Vs)
	make -f Makefile.coq all

clean:
	-make -f Makefile.coq clean
	-rm Makefile.coq

coq.html: $(VS) Makefile.coq
	make -f Makefile.coq html
	cp coqdoc.css html/

coq.pdf: $(VS) Makefile.coq
	make -f  Makefile.coq all.pdf


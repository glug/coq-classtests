.PHONY: all clean allcoq coq.html coq.pdf

CoqMakeVars :=
	#COQDOC = "~/bin/coqdoc -s"

CLASSES := Cat Monoid Functor Pointed Applicative Monad
INSTANCES := Cont
Vm := $(CLASSES:%=Classes/%) $(INSTANCES:%=Instances/%)
Vs := $(Vm:%=%.v)

all: allcoq deps.png coq.html

Makefile.coq: Makefile $(Vs)
	coq_makefile $(CoqMakeVars) -R Classes Classes $(Vs) -o Makefile.coq

allcoq: Makefile.coq $(Vs)
	make -f Makefile.coq all

deps.png: deps.dot
	dot -Tpng deps.dot > deps.png

clean:
	-make -f Makefile.coq clean
	-rm Makefile.coq

coq.html: $(Vs) Makefile.coq
	make -f Makefile.coq html
	cp coqdoc.css html/

coq.pdf: $(Vs) Makefile.coq
	make -f  Makefile.coq all.pdf


.PHONY: all clean allcoq coq.html coq.pdf

CLASSES := Category
Vm := Init $(CLASSES:%=Classes/%)
Vs := $(Vm:%=%.v)

all: allcoq

Makefile.coq: Makefile $(Vs)
	coq_makefile $(Vs) -o Makefile.coq

allcoq: Makefile.coq $(Vs)
	make -f Makefile.coq all

clean:
	-make -f Makefile.coq clean
	-rm Makefile.coq

coq.html: $(VS) Makefile.coq
	make -f Makefile.coq html

coq.pdf: $(VS) Makefile.coq
	make -f  Makefile.coq all.pdf


OCAMLBUILD = ocamlbuild -use-ocamlfind -pkgs cryptokit,ipaddr -I Extraction/src -I Extraction/src/toychain

SRC_DIRS := 'coqtla/src' 'coqtla/external'
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")

all: default

default: Makefile.coq
	$(MAKE) -f Makefile.coq

node: default
	$(OCAMLBUILD) node.native

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -f Extraction/src/toychain/*.ml Extraction/src/toychain/*.mli
	$(OCAMLBUILD) -clean

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq $(ALL_VFILES)

.PHONY: all default quick install clean node

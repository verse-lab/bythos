SRC_DIRS := 'coqtla/src' 'coqtla/external/stdpp/stdpp' 'coqtla/external/coq-record-update'
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")

all: default extraction_core

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq clean_extraction
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

clean_extraction:
	cd Extraction/; rm -f extracted/*.ml extracted/*.mli; dune clean; cd ..

clean_driver:
	rm -f Extraction/Driver.vo

extraction: clean_driver extraction_core

extraction_core:
	$(MAKE) -f Makefile.coq Extraction/Driver.vo
	cd Extraction/; dune build; cd ..

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq $(ALL_VFILES)

.PHONY: all default quick install extraction_core extraction clean clean_driver clean_extraction

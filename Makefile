SRC_DIRS := 'coqtla/src' 'coqtla/external/stdpp/stdpp' 'coqtla/external/coq-record-update'
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")

all: default

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
	rm -f Extraction/extracted/*.ml Extraction/extracted/*.mli
	rm -rf Extraction/_build

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq $(ALL_VFILES)

.PHONY: all default quick install clean clean_extraction

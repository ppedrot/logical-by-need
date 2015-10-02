Makefile.coq: Make
	$(COQBIN)/coq_makefile -o Makefile.coq -f Make

-include Makefile.coq

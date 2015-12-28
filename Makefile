-include Makefile.coq
Makefile.coq: _CoqProject Makefile
	$(COQBIN)coq_makefile -f $< -o $@.new
	mv $@.new $@

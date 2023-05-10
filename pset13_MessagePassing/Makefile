.PHONY: coq clean

COQC=coqc -q -R ../frap Frap -R . Pset13

coq:
	$(COQC) ../frap/MessagesAndRefinement.v
	$(COQC) Pset13Sig.v
	$(COQC) Pset13.v

clean:
	rm -f *.vo *.vok *.vos *.glob

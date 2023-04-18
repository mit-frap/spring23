.PHONY: coq clean

COQC=coqc -q -R ../frap Frap -R . Pset10

coq:
	$(COQC) Pset10Sig.v
	$(COQC) Pset10.v

clean:
	rm -f *.vo *.vok *.vos *.glob

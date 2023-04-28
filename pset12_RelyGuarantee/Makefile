.PHONY: coq clean

COQC=coqc -q -R ../frap Frap -R . Pset12

coq:
	$(COQC) Pset12Sig.v
	$(COQC) Pset12Example.v
	$(COQC) Pset12.v

clean:
	rm -f *.vo *.vok *.vos *.glob

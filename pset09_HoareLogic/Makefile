.PHONY: coq clean

COQC=coqc -q -R ../frap Frap -R . Pset9

coq:
	$(COQC) Pset9Sig.v
	$(COQC) Pset9.v

clean:
	rm -f *.vo *.vok *.vos *.glob

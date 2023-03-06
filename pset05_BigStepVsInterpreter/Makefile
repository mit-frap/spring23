.PHONY: coq clean

COQC=coqc -q -R ../frap Frap -R . Pset5

coq:
	$(COQC) Pset5Sig.v
	$(COQC) Pset5.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .*.cache *.vok *.vos

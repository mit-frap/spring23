.PHONY: coq clean

COQC=coqc -q -R ../frap Frap -R . Pset6

coq:
	$(COQC) Pset6Sig.v
	$(COQC) Pset6.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .*.cache *.vok *.vos

.PHONY: coq clean

COQC=coqc -q -R ../frap Frap -R . Pset8

coq:
	$(COQC) Pset8Sig.v
	$(COQC) Pset8.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .lia.cache .nia.cache *.vok *.vos

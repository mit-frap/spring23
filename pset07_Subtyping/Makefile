.PHONY: coq clean

COQC=coqc -q -R ../frap Frap -R . Pset7

coq:
	$(COQC) Pset7Sig.v
	$(COQC) Pset7.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .lia.cache .nia.cache *.vok *.vos

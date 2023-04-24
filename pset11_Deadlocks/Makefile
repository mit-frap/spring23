.PHONY: coq clean

COQC=coqc -q -R ../frap Frap -R . Pset11

coq:
	$(COQC) Pset11Sig.v
	$(COQC) Pset11.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .lia.cache .nia.cache *.vok *.vos

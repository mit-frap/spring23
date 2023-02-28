.PHONY: coq clean

COQC=coqc -q -R ../frap Frap -R . Pset4

coq:
	$(COQC) Pset4Sig.v
	$(COQC) Pset4.v

clean:
	rm -f *.vo* .*.aux *.cache *.glob

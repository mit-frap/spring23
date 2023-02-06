.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset1Signature.v
	$(COQC) Pset1Implementation.v

clean:
	rm -f *.vo *.glob

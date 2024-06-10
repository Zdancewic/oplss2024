COQMFFLAGS := -Q . RIP  

ALLVFILES := OPLSS.v Preface.v Maps.v Imp.v ImpShort.v Hoare.v Introduction.v Monads.v Free.v ITrees.v ITreesEquiv.v ImpDenotation.v ImpEquiv.v Hoare3.v Further.v Utils.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean

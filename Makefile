GHC = ghc
GHCOPT = -fno-monomorphism-restriction # -prof -auto-all # -O
OHIDIR = .ofiles
ALICE = alice
MOSES = moses

.PHONY: $(ALICE) $(MOSES) clean

all: $(ALICE) $(MOSES)

$(ALICE):
	$(GHC) --make Alice/Main.hs -o $@ $(GHCOPT) -odir $(OHIDIR) -hidir $(OHIDIR)
	strip -s $@

#%:
#	$(GHC) --make $@ $(GHCOPT) -odir $(OHIDIR) -hidir $(OHIDIR)

$(MOSES):
	$(MAKE) -C $@

clean:
	rm -rf $(ALICE) $(OHIDIR)/*
	$(MAKE) -C $(MOSES) clean


### Compilers and flags ###

HC = ghc
HFLAGS = -fno-monomorphism-restriction # -prof -auto-all # -O

CC = gcc
CFLAGS = -Wall -O2 -finline-functions

### Targets ###

ALICE = alice
MOSES = provers/moses

ALICEDIR = Alice
MOSESDIR = moses
BUILDDIR = .build

all: $(ALICE) $(MOSES)

.PHONY: all $(ALICE) release binary clean depend

### Alice ###

$(ALICE):	$(BUILDDIR)
	$(HC) --make $(ALICEDIR)/Main.hs -o $@ $(HFLAGS) -odir $(BUILDDIR) -hidir $(BUILDDIR)
	strip -s $@

#%:
#	$(HC) --make $@ $(HFLAGS) -odir $(BUILDDIR) -hidir $(BUILDDIR)

### Moses ###

MOSESSRC = $(wildcard $(MOSESDIR)/*.c)
MOSESOBJ = $(addprefix $(BUILDDIR)/,$(MOSESSRC:.c=.o))

$(MOSES):	$(BUILDDIR)/$(MOSESDIR) $(MOSESOBJ)
	$(CC) -o $@ $(MOSESOBJ)

$(BUILDDIR)/$(MOSESDIR)/%.o:	$(MOSESDIR)/%.c
	$(CC) -o $@ $(CFLAGS) -c $<

### Create build directories ###

$(BUILDDIR):
	mkdir -p $@

$(BUILDDIR)/$(MOSESDIR):
	mkdir -p $@

### Release ###

RELNAME = sad-$(shell date +%y%m%d)
RELBIN  = $(RELNAME)-$(shell uname -m)

release:
	tar -czf $(RELNAME).tar.gz --transform='s=^=$(RELNAME)/=' \
	    Alice COPYING Makefile doc examples init.opt moses \
	    provers/provers.dat

binary: all
	tar -cjf $(RELBIN).tar.bz2 --transform='s=^=$(RELNAME)/=' \
	    Alice COPYING Makefile doc examples init.opt moses \
	    alice provers

### Janitory ###

clean:
	rm -rf $(ALICE) $(MOSES) $(BUILDDIR) core

depend:
	makedepend -Y -p $(BUILDDIR)/ -- $(CFLAGS) -- $(MOSESDIR)/*.c
	rm Makefile.bak

# DO NOT DELETE

.ofiles/moses/core.o: moses/core.h moses/env.h moses/main.h moses/term.h
.ofiles/moses/env.o: moses/env.h moses/main.h moses/term.h
.ofiles/moses/main.o: moses/main.h moses/core.h moses/env.h moses/term.h
.ofiles/moses/term.o: moses/env.h moses/main.h moses/term.h

### Compilers and flags ###

HC = ghc
HFLAGS = -O2 -XPolymorphicComponents

CC = gcc
CFLAGS = -Wall -O2 -finline-functions

STRIP = strip

### Targets ###

ALICE = alice
MOSES = provers/moses

ALICEDIR = Alice
MOSESDIR = moses
BUILDDIR = .build

BUILDOPT = -odir $(BUILDDIR) -hidir $(BUILDDIR)
PROFLOPT = -prof -auto-all -osuf p.o -hisuf p.hi $(BUILDOPT)
COVEROPT = -fhpc -osuf hpc.o -hisuf hpc.hi $(BUILDOPT)

all: $(ALICE) $(MOSES)
prof: $(ALICE).p
hpc: $(ALICE).hpc

.PHONY: all prof hpc $(ALICE) $(ALICE).p $(ALICE).hpc \
	source binary getall clean depend

### Alice ###

$(ALICE):	$(BUILDDIR)
	$(HC) --make $(ALICEDIR)/Main.hs -o $@ $(HFLAGS) $(BUILDOPT)
	$(if $(STRIP),$(STRIP) -s $@)

$(ALICE).p:	$(BUILDDIR)
	$(HC) --make $(ALICEDIR)/Main.hs -o $@ $(HFLAGS) $(PROFLOPT)
	$(if $(STRIP),$(STRIP) -s $@)

$(ALICE).hpc:	$(BUILDDIR)
	$(HC) --make $(ALICEDIR)/Main.hs -o $@ $(HFLAGS) $(COVEROPT)
	$(if $(STRIP),$(STRIP) -s $@)

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

### Janitory ###

clean:
	rm -rf $(ALICE) $(ALICE).p $(ALICE).hpc .hpc $(MOSES) $(BUILDDIR) core

depend:
	makedepend -Y -p $(BUILDDIR)/ -- $(CFLAGS) -- $(MOSESDIR)/*.c
	rm Makefile.bak

### Release ###

TAR = tar --transform='s=^=$(RELNAME)/='

RELNAME = sad-$(shell date +%y%m%d)
RELBIN  = $(RELNAME)-$(shell uname -m)

COMMON = $(SUBDIR) $(TOPDIR)
SUBDIR = Alice moses doc examples
TOPDIR = Makefile COPYING README init.opt
SOURCE = $(COMMON) provers/provers.dat
BINARY = $(SOURCE) alice provers/moses
GETALL = $(COMMON) alice provers

source:
	$(TAR) -czf $(RELNAME).tar.gz $(SOURCE)

binary: all
	$(TAR) -cjf $(RELBIN).tar.bz2 $(BINARY)

getall: all
	$(TAR) -cjf $(RELBIN).tar.bz2 $(GETALL)

# DO NOT DELETE

.ofiles/moses/core.o: moses/core.h moses/env.h moses/main.h moses/term.h
.ofiles/moses/env.o: moses/env.h moses/main.h moses/term.h
.ofiles/moses/main.o: moses/main.h moses/core.h moses/env.h moses/term.h
.ofiles/moses/term.o: moses/env.h moses/main.h moses/term.h

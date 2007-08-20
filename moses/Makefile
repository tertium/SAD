CC = gcc
CFLAGS = -Wall -O2 -finline-functions
OBJS = core.o env.o main.o term.o
TARGET = moses

$(TARGET):	$(OBJS)
	$(CC) -o $@ $(OBJS)

.PHONY: clean depend

clean:
	rm -f $(TARGET) $(OBJS) core

depend:
	makedepend -Y *.c 2>/dev/null
	rm Makefile.bak

# DO NOT DELETE

core.o: core.h env.h main.h term.h
env.o: env.h main.h term.h
main.o: main.h core.h env.h term.h
term.o: env.h main.h term.h

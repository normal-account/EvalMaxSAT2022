#-----------------------------------------------------------------------#
#- GLOBAL DEFS ---------------------------------------------------------#
#-----------------------------------------------------------------------#

# Keep this as generic as possible.

NAME=solver
VERSION=2022

#-----------------------------------------------------------------------#
# Solver signatures have to be both valid file names and C symbols.

SIG=$(NAME)$(VERSION)
TARGET=libipamir$(SIG).a

#-----------------------------------------------------------------------#

CC=g++
CFLAGS=-Wall -DNDEBUG -O3 -std=c++17

#-----------------------------------------------------------------------#
#- REQUIRED TOP RULES --------------------------------------------------#
#-----------------------------------------------------------------------#

all: $(TARGET)

clean:
	make -C ../../sat/$(IPASIRSOLVER) clean
	rm -rf pblib
	rm -f *.o *.a

#-----------------------------------------------------------------------#
#- INVISIBLE INTERNAL SUB RULES ----------------------------------------#
#-----------------------------------------------------------------------#

IPASIRSOLVER	?= minisat220
LIBS	=	-L../../sat/$(IPASIRSOLVER)/ -lipasir$(IPASIRSOLVER)
LIBS	+=	-Lpblib -lpblib
LIBS	+=	$(shell cat ../../sat/$(IPASIRSOLVER)/LIBS 2>/dev/null)
LINK	=	$(shell	if [ -f ../../sat/$(IPASIRSOLVER)/LINK ]; \
			then \
			  cat ../../sat/$(IPASIRSOLVER)/LINK; \
			else \
			  echo $(CC) $(CFLAGS); \
			fi)

pblib/libpblib.a:
	./buildPblib.sh

ipamir$(NAME)glue.o: ipamir$(NAME)glue.cc ipamir.h ipasir.h makefile pblib/libpblib.a
	$(CC) $(CFLAGS) -c ipamir$(NAME)glue.cc

libipamir$(SIG).a: ipamir$(NAME)glue.o
	make -C ../../sat/$(IPASIRSOLVER)
	cp ../../sat/$(IPASIRSOLVER)/libipasir$(IPASIRSOLVER).a $(TARGET)
	ar x pblib/libpblib.a
	ar r $(TARGET) *.o
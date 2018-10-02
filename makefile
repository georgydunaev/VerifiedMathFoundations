PATH2C = /home/user/opam-coq.8.8.1/4.02.3/bin/
CC = $(PATH2C)coqc ./

Terms:
	$(CC) Terms.v
Formulas:
	$(CC) Formulas.v

new:
	for number in 1 2 3 4 ; do \
	    ./a.out $$number ; \
	done

all:
	g++ compile.cpp -o compile.o && ./compile.o

 
oldall:
	cp *.v library/
	cd library && echo "The output will be in /library/." && \
	$(CC)Misc.v && \
	$(CC)Valuation.v && \
	$(CC)eqb_nat.v && \
	$(CC)UNIV_INST.v && \
	$(CC)Terms.v && \
	$(CC)Poly.v && \
	$(CC)Formulas.v && \
	$(CC)Provability.v && \
	$(CC)Deduction.v && \
	$(CC)PredicateCalculus.v && \
	$(CC)cexamp.v  && \
	$(CC)Ackermann.v

PATH2C = /home/user/opam-coq.8.8.1/4.02.3/bin/
CC = $(PATH2C)coqc

Terms:
	$(CC) Terms.v
 
all:
	$(CC) eqb_nat.v
	$(CC) UNIV_INST.v
	$(CC) Terms.v
	$(CC) PredicateCalculus.v

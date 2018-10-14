# VerifiedMathFoundations
Verified theorems about first-order theories.

[https://www.mccme.ru/free-books/shen/shen-logic-part2-2.pdf](https://www.mccme.ru/free-books/shen/shen-logic-part2-2.pdf)

# Installation instructions

## Windows
1. Open runme.bat with text editor notepad.
2. Change path inside it to 
   ```C:\your\path\to\Coq\bin\coqc.exe```
3. Open the console cmd. 
4. Change directory with
```
   CD /d C:\your\path\to\VerifiedMathFoundations-master
```
5. Execute the batch file.
```
   runme.bat
```
## Linux (1st variant)
1. Change path in compile.cpp
2. Create /library/ folder
3. Compile the program
```
g++ compile.cpp -o compile.o
```
4. Run the program
```
./compile.o
```
## Linux (2nd variant)
1. Change path in compile.cpp
2. Create /library/ folder
3. Make the makefile
```
   make all
```
## Linux (3rd variant)
1. Change path in makefile
2. Create /library/ folder
3. Make the makefile
```
   make all
```

# Description

Misc.v 
Valuation.v
eqb_nat.v
UNIV_INST.v - universal instantiation for vectors
Terms.v - terms for predicate calculus (PC)
Poly.v - experimental polymorphism for semantics
Formulas.v - formuli of the PC
Provability.v - provability predicate for PC
Deduction.v - deduction theorem for PC
PredicateCalculus.v - soundness theorem for PC
cexamp.v - (not finished)
Ackermann.v - set theory implementation (work in progress)
Propositional.v - deduction, soundness of intuitionistic propositional logic (IProL)
Translation.v - for using theorems from IProL in PC


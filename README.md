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
1. Change path in makefile
2. Create /library/ folder
3. Make the makefile
```
   make all
```
## Linux (2nd variant)
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

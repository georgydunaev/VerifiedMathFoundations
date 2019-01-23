if exist .\library\ ^
del /Q .\library\ && ^
rmdir /Q .\library\

mkdir library
for /f %%G in (compilation2Pred.txt) do ^
echo Add LoadPath "%~dp0library\". > .\library\%%G && ^
type %%G >> .\library\%%G && ^
O:\geo\2018\Coq\bin\coqc.exe .\library\%%~G




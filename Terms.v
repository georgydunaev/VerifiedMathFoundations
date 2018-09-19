Module Type terms_mod .
Parameter FuncSymb : Set.
Record FSV := {
 fs : FuncSymb;
 fsv : nat;
}.
End terms_mod.
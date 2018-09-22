Require Import Coq.Structures.Equalities.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations".
Require Export Formulas.

Module Provability_mod (SetVars FuncSymb PredSymb: UsualDecidableTypeFull).
Module X := Formulas_mod SetVars FuncSymb PredSymb.
Export X.

Notation SetVars := SetVars.t.
Notation PredSymb := PredSymb.t.
Notation FuncSymb := FuncSymb.t.
(*Notation " x --> y ":=(Impl x y) (at level 80).*)

Open Scope list_scope.
Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.

Inductive PR (axi:list Fo) : Fo -> Type :=
| hyp (A : Fo): (InL A axi)-> @PR axi A
| a1 (A B: Fo) : @PR axi (Impl A (Impl B A))
| a2 (A B C: Fo) : @PR axi ((A-->(B-->C))-->((A-->B)-->(A-->C)))
| a12 (ph: Fo) (t:Terms) (xi:SetVars)
: @PR axi (match (substF t xi ph) with 
      | Some q => (Impl (Fora xi ph) q)
      | None => Top
      end)
| b1 (ps ph: Fo) (xi:SetVars) (H:isParamF xi ps = false):
@PR axi (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
| MP (A B: Fo) : (@PR axi A)->(@PR axi (Impl A B))->(@PR axi B)
| GEN (A : Fo) (xi:SetVars): (@PR axi A)->(@PR axi (Fora xi A))
.


End Provability_mod.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Require Formulas.
Export Formulas.
Export Coq.Lists.List.

Module Provability_mod (SetVars FuncSymb PredSymb: UsualDecidableTypeFull).
Module XPro := Formulas_mod SetVars FuncSymb PredSymb.
Export XPro.

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

Inductive AxiomH : Fo -> Type :=
| Ha1  : forall A B, AxiomH (A-->(B-->A))
| Ha2  : forall A B C, AxiomH ((A-->(B-->C))-->((A-->B)-->(A-->C)))
| Ha12 : forall (ph: Fo) (t:Terms) (xi:SetVars)
 (r:Fo) (s:(substF t xi ph)=Some r), AxiomH (Impl (Fora xi ph) r)
| Hb1  : forall (ps ph: Fo) (xi:SetVars) (H:isParamF xi ps = false),
AxiomH (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
.

Inductive PR (axi:list Fo) : Fo -> Type :=
| hyp (A : Fo): (InL A axi)-> @PR axi A
| Hax (A : Fo): (AxiomH A) -> @PR axi A
(*| a1 (A B: Fo) : @PR axi (Impl A (Impl B A))
| a2 (A B C: Fo) : @PR axi ((A-->(B-->C))-->((A-->B)-->(A-->C)))*)
(*| a12 (ph: Fo) (t:Terms) (xi:SetVars)
: @PR axi (match (substF t xi ph) with 
      | Some q => (Impl (Fora xi ph) q)
      | None => Top
      end)
| b1 (ps ph: Fo) (xi:SetVars) (H:isParamF xi ps = false):
@PR axi (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) ) *)
| MP (A B: Fo) : (@PR axi A)->(@PR axi (Impl A B))->(@PR axi B)
| GEN (A : Fo) (xi:SetVars): (@PR axi A)->(@PR axi (Fora xi A))
.

Definition a1 axi A B : @PR axi (Impl A (Impl B A)).
Proof. apply Hax, Ha1. Defined.
Definition a2 axi A B C : @PR axi ((A-->(B-->C))-->((A-->B)-->(A-->C))).
Proof. apply Hax, Ha2. Defined.
Definition b1 axi (ps ph: Fo) (xi:SetVars) (H:isParamF xi ps = false):
@PR axi (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) ).
Proof. apply Hax, Hb1, H. Defined.


Definition AtoA {axi} (A:Fo) : PR axi (A-->A).
Proof.
apply (MP axi (A-->(A-->A)) _).
apply a1. (* apply (Hax _ _ (Ha1 _ _)).*)
apply (MP axi (A-->((A-->A)-->A)) _).
apply a1.
apply a2.
Defined.

Definition a12 axi ph t xi : @PR axi (match (substF t xi ph) with 
      | Some q => (Impl (Fora xi ph) q)
      | None => Top
      end).
Proof. induction (substF t xi ph) eqn:g. eapply Hax, Ha12, g.
unfold Top.
exact (AtoA  Bot).
Defined.

End Provability_mod.
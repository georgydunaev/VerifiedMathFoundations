(* Here will be theorems about propositional logic.
Then I'll decide how to unite it with the rest. *)

Require Export Coq.Vectors.Vector.
Require Import Coq.Structures.Equalities.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".

Require Poly.
Export Poly.ModProp.

Module  Formulas_mod (PropVars : UsualDecidableTypeFull).

Inductive Fo :=
 |Atom (p:PropVars.t) :> Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
.

Notation " x --> y ":=(Impl x y) (at level 80).
Notation " x -/\ y ":=(Conj x y) (at level 80).
Notation " x -\/ y ":=(Disj x y) (at level 80).

(* Substitution *)
Fixpoint subPF (t:Fo) (xi: PropVars.t) (u : Fo): Fo.
Proof.
Abort. (*Defined.*)

Definition Top:Fo := Impl Bot Bot.

Notation " x --> y ":=(Impl x y) (at level 80).
(* HERE *)
Section Interpretation.
Context (val:PropVars.t->Omega).
Fixpoint foI (f:Fo): Omega.
Proof.
destruct f eqn:h.
+ exact (val p).
+ exact OFalse.
+ exact ( OAnd (foI f0_1) (foI f0_2)).
+ exact (  OOr (foI f0_1) (foI f0_2)).
+ exact ( OImp (foI f0_1) (foI f0_2)).
Show Proof.
Defined.
(*
Fixpoint foI (val:SetVars->X) (f:Fo): Omega.
Proof.
destruct f.
+ refine (prI p _).
  apply (Vector.map  (teI val)).
  exact t.
+ exact false.
+ exact ( andb (foI val f1) (foI val f2)).
+ exact (  orb (foI val f1) (foI val f2)).
+ exact (implb (foI val f1) (foI val f2)).
+  (*Infinite conjunction!!!*)
 Show Proof.
*)
End Interpretation.

End Formulas_mod.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require List.
Require Bool.
Require Import Coq.Structures.Equalities.
Require Export Provability.

Export Coq.Lists.List.
Import Bool.Bool.

Module Ackermann_mod (*SetVars FuncSymb PredSymb: UsualDecidableTypeFull*).
Module SetVars : UsualDecidableTypeFull :=PeanoNat.Nat.
Module FuncSymb : UsualDecidableTypeFull := PeanoNat.Nat.
Module PredSymb : UsualDecidableTypeFull := PeanoNat.Nat.

Module X := Provability_mod SetVars FuncSymb PredSymb.
Export X.
Module Facts := BoolEqualityFacts SetVars.
Check substF.

(*Local Notation SetVars := SetVars.t (only parsing).
Local Notation FuncSymb := FuncSymb.t (only parsing).
Local Notation PredSymb := PredSymb.t (only parsing). *)

Import VectorNotations.
(*Check substF.*)

Section inf_sec.
Context (en:nat->PredSymb.t) (enInj: forall x1 x2, en x1 = en x2 -> x1=x2).
(*Module Facts := BoolEqualityFacts SetVars.*)
Inductive AxiomAST : Fo -> Type :=
| aPC  :> forall {A}, (AxiomH A) -> (AxiomAST A)
| aeq1 : forall (x:SetVars.t), (AxiomAST (Atom (MPSV (en 0) 2) [FVC x ; FVC x]))
| aeq2 : forall (x y:SetVars.t) (f r:Fo)
(H:substF y x f = Some r)
, (AxiomAST (Atom (MPSV (en 0) 2) [FVC x ; FVC y] --> ( r --> f) ))
.

(* (MPSV 0 2) - = 
   (MPSV 1 2) - \in
*)
(*Check AxiomAST (Ha1 Bot Bot). ? *)

Notation "( a '==' b )" := (Atom (MPSV (en 0) 2) [a ; b]).
Notation "( a 'e.' b )" := (Atom (MPSV (en 1) 2) [a ; b]).

(* Provability in Ackermann set theory *)
Definition APR := @GPR AxiomAST.
(* Mendelson p.102/447 *)
(*Coercion FVC : SetVars.t >-> Terms.*)
(*Coercion Q : (Vector.t SetVars.t n) >-> (Vector.t Terms n).*)

Definition p2_23_a ctx (t:Terms) (x:SetVars.t): 
APR ctx (Atom (MPSV (en 0) 2) [t ; t]).
Proof. (* (Atom (MPSV (en 0) 2) [FVC x ; FVC x]) *)
apply MP with (A:= Fora x (FVC x== FVC x)).
apply GEN.
apply Hax, (aeq1 x).
apply Hax, aPC.
apply Ha12 with (t:=t).
simpl.
rewrite -> Facts.eqb_refl.
reflexivity.
Defined.
Definition p2_23_b ctx (t s:Terms) (x:SetVars.t): 
APR ctx ((Atom (MPSV (en 0) 2) [t ; t]) --> (Atom (MPSV (en 0) 2) [t ; t]) ).
Proof.

Abort.
End inf_sec.

End Ackermann_mod.
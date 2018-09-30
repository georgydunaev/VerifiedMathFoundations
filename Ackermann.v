Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Import Misc.
Require Import Deduction.
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

(* Module X := Provability_mod SetVars FuncSymb PredSymb.
Export X. *)
Module X := Deduction_mod SetVars FuncSymb PredSymb.
Export X.
Module Facts := BoolEqualityFacts SetVars.

(*Local Notation SetVars := SetVars.t (only parsing).
Local Notation FuncSymb := FuncSymb.t (only parsing).
Local Notation PredSymb := PredSymb.t (only parsing). *)

Import VectorNotations.
(*Check substF.*)

Section inf_sec.
Context (en:nat->PredSymb.t) (enInj: forall x1 x2, en x1 = en x2 -> x1=x2).
Context (es:nat->SetVars.t) (esInj: forall x1 x2, es x1 = es x2 -> x1=x2).
(*Module Facts := BoolEqualityFacts SetVars.*)
(*Notation "( a '==' b )" :=
(Atom {| ps := en 0; psv := 2 |} [a:Terms; b:Terms]).*)
Notation "( a '==' b )" :=
(Atom {| ps := en 0; psv := 2 |} 
(@Vector.cons Terms a 1 (@Vector.cons Terms b 0 (@Vector.nil Terms)))
).
Coercion es:nat>->SetVars.t.

Notation "( a 'e.' b )" := (Atom {| ps := en 1; psv := 2 |} [a:Terms; b:Terms]).

Inductive AxiomAST : Fo -> Type :=
| aPC  :> forall {A}, (PRECA A) -> (AxiomAST A)
| aeq1 : forall (x:SetVars.t), AxiomAST (Fora 0 (0 == 0))
(*AxiomAST (Atom (MPSV (en 0) 2) [FVC x ; FVC x])*)
| aeq2 : forall (x y:SetVars.t) (f r:Fo)
(H:substF y x f = Some r)
, AxiomAST ((x == y) --> ( r --> f ))
(*AxiomAST (Atom (MPSV (en 0) 2) [FVC x ; FVC y] --> ( r --> f) ))*)
.

(* (MPSV 0 2) - = 
   (MPSV 1 2) - \in
*)
(*Check AxiomAST (Ha1 Bot Bot). ? *)
(*Notation "( a '==' b )" := (Atom (MPSV (en 0) 2) [FVC a ; FVC b]).*)
(*Notation "( a '==' b )" := (Atom (MPSV (en 0) 2) [a:Terms ; b:Terms]).
Notation "( a 'e.' b )" := (Atom (MPSV (en 1) 2) [a:Terms ; b:Terms]).
*)


(* Provability in Ackermann set theory *)
Definition APR := GPR dcb AxiomAST.
(* Mendelson p.102/447 *)
(*Coercion FVC : SetVars.t >-> Terms.*)
(*Coercion Q : (Vector.t SetVars.t n) >-> (Vector.t Terms n).*)
Theorem J (y:SetVars.t): Terms. exact y. Defined.

Theorem q x: (x == x) = (Atom {| ps := en 0; psv := 2 |} [x; x]).
Proof. reflexivity. Defined.

Definition p2_23_a ctx (t:Terms) (*x:SetVars.t*): APR ctx (t == t).
pose (x:=0).
Proof. 
(*apply MP with (A:= Fora x (x == x)).
change (Atom {| ps := en 0; psv := 2 |} [FVC x; FVC x]) with (x == x).
*)
apply MP with (A:= Fora x ( x == x)) (1:=I).
(*
try fold (Fora x (x == x)).
try rewrite <- q.
pose (q:= (x == x)).
replace (Atom {| ps := en 0; psv := 2 |} [FVC x; FVC x]) with (x == x).
*)
(*apply GEN.*)
apply Hax, (aeq1 x).
apply Hax, aPC.
apply Ha12 with (t:=t).
simpl.
rewrite -> Facts.eqb_refl.
reflexivity.
Defined.

(*TODO Prove the completeness theorem. *)
(*Definition swap ctx A B C: 
(PR ctx (A --> (B --> C) --> (B --> (A --> C)) )).
Proof.
Fail Check Ded.
Fail intro b.
Admitted.*)
Check swapSIMPL.

Definition p2_23_b ctx (t s:Terms) (x y:SetVars.t):
APR ctx ((t==s) --> (s==t) ).
Proof.
pose (step1 := aeq2 x y (y == x) (x == x)).
pose (step2 := swap ctx (x == y) (x == x) (y == x)).
(*Check MP _ ctx (x == x) ((x == y) --> (y == x)). *)
(*apply MP with .
apply MP with (A:= Fora x (x == x)).
apply aeq2.*)
Abort.


End inf_sec.

End Ackermann_mod.

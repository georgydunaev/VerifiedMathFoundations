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
Notation "( a '==' b )" :=
(Atom {| ps := en 0; psv := 2 |} [a:Terms; b:Terms]).
Notation "( a 'e.' b )" := (Atom {| ps := en 1; psv := 2 |} [a:Terms; b:Terms]).

Inductive AxiomAST : Fo -> Type :=
| aPC  :> forall {A}, (AxiomH A) -> (AxiomAST A)
| aeq1 : forall (x:SetVars.t), AxiomAST (x == x)
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
Check Vector.cons .
(*Notation "( a '==' b )" := (Atom (MPSV (en 0) 2) [FVC a ; FVC b]).*)
(*Notation "( a '==' b )" := (Atom (MPSV (en 0) 2) [a:Terms ; b:Terms]).
Notation "( a 'e.' b )" := (Atom (MPSV (en 1) 2) [a:Terms ; b:Terms]).
*)


(* Provability in Ackermann set theory *)
Definition APR := @GPR AxiomAST.
(* Mendelson p.102/447 *)
(*Coercion FVC : SetVars.t >-> Terms.*)
(*Coercion Q : (Vector.t SetVars.t n) >-> (Vector.t Terms n).*)
Theorem J (y:SetVars.t): Terms.
exact y. Defined.
Definition p2_23_a ctx (t:Terms) (x:SetVars.t): APR ctx (t == t).

Theorem q x: (x == x) = (Atom {| ps := en 0; psv := 2 |} [x; x]).
Proof. reflexivity. Defined.

Proof. 
apply MP with (A:= Fora x (x == x)).
(*
try fold (Fora x (x == x)).
try rewrite <- q.
pose (q:= (x == x)).
replace (Atom {| ps := en 0; psv := 2 |} [FVC x; FVC x]) with (x == x).
*)
apply GEN.
apply Hax, (aeq1 x).
apply Hax, aPC.
apply Ha12 with (t:=t).
simpl.
rewrite -> Facts.eqb_refl.
reflexivity.
Defined.
Definition p2_23_b ctx (t s:Terms) (x:SetVars.t):
APR ctx ((t==s) --> (s==t) ).
Proof.

Abort.
End inf_sec.

End Ackermann_mod.

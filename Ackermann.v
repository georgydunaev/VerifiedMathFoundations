Require List.
Require Bool.
Require Import Coq.Structures.Equalities.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Export Provability.

Module Ackermann_mod (*SetVars FuncSymb PredSymb: UsualDecidableTypeFull*).
Module SetVars := PeanoNat.Nat.
Module FuncSymb := PeanoNat.Nat.
Module PredSymb := PeanoNat.Nat.
Module X := Provability_mod SetVars FuncSymb PredSymb.
Export X.
Export Coq.Lists.List.
Import Bool.Bool.

(*Notation SetVars := SetVars.t (*only parsing*).
Notation FuncSymb := FuncSymb.t (only parsing).
Notation PredSymb := PredSymb.t (*only parsing*).*)
Check substF.
Import VectorNotations.
(*Check substF.*)

(*Module Facts := BoolEqualityFacts SetVars.*)
Inductive AxiomAST : Fo -> Type :=
| aPC  :> forall {A}, (AxiomH A) -> (AxiomAST A)
| aeq1 : forall (x:SetVars), (AxiomAST (Atom (MPSV 0 2) [FVC x ; FVC x]))
| aeq2 : forall (x y:SetVars) (f r:Fo) 
(*H: substF y *)
, (AxiomAST (Atom (MPSV 0 1) [FVC x] ))
.

(* (MPSV 0 2) - = 
   (MPSV 1 2) - \in
*)
(*Check AxiomAST (Ha1 Bot Bot). ? *)



(* Provability in Ackermann set theory *)
Definition APR := @GPR AxiomAST.



End Ackermann_mod.
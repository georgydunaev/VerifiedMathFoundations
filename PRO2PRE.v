(* PUBLIC DOMAIN *)
(* Author: Georgy Dunaev, georgedunaev@gmail.com *)
Require Vector.
Require List.
Require Import Bool.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Export UNIV_INST.
Require Export Provability.
Require Export Misc.
(*Require Poly.*)
Require Valuation.
Require Import Coq.Structures.Equalities.
Require Import PropLang.

Module PRO2PRE_mod
(SetVars FuncSymb PredSymb PropVars : UsualDecidableTypeFull).
Module PRE := Provability.Provability_mod SetVars FuncSymb PredSymb.
Export PRE.
(*
Module Facts := BoolEqualityFacts SetVars.
Module cn := Valuation.Valuation_mod SetVars.
Export cn.
*)
Check Fo.
Module PRO := PropLang.Lang PropVars.
(*Export PRO.*)
Check Fora.

Print PRE.Fo.
Print PRO.Fo.

(* Interpretations *)
Definition ints :=PropVars.t->PRE.Fo.

Section transl_sec.
Context (I:ints).
Fixpoint O2E (A:PRO.Fo):PRE.Fo :=
match A with
 | PRO.Atom p => I p
 | PRO.Bot => PRE.Bot
 | PRO.Conj x1 x2 => PRE.Conj (O2E x1) (O2E x2)
 | PRO.Disj x1 x2 => PRE.Disj (O2E x1) (O2E x2)
 | PRO.Impl x1 x2 => PRE.Impl (O2E x1) (O2E x2)
end.

Theorem PRO2PRE (A:PRO.Fo):
 PRO.PR PRO.PROCAI PRO.empctx A -> PREPR nil (O2E A).
Proof.
intro H. induction H as [f c|f a|A B a IHa a2b IHa2b].
+ destruct c.
+ destruct a;
  simpl;
  apply Hax_E;
  constructor;
  constructor.
+ eapply MP_E. exact IHa. exact IHa2b.
Defined.
Check PRO.propswap.

Definition dswap A B C := PRO2PRE _ (PRO.propswap A B C).

End transl_sec.

(*Export FormulasNotationsUnicode.
Open Scope uninot.
Definition swap ctx (A B C:PRE.Fo) :
(PREPR ctx ((A → (B → C)) → (B → (A → C)) )).
*)
End PRO2PRE_mod.


Require Import Arith.PeanoNat.
Module m2 <: UsualDecidableTypeFull.
Definition t:=nat.
Definition eq := @eq nat.
Definition eq_refl:=@eq_refl nat.
Definition eq_sym:=@eq_sym nat.
Definition eq_trans:=@eq_trans nat.
Definition eq_equiv:Equivalence eq := Nat.eq_equiv.
Definition eq_dec := Nat.eq_dec.
Definition eqb:=Nat.eqb.
Definition eqb_eq:=Nat.eqb_eq.
End m2.


Module SWAP_mod
(SetVars FuncSymb PredSymb : UsualDecidableTypeFull).

Module PRE := PRO2PRE_mod SetVars FuncSymb PredSymb m2.
Import PRE.
Print ints.

(* Theorem test : m2.t. Proof. exact 0. Defined. OK! *)

Section swap_sec.
Context (A B C:PRE.Fo).
Definition myI : ints.
Proof.
intro n.
exact (
match n with
 | S (S y) => C
 | S x => B
 | O => A
end).
Defined.

Check PRE.Impl.
Import PredFormulasNotationsASCII.
(*Import PropFormulasNotationsASCII.*)
(*Locate "→".*)
Open Scope pretxtnot.

Definition swap :
(PREPR nil ((A --> (B --> C)) --> (B --> (A --> C)) )).
Proof.
Close Scope pretxtnot.
Export PRO.
Check PRO2PRE myI ((0 --> 1 --> 2) --> 1 --> 0 --> 2).
eapply (PRO2PRE myI ((0 --> 1 --> 2) --> 1 --> 0 --> 2)).
exact (propswap 0 1 2).
Defined.
End swap_sec.
Check swap.
Locate "-->".
Open Scope pretxtnot.
End SWAP_mod.

Module chk (SetVars FuncSymb PredSymb : UsualDecidableTypeFull).
Module SWP := SWAP_mod SetVars FuncSymb PredSymb.
Import SWP.
Print PRE.PRE.PRE.Fo.
Import PRE.
Import PRE. (* Why I shall do it again? *)
Print Fo.
Import PredFormulasNotationsASCII.

Check swap.
(* So "swap" theorem is translated from proposition logic
  to predicate logic. *)
End chk.
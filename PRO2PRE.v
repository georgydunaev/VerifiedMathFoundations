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
Export PRO.
Check Fora.

Print PRE.Fo.
Print PRO.Fo.

(* Interpretations *)
Definition ints :=PropVars.t->PRE.Fo.

Section transl_sec.
Context (I:ints).
Fixpoint O2E (A:PRO.Fo):PRE.Fo :=
match A with
 | Atom p => I p
 | Bot => PRE.Bot
 | Conj x1 x2 => PRE.Conj (O2E x1) (O2E x2)
 | Disj x1 x2 => PRE.Disj (O2E x1) (O2E x2)
 | Impl x1 x2 => PRE.Impl (O2E x1) (O2E x2)
end.

Theorem PRO2PRE (A:PRO.Fo):
 PR PROCAI empctx A -> PREPR nil (O2E A).
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

End transl_sec.

End PRO2PRE_mod.
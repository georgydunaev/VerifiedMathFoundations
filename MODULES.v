Require Coq.Structures.Equalities.
Import Coq.Structures.Equalities.
Module Terms_mod (SetVars FuncSymb: UsualDecidableTypeFull).
End Terms_mod.

Module m1 : Typ.
Definition t:=nat.
End m1.

Require Import Arith.PeanoNat.
Module m2 : UsualDecidableTypeFull.
Definition t:=nat.
Definition eq := @eq nat.
Definition eq_refl:=@eq_refl nat.
Definition eq_sym:=@eq_sym nat.
Definition eq_trans:=@eq_trans nat.
(*
Theorem eq_equiv:Equivalence eq.
Proof.
apply Build_Equivalence.
+ unfold Reflexive. (*intro x.*) exact eq_refl.
+ unfold Symmetric. exact eq_sym.
(*intros x y p. destruct p. reflexivity.*)
+ unfold Transitive. exact eq_trans.
(*intros x y z p1 p2. transitivity y.
exact p1. exact p2.*)
Defined.

Check Nat.eq_dec.
*)
Definition eq_equiv:Equivalence eq := Nat.eq_equiv.
(*
Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  induction n; destruct m.
  - now left.
  - now right.
  - now right.
  - destruct (IHn m); [left|right]; auto.
Defined.
*)
Definition eq_dec := Nat.eq_dec.
Definition eqb:=Nat.eqb.
Definition eqb_eq:=Nat.eqb_eq.
(*
Lemma eqb_eq n m : eqb n m = true <-> n = m.
Proof.
 revert m.
 induction n; destruct m; simpl; rewrite ?IHn; split; try easy.
 - now intros ->.
 - now injection 1.
Qed.
*)
End m2.

(*Definition eqb_eq:=Nat.eqb_eq.*)
(*Definition eq_dec:=@eq_dec nat.*)
(*Import Typ.

Module XFo := Terms_mod nat nat.
SetVars FuncSymb.
Export cn.
Export XFo.

Import Terms_mod nat.
*)
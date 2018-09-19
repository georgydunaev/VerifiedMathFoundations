Require Import Arith.Peano_dec.
Require Import Bool.Bool.

Lemma eqb_comm x xi : PeanoNat.Nat.eqb xi x =  PeanoNat.Nat.eqb x xi.
Proof.
destruct (PeanoNat.Nat.eqb xi x) eqn:e1.
symmetry.
pose (Y:= proj1 (PeanoNat.Nat.eqb_eq xi x) e1).
rewrite -> Y at 1.
rewrite <- Y at 1.
exact e1.
symmetry.
pose (n3:= proj2 (not_iff_compat (PeanoNat.Nat.eqb_eq x xi)) ).
apply not_true_iff_false.
apply n3.
intro q.
symmetry in q.
revert q.
fold (xi <> x).
pose (n5:= proj1 (not_iff_compat (PeanoNat.Nat.eqb_eq xi x)) ).
apply n5.
apply not_true_iff_false.
exact e1.
Defined.

(*pose (n4:= n3 (proj2 (not_true_iff_false (PeanoNat.Nat.eqb x xi)) i)).
unfold PeanoNat.Nat.eqb.
Admitted.*)

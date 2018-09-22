Require Import Coq.Structures.Equalities.
Module Valuation_mod (SetVars : UsualDecidableTypeFull).
(** (\pi + (\xi \mapsto ?) ) **)
Section a.
Context {X:Type}.

Definition cng (val:SetVars.t -> X) (xi:SetVars.t) (m:X) :=
 (fun r:SetVars.t =>
 match SetVars.eqb r xi with
 | true => m
 | false => (val r)
 end).

Lemma dbl_cng  pi xi m1 m2: forall q,(cng (cng pi xi m1) xi m2) q = (cng pi xi m2) q.
Proof. intro q. unfold cng. destruct (SetVars.eqb q xi); reflexivity. Defined.

Lemma twice_the_same (pi:SetVars.t->X) x m0 m1 : 
forall u, (cng (cng pi x m0) x m1) u = (cng pi x m1) u.
Proof.
intro u.
unfold cng.
destruct (SetVars.eqb u x).
reflexivity.
reflexivity.
Defined.

End a.

End Valuation_mod.

Require Import Coq.Structures.Equalities.
Module Valuation_mod (SetVars : UsualDecidableTypeFull).
(** (\pi + (\xi \mapsto ?) ) **)
Section a.
Context {X:Type}.
(*Notation "'cng'" := (fun (val:SetVars.t -> X) (xi:SetVars.t) (m:X) =>
(fun r:SetVars.t =>
match SetVars.eqb r xi with
| true => m
| false => (val r)
end)).*)

Definition cng (val:SetVars.t -> X) (xi:SetVars.t) (m:X) :=
(fun r:SetVars.t =>
match SetVars.eqb r xi with
| true => m
| false => (val r)
end).

Lemma dbl_cng  pi xi m1 m2: forall q,(cng (cng pi xi m1) xi m2) q = (cng pi xi m2) q.
Proof. intro q. unfold cng. destruct (SetVars.eqb q xi); reflexivity. Defined.
End a.

(*Transparent cng dbl_cng.
Definition y:= @cng unit. Print y.*)
End Valuation_mod.

Require Import Coq.Structures.Equalities.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
(*Require PredicateCalculus.*)
Require Terms.
(*UsualDecidableTypeFull)*)
Module nat_is_UDTF . 
Definition t :=nat.
Definition SetVars:=nat.
End nat_is_UDTF.
Module eexampl := Terms.terms_mod PeanoNat.Nat PeanoNat.Nat.

Module counterexample.
Import eexampl.
Print SetVars.
Print FuncSymb.
Print eexampl.FSV.
Check FSV.
(*Module example1 : Terms.terms_mod PeanoNat.Nat (*nat_is_UDTF*).*)
(*Definition FuncSymb := nat.
Record FSV := {
 fs : FuncSymb;
 fsv : nat;
}.*)
(*Definition SetVars:=nat.*)
(*Notation  SetVars:=nat.
Check PeanoNat.Nat.t.
Notation SetVars := SetVars.t.
Check example0.t.
(*Notation SetVars := PeanoNat.Nat.t.*)
Unset Elimination Schemes.
Inductive Terms : Type :=
| FVC :> SetVars -> Terms
| FSC (f:FSV) : (Vector.t Terms (fsv f)) -> Terms.
Set Elimination Schemes.
*)

(* TODO: add *)
Print Fo.
Check Atom.
Print PSV.
Check Atom (MPSV 0 2).
Print Terms.
Check Atom (MPSV 0 2).
Print Vector.t.
Import

End counterexample.

Module Type exVS (X: Terms.terms_mod).
Check X.FuncSymb.
Print X.FSV.
End exVS.

Module example2 : exVS example1.

Check example1.FuncSymb.
Print Fo.

(*Check newt.PR.*)

End example2.


Module example2_1 : exVS.
Module X := example1.
Import X.
End example2_1.


Module Type newt (v:PredicateCalculus.VS).




(* COUNTEREXAMPLE
Check Vector.cons _ (FVC 1) _ (Vector.cons _ (FVC v0) _ (Vector.nil _ )).
Check Atom (MPSV 0 2) 
(Vector.cons _ (FVC 1) _ (Vector.cons _ (FVC 0) _ (Vector.nil _ ))).
Definition xeqy := Atom (MPSV 0 2) 
(Vector.cons _ (FVC 1) _ (Vector.cons _ (FVC 0) _ (Vector.nil _ ))).

Theorem upr : PR (xeqy::nil) (Fora 2 xeqy).
Proof.
apply GEN.
apply hyp.
simpl. (*Print "+"%type.*) 
apply inl.
reflexivity.
Defined.
(* PR is from provability, but it is better to call it derivability.*)

Theorem badcorrect (x1 x2 : X) (nequ : ~(x1=x2))
(f:Fo) (l:list Fo) (m:PR l f) :
~ (forall(val:SetVars->X) (lfi : forall h:Fo, (InL h l)->(foI val h)), foI val f).
Proof.
intro H.
assert (val:SetVars->X).
 intro n. destruct n eqn:nn. exact x1.
          destruct s eqn:ss. exact x2. exact x2.
Abort.*)

(* IT IS NOT POSSIBLE TO PROVE THIS THEOREM:
Fixpoint correct (f:Fo) (l:list Fo) (val:SetVars->X) (m:PR l f) 
(lfi : forall h:Fo, (InL h l)->(foI val h)) {struct m}: foI val f.
Proof.
revert val lfi.
induction m (* eqn: meq *); intros val lfi.
+ exact (lfi A i).
+ simpl.
  intros a b.
  exact a.
+ simpl.
  intros a b c.
  exact (a c (b c)).
+ simpl in *|-*.
  destruct (substF t xi ph) eqn: j.
  apply (UnivInst ph val xi t f j).
  simpl. firstorder.
+ simpl in *|-*.
  unfold OImp.
  intros H0 H1 m.
  apply H0.
  rewrite -> (NPthenNCACVF xi ps0 m val H).
  exact H1.
+ simpl in * |- *.
  unfold OImp in IHm2.
apply IHm2.
apply lfi.
apply IHm1.
apply lfi. (*  exact (IHm2 IHm1).*)
+ simpl in * |- *.
  intro m0.
apply IHm.
intros h B.
unfold InL in B.
(*Check correct A l val m lfi.*)
Check NPthenNCACVF xi ps0 m val H.
  destruct (substF t xi ph) eqn: j.
  apply (UnivInst ph val xi t f j).
  simpl. firstorder.

*)


(* old trash
unfold InL in B.
(*Check correct A l val m lfi.*)
Check NPthenNCACVF xi ps0 m val H.
  destruct (substF t xi ph) eqn: j.
  apply (UnivInst ph val xi t f j).
  simpl. firstorder.



  2 : { simpl. trivial. unfold OImp. firstorder. }
  apply (correct _ l).
  2 : {assumption. }
  simpl.
Check fun pi => UnivInst ph pi xi t f j. 
(*forall pi : SetVars -> X, foI pi (Impl (Fora xi ph) f)*)
Show Proof.
Check PR.
pose (Z:=(@Ded (Fora xi ph) f l )).
simple refine (Z _ _ ).
Check correct.
apply correct.
2 : { 
intros.
Check notGenWith.
simpl.
(*
  pose (W:= lfi f).
  destruct (Nat.eqb r xi).
  simpl in H.
  exact H.
  unfold foI. 
  simpl.
*)
Abort. *)
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Import Coq.Structures.Equalities.
Require PredicateCalculus.
Require Terms.

(*UsualDecidableTypeFull)*)
Module nat_is_UDTF .
Definition t :=nat.
Definition SetVars:=nat.
End nat_is_UDTF.

Module SetVars := PeanoNat.Nat.
Module FuncSymb := PeanoNat.Nat.
Module PredSymb := PeanoNat.Nat.
Module eexampl := 
PredicateCalculus.Soundness_mod SetVars FuncSymb PredSymb.
(*Module eexampl := 
PredicateCalculus.Soundness_mod PeanoNat.Nat PeanoNat.Nat PeanoNat.Nat.*)

Module counterexample.
Export eexampl.
(*
Print SetVars.
Print FuncSymb.
Check FSV.
*)
(*Print eexampl.FSV.*)

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

(* OK!
Print Fo.
Check Atom.
Print PSV.
Check Atom (MPSV 0 2).
Print Terms.
Check Atom (MPSV 0 2).
Print Vector.t.
Check Vector.cons _ (FVC 1) _ (Vector.cons _ (FVC 0) _ (Vector.nil _ )).
Check Atom (MPSV 0 2)
(Vector.cons _ (FVC 1) _ (Vector.cons _ (FVC 0) _ (Vector.nil _ ))).
*)

Definition xeqy := Atom (MPSV 0 2) 
(Vector.cons _ (FVC 1) _ (Vector.cons _ (FVC 0) _ (Vector.nil _ ))).

Theorem upr : PREPR (xeqy::nil) (Fora 2 xeqy).
Proof.
apply GEN_E.
{ intros A M. destruct M. 
  + rewrite <- e. unfold xeqy. simpl. reflexivity.
  +  destruct i. }
apply hyp_E.
simpl.
apply inl.
reflexivity.
Defined.
(* COUNTEREXAMPLE*)
(* PR is from provability, but it is better to call it derivability.*)
Section cor.
Context (X:Type).
Context (fsI:forall(q:FSV),(Vector.t X (fsv q))->X).
Context (prI:forall(q:PSV),(Vector.t X (psv q))->Omega).
(*Arguments foI X fsI prI .
Print Implicit foI.
Check foI.*)
Definition foIn := @foI X fsI prI.
Theorem badcorrect (x1 x2 : X) (nequ : ~(x1=x2))
(f:Fo) (l:list Fo) (m : PREPR l f) :
~ (forall(val:SetVars.t->X) (lfi : forall h:Fo, (InL h l)->(foIn val h)), foIn val f).
Proof.
intro H.
assert (val:SetVars.t->X).
 intro n. destruct n eqn:nn. exact x1.
(*          destruct s eqn:ss. exact x2. exact x2.*)
Abort.
End cor.

End counterexample.

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

(*TRASH
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

*)
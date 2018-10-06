(* PUBLIC DOMAIN *)
(* Author: Georgy Dunaev, georgedunaev@gmail.com *)
Require Vector.
Require List.
Require Bool.
Import Bool.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Export UNIV_INST.
Require Provability.
Require Misc.
Require Poly.
Require Valuation.
Export Provability.
Export Misc.
Require Import Coq.Structures.Equalities.

Module Soundness_mod (SetVars FuncSymb PredSymb: UsualDecidableTypeFull).
Module XPr := Provability.Provability_mod SetVars FuncSymb PredSymb.
Module Facts := BoolEqualityFacts SetVars.
Module cn := Valuation.Valuation_mod SetVars.
Export XPr.
Export cn.

(* Here we choose an interpretation. *)
(*Export ModBool.*)
Export Poly.ModProp. (* + classical axioms *)
(*Export ModType. It doesn't work properly. *)
(** Soundness theorem section **)
Section cor.
Context (X:Type).
Context (fsI:forall(q:FSV),(Vector.t X (fsv q))->X).
Context (prI:forall(q:PSV),(Vector.t X (psv q))->Omega).

Section Lem1.
(* page 136 of the book *)
Definition lem1 (t : Terms) : forall (u :Terms) 
(xi : SetVars.t) (pi : SetVars.t->X) ,
(@teI X fsI pi (substT t xi u))=(@teI X fsI (cng pi xi (@teI X fsI pi t)) u).
Proof.
fix lem1 1.
intros.
induction u as [s|f].
+ simpl.
  unfold cng.
  destruct (SetVars.eqb s xi) eqn:ek.
  * reflexivity.
  * simpl.
    reflexivity.
+ simpl.
  destruct f.
  simpl.
  apply ap.
  simpl in * |- *.
  apply (proj1 (
   eq_nth_iff X fsv0
   (Vector.map (teI pi) (Vector.map (substT t xi) v))
   (Vector.map (teI (cng pi xi (teI pi t))) v)
  )).
  intros.
  simpl in * |- *.
  rewrite -> (nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0).
  rewrite -> (nth_map (teI (cng pi xi (teI pi t))) v p2 p2 ).
  rewrite -> (nth_map (substT t xi) v p2 p2 eq_refl).
  exact (H p2).
  reflexivity.
Defined.
End Lem1.

Lemma all_then_someP (A:Type)(n:nat)(p:Fin.t (n)) (v:Vector.t A (n)) (P:A->bool)
(H : Vector.fold_left orb false (Vector.map P v) = false)
 : (P (Vector.nth v p)) = false.
Proof.
rewrite <- (nth_map P v p p eq_refl).
apply all_then_someV. trivial.
Defined.

(* Not a parameter then not changed afted substitution (for Terms) *)
Lemma NPthenNCAST (u:Terms)(xi:SetVars.t)(t:Terms) (H:(isParamT xi u=false))
: (substT t xi u) = u.
Proof. induction u.
+ simpl in * |- *.
  rewrite H. reflexivity.
+ simpl in * |- *.
  apply ap.
  apply eq_nth_iff.
  intros p1 p2 ppe.
  rewrite (nth_map _ _ _ p2 ppe).
  apply H0.
  simpl.
  apply all_then_someP.
  trivial.
Defined.

Lemma NPthenNCAST_vec:forall p xi t ts (H:(isParamF xi (Atom p ts)=false)), 
  (Vector.map (substT t xi) ts) = ts.
Proof.
intros p xi t1 ts H.
apply eq_nth_iff.
intros p1 p2 H0.
rewrite -> (nth_map (substT t1 xi) ts p1 p2 H0).
apply NPthenNCAST.
apply all_then_someP.
simpl in H.
exact H.
Defined.

(* Not a parameter then not changed afted substitution (for Formulas) *)
Fixpoint NPthenNCASF (mu:Fo) : forall (xi:SetVars.t)(t:Terms) (H:(isParamF xi mu=false))
   , substF t xi mu = Some mu .
Proof. (*induction mu eqn:u0.*)
destruct mu eqn:u0.
* intros xi t0 H.
  simpl.
  rewrite -> NPthenNCAST_vec; (trivial || assumption).
* intros xi t H.
  simpl; trivial.
* intros xi t H.
  simpl.
  simpl in H.
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF .
  rewrite -> NPthenNCASF .
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF.
  rewrite -> NPthenNCASF.
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF.
  rewrite -> NPthenNCASF.
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (SetVars.eqb x xi) eqn:u2.
  trivial.
  destruct (isParamF xi f) eqn:u1.
  inversion H.
  trivial.
* simpl.
  intros xi t H.
  destruct (SetVars.eqb x xi) eqn:u2.
  trivial.
  destruct (isParamF xi f) eqn:u1.
  inversion H.
  trivial.
Defined.

(* p.137 *)
Section Lem2.

Lemma mqd x t pi m (H:isParamT x t = false): 
(@teI X fsI (cng pi x m) t) = (@teI X fsI pi t).
Proof.
induction t.
simpl.
simpl in H.
unfold cng.
rewrite -> H.
reflexivity.
simpl.
simpl in H.
apply ap.
apply eq_nth_iff.
intros.
rewrite -> (nth_map (teI (cng pi x m)) v p1 p1 eq_refl).
rewrite -> (nth_map (teI pi) v p2 p2 eq_refl).
rewrite <- H1.
apply H0.
exact (all_then_someP _ _ p1 _ (isParamT x) H).
Defined.

(* USELESS THEOREM *)
Lemma cng_commT  x xi m0 m1 pi t :
SetVars.eqb x xi = false -> 
@teI X fsI (cng (cng pi x m0) xi m1) t = @teI X fsI (cng (cng pi xi m1) x m0) t.
Proof. intro i.
revert pi.
induction t; intro pi.
simpl.
unfold cng.
pose (n3:= proj1 (not_iff_compat (SetVars.eqb_eq x xi)) ).
pose (n4:= n3 (proj2 (not_true_iff_false (SetVars.eqb x xi)) i)).
destruct (SetVars.eq_dec sv xi).
rewrite -> e.
rewrite -> (Facts.eqb_refl xi).
destruct (SetVars.eq_dec x xi).
destruct (n4 e0).
pose (hi := (not_eq_sym n)).
pose (ih:= not_true_is_false _ (proj2 (not_iff_compat (SetVars.eqb_eq xi x)) hi)).
rewrite ih.
reflexivity.
pose (ih:= not_true_is_false _ (proj2 (not_iff_compat (SetVars.eqb_eq sv xi)) n)).
rewrite -> ih.
reflexivity.
simpl.
apply ap.
apply eq_nth_iff.
intros p1 p2 HU.
rewrite -> (nth_map (teI (cng (cng pi x m0) xi m1)) v p1 p2 HU).
rewrite -> (nth_map (teI (cng (cng pi xi m1) x m0)) v p2 p2 eq_refl).
apply H.
Defined.

Lemma weafunT pi mu (q: forall z, pi z = mu z) t :
@teI X fsI pi t = @teI X fsI mu t.
Proof.
induction t.
+ simpl. exact (q sv).
+ simpl. apply ap.
  apply eq_nth_iff.
  intros p1 p2 HU.
  rewrite -> (nth_map (teI pi) v p1 p2 HU).
  rewrite -> (nth_map (teI mu) v p2 p2 eq_refl).
  apply H.
Defined.

Lemma weafunF (pi mu:SetVars.t->X) (q: forall z, pi z = mu z) fi
: @foI X fsI prI pi fi <-> @foI X fsI prI mu fi.
Proof.
revert pi mu q.
induction fi.
intros pi mu q.
+ simpl.
  apply EqualThenEquiv.
  apply ap.
  apply eq_nth_iff.
  intros p1 p2 HU.
  rewrite -> (nth_map (teI pi) t p1 p2 HU).
  rewrite -> (nth_map (teI mu) t p2 p2 eq_refl).
  apply weafunT.
  apply q.
+ simpl. reflexivity.
+ simpl. intros. 
  rewrite -> (IHfi1 pi mu q).
  rewrite -> (IHfi2 pi mu q).
  reflexivity.
+ simpl. intros. 
  rewrite -> (IHfi1 pi mu q).
  rewrite -> (IHfi2 pi mu q).
  reflexivity.
+ simpl.
  unfold OImp.
  split;
  intros;
  apply (IHfi2 pi mu q);
  apply H;
  apply (IHfi1 pi mu q);
  apply H0. (*twice*)
+ simpl.
  split.
  * intros.
    rewrite IHfi.
    apply H with (m:=m).
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    symmetry.
    apply q.
  * intros.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    apply q.
+ simpl.
  split.
  * intros.
destruct H as [m H].
exists m.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    symmetry.
    apply q.
  * intros.
destruct H as [m H].
exists m.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    apply q.
Defined.

Lemma cng_commF_EQV  xe xi m0 m1 pi fi :
SetVars.eqb xe xi = false -> 
(@foI X fsI prI (cng (cng pi xe m0) xi m1) fi <-> @foI X fsI prI (cng (cng pi xi m1) xe m0) fi).
Proof.
intros H.
apply weafunF.
intros z.
unfold cng.
destruct (SetVars.eqb z xi) eqn:e0, (SetVars.eqb z xe) eqn:e1.
pose (U0:= proj1 (SetVars.eqb_eq z xi) e0).
rewrite U0 in e1.
pose (U1:= proj1 (SetVars.eqb_eq xi xe) e1).
symmetry in U1.
pose (U2:= proj2 (SetVars.eqb_eq xe xi) U1).
rewrite U2 in H.
inversion H.
reflexivity. reflexivity. reflexivity.
Defined.

Lemma lem2caseAtom : forall (p : PSV) (t0 : Vector.t Terms (psv p))
(t : Terms) (xi : SetVars.t) (pi : SetVars.t->X)
(r:Fo) (H:(substF t xi (Atom p t0)) = Some r) ,
@foI X fsI prI pi r <-> @foI X fsI prI (cng pi xi (@teI X fsI pi t)) (Atom p t0).
Proof.
intros.
+ simpl in H.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply EqualThenEquiv.
  apply ap.
  apply 
    (proj1 (
      eq_nth_iff X (psv p) 
      (Vector.map (teI pi) (Vector.map (substT t xi) t0))
      (Vector.map (teI (cng pi xi (teI pi t))) t0)
    )).
  rename t0 into v.
  intros p1 p2 H0.
  rewrite -> (nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0).
  rewrite -> (nth_map (teI (cng pi xi (teI pi t))) v p2 p2 ).
  rewrite -> (nth_map (substT t xi) v p2 p2 eq_refl).
  apply lem1. reflexivity.
Defined.

Lemma NPthenNCACVT x t m pi: 
 isParamT x t = false -> 
(@teI X fsI (cng pi x m) t) = (@teI X fsI pi t).
Proof.
intros H.
induction t.
unfold cng.
simpl in * |- *.
rewrite H.
reflexivity.
simpl in * |- *.
apply ap.
apply eq_nth_iff.
intros.
rewrite -> (nth_map (teI (cng pi x m)) v p1 p2 H1).
rewrite -> (nth_map (teI pi) v p2 p2 eq_refl).
apply H0.
apply (all_then_someP Terms (fsv f) p2 v (isParamT x) H).
Defined.

Lemma EXISTS_EQV : forall A0 A1 : X -> Prop, 
(forall m, A0 m <-> A1 m) -> ((exists m:X, A0 m) <-> (exists m:X, A1 m)).
Proof.
intros A0 A1 H0.
split.
+ intros.
  destruct H as [x Hx].
  exists x.
  rewrite <- H0.
  exact (Hx).
+ intros.
  destruct H as [x Hx].
  exists x.
  rewrite -> H0.
  exact (Hx).
Defined.

Lemma eqb_comm x xi : SetVars.eqb xi x =  SetVars.eqb x xi.
Proof.
destruct (SetVars.eqb xi x) eqn:e1.
symmetry.
pose (Y:= proj1 (SetVars.eqb_eq xi x) e1).
rewrite -> Y at 1.
rewrite <- Y at 1.
exact e1.
symmetry.
pose (n3:= proj2 (not_iff_compat (SetVars.eqb_eq x xi)) ).
apply not_true_iff_false.
apply n3.
intro q.
symmetry in q.
revert q.
fold (xi <> x).
pose (n5:= proj1 (not_iff_compat (SetVars.eqb_eq xi x)) ).
apply n5.
apply not_true_iff_false.
exact e1.
Defined.

Lemma NPthenNCACVF xi fi m mu :  isParamF xi fi = false ->
@foI X fsI prI (cng mu xi m) fi <-> @foI X fsI prI mu fi.
Proof.
revert mu.
induction fi; intro mu;
intro H;
simpl in * |- *.
* apply EqualThenEquiv.
  apply ap.
  apply eq_nth_iff.
  intros p1 p2 H0.
  rewrite -> (nth_map (teI (cng mu xi m)) t p1 p2 H0).
  rewrite -> (nth_map (teI mu) t p2 p2 eq_refl).
  apply NPthenNCACVT.
  apply (all_then_someP Terms (psv p) p2 t (isParamT xi) H).
  (*1st done *)
* firstorder.
* apply AND_EQV.
  apply IHfi1. destruct (orb_elim _ _ H). apply H0.
  apply IHfi2. destruct (orb_elim _ _ H). apply H1.
* apply OR_EQV.
  apply IHfi1. destruct (orb_elim _ _ H). apply H0.
  apply IHfi2. destruct (orb_elim _ _ H). apply H1.
* apply IMP_EQV.
  apply IHfi1. destruct (orb_elim _ _ H). apply H0.
  apply IHfi2. destruct (orb_elim _ _ H). apply H1.
* apply FORALL_EQV. intro m0.
  destruct (SetVars.eqb x xi) eqn:e1.
  pose (C:=proj1 (SetVars.eqb_eq x xi) e1).
  rewrite <- C.
  pose (D:= twice_the_same mu x m m0).
  exact (weafunF _ _ D fi).
  rewrite cng_commF_EQV.
  (*here inductive IHfi*)
  apply IHfi.
  exact H.
  rewrite <-(eqb_comm xi x).
  exact e1.
* apply EXISTS_EQV. intro m0.
  fold (cng (cng mu xi m) x m0).
  fold (cng mu x m0).
  destruct (SetVars.eqb x xi) eqn:e1.
  pose (C:=proj1 (SetVars.eqb_eq x xi) e1).
  rewrite <- C.
  pose (D:= twice_the_same mu x m m0).
  exact (weafunF _ _ D fi).
  rewrite cng_commF_EQV.
  (*here inductive IHfi*)
  apply IHfi.
  exact H.
  rewrite <-(eqb_comm xi x).
  exact e1.
Defined.

Definition lem2 (t : Terms) : forall (fi : Fo) (xi : SetVars.t) 
(pi : SetVars.t->X)
(r:Fo) (H:(substF t xi fi) = Some r), (*(SH:sig (fun(r:Fo)=>(substF t xi fi) = Some r)),*)
(@foI X fsI prI pi r)<->(@foI X fsI prI (cng pi xi (@teI X fsI pi t)) fi).
Proof.
fix lem2 1.
(*H depends on t xi fi r *)
intros fi xi pi r H.
revert pi r H.
induction fi;
intros pi r H.
+ apply lem2caseAtom.
  exact H.
+ inversion H. simpl. reflexivity.
+ simpl in *|-*.
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  unfold OAnd.
  apply AND_EQV.
  simpl in * |- *.
  * apply (IHfi1 pi f1 eq_refl).
  * apply (IHfi2 pi f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in *|-*.
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl in * |- *.
  apply OR_EQV.
  * apply (IHfi1 pi f1 eq_refl).
  * apply (IHfi2 pi f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in *|-*.
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl in * |- *.
  apply IMP_EQV.
  * apply (IHfi1 pi f1 eq_refl).
  * apply (IHfi2 pi f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in * |- *.
  destruct (SetVars.eqb x xi) eqn:l2.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply FORALL_EQV.
  intro m.
  assert (RA : x = xi).
  apply (SetVars.eqb_eq x xi ).
  exact l2.
  rewrite <- RA.
  rewrite -> (weafunF (cng (cng pi x (teI pi t)) x m) (cng pi x m) 
   (twice_the_same pi x (teI pi t) m) fi).
  firstorder.
  destruct (isParamF xi fi) eqn:l1.
  pose(xint := (isParamT x t)).
  destruct (isParamT x t) eqn:l3.
  inversion H.
  destruct (substF t xi fi) eqn:l4.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply FORALL_EQV.
  intro m.
  rewrite cng_commF_EQV.
  2 : {
    rewrite -> eqb_comm .
    exact l2.
  }
  rewrite <- (NPthenNCACVT x t m pi l3).
  exact (IHfi (cng pi x m) f eq_refl).
  inversion H.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply FORALL_EQV.
  intro m.
  rewrite cng_commF_EQV.
  symmetry.
  exact (NPthenNCACVF xi fi (teI pi t) (cng pi x m) l1).
  rewrite -> (eqb_comm x xi).
  exact l2. (* end of FORALL case*)
+ simpl in * |- *.
  destruct (SetVars.eqb x xi) eqn:l2.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply EXISTS_EQV.
  intro m.
  assert (RA : x = xi).
  apply (SetVars.eqb_eq x xi ).
  exact l2.
  rewrite <- RA.
  rewrite -> (weafunF (cng (cng pi x (@teI X fsI pi t)) x m) (cng pi x m) 
   (twice_the_same pi x (@teI X fsI pi t) m) fi).
  firstorder.
  destruct (isParamF xi fi) eqn:l1.
  pose(xint := (isParamT x t)).
  destruct (isParamT x t) eqn:l3.
  inversion H.
  destruct (substF t xi fi) eqn:l4.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply EXISTS_EQV.
  intro m.
  fold (cng  pi x m ).
  fold (cng  (cng pi xi (@teI X fsI pi t)) x m ).
  rewrite cng_commF_EQV.
  2 : {
    rewrite -> eqb_comm .
    exact l2.
  }
  rewrite <- (NPthenNCACVT x t m pi l3).
  exact (IHfi (cng pi x m) f eq_refl).
  inversion H.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply EXISTS_EQV.
  intro m.
  fold (cng  pi x m ).
  fold (cng  (cng pi xi (@teI X fsI pi t)) x m ).
  rewrite cng_commF_EQV.
  symmetry.
  exact (NPthenNCACVF xi fi (teI pi t) (cng pi x m) l1).
  rewrite -> (eqb_comm x xi).
  exact l2.
Defined. (* END OF LEM2 *)
End Lem2.

Lemma UnivInst : forall (fi:Fo) (pi:SetVars.t->X) (x:SetVars.t) (t:Terms)
(r:Fo) (H:(substF t x fi)=Some r), @foI X fsI prI pi (Impl (Fora x fi) r).
Proof.
intros fi pi x t r H.
simpl.
intro H0.
apply (lem2 t fi x pi r H).
apply H0.
Defined.

Lemma ExisGene : forall (fi:Fo) (pi:SetVars.t->X) (x:SetVars.t) (t:Terms)
(r:Fo) (H:(substF t x fi)=Some r), @foI X fsI prI pi (Impl r (Exis x fi)).
Proof.
intros fi pi x t r H.
simpl.
intro H0.
exists (@teI X fsI pi t).
fold (cng pi x (@teI X fsI pi t)).
apply (lem2 t fi x pi r H).
apply H0.
Defined.

(* PROOF OF THE SOUNDNESS *)
Theorem correct (f:Fo) (l:list Fo) (m : PREPR l f) 
(lfi : forall  (h:Fo), (InL h l)-> forall (val:SetVars.t->X), 
(@foI X fsI prI val h)) : 
forall (val:SetVars.t->X), @foI X fsI prI val f.
Proof.
revert lfi.
induction m (* eqn: meq *); intros lfi val.
+ exact (lfi A i _).
+ destruct a eqn:k.
  ++ destruct p.
     * simpl.
       intros a0 b.
       exact a0.
     * simpl.
       intros a0 b c.
       exact (a0 c (b c)).
  ++ simpl in *|-*.
  (*destruct (substF t xi ph) eqn: j.*)
  apply (UnivInst ph val xi t r s).
  (*simpl. firstorder.*)
  ++ simpl in *|-*.
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
  intro val2.
  apply lfi.
  exact B.
Defined.
(** SOUNDNESS IS PROVED **)

(*Check foI.*)

(*
Theorem completeness (f:Fo)
(H : forall (val:SetVars.t->X), @foI X fsI prI val f)
 : 
exists  (l:list Fo)
(lfi : forall  (h:Fo), (InL h l)-> forall (val:SetVars.t->X), 
(@foI X fsI prI val h)), PREPR l f
.
Proof.
Defined. *)
End cor.
(*Print Assumptions correct.*)


(*End sec0.*)
End Soundness_mod.
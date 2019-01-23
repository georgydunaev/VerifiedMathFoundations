Require Import FunctionalExtensionality.
Require Import Logic.Classical_Prop.
Require Import Logic.Classical_Pred_Type.
Require Import Logic.ChoiceFacts.
Require Import Logic.IndefiniteDescription.

Require Export Coq.Lists.List.
Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.

Require Import Relations. (*for transitive*)
Require Import Coq.Structures.Equalities.
Module Lang (PropVars : UsualDecidableTypeFull).
 (** Language of the propositional logic. **)
 Inductive Fo :=
 |Atom (p:PropVars.t) :> Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
 .

 Notation " x --> y ":=(Impl x y) (at level 80, right associativity).
 Notation " x -/\ y ":=(Conj x y) (at level 80).
 Notation " x -\/ y ":=(Disj x y) (at level 80).
 Notation " -. x " :=(Impl x Bot) (at level 80).
 Definition Neg (A:Fo):Fo := Impl A Bot.
 Definition Top:Fo := Neg Bot.


 (** ==== Contexts ==== **)
 Theorem lf2ft :(list Fo) -> (Fo->Type).
 Proof. intros lf f. exact (InL f lf). Defined.
 (*Coercion lf2ft. : (list Fo) >-> (Fo->Type).*)

 Inductive empctx : Fo -> Type :=. (*Empty context*)

 Definition add2ctx (A:Fo) (l:Fo->Type) : Fo->Type 
 := fun f=> sum (A=f) (l f). (* add head *)

 Definition cnctctx (l1 l2:Fo->Type) : Fo->Type 
 := fun f=> sum (l1 f) (l2 f). (* concat *)

 Lemma addempeqv (il:Fo->Type) : forall (f:Fo), 
 (cnctctx il empctx) f -> il f.
 Proof. intros f q. destruct q. exact i. destruct e. Defined.


 (* Proposional calculus' axioms (Intuitionistic) *)
 Inductive PROCAI : Fo -> Type :=
 | Ha1  : forall A B, PROCAI (A-->(B-->A))
 | Ha2  : forall A B C, PROCAI ((A-->(B-->C))-->((A-->B)-->(A-->C)))
 | Ha3  : forall A B, PROCAI ((A-/\ B)--> A)
 | Ha4  : forall A B, PROCAI ((A-/\ B)--> B)
 | Ha5  : forall A B, PROCAI (A-->(B-->(A-/\B)))
 | Ha6  : forall A B, PROCAI (A-->(A-\/ B))
 | Ha7  : forall A B, PROCAI (B-->(A-\/ B))
 | Ha8  : forall A B C, PROCAI ((A-->C)-->((B-->C)-->((A-\/ B)-->C)))
 | Ha9  : forall A B, PROCAI (-.A --> (A --> B) )
 | Ha10  : forall A B, PROCAI ((A-->B)-->(A -->-.B)-->-.A)
 .

 Inductive PROCA : Fo -> Type :=
 | Intui :> forall f, PROCAI f -> PROCA f
 | Ha11  : forall A, PROCA (A -\/ -.A)
 .

 Section PR.
  Context (ctx:Fo -> Type).
  Context (axs:Fo -> Type).
  Inductive PR : Fo -> Type :=
  | hyp (A : Fo) : (*InL A ctx*) ctx A -> PR A
  | Hax :> forall (A : Fo), (axs A) -> PR A
  | MP (A B: Fo) : (PR A)->(PR (Impl A B))->(PR B)
  .
 End PR.

 Definition AtoA_I {ctx} (A:Fo) : PR ctx PROCAI (A-->A).
 Proof.
 apply MP with (A-->(A-->A)).
 apply Hax, Ha1. (* apply (Hax _ _ (Ha1 _ _)).*)
 apply MP with (A-->((A-->A)-->A)) (*1:=I*).
 apply Hax, Ha1.
 apply Hax, Ha2.
 Defined.

 Theorem subcalc {ctx} {B} : (PR ctx PROCAI B) -> (PR ctx PROCA B).
 Proof.
 intro m.
 induction m.
 + apply hyp. assumption.
 + apply Hax. apply Intui. assumption.
 + eapply MP. exact IHm1. exact IHm2.
 Defined.

 Definition AtoA {ctx} (A:Fo) : PR ctx PROCA (A-->A) 
  := subcalc (AtoA_I A).

 Definition a1i_I (A B : Fo)(l : Fo->Type):
 (PR l PROCAI B)->(PR l PROCAI (Impl A B)).
 Proof.
 intros x.
 apply MP with (A:= B).
 exact x.
 eapply (*subcalc_OE,*) Hax,Ha1.
 Defined.

 Definition a1i (A B : Fo)(l : Fo->Type):
 (PR l PROCA B)->(PR l PROCA (Impl A B)).
 Proof.
 intros x.
 apply MP with (A:= B).
 exact x.
 eapply (*subcalc_OE,*) Hax, Intui, Ha1.
 Defined.

 (*Fixpoint *)
 Theorem weak (axs:Fo -> Type)
 (A F:Fo) (*l :list Fo*) (l:Fo->Type)
 (x: (PR l axs F)) : (PR (add2ctx A l) axs F).
 Proof.
 induction x.
 + apply hyp.
   right.
   assumption.
 + apply Hax, a.
 + exact (MP (add2ctx A l) axs A0 B IHx1 IHx2).
 Defined.

 (*Fixpoint*)
 Definition weaken axs (F:Fo) (li l :Fo->Type) (x: (PR l axs F))
 (*{struct li}*): (PR (cnctctx li l) axs F).
 Proof.
 induction x.
 + apply hyp.
   right.
   assumption.
 + apply Hax, a.
 + exact (MP (cnctctx li l) _ A B IHx1 IHx2).
 (*destruct li.
 simpl.
 exact x.
 simpl.
 simple refine (@weak _ f F (li ++ l)%list _).
 apply weaken.
 exact x.*)
 Defined.

 (* ==== Deduction ==== *)
 Theorem DedI (A B:Fo)(il:Fo->Type)(m:(PR (add2ctx A il) PROCAI B)) 
 :(PR il PROCAI (A-->B)).
 Proof.
 induction m.
 + (*unfold InL in c.*)
   simpl in c .
   destruct c .
   * rewrite <- e.
     pose (J:=weaken PROCAI _ il empctx (AtoA_I A )).
     (* rewrite app_nil_r in J.*)
     induction J.
     - destruct c.
       apply hyp. assumption.
       destruct e0.
     - apply Hax. assumption.
     - apply MP with (A:=A1); assumption.
     (*rewrite - addempeqv in J.
     exact J.*)
   * simpl in i.
     apply a1i_I.
     apply hyp with (ctx:=il) (1:=i).
 + apply a1i_I.
   apply Hax, a.
 + apply MP with (A-->A0).
   exact IHm1.
   apply MP with (A-->A0-->B).
   exact IHm2.
   apply Hax.
   apply Ha2.
 Defined.

 Theorem invDedI (A B:Fo)(il:Fo->Type)(m:(PR il PROCAI (A-->B)))
 :(PR (add2ctx A il) PROCAI B).
 Proof.
 pose(U:=(weak PROCAI A _ il m)).
 assert (N:PR (add2ctx A il) PROCAI A).
 apply hyp. simpl. left. reflexivity.
 apply MP with A.
 exact N.
 exact U.
 Defined.


 Theorem Ded (A B:Fo)(il:Fo->Type)(m:(PR (add2ctx A il) PROCA B)) 
 :(PR il PROCA (A-->B)).
 Proof.
 induction m.
 + (*unfold InL in c.*)
   simpl in c .
   destruct c .
   * rewrite <- e.
     pose (J:=weaken PROCA _ il empctx (AtoA A)).
     (* rewrite app_nil_r in J.*)
     induction J.
     - destruct c.
       apply hyp. assumption.
       destruct e0.
     - apply Hax. assumption.
     - apply MP with (A:=A1); assumption.
     (*rewrite - addempeqv in J.
     exact J.*)
   * simpl in i.
     apply a1i.
     apply hyp with (ctx:=il) (1:=i).
 + apply a1i.
   apply Hax, a.
 + apply MP with (A-->A0).
   exact IHm1.
   apply MP with (A-->A0-->B).
   exact IHm2.
   apply Hax.
   apply Intui, Ha2.
 Defined.

 (* Order of the context is not important. *)
 Lemma permut axs L1 L2 A (H: forall x, L1 x -> L2 x)
 : (PR L1 axs A) -> (PR L2 axs A).
 Proof.
 intro m.
 induction m.
 + apply hyp. apply (H A c).
 + apply Hax. apply a.
 + apply MP with A. exact IHm1. exact IHm2.
 Defined.

 Lemma PR_eqv C1 C2 A F (Q:forall x,C1 x <-> C2 x) (H:PR C1 A F) 
  : PR C2 A F.
 Proof.
 induction H.
 - apply Q in c. apply hyp. assumption.
 - apply Hax. assumption.
 - apply MP with (A:=A0); assumption.
 Defined.


 (*
    Classical semantics for the classical
    propositional logic("CPRoL"). (definitions)
 *)
 Section foI_cl.
  Context (val:PropVars.t->Prop).
  Fixpoint foI_cl (f:Fo) : Prop := 
  match f with 
   | Atom p => (val p)
   | Bot => False
   | f1 -/\ f2 => (foI_cl f1) /\ (foI_cl f2)
   | f1 -\/ f2 => (foI_cl f1) \/ (foI_cl f2)
   | f1 --> f2 => (foI_cl f1) -> (foI_cl f2)
  end.
 End foI_cl.

 (* Soundness of the classical semantics *)
 Theorem sou_cl f (H:PR empctx PROCA f) :
    forall (val:PropVars.t->Prop), foI_cl val f.
 Proof. intro val.
  induction H;firstorder.
  + induction a;firstorder.
    * induction p; firstorder.
    * simpl.
      destruct (classic (foI_cl val A)); firstorder.
 Defined.

 (*
    Double negation semantics for the classical
    propositional logic("CPRoL"). (definitions)
 *)
 Section foI_dn. (* Entails for double negation. *)
  Context (val:PropVars.t->Prop).
  Fixpoint foI_dn (f:Fo) : Prop := 
  match f with 
   | Atom p => (((val p)->False)->False)
   | Bot => False
   | f1 -/\ f2 => foI_dn f1 /\ foI_dn f2
   | f1 -\/ f2 => (((foI_dn f1 \/ foI_dn f2)->False)->False)
   | f1 --> f2 => (foI_dn f1) -> (foI_dn f2)
  end.
 End foI_dn.

 (* Soundness of the double-negation semantics *)
 Theorem sou_dn f (H:PR empctx PROCA f) :
    forall (val:PropVars.t->Prop), foI_dn val f.
 Proof. intro val.
  induction H;firstorder.
  + induction a;firstorder.
    * induction p; firstorder.
        simpl. intros.
        induction C ;firstorder.
 Defined.

 (* Boolean semantics for classical 
    propositional logic. (definitions) *)
 Section foI_bo.
  Context (val:PropVars.t->bool).
  Fixpoint foI_bo (f:Fo) : bool := 
  match f with 
   | Atom p => (val p)
   | Bot => false
   | f1 -/\ f2 => andb (foI_bo f1) (foI_bo f2)
   | f1 -\/ f2 => orb (foI_bo f1) (foI_bo f2)
   | f1 --> f2 => implb (foI_bo f1) (foI_bo f2)
  end.
 End foI_bo.

 (*Soundness of the boolean semantics *)
 Theorem sou_bo f (H:PR empctx PROCA f) :
    forall (val:PropVars.t->bool), (foI_bo val f)=true.
 Proof. intro val.
 induction H.
 + destruct c.
 + induction a.
   * induction p; simpl; destruct (foI_bo val A), (foI_bo val B); 
     try destruct (foI_bo val C); firstorder.
   * simpl; destruct (foI_bo val A); firstorder.
 + simpl in * |- *; destruct (foI_bo val A), (foI_bo val B); firstorder.
 Defined.


 (*
   Kripke semantics for the intuitionistic
   proposition logic.
 *)
 Open Scope type_scope.
 Section WR.
 Context (W:Set) (R:W->W->Prop) (R_transitive : transitive W R)
 (R_reflexive : reflexive W R).
 Context (vf:PropVars.t -> W -> Prop) 
 (mvf: forall (x y : W)(p:PropVars.t), vf p x -> R x y -> vf p y).

 Section foI_kr. (* Entails *)
 Fixpoint foI_kr (x:W) (f:Fo) : Prop := 
 match f with 
   | Atom p => (vf p x)
   | Bot => False
   | f1 -/\ f2 => foI_kr x f1 /\ foI_kr x f2
   | f1 -\/ f2 => foI_kr x f1 \/ foI_kr x f2
   | f1 --> f2 =>
 (forall y:W, R x y -> ((foI_kr y f1) -> (foI_kr y f2)))
 end. (*foI x f1 =-> foI x f2*)
 End foI_kr.

 Theorem utv1 x f: foI_kr x (f-->Bot) <-> forall y, R x y -> not (foI_kr y f).
 Proof.
 simpl. unfold not. reflexivity.
 (* split.
 + intros.
 simpl in H. destruct (H y H0).
 * exact H1.
 * destruct H1.
 + intros. left. exact (H y H0).*)
 Defined.

 Theorem utv2 x y f : foI_kr x f -> R x y -> foI_kr y f.
 Proof.
 intros H1 H2.
 induction f.
 + simpl in * |- *.
   apply mvf with x. apply H1. apply H2. (* , H2, H1 *)
 + exact H1.
 + simpl in * |- *.
   destruct H1 as [u1 u2].
   exact (conj (IHf1 u1) (IHf2 u2)).
 + simpl in * |- *.
   destruct H1 as [u1|u2].
   left. exact (IHf1 u1).
   right. exact (IHf2 u2).
 + simpl in * |- *.
   intros.
   apply H1.
   * apply (R_transitive x y y0 H2 H). (* !!! "transitivity y." *)
   * exact H0.
 Defined.

 (* Soundness of the Kripke semantics of IPro *)
 Theorem sou_kr f (H:PR empctx PROCAI f) : forall x, foI_kr x f.
 Proof.
 induction H.
 + destruct c. (*simpl in i. destruct i.*)
 + induction a.
   * simpl. intros.
     simpl in * |- *.
     apply utv2 with (x:=y).
     - exact H0.
     - exact H1.
   * simpl. intros.
 eapply (H0 y1 _ _ y1).
 apply R_reflexive.
 apply H2.
 apply H3.
 apply H4.
 (*unshelve eapply (H0 y0 _ _ y1 H3).
 - exact H1.
 - apply utv2 with y1.
   exact H4.
 simpl in * |- *.
 admit.*)
   * simpl. intros. destruct H0 as [LH0 RH0]. exact LH0.
   * simpl. intros. destruct H0 as [LH0 RH0]. exact RH0.
   * simpl. intros x y pxy yA z pyz zB. split.
     exact (utv2 y z A yA pyz).
    exact zB.
   * simpl. intros x y pxy H. left. exact H.
   * simpl. intros x y pxy H. right. exact H.
   * simpl. intros.
     destruct H4.
     - unshelve eapply H0. 2: exact H4. exact (R_transitive y y0 y1 H1 H3).
     - unshelve eapply H2. exact H3. exact H4.
   * simpl. intros. exfalso. eapply H0 with y0. exact H1. exact H2.
   * simpl. intros. 
(*eapply H2.
exact H3.
exact H4.*)
admit.
 + simpl in * |- *.
   intro x.
   unshelve apply (IHPR2 x).
   unshelve apply R_reflexive.
   unshelve apply IHPR1.
   Unshelve.
   exact (R_transitive y y0 y1 H1 H3).
   exact H4.
 Admitted. (*Defined.*)
 End WR.

End Lang.
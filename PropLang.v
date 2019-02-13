(* LC = Languages and Calculi (N.K. Vereschagin, A.Shen) *)
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

 (* BEGIN experimental *)
 Section exper_1.
 Inductive PROCAI_1 : Fo -> Type :=
 | eHa1  (A B:PropVars.t) :  PROCAI_1 (A-->(B-->A))
 | eHa2  (A B:PropVars.t): forall (C:PropVars.t),
          PROCAI_1 ((A-->(B-->C))-->((A-->B)-->(A-->C)))
 | eHa3  (A B:PropVars.t): PROCAI_1 ((A-/\ B)--> A)
 | eHa4  (A B:PropVars.t): PROCAI_1 ((A-/\ B)--> B)
 | eHa5  (A B:PropVars.t): PROCAI_1 (A-->(B-->(A-/\B)))
 | eHa6  (A B:PropVars.t): PROCAI_1 (A-->(A-\/ B))
 | eHa7  (A B:PropVars.t): PROCAI_1 (B-->(A-\/ B))
 | eHa8  (A B:PropVars.t): forall (C:PropVars.t),
          PROCAI_1 ((A-->C)-->((B-->C)-->((A-\/ B)-->C)))
 | eHa9  (A B:PropVars.t): PROCAI_1 (-.A --> (A --> B) )
 | eHa10 (A B:PropVars.t) : PROCAI_1 ((A-->B)-->(A -->-.B)-->-.A)
 .
 End exper_1.
 (* END experimental *)



 (** ==== Contexts ==== **)
 Theorem lf2ft :(list Fo) -> (Fo->Type).
 Proof. intros lf f. exact (InL f lf). Defined.
 (* Coercion lf2ft. : (list Fo) >-> (Fo->Type). *)

 Inductive empctx : Fo -> Type :=. (* empty context *)

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

 Theorem exper1 (A:Fo): (PROCAI_1 A) -> (PROCAI A).
 Proof.
 intro H.
 destruct H; constructor.
 Defined.

 (* Proposional calculus' axioms (Classical) *)
 Inductive PROCA : Fo -> Type :=
 | Intui :> forall f, PROCAI f -> PROCA f
 | Ha11  : forall A, PROCA (A -\/ -.A)
 .

 Section PR.
  Context (axs:Fo -> Type).
  Context (ctx:Fo -> Type).
  Inductive PR : Fo -> Type :=
  | hyp (A : Fo) : (*InL A ctx*) ctx A -> PR A
  | Hax :> forall (A : Fo), (axs A) -> PR A
  | MP (A B: Fo) : (PR A)->(PR (A-->B))->(PR B)
  .
 End PR.

 Section LPR. (* Less than PR : no context *)
  Context (axs:Fo -> Type).
  Inductive LPR : Fo -> Type :=
  | lHax :> forall (A : Fo), (axs A) -> LPR A
  | lMP (A B: Fo) : (LPR A)->(LPR (A-->B))->(LPR B)
  .
 End LPR.

 (* trivial *)
 Theorem LPR2PR axs A : LPR axs A -> PR axs empctx A.
 Proof.
 intro H. induction H.
 + apply Hax. exact a.
 + apply MP with A; assumption.
 Defined.

 Theorem PR2LPR axs A : PR axs empctx A -> LPR axs A.
 Proof.
 intro H. induction H.
 + destruct c.
 + apply lHax. exact a.
 + apply lMP with A; assumption.
 Defined.

 Theorem experB1 {ctx} (A:Fo) :
  (PR PROCAI_1 ctx A) -> (PR PROCAI ctx A).
 Proof.
 intro H.
 induction H.
 apply hyp. exact c.
 apply Hax, exper1, a.
 eapply MP. exact IHPR1. exact IHPR2.
 Defined.

Section subst_sec.
 Context (p:PropVars.t) (B:Fo).

Check p.
Check PropVars.eq_dec p p.
Locate "+".
Check sumbool.
 Fixpoint Sub (A:Fo) : Fo
  := match A with
   | Atom q => match (PropVars.eq_dec p q) with
               | left u => B
               | right v => (Atom q)
               end
   | Bot => Bot
   | Conj x1 x2 => Conj (Sub x1) (Sub x2)
   | Disj x1 x2 => Disj (Sub x1) (Sub x2)
   | Impl x1 x2 => Impl (Sub x1) (Sub x2)
   end.

Section ctx_Sub_sec.
Context (wct:Fo->Type).
Inductive ctx_Sub : Fo->Type 
:= | ctx_Sub_cons (f:Fo): wct f -> ctx_Sub (Sub f).
End ctx_Sub_sec.

(* REVERSE:
 Definition Sub_ctx :(Fo->Type)->(Fo->Type).
 Proof.
 intros wct f.
 exact (wct (Sub f)).
 Defined.*)

 Section MPR. (* More than PR : add substitution *)
  Context (axs:Fo -> Type).
  Inductive MPR : forall (ctx:Fo -> Type), Fo -> Type :=
  | mhyp (ctx:Fo -> Type) (A : Fo) : (*InL A ctx*) ctx A -> MPR ctx A
  | mHax (ctx:Fo -> Type) : forall (A : Fo), (axs A) -> MPR ctx A
  | mMP (ctx:Fo -> Type) (A B: Fo) :
     (MPR ctx A)->(MPR ctx (Impl A B))->(MPR ctx B)
  | mSub (ctx:Fo -> Type) (A B:Fo) (p:PropVars.t) :
    (MPR ctx A)->MPR (ctx_Sub ctx) (Sub A)
  .
 End MPR.
(*!!!
 Theorem MPR2PR axs ctx A : MPR axs ctx A -> PR axs ctx A.
 Proof.
 intro H. induction H.
 + apply mlHax. exact a.
 + apply mlMP with A; assumption.
 Defined.
*)


 Section MLPR. (* More than LPR : add substitution *)
  Context (axs:Fo -> Type).
  Inductive MLPR : Fo -> Type :=
  | mlHax :> forall (A : Fo), (axs A) -> MLPR A
  | mlMP (A B: Fo) : (MLPR A)->(MLPR (Impl A B))->(MLPR B)
  | mlSub (A B:Fo) (p:PropVars.t) : (MLPR A)->MLPR (Sub A)
  .
 End MLPR.

 (* trivial *)
 Theorem LPR2MLPR axs A : LPR axs A -> MLPR axs A.
 Proof.
 intro H. induction H.
 + apply mlHax. exact a.
 + apply mlMP with A; assumption.
 Defined.

 Lemma PROCAI_Sub (A : Fo) (a : PROCAI A) : PROCAI (Sub A).
 Proof.
 destruct a; simpl; constructor.
 Defined.

 Lemma PROCA_Sub (A : Fo) (a : PROCA A) : PROCA (Sub A).
 Proof.
 destruct a as [g p0| A].
 + apply Intui. eapply PROCAI_Sub, p0.
 + simpl. apply Ha11.
 Defined.

Section ghj_sec.
 Local Inductive ghj : Fo->Type := | ghj_c : ghj p.
 Context (jkl: (p:Fo)<>B).
 Local Lemma j1 : ~ forall (axs:Fo->Prop) (A : Fo), axs A -> axs (Sub A).
 Proof.
 intro H.
 assert (Q:=H (ghj) p ghj_c).
 inversion Q.
 destruct (PropVars.eq_dec p p).
 + compute in H1.
   simpl in H1.
   exact (jkl H1).
 + apply n.
   constructor.
 Defined.
End ghj_sec.

 (* Calculus with*)
 Section axs_resp_Sub.
 Context {axs:Fo -> Type} (j1:forall A, (axs A)->axs (Sub A)).
 Theorem  PR_Sub' {ctx} (A:Fo):
  (PR axs ctx A) -> (PR axs (ctx_Sub ctx) (Sub A)) .
 Proof.
 intro a.
 induction a.
 + apply hyp. constructor. exact c.
 + apply Hax. apply j1, a.
 + eapply MP. exact IHa1. exact IHa2.
 Defined.

 Theorem  LPR_Sub'  (A:Fo):
  (LPR axs A) -> (LPR axs (Sub A)) .
 Proof.
 intro a.
 induction a.
 + apply lHax. apply j1, a.
 + eapply lMP. exact IHa1. exact IHa2.
 Defined.

 Theorem MLPR2LPR A : MLPR axs A -> LPR axs A.
 Proof.
 intro H. induction H.
 + apply lHax. exact a.
 + apply lMP with A; assumption.
 + apply LPR_Sub'. assumption.
 Defined.
 End axs_resp_Sub.

 Theorem  PR_Sub {ctx} (A:Fo) :
  (PR PROCAI ctx A) -> (PR PROCAI (ctx_Sub ctx) (Sub A)) .
 Proof.
 intro a.
 induction a.
 + apply hyp. constructor. exact c.
 + apply Hax. destruct a; simpl; constructor.
 + eapply MP. exact IHa1. exact IHa2.
 Defined.


(* "ctx_Sub" preserve empty context *)
Theorem empctx_fix (f:Fo) : ((ctx_Sub empctx) f)->False.
Proof.
intro H.
destruct H as [g E].
destruct E.
Defined.

End subst_sec.

 Definition AtoA_I {ctx} (A:Fo) : PR PROCAI ctx (A-->A).
 Proof.
 apply MP with (A-->(A-->A)).
 apply Hax, Ha1. (* apply (Hax _ _ (Ha1 _ _)).*)
 apply MP with (A-->((A-->A)-->A)) (*1:=I*).
 apply Hax, Ha1.
 apply Hax, Ha2.
 Defined.


 Theorem subcalc {ctx} {B} : (PR PROCAI ctx B) -> (PR PROCA ctx B).
 Proof.
 intro m.
 induction m.
 + apply hyp. assumption.
 + apply Hax. apply Intui. assumption.
 + eapply MP. exact IHm1. exact IHm2.
 Defined.

 Definition AtoA {ctx} (A:Fo) : PR PROCA ctx (A-->A) 
  := subcalc (AtoA_I A).

 Definition a1i_I (A B : Fo)(l : Fo->Type):
 (PR PROCAI l B)->(PR PROCAI l (Impl A B)).
 Proof.
 intros x.
 apply MP with (A:= B).
 exact x.
 eapply (*subcalc_OE,*) Hax,Ha1.
 Defined.

 Definition a1i (A B : Fo)(l : Fo->Type):
 (PR PROCA l B)->(PR PROCA l (Impl A B)).
 Proof.
 intros x.
 apply MP with (A:= B).
 exact x.
 eapply (*subcalc_OE,*) Hax, Intui, Ha1.
 Defined.

 (*Fixpoint *)
 Theorem weak (axs:Fo -> Type)
 (A F:Fo) (*l :list Fo*) (l:Fo->Type)
 (x: (PR axs l F)) : (PR axs (add2ctx A l) F).
 Proof.
 induction x.
 + apply hyp.
   right.
   assumption.
 + apply Hax, a.
 + exact (MP axs (add2ctx A l) A0 B IHx1 IHx2).
 Defined.

 (*Fixpoint*)
 Definition weaken axs (F:Fo) (li l :Fo->Type) (x: (PR axs l F))
 (*{struct li}*): (PR axs (cnctctx li l) F).
 Proof.
 induction x.
 + apply hyp.
   right.
   assumption.
 + apply Hax, a.
 + exact (MP _ (cnctctx li l) A B IHx1 IHx2).
 (*destruct li.
 simpl.
 exact x.
 simpl.
 simple refine (@weak _ f F (li ++ l)%list _).
 apply weaken.
 exact x.*)
 Defined.

 (* ==== Deduction ==== *)
 Theorem DedI (A B:Fo)(il:Fo->Type)(m:(PR PROCAI (add2ctx A il) B)) 
 :(PR PROCAI il (A-->B)).
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

 Theorem invDedI (A B:Fo)(il:Fo->Type)(m:(PR PROCAI il (A-->B)))
 :(PR PROCAI (add2ctx A il) B).
 Proof.
 pose(U:=(weak PROCAI A _ il m)).
 assert (N:PR PROCAI (add2ctx A il) A).
 apply hyp. simpl. left. reflexivity.
 apply MP with A.
 exact N.
 exact U.
 Defined.

 Theorem invDed (A B:Fo)(il:Fo->Type)(m:(PR PROCA il (A-->B)))
 :(PR PROCA (add2ctx A il) B).
 Proof.
 pose(U:=(weak PROCA A _ il m)).
 assert (N:PR PROCA (add2ctx A il) A).
 apply hyp. simpl. left. reflexivity.
 apply MP with A.
 exact N.
 exact U.
 Defined.

 Theorem Ded (A B:Fo)(il:Fo->Type)(m:(PR PROCA (add2ctx A il) B)) 
 :(PR PROCA il (A-->B)).
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
 : (PR  axs L1 A) -> (PR axs L2 A).
 Proof.
 intro m.
 induction m.
 + apply hyp. apply (H A c).
 + apply Hax. apply a.
 + apply MP with A. exact IHm1. exact IHm2.
 Defined.

 Lemma PR_eqv C1 C2 A F (Q:forall x,C1 x <-> C2 x) (H:PR A C1 F)
  : PR A C2 F.
 Proof.
 eapply permut. 2 : exact H. intros x D. apply Q, D.
 (*induction H.
 - apply Q in c. apply hyp. assumption.
 - apply Hax. assumption.
 - apply MP with (A:=A0); assumption.*)
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

 (* Soundness of the classical semantics *) (*LC p.41 thm17*)
 Theorem sou_cl f (H:PR PROCA empctx f) :
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
 Theorem sou_dn f (H:PR PROCA empctx f) :
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
 Theorem sou_bo f (H:PR PROCA empctx f) :
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
 Theorem sou_kr f (H:PR PROCAI empctx f) : forall x, foI_kr x f.
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
     apply (H2 y1 H3 H4 y1).
     apply R_reflexive.
     apply H0.
     eapply R_transitive. exact H1. exact H3. exact H4.
 + simpl in * |- *.
   intro x.
   unshelve apply (IHPR2 x).
   unshelve apply R_reflexive.
   unshelve apply IHPR1.
   Unshelve.
   exact (R_transitive y y0 y1 H1 H3).
   exact H4.
 Defined.
 End WR.
 
 Lemma sile1 (A B:Prop) : (~~A)->A.
 Proof.
 intro H.
 destruct (classic A).
 trivial.
 destruct (H H0).
 Defined.

 Lemma sile0 A : PR PROCA empctx ((-.-.A) --> A).
 Proof.
 eapply MP.
 apply Hax, (Ha11 A).
 eapply MP. (* with ((-.A) --> (-.(-.A)) --> A).*)
 2 :  eapply MP. (* with (A --> (-.(-.A)) --> A). *)
 3 : {
eapply Hax, Intui.
Check Ha8 A (-.A) ((-.(-.A))-->A).
eapply Ha8.
(*eapply (Ha8 A (-.A) ((-.(-.A))-->A)).*)
}
 +
 eapply Ded, Ded.
 Abort.

 Lemma sile2 (A B:Prop) : ((A->B)->B)->A.
 Proof.
 intro H. PROCA
 destruct (classic A).
 trivial.
 destruct (classic B).
End Lang.
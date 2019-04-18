(* Used books:
 LC = Languages and Calculi (N.K. Vereschagin, A.Shen)
*)
Require Import FunctionalExtensionality.
Require Import Logic.Classical_Prop.
Require Import Logic.Classical_Pred_Type.
Require Import Logic.ChoiceFacts.
Require Import Logic.IndefiniteDescription.
Require Import PeanoNat.
Require Import Bool.
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

Module PropFormulasNotationsASCII.
 Notation " x --> y ":=(Impl x y) (at level 80, right associativity):protxtnot.
 Notation " x -/\ y ":=(Conj x y) (at level 80):protxtnot.
 Notation " x -\/ y ":=(Disj x y) (at level 80):protxtnot.
 Notation " -. x " :=(Impl x Bot) (at level 80):protxtnot.
 Definition Neg (A:Fo):Fo := Impl A Bot.
 Definition Top:Fo := Neg Bot.
 Delimit Scope protxtnot with otd.
End PropFormulasNotationsASCII.
Export PropFormulasNotationsASCII.
Open Scope protxtnot.
 (* BEGIN experimental *)
 Section exper_1.
 Inductive PROCAI_1 : Fo -> Type :=
 | eHa1  (A B:PropVars.t) :  PROCAI_1 (A-->(B-->A))%otd
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

(*Section ooop.
Context (Y:Type).
Definition HH1 := list Y.
 Theorem lf2ft : HH1 -> Y ->Type.
 Proof. intros lf f. exact (InL f lf). Defined.
 Coercion lf2ft : HH1 >-> Funclass.
End ooop.
Check (nil:list Fo) Bot.
Check (nil:HH1 Fo) Bot.*)
 (** ==== Contexts ==== **)
Definition listFo := list Fo.
(* Definition HH2 := (Fo->Type). *)
(*  Theorem lf2ft :(list Fo) -> (Fo->Type). *)
 Theorem lf2ft : listFo -> (Fo -> Type).
 Proof. intros lf f. exact (InL f lf). Defined.
Coercion lf2ft : listFo >-> Funclass.
Check (nil:listFo):Fo->Type.

(*
Coercion jjj :=lf2ft.
Identity Coercion lf2ft3 : HH1 >-> HH2.
Coercion jjj :=lf2ft.
list*)


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

Check Sub.
 Definition craig {ctx} (p : PropVars.t) (A:Fo) : 
  PR PROCAI ctx (A--> ((Sub p Top A)-\/(Sub p Bot A))).
 Proof.
 induction A.
 + simpl.
 Abort. (* proof through completeness... *)

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

 Definition contrap_I {ctx} (A B:Fo) 
(H:PR PROCAI ctx (A-->B)) : PR PROCAI ctx (-.B-->-.A).
 Proof.
apply DedI.
apply DedI.
eapply MP.
2 : { apply hyp. right. left. reflexivity. }
eapply MP.
2 : { apply weak. apply weak. exact H. }
apply hyp. left. reflexivity.
Defined.

 Definition contrap {ctx} (A B:Fo) 
(H:PR PROCA ctx (A-->B)) : PR PROCA ctx (-.B-->-.A).
 Proof.
apply Ded.
apply Ded.
eapply MP.
2 : { apply hyp. right. left. reflexivity. }
eapply MP.
2 : { apply weak. apply weak. exact H. }
apply hyp. left. reflexivity.
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

 (* axioms are sound *)
 Lemma axioms_sou (A : Fo) (a : PROCA A) : foI_bo A = true.
 Proof.
   induction a.
   * induction p; simpl; destruct (foI_bo A), (foI_bo B);
     try destruct (foI_bo C); firstorder.
   * simpl; destruct (foI_bo A); firstorder.
 Defined.

 (* strong soundness *)
 Theorem str_sou_bo ctx f (H:PR PROCA ctx f)
 (Q:forall g, (ctx g)-> (foI_bo g)=true): (foI_bo f)=true.
 Proof.
 induction H.
 + apply Q.
   exact c.
 + apply (axioms_sou _ a).
 + simpl in * |- *. 
(*destruct (foI_bo B). reflexivity.
rewrite IHPR1 in IHPR2.
destruct IHPR2.
simpl.
reflexivity.
simpl in IHPR2.*)
destruct (foI_bo A), (foI_bo B); firstorder.
 Defined.

 End foI_bo.

 (*Soundness of the boolean semantics *)
 (*Theorem sou_bo f (H:PR PROCA empctx f) :
    forall (val:PropVars.t->bool), (foI_bo val f)=true.
 Proof. intro val.
 induction H.
 + destruct c.
 + induction a.
   * induction p; simpl; destruct (foI_bo val A), (foI_bo val B); 
     try destruct (foI_bo val C); firstorder.
   * simpl; destruct (foI_bo val A); firstorder.
 + simpl in * |- *; destruct (foI_bo val A), (foI_bo val B); firstorder.
 Defined.*)


 (*Lemma axioms_sou (A : Fo) (a : PROCA A)
  (val : PropVars.t -> bool) : foI_bo val A = true.
 Proof.
   induction a.
   * induction p; simpl; destruct (foI_bo val A), (foI_bo val B); 
     try destruct (foI_bo val C); firstorder.
   * simpl; destruct (foI_bo val A); firstorder.
 Defined.*)

 (* strong soundness *)
 (*Theorem str_sou_bo ctx f (H:PR PROCA ctx f) (val:PropVars.t->bool)
 (Q:forall g, (ctx g)-> (foI_bo val g)=true): (foI_bo val f)=true.
 Proof.
 induction H.
 + apply Q.
   exact c.
 + apply (axioms_sou _ a).
 + simpl in * |- *; destruct (foI_bo val A), (foI_bo val B); firstorder.
 Defined.*)

 Theorem sou_bo f (H:PR PROCA empctx f) :
    forall (val:PropVars.t->bool), (foI_bo val f)=true.
 Proof. intro val.
 eapply str_sou_bo.
 + exact H.
 + intros g [].
 Defined.

(* Completeness *)
Axiom classicT : forall (P : Prop), {P} + {~ P}.
Axiom classicType : forall (P : Type), sum P (P->False).

Theorem choice :
 forall (A B : Type) (R : A->B->Prop),
   (forall x : A, exists y : B, R x y) ->
    exists f : A->B, (forall x : A, R x (f x)).
Proof. intros.
Abort.

(*Context (Delta:Fo->Type) (CG:complete Delta).
Definition nu (p:PropVars.t) : bool
:= if (classicType (PR PROCA Delta p)) then true else false.
*)
Definition fu : Prop -> bool := fun P => 
if (classicT P) then true else false.
(*with
| left _ => true
| right _ => false
end.*)
Definition fuT : Type -> bool := fun P => 
if (classicType P) then true else false.

Lemma fuPtrue P : (fu P = true)->P.
Proof.
intro K. unfold fu in K.
destruct (classicT P). exact p. inversion K.
Defined.

Lemma fuPfalse P : (fu P = false)->~P.
Proof.
intro K. unfold fu in K.
destruct (classicT P). inversion K. exact n.
Defined.

Lemma truePfu (P:Prop) : P->(fu P = true).
Proof.
intro K.
unfold fu.
destruct (classicT P). reflexivity.
destruct (n K).
Defined.

Lemma falsePfu (P:Prop) : ~P->(fu P = false).
Proof.
intro K.
unfold fu.
destruct (classicT P). 
destruct (K p).
reflexivity.
Defined.

Lemma fuTPtrue P : (fuT P = true)->P.
Proof.
intro K. unfold fuT in K.
destruct (classicType P). exact p. inversion K.
Defined.

Lemma fuTPfalse P : (fuT P = false)->(P->False).
Proof.
intro K. unfold fuT in K.
destruct (classicType P). inversion K. exact f.
Defined.

Lemma trueTPfu (P:Type) : P->(fuT P = true).
Proof.
intro K.
unfold fuT.
destruct (classicType P). reflexivity.
destruct (f K).
Defined.

Lemma falseTPfu (P:Type) : (P->False)->(fuT P = false).
Proof.
intro K.
unfold fuT.
destruct (classicType P). 
destruct (K p).
reflexivity.
Defined.

(*
Coercion ffu := fu.
Definition Q (n:nat) := if (fu(n=n)) then true else false.
Fail Definition Q (n:nat) := if ((n=n)) then true else false.
*)
(* Consistent *)
Definition consi G :=
 (sigT (fun A=> prod (PR PROCA G A) (PR PROCA G (Neg A)))->False).
Definition complete G := prod (consi G)
 (forall A:Fo, sum (PR PROCA G A) (PR PROCA G (Neg A))).
Section natnum.
Context (nomer:nat->Fo).
Context (remon:Fo->nat).
Context (nomer_sect: forall x:nat, remon (nomer x) = x).
Context (nomer_retr: forall x:Fo, nomer (remon x) = x).
Section W.
(*Context (Fm:Set).*)
Context (Gamma:Fo->Type).
Context (CG:consi Gamma).

Fixpoint fam (n:nat) : Fo->Type :=
match n with
| 0 => Gamma
| S n => (*let previou := fam n *)
         let G:= nomer n in
         let extctx := (add2ctx G (fam n)) in
         if (fu(consi extctx)) then extctx else (fam n)
end.

(*Context (fam : nat -> (Fm->Prop)). *)
(*sigT     existT
exists   ex_intro *)
(*"exists"*)
Definition Delta : Fo->Type := fun f=> sigT (fun n=> fam n f).

Definition fam_mon f n : fam n f -> fam (S n) f.
Proof.
intro H.
simpl.
destruct (fu (consi (add2ctx (nomer n) (fam n)))).
2 : exact H.
right. exact H.
Defined.

(* Here we find the smallest n,
 such that $\Gamma_n$ can prove A *)
Lemma max_m0 m : (Nat.max m 0) = m.
Proof.
induction m. trivial. simpl. reflexivity.
Defined.

Section finite_argument.
Definition small (A : Fo) (p : PR PROCA Delta A) : nat.
Proof.
induction p.
+ destruct c as [x fxA]. exact x.
+ exact 0.
+ exact (max IHp1 IHp2).
Defined.

(*bad*)

(*
Lemma grea a b : a <= max a b.
induction a, b.
+ apply le_n.
+ simpl. apply le_S. induction b. trivial. apply le_S. assumption.
+ simpl. apply le_n.
+ simpl.  simpl in IHa.
apply le_n_S. exact IHa.
firstorder.

(*unfold max.*)
induction a.
+ induction b.
  - apply le_n.
  - apply le_S. exact IHb.
+ simpl.
   induction b.
  - apply le_n.
  - apply le_n_S.
simpl in IHa.
apply le_S. exact IHb.
simpl.*)


Section upward_inhabited_family.
(* Author of section: ejgallego
https://stackoverflow.com/users/1955696/ejgallego *)
Context (fam : nat -> Type).
Context (fam_mon : forall n, fam n -> fam (S n)).
Lemma fam_gt n k (hb : fam n) : fam (n + k).
Proof. now rewrite Nat.add_comm; induction k; auto; apply fam_mon. Qed.
Lemma fam_leq n m (hl : n <= m) (hb : fam n) : fam m.
Proof. now rewrite <- (Nat.sub_add _ _ hl), Nat.add_comm; apply fam_gt. Qed.
Lemma mxinh m n (hb : fam n) : fam (max n m).
Proof. exact (fam_leq _ _ (Nat.le_max_l _ _) hb). Qed.
End upward_inhabited_family.


Lemma indstep1 m n (A : Fo) (c : fam n A) : fam (max n m) A.
Proof.
apply (mxinh (fun k=>fam k A) (fam_mon A)).
assumption.
Defined.
(*induction m; simpl.
exact c.
induction n.
apply fam_mon.
rewrite max_m0 in IHm.
exact IHm.
Admitted. (*Nat.max*)*)


Theorem max_sym n : forall m, (max m n) = (max n m).
Proof.
induction n.
+ intros. simpl. induction m; trivial.
+ intros. simpl. induction m; try trivial.
simpl. apply f_equal. apply IHn.
Defined.

(*
Theorem max_sym m n : (max m n) = (max n m).
Proof.
induction m,n.
+ trivial.
+ simpl. trivial.
+ simpl. trivial.
+ simpl. trivial.
simpl in IHm.
unfold Nat.max.
Admitted.
*)
(*/bad*)

Lemma lemJ0 A Q R: PR PROCA (fam Q) A ->
 PR PROCA (fam (max Q R)) A.
Proof.
intro x. induction x.
+ apply hyp. apply indstep1. exact c.
+ apply Hax. exact a.
+ simpl in *|-*.
  eapply MP.
  - apply IHx1.
  - apply IHx2.
Defined.

(*Lemma lemJ1 A Q R: PR PROCA (fam R) A ->
 PR PROCA (fam (max Q R)) A.
Admitted.*)

Definition it_works (A : Fo) (p : PR PROCA Delta A) :
PR PROCA (fam (small A p)) A .
Proof.
induction p.
+ apply hyp.
  simpl.
  destruct c. assumption.
+ apply Hax. exact a.
+ simpl in *|-*.
  eapply MP.
  - apply lemJ0. exact IHp1.
  - rewrite max_sym. apply lemJ0. exact IHp2.
Defined.

(*
Lemma Nat.max m (S n) 
simpl in IHm.
 simpl.
Lemma indstep m n (W:n<=m) (A : Fo) (c : fam n A) : fam m A.
Proof.
le
induction W.
pose (t:=(m - n)).
induction t eqn:h.
2 : {
destruct m.
(*destruct (lt n m).
destruct W. "<=" le*)
Abort.*)
(*
Lemma gr_easy m n A :
 PR PROCA (fam n) A -> PR PROCA (fam (max m n)) A.
Proof. intro H.
induction H.
+ apply hyp.1 apply lemJ1.
Abort.*)
(*
Require Import Omega.
Require Import Arith.
PeanoNat.max

auto with arith.
omega.
firstorder.
auto.
apply IHp1.

PR
(*+ destruct c as [x fxA]. exact x.
+ exact 0.
+ exact (max IHp1 IHp2).
Defined.*)
Admitted.

simpl in *|-*.*)

(*Theorem finite_proof (A : Fo) (p : PR PROCA Delta A)
:  .*)
End finite_argument.


Lemma consi_fam n : consi (fam n).
Proof.
induction n.
+ simpl. exact CG.
+ simpl.
  pose (t:= fu(consi (add2ctx (nomer n) (fam n)))).
induction (fu (consi (add2ctx (nomer n) (fam n)))) eqn:h.
  2 : { exact IHn. }
apply fuPtrue.
exact h.
Defined.

Theorem condel : consi Delta.
Proof.
unfold consi.
intros [A [p1 p2]].
(*apply (it_works A) in p1.*)
assert (q1:=it_works _ p1).
assert (q2:=it_works _ p2).
eapply lemJ0 in q1.
eapply lemJ0 in q2.
rewrite max_sym in q2.
eapply consi_fam.
exists A.
split.
- exact q1.
- exact q2.
Defined.

Lemma delta_mon A j : fam j A -> Delta A.
Proof. intro H.
unfold Delta. exists j. exact H.
Defined.

Lemma pr_del_mon A j:  PR PROCA (fam j) A -> PR PROCA Delta A.
Proof. intro H.
induction H.
+ apply hyp. eapply delta_mon. exact c.
+ apply Hax. exact a.
+ eapply MP. exact IHPR1. exact IHPR2.
Defined.

Axiom NNPP_Type : forall p : Type, ((p->False)->False) -> p.

Theorem comdel : complete Delta.
Proof.
unfold complete.
split.
+ exact condel.
+ intro A.
pose (i:=remon A).
pose (extctx := add2ctx A (fam i)).
destruct (classicT (consi extctx)).
- left.
  assert (R:fam (S i) A).
  { simpl. unfold i.
    rewrite nomer_retr.
    fold i. rewrite truePfu.
    2 : exact c.
    left. trivial. }
  apply hyp.
  eapply delta_mon. exact R.
- right. unfold consi,not in n.
  apply NNPP_Type in n.
  destruct n as [a [H1 H2]].
  apply Ded in H1.
  apply Ded in H2.
  eapply pr_del_mon.
  eapply MP.
  2 : eapply MP.
  3 : { apply Hax,Intui. eapply Ha10. }
  exact H2.
  exact H1.
Defined.
End W.
(* p.49 *)
(* Check classicT False. sumbool*)
Section lemma2.
Context (Delta:Fo->Type) (CG:complete Delta).
Definition nu (p:PropVars.t) : bool
:= fuT (PR PROCA Delta p).
(*if (classicType (PR PROCA Delta p)) then true else false.*)

Lemma lem_2_1 (A:Fo):
 (((foI_bo nu A)=true)->(PR PROCA Delta A)) *
 (((foI_bo nu A)=false)->(PR PROCA Delta (Neg A))).
Proof.
induction A.
+ simpl. split; intro w.
  - unfold nu in w.
    apply fuTPtrue in w.
    exact w.
  - unfold nu in w.
    destruct CG as [c s].
    destruct (s p) as [H|H].
    2 : { exact H. }
    exfalso.
    apply (fuTPfalse (PR PROCA Delta p)) in w.
    * destruct w.
    * exact H.
+ split;simpl;intros p. 
  - inversion p.
  - unfold Neg. apply AtoA.
+ split;simpl;intros p.
  - rewrite andb_true_iff in p.
    destruct p as [p1 p2].
destruct IHA1 as [IHA1 _]. apply IHA1 in p1.
destruct IHA2 as [IHA2 _]. apply IHA2 in p2.
eapply MP.
2 : eapply MP.
3 : eapply Hax, Intui, Ha5.
exact p2.
exact p1.
-
destruct IHA1 as [_ IHA1].
destruct IHA2 as [_ IHA2].
(*apply andb_false_iff in p.
Fail destruct p.*)
apply andb_false_elim in p.
destruct p.
* apply IHA1 in e.
  eapply MP. exact e.
  apply contrap.
  apply Hax, Intui, Ha3.
* apply IHA2 in e.
  eapply MP. exact e.
  apply contrap.
  apply Hax, Intui, Ha4.
+ split;simpl;intros p.
  - apply orb_true_elim in p.
    destruct p.
    * destruct IHA1 as [IHA1 _].
      apply IHA1 in e.
      eapply MP. exact e.
      eapply Hax, Intui. constructor.
    * destruct IHA2 as [IHA2 _].
      apply IHA2 in e.
      eapply MP. exact e.
      eapply Hax, Intui. constructor.
  - apply orb_false_elim in p.
    destruct p as [p1 p2].
    destruct IHA1 as [_ IHA1].
    destruct IHA2 as [_ IHA2].
    apply IHA1 in p1.
    apply IHA2 in p2.
    eapply MP. exact p2.
    eapply MP. exact p1.
    eapply Hax, Intui.
    constructor.
+ split;simpl;intros p.
  - rewrite <- leb_implb in p.
    unfold leb in p.
    destruct (foI_bo nu A1).
    * destruct IHA1 as [IHA1 _].
      destruct IHA2 as [IHA2 _].
      apply IHA2 in p.
      eapply MP. exact p. apply Hax, Intui, Ha1.
    * destruct IHA1 as [_ IHA1].
      eapply MP.
      apply IHA1; reflexivity.
      apply Hax, Intui, Ha9.
  - destruct (foI_bo nu A1); simpl in *|-*.
    * destruct IHA2 as [_ IHA2].
       apply IHA2 in p.
      eapply MP. exact p. eapply contrap.
      apply Ded.
      eapply MP. 2 : { apply hyp. left. reflexivity. }
      destruct IHA1 as [IHA1 _].
      assert (IHA1:=IHA1 eq_refl).
      apply weak, IHA1.
    * inversion p.
Defined.

(*Theorem lemma2 : fu*)
(*
Lemma lem_2_1 (A:Fo): if (foI_bo nu A)
 then (PR PROCA Delta A) else (PR PROCA Delta (Neg A)).
Proof.
induction A.
+ simpl. unfold nu.
induction (fuT (PR PROCA Delta p))eqn:b.
*)
End lemma2.

Definition satisf ctx : Prop :=
 exists (v:PropVars.t->bool), forall g, ctx g -> foI_bo v g = true.
Lemma compl ctx : (complete ctx) -> (satisf ctx).
Proof.
intro H.
exists (nu ctx).
intros g ctxg.
destruct (classic (foI_bo (nu ctx) g = true)).
+ assumption.
+ apply not_true_iff_false in H0.
exfalso.
destruct (lem_2_1 ctx H g) as [_ I2].
apply I2 in H0.
eapply hyp in ctxg.
destruct H as [c s].
unfold consi in c.
apply c.
exists g.
split.
- exact ctxg.
- exact H0.
Defined.
Check Delta.
Check pr_del_mon.

Lemma satsubctx ctx CTX 
(i:forall x, ctx x -> CTX x):
 (satisf CTX) -> (satisf ctx).
Proof.
unfold satisf.
intros [v H].
exists v. intros g cg.
apply H, i, cg.
Defined.
Lemma lem3 ctx : forall x : Fo, ctx x -> Delta ctx x.
Proof.
intros.
eapply (delta_mon ctx x 0).
simpl.
exact X.
Defined.

Lemma compl2 ctx : (consi ctx) -> (satisf ctx).
Proof.
intro H.
apply (satsubctx ctx (Delta ctx)).
exact (lem3 _).
apply compl.
apply comdel.
exact H.
Defined.

(*Check delta_mon.
unfold satisf.
exists (nu ctx).
intros g ctxg.
destruct (classic (foI_bo (nu ctx) g = true)).
+ assumption.
+ apply not_true_iff_false in H0.
Check lem_2_1.
exfalso.
Admitted.*)

Definition inconsi G :=
 {A : Fo & (PR PROCA G A * PR PROCA G (Neg A))%type}.
Lemma cimp ctx : (satisf ctx->False) -> inconsi (ctx).
Proof.
intro x.
unfold inconsi.
apply NNPP_Type.
intro K.
apply compl2 in K.
exact (x K).
Defined.

Lemma vse ctx f : inconsi (add2ctx f ctx) -> PR PROCA ctx (-.(f)).
Proof.
intro H.
destruct H as [A [p1 p2]].
apply Ded in p1.
apply Ded in p2.
eapply MP. exact p2.
eapply MP. exact p1.
apply Hax, Intui, Ha10.
Defined.

Lemma dne ctx f : PR PROCA ctx (-.(-.f)) -> PR PROCA ctx f.
Proof.
intro H.
assert (Q:PR PROCA ctx (f -\/ (-.f))).
{ apply Hax, Ha11. }
eapply MP.
exact Q.
1 : eapply MP.
2 : eapply MP.
3 : { eapply Hax, Intui, Ha8. }
+ apply Ded.
  eapply MP. apply hyp. left. reflexivity.
  eapply MP. apply weak. exact H.
  apply Hax, Intui, Ha9.
+ apply AtoA.
Defined.

 Theorem cmpl_bo f
(H: forall (val:PropVars.t->bool), (foI_bo val f)=true)
 : PR PROCA empctx f.
Proof.
apply dne.
apply vse.
apply cimp.
intro J.
unfold satisf in J.
destruct J as [val M].
assert (M:=M (-.f)).
assert (H:=H val).
assert (U:add2ctx (-.f) empctx (-.f)).
{ left. reflexivity. }
assert (M:=M U).
simpl in M.
destruct (foI_bo val f).
+ simpl in M. inversion M.
+ inversion H.
Defined.

(*
Axiom classicType : forall T : Type, sum T (T->False).
destruct (classicType (Delta A)). 
- left. apply hyp. exact d.
- right.
assert (easyly: forall i, fam i A -> False).
admit.
pose (i:=remon (Neg A)).
Check fam (remon (Neg A)).
(*assert (D:(PR PROCA Delta A->False)
 *(PR PROCA Delta (Neg A)->False)).
admit.
exfalso.
destruct D as [D1 D2].
Delta
Check remon A.
Theorem yorn A : Delta*)
Print fam.
Admitted.*)
End natnum.

Check cmpl_bo.



Record Model := {
 KM_W:Set;
 KM_R:KM_W->KM_W->Prop;
 KM_R_transitive : transitive KM_W KM_R;
 KM_R_reflexive : reflexive KM_W KM_R;
 KM_vf:PropVars.t -> KM_W -> Prop;
 KM_mvf: forall (x y : KM_W)(p:PropVars.t), KM_vf p x -> KM_R x y -> KM_vf p y
}.
 (*
   Kripke semantics for the intuitionistic
   proposition logic.
 *)
 Open Scope type_scope.
 Section WR.
 Variables (W:Set) (R:W->W->Prop) (R_transitive : transitive W R)
 (R_reflexive : reflexive W R).
 Variables (vf:PropVars.t -> W -> Prop)
 (mvf: forall (x y : W)(p:PropVars.t), vf p x -> R x y -> vf p y).

 Section foI_kr. (* Entails *)
 Fixpoint foI_kr (x:W) (f:Fo) : Prop. (* := *)
 Proof using W R R_transitive R_reflexive vf mvf.
 exact (
 match f with 
   | Atom p => (vf p x)
   | Bot => False
   | f1 -/\ f2 => foI_kr x f1 /\ foI_kr x f2
   | f1 -\/ f2 => foI_kr x f1 \/ foI_kr x f2
   | f1 --> f2 =>
 (forall y:W, R x y -> ((foI_kr y f1) -> (foI_kr y f2)))
 end
 ).
 Defined.
 (*foI x f1 =-> foI x f2*)
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
Check @foI_kr.

(* TODO:
 Theorem utv3 : exists (W:Set) (R:W->W->Prop) (R_transitive : transitive W R)
 (R_reflexive : reflexive W R) (vf:PropVars.t -> W -> Prop) 
 (mvf: forall (x y : W)(p:PropVars.t), vf p x -> R x y -> vf p y) (x:W), 
  ~ foI_kr W R vf x f
.
*)

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

 (*
 Lemma sile2 (A B:Prop) : ((A->B)->B)->A.
 Proof.
 intro H. PROCA
 destruct (classic A).
 trivial.
 destruct (classic B).
 *)
 Theorem propswap (A B C:Fo):
 PR PROCAI empctx ((A-->(B-->C))-->(B-->(A-->C))).
 Proof.
 eapply DedI, DedI, DedI.
 eapply MP.
 2 : {
 eapply MP.
 2 : {
 apply hyp.
 unfold add2ctx.
 right. right. left. reflexivity.
 }
 apply hyp.
 unfold add2ctx.
 left. reflexivity.
 }
 apply hyp.
 unfold add2ctx.
 right. left. reflexivity.
 Defined.
End Lang.

Check classic.
(* Here will be theorems about classical propositional logic. *)
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Import PropLang.
Require Import Logic.Classical.
Require Import Logic.ChoiceFacts.
Require Import Logic.IndefiniteDescription.
Require Import ClassicalDescription.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.

Require Import Coq.Structures.Equalities.

(*
Module Lang' (PropVars : UsualDecidableTypeFull).
 Module XLang := Lang PropVars.
 Export XLang.
End Lang'.
*)

(* Classical proposition interpretation *)
Module ProCl (PropVars : UsualDecidableTypeFull).
 Module XLang := Lang PropVars.
 Import XLang.

 Section lem3.
 Context (P Q:Fo).
 Definition PandQ: Fo->Type := fun f => (f=P)\/(f=Q).
 Definition PandNQ: Fo->Type := fun f => (f=P)\/(f=-.Q).
 Definition NPandQ: Fo->Type := fun f => (f=-.P)\/(f=Q).
 Definition NPandNQ: Fo->Type := fun f => (f=-.P)\/(f=-.Q).

 Theorem lem3_1: PR PandQ PROCA (P -/\ Q).
 Proof.
 unshelve eapply MP.
 exact Q.
 unfold PandQ.
 apply hyp. right. reflexivity.
 
 unshelve eapply MP.
 exact P.
 unfold PandQ.
 apply hyp. left. reflexivity.

 apply Hax. apply Intui, Ha5.
 Defined.

 (* TODO: lem3_2*)
 Section rule10. (*p.45*)
 Context (Gamma:Fo->Type).
 Context (A B:Fo).
 (*Check (fun x=>Gamma x \/ x=A).*)
 Theorem rule10 (H1:PR (add2ctx A Gamma) PROCA B )
  (H2:PR (add2ctx A Gamma) PROCA (-.B) )
 :
 PR Gamma PROCA (-.A).
 Proof.
 apply Ded in H1.
 apply Ded in H2.
 1 : eapply MP.
 2 : eapply MP.
 3 : apply Hax, Intui, Ha10.
 exact H2. exact H1.
 Defined.
 End rule10.

 Theorem lem3_3: PR NPandQ PROCA (-.(P -/\ Q)).
 Proof.
 unfold NPandQ.
 (* eapply permut. *)
 1 : eapply rule10.
 (*instantiate (1:= fun e=> e=-.P).*)
 (* intros x H. left. exact H.*)
 eapply MP.
 apply hyp.
 left. reflexivity.
 apply Hax. apply Intui. apply Ha3.
 apply hyp.
 right. left. reflexivity.
(*(add2ctx A Gamma)).
 specify (-.P).*)
 (*unshelve eapply MP.
 exact Q.
 unfold PandQ.
 apply hyp. right. reflexivity.
 
 unshelve eapply MP.
 exact P.
 unfold PandQ.
 apply hyp. left. reflexivity.

 apply Hax. apply Intui, Ha5.
 Defined.*)
 Defined.

 (* case analysis *)
 Theorem rule8 A B C Gamma (H1:PR (add2ctx A Gamma) PROCA C )
  (H2:PR (add2ctx B Gamma) PROCA C )
 :
 PR (add2ctx (A-\/ B) Gamma) PROCA C.
 Proof.
 apply Ded in H1.
 apply Ded in H2.
 apply invDed.
 1 : eapply MP.
 2 : eapply MP.
 3 : apply Hax, Intui, Ha8.
 exact H2.
 exact H1.
 Defined.

 Theorem rule9 A B Gamma (H1:PR Gamma PROCA A )
  (H2:PR Gamma PROCA (-.A) )
 :
 PR Gamma PROCA B.
 Proof.
 1 : eapply MP.
 2 : eapply MP.
 3 : apply Hax, Intui, Ha9.
 exact H1.
 exact H2.
 Defined.

 Theorem lem3_8: PR NPandNQ PROCA (-.(P -\/ Q)).
 Proof.
 unfold NPandNQ.
 eapply rule10.
 instantiate (1:=Bot).
 + apply rule8.
   * eapply rule9.
     apply hyp. left. reflexivity.
     apply hyp. right. left. reflexivity.
   * eapply rule9.
     apply hyp. left. reflexivity.
     apply hyp. right. right. reflexivity.
 + eapply rule8.
   * eapply rule9.
     apply hyp. left. reflexivity.
     apply hyp. right. left. reflexivity.
   * eapply rule9.
     apply hyp. left. reflexivity.
     apply hyp. right. right. reflexivity.
 Defined.
 End lem3.

(*
No result for Strong LEM:
grep -rnw '/home/user/opam-coq.8.8.1/4.02.3/lib/coq/theories/' -e 'classicT'
It mentioned here:
https://github.com/coq/coq/wiki/CoqAndAxioms
http://www.chargueraud.org/viewcoq.php?sFile=softs%2Ftlc%2Fsrc%2FUseClassic.v
Check excluded_middle_informative.
*)

 Definition ttt0 : (PropVars.t -> Prop) -> (PropVars.t -> bool).
 Proof.
 intros P p.
 destruct (excluded_middle_informative (P p)).
 exact true.
 exact false.
 Defined.
 Definition ttt1 : (PropVars.t -> bool) -> (PropVars.t -> Prop).
 Proof.
 intros f p.
 destruct (f p). (* eqn:s.*)
 exact True.
 exact False.
 Defined.
 Theorem ttt01 P : (ttt1 (ttt0 P)) = P.
 Proof.
 apply functional_extensionality.
 intro x.
 unfold ttt0,ttt1.
 apply propositional_extensionality.
 destruct (excluded_middle_informative (P x)).
 { split. intros _. exact p. intros _. constructor. }
 { split. intros []. exact n. }
 Defined.
 Theorem ttt10 f : (ttt0 (ttt1 f)) = f.
 Proof.
 apply functional_extensionality; intro x.
 unfold ttt0,ttt1.
 destruct (f x).
 + destruct (excluded_middle_informative True).
   reflexivity. destruct n. constructor.
 + destruct (excluded_middle_informative False).
   destruct f0. reflexivity.
 Defined.
(* EXPERIMENT:
Axiom type_extensionality : forall (A B:Type)
 (f:A->B) (invf:B->A) (H1: forall b, (f (invf b)) = b)
 (H2: forall a, (invf (f a)) = a), A = B.
Theorem Q : (PropVars.t -> Prop)=(PropVars.t -> bool).
Proof.
eapply type_extensionality.
exact ttt10.
exact ttt01.
Defined.
*)
 Definition fff0 : Prop -> bool.
 Proof.
 intros P.
 destruct (excluded_middle_informative P).
 exact true.
 exact false.
 Defined.
 Definition fff1 : bool -> Prop.
 Proof.
 intros b.
 destruct b. (* eqn:s.*)
 exact True.
 exact False.
 Defined.
 Theorem fff01 P : (fff1 (fff0 P)) = P.
 Proof.
 (* apply functional_extensionality.
 intro x.*)
 unfold fff0,fff1.
 apply propositional_extensionality.
 destruct (excluded_middle_informative P).
 { split. intros _. exact p. intros _. constructor. }
 { split. intros []. exact n. }
 Defined.
 Theorem fff10 b : (fff0 (fff1 b)) = b.
 Proof.
 (*apply functional_extensionality; intro x.*)
 unfold fff0,fff1.
 destruct b.
 + destruct (excluded_middle_informative True).
   reflexivity. destruct n. constructor.
 + destruct (excluded_middle_informative False).
   destruct f. reflexivity.
 Defined.

Inductive eq2 (A : Type) (x : A) : A -> Prop :=
 eq2_refl : @eq2 A x x.

Inductive paths {A : Type} (a : A) : A -> Type :=
 idpath : paths a a.

Theorem thm1 (A:Type) a b: (@paths A a b)-> a=b.
Proof.
intro H.
destruct H.
reflexivity.
Defined.

(*
Check (PropVars.t -> Prop).
Check (PropVars.t -> bool).
*)
 Section lem4. (* LC p.47 *)
 Definition ne (b:bool) (A:Fo) : Fo := if b then A else -.A .
 Inductive ctx_bld (str:PropVars.t -> bool) : Fo -> Type :=
 | con : forall p:PropVars.t, ctx_bld str (ne (str p) (Atom p)).

(* Definition ctx_bld (str:PropVars.t -> bool) : Fo -> Type.
 Proof.
 intro f.
 Admitted. *)
 Theorem lem4 (A:Fo) (str:PropVars.t -> bool) (eps:bool)
  : 
  PR (ctx_bld str) PROCA (ne (fff0 (foI_cl (ttt1 str) A)) A).
 Proof.
 induction A; simpl.
 + unfold fff0,fff1, ne.
   destruct (excluded_middle_informative (ttt1 str p)).

 Abort.
 End lem4.

 (* lem3, page 47 *)
 Section lem3'.
 Context (A:Fo).
 Fixpoint vblesoffm (F:Fo) (v:PropVars.t) : Type :=
 match F with
 | Atom p => (v=p)
 | Bot => False
 | Conj f0 f1 | Disj f0 f1 | Impl f0 f1 =>
    sum (vblesoffm f0 v) (vblesoffm f1 v)
 end.
(*
 destruct F.
 Definition 
 Theorem 
*)
 End lem3'.
 (* Completeness theorem for DN semantics of the CProL*)
 Theorem com_dn f (H : forall (val:PropVars.t->Prop), foI_dn val f) : 
  PR empctx PROCA f.
 Proof.
 Abort.

 (* Unfinished completeness theorem. *)
 Definition Consis (G:Fo -> Type) := (PR G PROCA Bot)->False.

 Definition MaxCon (G:Fo -> Type) (Y:Consis G) :=
  (forall F:Fo, sum (G F) (G (-.F)) ).
 Definition conca (A:Fo) (G:Fo -> Type) :Fo -> Type 
:= fun X :Fo => sum (X=A) (G A).

 Theorem lem1_0 G (H:Consis G) A :
  (Consis (conca A G))+(Consis (conca (-.A) G)).
 Admitted.
 Section assump. (*temporary*)
 Context (enu: nat -> Fo).
 Context (surj: forall f:Fo, sig (fun n:nat=> f = enu n)).
 Inductive steps : forall (G:Fo->Type) (H:Consis G), Fo -> Type :=
 | base : forall (f:Fo) (G:Fo->Type) (H:Consis G), G f -> steps G H f
 | addl : forall A G (H:(Consis (conca A G))),
   steps (conca A G) H A
 | addr : forall A G (H:(Consis (conca (-.A) G))),
   steps (conca (-.A) G) H (-.A)
 .
(* | addi : forall A G 
  (H:sum (Consis (conca A G)) (Consis (conca (-.A) G))),
  match H with 
  | inl HL => MaxC (conca A G) HL A
  | inr HR => MaxC (conca (-.A) G) HR A
  end.*)

 Definition isMax (G:Fo->Type) := prod (Consis G) 
(forall f:Fo, (Consis (conca f G)) -> G f).

 Definition isMax' (G:Fo->Type) := prod (Consis G) 
((exists f:Fo , ((Consis (conca f G)) -> G f) -> False)->False).

 (* *)
 Definition MaxC (acc : Fo->Type) (H:Consis acc) (n:nat) : 
  sig (fun Q : Fo->Type => Consis Q).
 Proof.
 induction n as [|n].
 - exists acc. exact H.
 - destruct IHn as [Q K].
   destruct (lem1_0 Q K (enu n)) as [HL|HR].
   exists (conca (enu n) Q). exact HL.
   exists (conca (-.(enu n)) Q). exact HR.
 Defined.

 (* Maximal & consistent type.*)
 Section Delta.
 Context (acc : Fo->Type) (H:Consis acc).
 Definition Delta  : Fo->Type.
 Proof.
 intros f.
 refine (sigT (fun n:nat=> _)).
 exact ((proj1_sig (MaxC acc H n)) f).
 Defined.

 (* Property 1*)
 Theorem py1 : Consis Delta.
 Proof.
unfold Consis.
unfold Delta.
 Abort.
 End Delta.

 (*induction (surj f).*)

 Definition MaxCe (acc : Fo->Type) (H:Consis acc) (n:nat) : 
  sig (fun Q : Fo->Type => Consis Q).
 Proof.
 induction n as [|n].
 - exists acc. exact H.
 - destruct IHn as [Q K].
   destruct (lem1_0 Q K (enu n)) as [HL|HR].
   exists (conca (enu n) Q). exact HL.
   exists (conca (-.(enu n)) Q). exact HR.
 Defined.


(*
Check sig.
Check proj1_sig.
Context (acc:Fo->Type) (H :Consis acc).
 forall f:Fo, (proj1_sig (MaxC acc H (enu f)))
*)
 Definition unio (acc : Fo->Type) (H:Consis acc) : Fo->Type.
 Proof. intros f.
 destruct (surj f).
 pose (m:= MaxC acc H (S x)).
 destruct m.
 (*exact exists
refine (sigT (fun n=>)).*)
 Abort.

 Definition MaxC' (acc : Fo->Type) (H:Consis acc) (n:nat) : 
 sigT (fun Q : Fo->Type => 
   prod (Consis Q) (forall F:Fo, sum (Q F) (Q (-.F)))).
 Proof.
 induction n.
 - exists acc. 
   split.
   exact H.
 Abort.

 Definition MaxC'' (acc : Fo->Type) (H:Consis acc) : 
  exists Q : Fo->Type, Consis Q.
 (* induction n.
 admit. *)
 Abort.

 Definition MaxCx (acc : Fo->Type) (H:Consis acc) (n:nat) : Fo->Type.
 Proof.
 intros f.
 induction f.
 unfold Consis in H.
 (*Check lem1_0 acc (H:Consis G) A.
 Consis (conca A G))+(Consis (conca (-.A) G)*)
 (*induction n.
 + *)
 Abort.

 (*Theorem thm (G:Fo->Type) (H:Consis G) : isMax (MaxC G H).
 Proof.
 Definition MaxC : forall (G:Fo->Type) (H:Consis G),

 Theorem com_bo f
  (H : forall (val:PropVars.t->bool), foI_bo val f = true) :
  PR [] PROCA f.
 Proof.
  induction f.
  simpl in * |- *.
 Abort.*)
 End assump.
End ProCl.
(*
(* TODO RENAME and UNIFY *)
Require Import Relations.
Require Import Classes.RelationClasses.
Require Export Coq.Vectors.Vector.

Require Poly.
Export Poly.
(*Export Poly.ModProp.*)

Module Prop_mod (PropVars : UsualDecidableTypeFull).
Inductive Fo :=
 |Atom (p:PropVars.t) :> Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
.

(* Substitution *)
Fixpoint subPF (t:Fo) (xi: PropVars.t) (u : Fo): Fo.
Proof.
Abort. (*Defined.*)


Section OmegaInterpretation.
Definition Omega := Prop.
(* Propositional variant
Context (val:PropVars.t->Omega).
(*Fixpoint foI (f:Fo): Omega.
Proof.
destruct f (*eqn:h*).
+ exact (val p).
+ exact OFalse.
+ exact ( OConj (foI f1) (foI f2)).
+ exact ( ODisj (foI f1) (foI f2)).
+ exact ( OImpl (foI f1) (foI f2)).
Show Proof.
Defined.*)
Fixpoint foI (f : Fo) : Omega :=
   match f with
   | Atom p => val p
   | Bot => OFalse
   | f1 -/\ f2 => foI f1 =/\ foI f2
   | f1 -\/ f2 => foI f1 =\/ foI f2
   | f1 --> f2 => foI f1 =-> foI f2
   end.
*)

(*Check Ha9.*)

Section WR.
Context (W:Set) (R:W->W->Prop) (R_transitive : transitive W R)
(R_reflexive : reflexive W R).
Context (vf:PropVars.t -> W -> Prop) 
(mvf: forall (x y : W)(p:PropVars.t), vf p x -> R x y -> vf p y).

Section foI. (* Entails *)
Fixpoint foI (x:W) (f:Fo) : Prop := 
match f with 
   | Atom p => (vf p x)
   | Bot => False
   | f1 -/\ f2 => foI x f1 /\ foI x f2
   | f1 -\/ f2 => foI x f1 \/ foI x f2
   | f1 --> f2 => 
(forall y:W, R x y -> ((foI y f1) -> (foI y f2)))
end. (*foI x f1 =-> foI x f2*)
End foI.

Theorem utv1 x f: foI x (f-->Bot) <-> forall y, R x y -> not (foI y f).
Proof.
simpl. unfold not. reflexivity.
(* split.
+ intros.
simpl in H. destruct (H y H0).
* exact H1.
* destruct H1.
+ intros. left. exact (H y H0).*)
Defined.

Theorem utv2 x y f :foI x f -> R x y -> foI y f.
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

(* Soundness of IPro *)
Export List.ListNotations.
Theorem sou f (H:PR [] PROCA f) : forall x, foI x f.
Proof.
induction H.
+ simpl in i. destruct i.
+ induction a.
  * simpl. intros.
    simpl in * |- *.
    apply utv2 with (x:=y).
    - exact H0.
    - exact H1.
  * simpl. intros.
(*Show Proof.
Check (H0 y1 _ _ y1).*)
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
+ simpl in * |- *.
  intro x.
  unshelve apply (IHPR2 x).
  unshelve apply R_reflexive.
  unshelve apply IHPR1.
Unshelve.
exact (R_transitive y y0 y1 H1 H3).
exact H4.
Defined.

(*Check nil%list.*)
Fixpoint CONJ (l:list Fo) : Fo :=
match l return Fo with
| List.nil  => Top
| (h::t)%list => h -/\ CONJ t
end.
Fixpoint DISJ (l:list Fo) : Fo :=
match l return Fo with
| List.nil  => Bot
| (h::t)%list => h -\/ DISJ t
end.
(*Consistent Pair*)
Definition conpa (G D:list Fo) : Type
:= (PR [] PROCA ((CONJ G) --> (DISJ D))) -> False.

Definition incpa (G D:list Fo) : Type
:=  PR [] PROCA ((CONJ G) --> (DISJ D)).


Inductive SubFo (f:Fo): Fo -> Type :=
| sfrefl : SubFo f f
| sfal : forall (g1 g2 : Fo), (SubFo f g1) -> (SubFo f (g1 -/\ g2))
| sfar : forall (g1 g2 : Fo), (SubFo f g2) -> (SubFo f (g1 -/\ g2))
| sfol : forall (g1 g2 : Fo), (SubFo f g1) -> (SubFo f (g1 -\/ g2))
| sfor : forall (g1 g2 : Fo), (SubFo f g2) -> (SubFo f (g1 -\/ g2))
| sfil : forall (g1 g2 : Fo), (SubFo f g1) -> (SubFo f (g1 --> g2))
| sfir : forall (g1 g2 : Fo), (SubFo f g2) -> (SubFo f (g1 --> g2))
.

Definition AtoA {ctx} (A:Fo) : PR ctx PROCA (A-->A).
Proof.
apply MP with (A-->(A-->A)).
apply Hax, Ha1. (* apply (Hax _ _ (Ha1 _ _)).*)
apply MP with (A-->((A-->A)-->A)) (*1:=I*).
apply Hax, Ha1.
apply Hax, Ha2.
Defined.


(*Fixpoint *)
Theorem weak (axs:Fo -> Type)
(A F:Fo) (l :list Fo) (x: (PR l axs F)) : (PR (A::l) axs F).
Proof.
induction x.
+ apply hyp.
  right.
  exact i.
+ apply Hax, a.
+ exact (MP (A::l) axs A0 B IHx1 IHx2).
Defined.

Fixpoint weaken (F:Fo) (li l :list Fo) (x: (PR l PROCA F)) {struct li}:
 (PR (li ++ l) PROCA F).
Proof.
destruct li.
simpl.
exact x.
simpl.
simple refine (@weak _ f F (li ++ l)%list _).
apply weaken.
exact x.
Defined.

Export Coq.Lists.List.

Definition neg (f:Fo):= (Impl f Bot).

Definition a1i (A B : Fo)(l : list Fo):
(PR l PROCA B)->(PR l PROCA (Impl A B)).
Proof.
intros x.
apply MP with (A:= B).
exact x.
eapply (*subcalc_OE,*) Hax,Ha1.
Defined.

(* Deduction *)
Theorem Ded (A B:Fo)(il:list Fo)(m:(PR (A::il) PROCA B)) 
:(PR il PROCA (A-->B)).
Proof.
induction m.
+ unfold InL in i.
  simpl in i .
  destruct i .
  * rewrite <- e.
    pose (J:=weaken _ il [] (AtoA A )).
    rewrite app_nil_r in J.
    exact J.
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
  apply Ha2.
Defined.

Theorem invDed (A B:Fo)(il:list Fo)(m:(PR il PROCA (A-->B)))
:(PR (A::il) PROCA B).
Proof.
pose(U:=(weak PROCA A _ il m)).
assert (N:PR (A :: il) PROCA A).
apply hyp. simpl. left. reflexivity.
apply MP with A.
exact N.
exact U.
Defined.

(* Order of the context is not important. *)
Lemma permut axs L1 L2 A (H: forall x, InL x L1 -> InL x L2)
: (PR L1 axs A) -> (PR L2 axs A).
Proof.
intro m.
induction m.
+ apply hyp. apply (H A i).
+ apply Hax. apply a.
+ apply MP with A. exact IHm1. exact IHm2.
Defined.

(* Both are inconsistent then (G,D) is inconsistent*)
Lemma lem1_0 G D s g (J1:SubFo s g) 
(a1: incpa (s :: G) D )
(a2: incpa G (s :: D) ) : incpa G D.
Proof.
unfold incpa in * |- *.
simpl in * |- *.
apply Ded.
apply MP with (s-\/(DISJ D)).
+ apply invDed in a2.
  exact a2.
+ apply MP with (DISJ D --> DISJ D).
  apply AtoA.
  apply MP with (s --> DISJ D).
  2 : {apply Hax. apply Ha8. }
  pose (r:=Hax [] PROCA _ (Ha5 s (CONJ G))).
  apply invDed in r.  apply invDed in r.
  apply weak with (A:=s) in a1.
  apply weak with (A:=CONJ G) in a1.
  assert (K:PR [CONJ G;s] PROCA (DISJ D)).
  apply MP with (A:=s-/\ CONJ G).
  exact r. exact a1.
  apply Ded.
  apply permut with (L1:=[CONJ G;s]).
  2 : exact K.
  simpl.
  firstorder.
Defined.
(*Locate prod.
Print Scopes.*)
Open Scope type_scope.

Section Completeness.
Context (phi:Fo).
End Completeness.

(*
Lemma lem1 (G D:list Fo) (J:incpa G D) : 
exists GG DD:list Fo, (incpa GG DD) * 
(forall x, InL x G -> InL x GG) *
(forall x, InL x D -> InL x DD).
UNIVERSE INCONSISTENCY
*)

(*assert (asse:PR [CONJ G] PROCA (s -\/ DISJ D)).
admit.
simpl in asse.
pose (Q:= Hax [] PROCA _ (Ha5 s (CONJ G))).
destruct asse.
Abort.*)

End WR.

(*
Inductive Entails (x:W) : Fo -> Prop :=
| am : forall  (p:PropVars.t), vf p x -> Entails x (Atom p)
| im A B: (forall y:W, R x y -> (Entails y B \/ not (Entails y A)))
-> Entails x (A --> B)
.
*)

(*Record MonVal := {
vf:PropVars.t -> W -> bool;
mf:
}.*)

(*Record KripkeModel := {
W:Set;
R:W->W->Prop;
}.*)

End OmegaInterpretation.
End Prop_mod.*)
(* Here will be theorems about propositional logic.
Then I'll decide how to unite it with the rest. *)

(* TODO RENAME and UNIFY *)
Require Import Relations.
Require Import Classes.RelationClasses.
Require Export Coq.Vectors.Vector.
Require Import Coq.Structures.Equalities.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Import PropLang.

Require Export Coq.Lists.List.
Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.

Require Poly.
Export Poly.
(*Export Poly.ModProp.*)

Module Prop_mod (PropVars : UsualDecidableTypeFull).

(*
Inductive Fm_O :=
 |Atom_O (p:PropVars.t) :> Fm_O
 |Bot_O :Fm_O
 |Conj_O:Fm_O->Fm_O->Fm_O
 |Disj_O:Fm_O->Fm_O->Fm_O
 |Impl_O:Fm_O->Fm_O->Fm_O
.
*)
Inductive Fo :=
 |Atom (p:PropVars.t) :> Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
.

Notation " x --> y ":=(Impl x y) (at level 80, right associativity). 
(*81, right associativity*)
Notation " x -/\ y ":=(Conj x y) (at level 80).
Notation " x -\/ y ":=(Disj x y) (at level 80).
Notation " -. x " :=(Impl x Bot) (at level 80).
(* Substitution *)
Fixpoint subPF (t:Fo) (xi: PropVars.t) (u : Fo): Fo.
Proof.
Abort. (*Defined.*)

Definition Top:Fo := Impl Bot Bot.

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
Inductive PROCAI : Fo -> Type :=
| Ha1  : forall A B, PROCAI (A-->(B-->A))
| Ha2  : forall A B C, PROCAI ((A-->(B-->C))-->((A-->B)-->(A-->C)))
| Ha3  : forall A B, PROCAI ((A-/\ B)--> A)
| Ha4  : forall A B, PROCAI ((A-/\ B)--> B)
| Ha5  : forall A B, PROCAI (A-->(B-->(A-/\B)))
| Ha6  : forall A B, PROCAI (A-->(A-\/ B))
| Ha7  : forall A B, PROCAI (B-->(A-\/ B))
| Ha8  : forall A B C, PROCAI ((A-->C)-->((B-->C)-->((A-\/ B)-->C)))
| Ha9  : forall A B, PROCAI (-.A --> A --> B )
.
(*Check Ha9.*)

Section PR.
Context (ctx:Fo -> Type). (*Context (ctx:list Fo).*)
Context (axs:Fo -> Type).
Inductive PR : Fo -> Type :=
| hyp (A : Fo) : (ctx A) -> PR A
| Hax :> forall (A : Fo), (axs A) -> PR A
| MP (A B: Fo) : (PR A)->(PR (Impl A B))->(PR B)
.
End PR.

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

(* Soundness of IPro *)
Export List.ListNotations.
Theorem lf2ft :(list Fo) -> (Fo->Type).
Proof. intros lf f. exact (InL f lf). Defined.

(*Coercion lf2ft. : (list Fo) >-> (Fo->Type).*)

Inductive empctx : Fo -> Type :=.
Theorem sou f (H:PR empctx PROCAI f) : forall x, foI_kr x f.
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
:= (PR empctx PROCAI ((CONJ G) --> (DISJ D))) -> False.

Definition incpa (G D:list Fo) : Type
:=  PR empctx PROCAI ((CONJ G) --> (DISJ D)).


Inductive SubFo (f:Fo): Fo -> Type :=
| sfrefl : SubFo f f
| sfal : forall (g1 g2 : Fo), (SubFo f g1) -> (SubFo f (g1 -/\ g2))
| sfar : forall (g1 g2 : Fo), (SubFo f g2) -> (SubFo f (g1 -/\ g2))
| sfol : forall (g1 g2 : Fo), (SubFo f g1) -> (SubFo f (g1 -\/ g2))
| sfor : forall (g1 g2 : Fo), (SubFo f g2) -> (SubFo f (g1 -\/ g2))
| sfil : forall (g1 g2 : Fo), (SubFo f g1) -> (SubFo f (g1 --> g2))
| sfir : forall (g1 g2 : Fo), (SubFo f g2) -> (SubFo f (g1 --> g2))
.

Definition AtoA {ctx} (A:Fo) : PR ctx PROCAI (A-->A).
Proof.
apply MP with (A-->(A-->A)).
apply Hax, Ha1. (* apply (Hax _ _ (Ha1 _ _)).*)
apply MP with (A-->((A-->A)-->A)) (*1:=I*).
apply Hax, Ha1.
apply Hax, Ha2.
Defined.

Definition add2ctx (A:Fo) (l:Fo->Type) : Fo->Type 
:= fun f=> sum (A=f) (l f). (* add head *)

Definition cnctctx (l1 l2:Fo->Type) : Fo->Type 
:= fun f=> sum (l1 f) (l2 f). (* concat *)

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
Definition weaken (F:Fo) (li l :Fo->Type) (x: (PR l PROCAI F)) 
(*{struct li}*): (PR (cnctctx li l) PROCAI F).
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

Export Coq.Lists.List.

Definition neg (f:Fo):= (Impl f Bot).

Definition a1i (A B : Fo)(l : Fo->Type):
(PR l PROCAI B)->(PR l PROCAI (Impl A B)).
Proof.
intros x.
apply MP with (A:= B).
exact x.
eapply (*subcalc_OE,*) Hax,Ha1.
Defined.

Lemma addempeqv (il:Fo->Type) : forall (f:Fo), 
(cnctctx il empctx) f -> il f.
Proof. intros f q. destruct q. exact i. destruct e. Defined.

(*
PR (cnctctx il empctx) PROCAI (A --> A)
PR il PROCAI (A --> A)
*)

(* Deduction *)
Theorem Ded (A B:Fo)(il:Fo->Type)(m:(PR (add2ctx A il) PROCAI B)) 
:(PR il PROCAI (A-->B)).
Proof.
induction m.
+ (*unfold InL in c.*)
  simpl in c .
  destruct c .
  * rewrite <- e.
    pose (J:=weaken _ il empctx (AtoA A )).
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
  apply Ha2.
Defined.

Theorem invDed (A B:Fo)(il:Fo->Type)(m:(PR il PROCAI (A-->B)))
:(PR (add2ctx A il) PROCAI B).
Proof.
pose(U:=(weak PROCAI A _ il m)).
assert (N:PR (add2ctx A il) PROCAI A).
apply hyp. simpl. left. reflexivity.
apply MP with A.
exact N.
exact U.
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
  pose (r:=Hax empctx PROCAI _ (Ha5 s (CONJ G))).
  apply invDed in r.  apply invDed in r.
  apply weak with (A:=s) in a1.
  apply weak with (A:=CONJ G) in a1.

  assert (K:PR (lf2ft [CONJ G;s]) PROCAI (DISJ D)). (*[CONJ G;s]*)
  apply MP with (A:=s-/\ CONJ G).

 unfold lf2ft. simpl.
Abort.
(*
-- destruct r. unfold add2ctx in a.
apply hyp.
destruct a as [a|[a|a]].
left. assumption.
right. left. assumption.
destruct a.
apply Hax. assumption.
apply MP with (A:=A). assumption.
STOP HERE 
unfold empctx in a.
 simpl in a.
 simpl in r.
 unshelve eapply PR_eqv. *)
(* good for "list Fo"
  exact r. exact a1.
  apply Ded.
  apply permut with (L1:=[CONJ G;s]).
  2 : exact K.
  simpl.
  firstorder.
Defined.*)
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

(*assert (asse:PR [CONJ G] PROCAI (s -\/ DISJ D)).
admit.
simpl in asse.
pose (Q:= Hax [] PROCAI _ (Ha5 s (CONJ G))).
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
End Prop_mod.
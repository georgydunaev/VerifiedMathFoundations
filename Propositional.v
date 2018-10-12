(* Here will be theorems about propositional logic.
Then I'll decide how to unite it with the rest. *)

(* TODO RENAME and UNIFY *)
Require Import Relations.
Require Import Classes.RelationClasses.
Require Export Coq.Vectors.Vector.
Require Import Coq.Structures.Equalities.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".

Require Poly.
Export Poly.
(*Export Poly.ModProp.*)

Module  Formulas_mod (PropVars : UsualDecidableTypeFull).

Inductive Fo :=
 |Atom (p:PropVars.t) :> Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
.

Notation " x --> y ":=(Impl x y) (at level 80).
Notation " x -/\ y ":=(Conj x y) (at level 80).
Notation " x -\/ y ":=(Disj x y) (at level 80).

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
Inductive PROCA : Fo -> Type :=
| Ha1  : forall A B, PROCA (A-->(B-->A))
| Ha2  : forall A B C, PROCA ((A-->(B-->C))-->((A-->B)-->(A-->C)))
.
Section PR.
Context (ctx:list Fo).
Context (axs:Fo -> Type).
Inductive PR : Fo -> Type :=
| hyp (A : Fo) : (InL A ctx) -> PR A
| Hax :> forall (A : Fo), (axs A) -> PR A
| MP (A B: Fo) : (PR A)->(PR (Impl A B))->(PR B)
.
End PR.
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
Show Proof.
Check (H0 y1 _ _ y1).
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
+ simpl in * |- *.
  intro x.
  unshelve apply (IHPR2 x).
  unshelve apply R_reflexive.
  unshelve apply IHPR1.
Unshelve.
exact (R_transitive y y0 y1 H1 H3).
exact H4.
Defined.

Check nil%list.
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

Lemma lem1 G D s g (J1:SubFo s g) 
(a1: incpa (s :: G) D )
(a2: incpa G (s :: D) ) : incpa G D.
Proof.
unfold incpa in * |- *.
simpl in * |- *.
Abort.

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
End Formulas_mod.
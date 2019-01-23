(* Here is Kripke semantics and attempt to prove completeness *)
(* Contents:
   # Completeness
*)
(* TODO RENAME and UNIFY *)
Require Import Relations.
Require Import Classes.RelationClasses.
Require Export Coq.Vectors.Vector.
Require Import Coq.Structures.Equalities.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Import PropLang.

(*
Require Poly.
Export Poly.
*) (*Export Poly.ModProp.*)

Module Prop_mod (PropVars : UsualDecidableTypeFull).

 Module XLang := Lang PropVars.
 Import XLang.

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

(*Section PR.
Context (ctx:Fo -> Type). (*Context (ctx:list Fo).*)
Context (axs:Fo -> Type).
Inductive PR : Fo -> Type :=
| hyp (A : Fo) : (ctx A) -> PR A
| Hax :> forall (A : Fo), (axs A) -> PR A
| MP (A B: Fo) : (PR A)->(PR (Impl A B))->(PR B)
.
End PR.*)














(** ==== COMPLETENESS ==== **)
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


Export List.ListNotations.
(* Both are inconsistent then (G,D) is inconsistent*)
Lemma lem1_0 G D s g (J1:SubFo s g) 
(a1: incpa (s :: G) D )
(a2: incpa G (s :: D) ) : incpa G D.
Proof.
unfold incpa in * |- *.
simpl in * |- *.
apply DedI.
apply MP with (s-\/(DISJ D)).
+ apply invDedI in a2.
  exact a2.
+ apply MP with (DISJ D --> DISJ D).
  apply AtoA_I.
  apply MP with (s --> DISJ D).
  2 : {apply Hax. apply Ha8. }
  pose (r:=Hax empctx PROCAI _ (Ha5 s (CONJ G))).
  apply invDedI in r.  apply invDedI in r.
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
Require Setoid.
Require Bool.Bool.

Definition ap {A B}{a0 a1:A} (f:A->B) (h:a0=a1):((f a0)=(f a1))
:= match h in (_ = y) return (f a0 = f y) with
   | eq_refl => eq_refl
   end.

Theorem SomeInj {foo} :forall (a b : foo), Some a = Some b -> a = b.
Proof.
  intros a b H.
  inversion H.
  reflexivity.
Defined.

Lemma EqualThenEquiv A B: A=B -> (A<->B). intro H. rewrite H. exact (iff_refl B). Defined.

Lemma AND_EQV : forall A0 B0 A1 B1 : Prop, 
(A0 <-> A1) -> (B0 <-> B1) -> ((A0 /\ B0) <-> (A1 /\ B1)).
Proof.
intros A0 B0 A1 B1 H0 H1.
rewrite H0.
rewrite H1.
reflexivity.
Defined.

Lemma OR_EQV : forall A0 B0 A1 B1 : Prop, 
(A0 <-> A1) -> (B0 <-> B1) -> ((A0 \/ B0) <-> (A1 \/ B1)).
Proof.
intros A0 B0 A1 B1 H0 H1.
rewrite H0.
rewrite H1.
reflexivity.
Defined.

Lemma IMP_EQV : forall A0 B0 A1 B1 : Prop, 
(A0 <-> A1) -> (B0 <-> B1) -> ((A0 -> B0) <-> (A1 -> B1)).
Proof.
intros A0 B0 A1 B1 H0 H1.
rewrite H0.
rewrite H1.
reflexivity.
Defined.

Lemma FORALL_EQV {X}: forall A0 A1 : X -> Prop, 
(forall m, A0 m <-> A1 m) -> ((forall m:X, A0 m) <-> (forall m:X, A1 m)).
Proof.
intros A0 A1 H0.
split.
+ intros.
  rewrite <- H0.
  exact (H m).
+ intros.
  rewrite -> H0.
  exact (H m).
Defined.

Lemma EXISTS_EQV {X}: forall A0 A1 : X -> Prop, 
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

Import Bool.
Lemma orb_elim (a b:bool): ((a||b)=false)->((a=false)/\(b=false)).
Proof.
intros. destruct a,b. 
simpl in H. inversion H.
simpl in H. inversion H.
firstorder.
firstorder.
Defined.

Lemma orb_intro (a b:bool): ((a=false)/\(b=false))->((a||b)=false).
Proof.
intros. firstorder.
Defined.

(*lm2*)
Theorem conj_true_then_right (a b :bool)(G:true = (a && b) ): true = b.
Proof.
destruct a.
trivial.
inversion G.
Defined.

Theorem bool_eq_true_or_false (rr:bool): (true=rr \/ rr=false).
Proof.
destruct rr; firstorder.
Defined.



Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint A2 l :fold_left orb l true = true.
Proof.
destruct l; simpl.
reflexivity.
apply A2.
Defined.

Theorem A1 (x y:bool): (orb x y = false)->(x=false)/\(y=false).
Proof. intro H. destruct x, y; firstorder || inversion H. Defined.

Fixpoint A0 b l : fold_left orb (b :: l) false = orb b (fold_left orb l false) .
Proof.
destruct l.
simpl. firstorder.
simpl.
destruct b.
simpl.
apply A2.
simpl.
reflexivity.
Defined.

Fixpoint all_then_some (l:list bool) {struct l}:
(List.fold_left orb l false) = false ->
(forall (p:nat), (List.nth p l false) = false).
Proof.
intros.
destruct l. simpl. destruct p; trivial.
simpl.
rewrite A0 in H.
pose (Q:=A1 _ _ H).
destruct Q.
destruct p. trivial.
apply all_then_some.
trivial.
Defined.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Fixpoint B2 (n:nat) (l:t bool n) :fold_left orb true l  = true.
Proof.
destruct l; simpl.
reflexivity.
apply B2.
Defined.

Fixpoint B0 b (n:nat) (l:t bool n) : 
fold_left orb false (b :: l)  = orb b (fold_left orb false l) .
Proof.
destruct l.
simpl. firstorder.
simpl.
destruct b.
simpl.
apply B2.
simpl.
reflexivity.
Defined.

Definition G h (n:nat) (l:Vector.t bool n) : Prop :=
 @eq bool (@fold_left bool bool orb false (S n) (cons bool h n l)) false.

Print IDProp.
Definition mIDProp : Prop := (forall A : Prop, A -> A).
(*Check False_ind (@IDProp).*)

Definition McaseS {A} (P : forall {n}, t A (S n) -> Prop)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with
  |h :: t => H h t
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

(*
Check McaseS.
Definition McaseSs {A} (P : forall {n}, t A (S n) -> Prop)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v.
induction v.
destruct v.
Check @IDProp.
Check False_ind.
*)
(* useless
Definition McaseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Prop)
  (H : forall h t, P (h :: t)), P v :=
  match v with
  | h :: t => fun P H => H h t
  | _ => fun devil => False_ind (@IDProp) devil
  end.
*)

Lemma vp1 (n:nat) (l : t bool (S n)) : exists (q:bool) (m:t bool n), l = (q::m).
Proof.
apply (@McaseS bool (fun n => 
fun (l : t bool (S n)) => exists (q : bool) (m : t bool n), l = q :: m)).
intros.
exists h.
exists t.
reflexivity.
Defined.

Fixpoint all_then_someV (n:nat) (l:Vector.t bool n) {struct l}:
(Vector.fold_left orb false l ) = false ->
(forall p, (Vector.nth l p  ) = false).
Proof.
intros.
(*induction*)
destruct l (*eqn:equa*).
inversion p. (* simpl. destruct p; trivial.*)
fold G in H.
assert (vari : G h n l).
exact H.
clear H.
revert h l vari.
set (P := fun n p => forall (h : bool) (l : t bool n) (_ : G h n l),
@eq bool (@nth bool (S n) (cons bool h n l) p) false).
revert n p.
fix loop 1.
intros n;revert n.
unshelve eapply (@Fin.rectS P).
unfold P.
intros.
simpl.
unfold G in H.
rewrite -> (B0 h n l) in H.
pose (Q:=A1 _ _ H).
destruct Q as [H0 H1].
exact H0.
(* OK!! *)
unfold P.
intros.
unfold G in H0.
simpl in  |- *.
rewrite -> (B0 h (S n) l) in H0.
pose (Q:=A1 _ _ H0).
destruct Q as [HH0 HH1].
pose (YO := vp1 n l).
destruct YO as [YO1 [YO2 YO3]].
rewrite -> YO3.
apply H.
unfold G.
rewrite <- YO3.
exact HH1.
Defined.
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

Definition G h (n:nat) (l:Vector.t bool n) := 
 @eq bool (@fold_left bool bool orb false (S n) (cons bool h n l)) false.


Definition McaseS {A} (P : forall {n}, t A (S n) -> Prop)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with
  |h :: t => H h t
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

Definition McaseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Prop)
  (H : forall h t, P (h :: t)), P v :=
  match v with
  | h :: t => fun P H => H h t
  | _ => fun devil => False_ind (@IDProp) devil
  end.


Lemma vp1 (n:nat) (l : t bool (S n)) : exists (q:bool) (m:t bool n), l = (q::m).
Check @caseS bool.
Check @McaseS bool (fun n => 
fun (l : t bool (S n)) => exists (q : bool) (m : t bool n), l = q :: m).
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
Check @Vector.rectS .
Check @Fin.rectS .
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
Check B0 h n l.
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
(* USE H!!!*)


pose (YO := vp1 n l).
destruct YO as [YO1 [YO2 YO3]].
rewrite -> YO3.
apply H.
unfold G.
rewrite <- YO3.
exact HH1.
Defined.
(*********************** THE END ***********)
(*
destruct l.
eapply loop.
unfold G.
exact H0.
Defined.

rewrite -> (B0 h (S n) l) in H0.
pose (Q:=A1 _ _ H0).
destruct Q as [HH0 HH1].
simpl in loop.
eapply all_then_someV.
exact HH1.
Defined.
simpl in H0.
(*simpl in H.*)
exact H0.
Defined.

simpl in P.
apply P.
Check @Fin.FS.
eapply all_then_someV.
unfold G in H0.
exact H0.
Defined.



simpl in H.
unshelve eapply all_then_someV.

unshelve eapply P.
simpl.
simpl in * |- *.
exact n.
destruct p.


Definition rectS (P: forall {n}, t (S n) -> Type)
(*pose vari := *)
(*simpl.*)
destruct p.



rewrite B0 in H.
pose (Q:=A1 _ _ H).
destruct Q.
Definition openVector_when_S
   h (n: nat) : Vector.t bool n -> Prop :=
  match n return Vector.t bool n -> Prop with
    | O => fun _ => True
    | S n => fun t => forall p : Fin.t (S (S n)),
 @eq bool (@nth bool (S (S n)) (VectorDef.cons bool h (S n) t) p) false
  end.
revert  l t equa H  H1.
destruct p.


revert p.
revert  l t equa H IHt H1.
intro p.
destruct n.
destruct p.
intros.
si1mpl.
induction p.

destruct n.
admit.
rewrite <- openVector_when_S.
Definition openVector_when_S
  (A: Type) h (n: nat) : Vector.t A n -> Fin.t n -> Prop :=
  match n return Vector.t A n -> Fin.t n -> Prop with
    | O => fun _ _ => True
    | S n => fun t p => @eq bool (@nth bool (S n) (VectorDef.cons bool h n t) p) false
  end.

Check 
induction p.
refine (
match p as ho with
| @Fin.F1  => _ 
| @Fin.FS b m => _
end ).
(*apply IHt.*)
simpl in * |-.
assert (W : p = @Fin.F1 n).
admit.
rewrite -> W.
simpl. exact H0.
assert (Y: b=n).
admit.
rewrite -> Y in m.
assert (W2 : p = @Fin.FS n m).
admit.
rewrite -> W2.
simpl.
apply all_then_someV.
trivial.
Defined.

Fixpoint all_then_someV (n:nat) (l:Vector.t bool n) {struct l}:
(Vector.fold_left orb false l ) = false ->
(forall p, (Vector.nth l p  ) = false).
Proof.
intros.
destruct l eqn:equa.
inversion p. (* simpl. destruct p; trivial.*)
(*simpl.*)
rewrite B0 in H.
pose (Q:=A1 _ _ H).
destruct Q.
Check caseS.
Check 
fun n p => forall l, @eq bool (@nth bool (S n) (cons bool h n l) p) false.
pose (P:=fun n p => 
forall l, @eq bool (@nth bool (S n) (cons bool h n l) p) false).
Check Fin.caseS P.
unshelve eapply (Fin.caseS P).
simpl.
(h :: l)[@p] = false
(*revert l H H1. *)
(*Unset  Printing Synth.*)
refine (
match p as ho with
| @Fin.F1  => _ 
| @Fin.FS b m => _
end ).
assert (W : p = @Fin.F1 n).
admit.
rewrite -> W.
simpl. exact H0.
assert (Y: b=n).
admit.
rewrite -> Y in m.
assert (W2 : p = @Fin.FS n m).
admit.
rewrite -> W2.
simpl.
apply all_then_someV.
trivial.
Defined.

(*trivial.
(*induction p.*)
Check caseS.
  destruct p. trivial.
*)
*)
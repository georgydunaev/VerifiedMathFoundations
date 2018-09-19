(* PUBLIC DOMAIN *)
(* Author: Georgy Dunaev, georgedunaev@gmail.com *)
Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.
(*Require Import Logic.FunctionalExtensionality.*)
Require Import Coq.Program.Wf.
Require Import Lia.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations".
Require Export UNIV_INST.
Require Export eqb_nat.
(*Require Import Logic.ClassicalFacts.*)
(*Axiom EquivThenEqual: prop_extensionality.*)

Module ModProp.
Definition Omega := Prop.
Definition OFalse := False.
Definition OAnd := and.
Definition OOr := or.
Definition OImp := (fun x y:Omega => x->y).
Notation Osig := ex.
End ModProp.

Module ModType.
Notation Omega := Type.
Definition OFalse := False.
Print "+"%type.
Definition OAnd := prod.
Definition OOr := sum.
Definition OImp := (fun x y:Omega => x->y).
Notation Osig := sigT.
End ModType.


Module ModBool.
Definition Omega := bool.
Definition OFalse := false.
Definition OAnd := andb.
Definition OOr := orb.
Definition OImp := implb.
End ModBool.


Inductive myeq (A : Type) (x : A) : A -> Type :=
| myeq_refl : myeq A x x.


Fixpoint myvec_comp_as {A B C} (f:B->C) (g:A->B) (n:nat) (t0: Vector.t A n) :
myeq _ (Vector.map f (Vector.map g t0))
(Vector.map (fun x=>(f(g x))) t0).
Proof.
destruct t0.
simpl.
reflexivity.
simpl.
rewrite -> myvec_comp_as.
reflexivity.
Defined.

Fixpoint vec_comp_as {A B C} (f:B->C) (g:A->B) (n:nat) (t0: Vector.t A n) :
Vector.map f (Vector.map g t0) =
Vector.map (fun x=>(f(g x))) t0.
Proof.
destruct t0.
simpl.
reflexivity.
simpl.
rewrite -> vec_comp_as.
reflexivity.
Defined.


Module VS.
(* TODO: *)
Section sec0.
Definition SetVars := nat.
Variable FuncSymb : Set.

(*Definition FuncSymb := nat.*)
Definition PredSymb := nat.
Record FSV := {
 fs : FuncSymb;
 fsv : nat;
}.
Record PSV := MPSV{
 ps : PredSymb;
 psv : nat;
}.
Check MPSV 0 0.
Notation A1Type:=Set.
Unset Elimination Schemes.
Inductive Terms : A1Type :=
| FVC :> SetVars -> Terms
| FSC (f:FSV) : (Vector.t Terms (fsv f)) -> Terms.
Set Elimination Schemes.

Definition Terms_rect (T : Terms -> Type)
                      (H_FVC : forall sv, T (FVC sv))
                      (H_FSC : forall f v, (forall n, T (Vector.nth v n)) -> T (FSC f v)) :=
  fix loopt (t : Terms) : T t :=
    match t with
    | FVC sv  => H_FVC sv
    | FSC f v =>
      let fix loopv s (v : Vector.t Terms s) : forall n, T (Vector.nth v n) :=
        match v with
        | @Vector.nil _ => Fin.case0 _
        | @Vector.cons _ t _ v => fun n => Fin.caseS' n (fun n => T (Vector.nth (Vector.cons _ t _ v) n))
                                                      (loopt t)
                                                      (loopv _ v)
        end in
      H_FSC f v (loopv _ v)
    end.

Definition Terms_ind (T : Terms -> Prop)
                      (H_FVC : forall sv, T (FVC sv))
                      (H_FSC : forall f v, (forall n, T (Vector.nth v n)) -> T (FSC f v)) :=
  fix loopt (t : Terms) : T t :=
    match t with
    | FVC sv  => H_FVC sv
    | FSC f v =>
      let fix loopv s (v : Vector.t Terms s) : forall n, T (Vector.nth v n) :=
        match v with
        | @Vector.nil _ => Fin.case0 _
        | @Vector.cons _ t _ v => fun n => Fin.caseS' n (fun n => T (Vector.nth (Vector.cons _ t _ v) n))
                                                      (loopt t)
                                                      (loopv _ v)
        end in
      H_FSC f v (loopv _ v)
    end.


(*Formulas*)
(*Unset Elimination Schemes.*)
Inductive Fo :=
|Atom (p:PSV) : (Vector.t Terms (psv p)) ->  Fo
|Bot :Fo
|Conj:Fo->Fo->Fo
|Disj:Fo->Fo->Fo
|Impl:Fo->Fo->Fo
|Fora(x:SetVars)(f:Fo): Fo
|Exis(x:SetVars)(f:Fo): Fo
.
(*Set Elimination Schemes.
Section Fo_rect_section.
Definition Fo_rect (T : Fo -> Type)
                      (H_FVC : forall sv, T (FVC sv))
                      (H_FSC : forall f v, (forall n, T (Vector.nth v n)) -> T (FSC f v)) :=
  fix loopt (t : Terms) : T t :=
    match t with
    | FVC sv  => H_FVC sv
    | FSC f v =>
      let fix loopv s (v : Vector.t Terms s) : forall n, T (Vector.nth v n) :=
        match v with
        | @Vector.nil _ => Fin.case0 _
        | @Vector.cons _ t _ v => fun n => Fin.caseS' n (fun n => T (Vector.nth (Vector.cons _ t _ v) n))
                                                      (loopt t)
                                                      (loopv _ v)
        end in
      H_FSC f v (loopv _ v)
    end.
End Fo_rect_section.*)


(* Substitution *)

Fixpoint substT (t:Terms) (xi: SetVars) (u:Terms): Terms. 
Proof.
destruct u.
2 : { refine (FSC _ _). 
Check @Vector.map.
Check @Vector.map _ _ (substT t xi) _ t0.
exact ( @Vector.map _ _ (substT t xi) _ t0 ). }

{
(*Check my.beq_natP s xi.*)
destruct (PeanoNat.Nat.eqb s xi).
Print bool.
exact t.
exact s. }
(*Show Proof.*)
Defined.


Fixpoint isParamT (xi : SetVars) (t : Terms) {struct t} : bool :=
   match t with
   | FVC s => PeanoNat.Nat.eqb s xi
   | FSC f t0 => Vector.fold_left orb false (Vector.map (isParamT xi) t0)
   end.

Fixpoint isParamF (xi:SetVars) (f:Fo): bool.
Proof.
(*elim f; intros. *)
destruct f.
Show Proof.
Search "Exists".
exact (Vector.fold_left orb false (Vector.map (isParamT xi) t)).
exact false.
Show Proof.
exact (orb (isParamF xi f1) (isParamF xi f2)).
exact (orb (isParamF xi f1) (isParamF xi f2)).
exact (orb (isParamF xi f1) (isParamF xi f2)).
Show Proof.
exact (match (PeanoNat.Nat.eqb x xi) with
       | true => false
       | false => (isParamF xi f)
       end).
exact (match (PeanoNat.Nat.eqb x xi) with
       | true => false
       | false => (isParamF xi f)
       end).
Show Proof.
Defined.

Fixpoint substF (t:Terms) (xi: SetVars) (u : Fo): option Fo. 
Proof.
pose(g := substT t xi).
pose(f := substF t xi).
destruct u.
refine (Some (Atom p _)).
exact (Vector.map g t0).
exact (Some Bot).
 exact (
 match (f u1),(f u2) with
 | Some f0,Some f1 => (Some (Conj f0 f1))
 | _,_ => None
 end).
 exact (
 match (f u1),(f u2) with
 | Some f0,Some f1 => (Some (Disj f0 f1))
 | _,_ => None
 end).
 exact (
 match (f u1),(f u2) with
 | Some f0,Some f1 => (Some (Impl f0 f1))
 | _,_ => None
 end).
(*destruct (isParamF xi (Fora x0 u)).*)
refine (match (isParamF xi (Fora x u)) with 
| true => match (isParamT x t) with 
          | false => match substF t xi u with
                    | Some q => Some (Fora x q)
                    | None => None
                    end
          | true => None
          end
| false => Some (Fora x u) end).
refine (match (isParamF xi (Exis x u)) with 
| true => match (isParamT x t) with 
          | false => match substF t xi u with
                    | Some q => Some (Exis x q)
                    | None => None
                    end
          | true => None
          end
| false => Some (Exis x u) end).
Defined.


Definition Top:Fo := Impl Bot Bot.

Notation " x --> y ":=(Impl x y) (at level 80).
(*
Notation " u '[' t >> xi ] ":=(substT t xi u ) (at level 10).
Set Warnings "-notation-overridden".
Notation " ph [ t | xi ] ":=(substF t xi ph ) (at level 10).
(*Set Warnings "default".*)
Check fun (t:Terms) (x:SetVars) => ( t [ t >> x ]).
Check fun (t:Terms) (x:SetVars) (ph:Fo) => ( ph [ t | x ] ).
*)

Open Scope list_scope.
Print List.In.
Locate "+".
Print sum.
Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.

Inductive PR (axi:list Fo) : Fo -> Type :=
| hyp (A : Fo): (InL A axi)-> @PR axi A
| a1 (A B: Fo) : @PR axi (Impl A (Impl B A))
| a2 (A B C: Fo) : @PR axi ((A-->(B-->C))-->((A-->B)-->(A-->C)))
| a12 (ph: Fo) (t:Terms) (xi:SetVars)
: @PR axi (match (substF t xi ph) with 
      | Some q => (Impl (Fora xi ph) q)
      | None => Top
      end)
| b1 (ps ph: Fo) (xi:SetVars) (H:isParamF xi ps = false):
@PR axi (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
| MP (A B: Fo) : (@PR axi A)->(@PR axi (Impl A B))->(@PR axi B)
| GEN (A : Fo) (xi:SetVars): (@PR axi A)->(@PR axi (Fora xi A))
.

Check @PR.
Definition AtoA (A:Fo) : PR (List.nil) (A-->A).
Proof.
apply (MP nil (A-->(A-->A)) _).
apply a1.
apply (MP nil (A-->((A-->A)-->A)) _).
apply a1.
apply a2.
Defined.

Definition B1 (ps ph:Fo) (xi:SetVars) (H:isParamF xi ps = false): 
 PR nil (ps --> ph) -> PR nil (ps --> Fora xi ph).
Proof.
intro q.
apply (MP nil (Fora xi (ps --> ph))).
+ apply GEN.
  exact q.
+ apply (b1 _).
  exact H.
Defined.

Definition gen (A:Fo) (xi:SetVars) (*Generalization from Bernay's rule*)
: PR nil (A) -> PR nil (Fora xi A).
Proof.
intro q.
apply (MP nil Top).
unfold Top.
exact (AtoA Bot).
apply (MP nil (Fora xi (Top --> A))).
* apply GEN.
  apply (MP nil A).
  + exact q.
  + apply a1.
* apply b1.
  trivial.
Defined.

Definition neg (f:Fo):= (Impl f Bot).

Definition a1i (A B : Fo)(l : list Fo):(PR l B)->(PR l (Impl A B)).
Proof.
intros x.
apply (MP l B).
exact x.
apply a1.
Defined.

Fixpoint weak (A F:Fo) (l :list Fo) (x: (PR l F)) : (PR (A::l) F).
Proof.
destruct x.
apply hyp.
apply inr. (*or_intror *)
exact i.
apply a1.
apply a2.
apply a12.
apply b1.
assumption.
apply (@MP _ A0).
apply weak.
exact x1.
apply weak.
exact x2.
apply GEN. (* Order is not important! *)
apply weak. (* Order is not important! *)
exact x.
Defined.

Fixpoint weaken (F:Fo) (li l :list Fo) (x: (PR l F)) {struct li}: (PR (li ++ l) F).
Proof.
destruct li.
simpl.
exact x.
simpl.
simple refine (@weak f F (li ++ l) _).
apply weaken.
exact x.
Defined.

(*Export List Notations.*)
Fixpoint notGenWith (xi:SetVars)(l:list Fo)(B:Fo)(m:(PR l B)){struct m}:bool.
Proof.
destruct m. 
exact true.
exact true.
exact true.
exact true.
exact true.
exact (andb (notGenWith xi l _ m1) (notGenWith xi l _ m2)).
exact (andb (negb (PeanoNat.Nat.eqb xi xi0)) (notGenWith xi l _ m) ).
Defined.
Check isParamF.
(*Check fun A B=> forall xi:SetVars, (true = isParamF xi A)->(notGenWith xi m).*)
Fixpoint HA xi : true = PeanoNat.Nat.eqb (xi) (xi).
Proof.
destruct xi.
reflexivity.
simpl.
exact (HA xi).
Defined.

Fixpoint ZX (xi:SetVars) :true = negb (PeanoNat.Nat.eqb xi xi) -> False.
Proof.
intro q.
destruct xi.
compute in q.
inversion q.
rewrite <- HA in q.
inversion q.
Defined.


Theorem lm (a b :bool)(G:true = (a && b) ): true = a.
Proof.
destruct a.
trivial.
inversion G.
Defined.

Theorem lm2 (a b :bool)(G:true = (a && b) ): true = b.
Proof.
destruct a.
trivial.
inversion G.
Defined.

Theorem N (rr:bool): (true=rr \/ rr=false).
Proof.
destruct rr; firstorder.
Defined.

Fixpoint Ded (A B:Fo)(il:list Fo)(m:(PR (cons A il) B)) 
(H:forall xi:SetVars, (true = isParamF xi A)->(true=notGenWith xi _ _ m))
{struct m}:(PR il (A-->B)).
Proof.
destruct m. (*as [i|i|i|i|i|i|i].*)
+ unfold In in i.
  simpl in i .
  destruct i .
  * rewrite <- e.
    pose (J:=weaken _ il nil (AtoA A )).
    rewrite app_nil_r in J.
    exact J.
(*exact (weaken _ il nil (AtoA A )).
apply weak.
exact (AtoA A ).
exfalso.*)
  * simpl in H.
    apply a1i.
    exact (hyp il _ i).
+ apply a1i.
  apply a1.
+ apply a1i.
  apply a2.
+ apply a1i.
  apply a12.
+ apply a1i.
  apply b1.
  trivial.
+ apply (MP _ (A-->A0)).
- simple refine (@Ded _ _ _ _ _).
  exact m1.
  intros xi H0.
  pose (W:=H xi H0).
  simpl in W.
  pose (J:=notGenWith xi (A :: il) A0 m1).
  try reflexivity.
  fold J.
  fold J in W.
  apply (lm _ _ W).
-
apply (MP _ (A-->(A0-->B))).
simple refine (@Ded _ _ _ _ _).
  exact m2.
  intros xi H0.
  pose (W:=H xi H0).
  simpl in W.
  apply (lm2 _ _ W).
(*Last part about GEN*)
apply a2.
+
apply (MP _ (Fora xi (A-->A0))).
apply GEN.
simple refine (@Ded _ _ _ _ _).
  exact m.
  intros xi0 H0.
  pose (W:=H xi0 H0).
  simpl in W.
* exact (lm2 _ _ W).
* simpl.
apply b1.
pose (r := isParamF xi A).
pose (U := H xi).
fold r in U |- *.
simpl in U.

destruct (N r).
pose (C:= lm _ _(U H0)).
exfalso.
exact (ZX _ C).
exact H0.
Show Proof.
Defined.

(*Fixpoint Ded (A B:Fo)(m:(PR (cons A nil) B)) *)

Definition lm3 (a b :bool)(A: true = a)(B: true = b):true = (a && b) 
:=
 (if a as a0 return (true = a0 -> true = a0 && b)
  then
   fun _ : true = true =>
   (if b as b0 return (true = b0 -> true = true && b0)
    then fun _ : true = true => eq_refl
    else fun B0 : true = false => B0) B
  else
   fun A0 : true = false =>
   (if b as b0 return (true = b0 -> true = false && b0)
    then fun _ : true = true => A0
    else fun _ : true = false => A0) B) A.
(*destruct a,b.
reflexivity.
simpl.
exact B.
simpl.
exact A.
simpl.
exact A.
Show Proof.
Defined.*)


Fixpoint forClosed (A B:Fo)(m:(PR (cons A nil) B)):
(forall xi:SetVars, (false = isParamF xi A))
->
(forall xi:SetVars, (true = isParamF xi A)->(true=notGenWith xi _ _ m)).
Proof.
intros H xi Q.
destruct m; simpl; try reflexivity.
+ apply lm3.
  simple refine (@forClosed _ _ _ _ _ _); assumption.
  simple refine (@forClosed _ _ _ _ _ _); assumption.
+ apply lm3.
  2 : simple refine (@forClosed _ _ _ _ _ _); assumption.
  pose (U:=H xi).
  rewrite <- Q in U.
  exfalso.
  inversion U.
Show Proof.
Defined.

Fixpoint SimplDed (A B:Fo) (il: list Fo)(m:(PR (cons A il) B))
(NP:forall xi:SetVars, (false = isParamF xi A)) 
{struct m}:(PR il (A-->B)).
Proof.
simple refine (Ded _ _ _ _ _).
exact m.
intros xi H.
rewrite <- NP in H.
inversion H.
Defined.


(* Here we choose an interpretation. *)
(*Export ModBool.*)
Export ModProp. (* + classical axioms *)
(*Export ModType. It doesn't work properly. *)
(** Soundness theorem section **)
Section cor.
 (* Truth values*)
Context (X:Type).
Check FSV.
(*Context (val:SetVars->X).*)
Context (fsI:forall(q:FSV),(Vector.t X (fsv q))->X).
Context (prI:forall(q:PSV),(Vector.t X (psv q))->Omega).
(*Context (prI:forall(q:PSV),(Vector.t X (psv q))->Prop).*)

Fixpoint teI (val:SetVars->X) (t:Terms): X.
Proof.
destruct t.
exact (val s).
refine (fsI f _).
simple refine (@Vector.map _ _ _ _ _).
2 : apply teI.
exact val.
exact t.
Show Proof.
Defined.
(*
Fixpoint foI (val:SetVars->X) (f:Fo): Omega.
Proof.
destruct f.
+ refine (prI p _).
  apply (Vector.map  (teI val)).
  exact t.
+ exact false.
+ exact ( andb (foI val f1) (foI val f2)).
+ exact (  orb (foI val f1) (foI val f2)).
+ exact (implb (foI val f1) (foI val f2)).
+  (*Infinite conjunction!!!*)
 Show Proof.
*)

(** (\pi + (\xi \mapsto ?) ) **)
Definition cng (val:SetVars -> X) (xi:SetVars) (m:X) :=
(fun r:SetVars =>
match PeanoNat.Nat.eqb r xi with
| true => m
| false => (val r)
end).

(*Inductive foI (val:SetVars->X) (f:Fo): Prop
:=
   | cAtom p t0 => ?Goal0@{t:=t0}
.
   | cBot => ?Goal
   | cConj f1 f2 => ?Goal1
   | cDisj f1 f2 => ?Goal2
   | cImpl f1 f2 => ?Goal3
   | cFora x f0 => ?Goal4@{f:=f0}
   | cExis x f0 => ?Goal5@{f:=f0}
.*)

Fixpoint foI (val:SetVars->X) (f:Fo): Omega.
Proof.
destruct f.
Show Proof.
+ refine (prI p _).
  apply (@Vector.map Terms X (teI val)).
  exact t.
+ exact OFalse.
+ exact ( OAnd (foI val f1) (foI val f2)).
+ exact (  OOr (foI val f1) (foI val f2)).
+ exact ( OImp (foI val f1) (foI val f2)).
Show Proof.
+ exact (forall m:X, foI (cng val x m) f).
(*forall m:X, foI (fun r:SetVars =>
match Nat.eqb r x with
| true => m
| false => (val r)
end
) f*)
(*Locate "exists".*)
+ exact (Osig (fun m:X => foI (fun r:SetVars =>
match PeanoNat.Nat.eqb r x with
| true => m
| false => (val r)
end
) f)
).
(*+ exact (exists m:X, foI (fun r:SetVars =>
match PeanoNat.Nat.eqb r x with
| true => m
| false => (val r)
end
) f
).*)
Defined.

Definition ap {A B}{a0 a1:A} (f:A->B) (h:a0=a1):((f a0)=(f a1))
:= match h in (_ = y) return (f a0 = f y) with
   | eq_refl => eq_refl
   end.


Section Lem1.
(*Context (t : Terms).*)

(* page 136 of the book *)
Definition lem1 (t : Terms) : forall (u :Terms) (xi : SetVars) (pi : SetVars->X) ,
(teI pi (substT t xi u))=(teI (cng pi xi (teI pi t)) u).
Proof.
fix lem1 1.
intros.
induction u as [s|f].
(*destruct u as [s|f] .*)
+ simpl.
  unfold cng.
  destruct (Nat.eqb s xi) eqn:ek. (* fsI as [H1|H2].*)
  * reflexivity.
  * simpl.
    reflexivity.
Show Proof.
+
  simpl. (* fsI teI *)
  destruct f.
  simpl.
  apply ap.
 simpl in * |- *.
apply (*Check *)
(proj1 (
eq_nth_iff X fsv0 
(Vector.map (teI pi) (Vector.map (substT t xi) v))
(Vector.map (teI (cng pi xi (teI pi t))) v)
)).
intros.
(*rewrite H0.*)
 simpl in * |- *.
(* now I need to show that .nth and .map commute *)
Check nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0.
rewrite -> (nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0).
Check nth_map (teI (cng pi xi (teI pi t))) v.
rewrite -> (nth_map (teI (cng pi xi (teI pi t))) v p2 p2 ).
Check nth_map (substT t xi) v p2 p2 eq_refl.
rewrite -> (nth_map (substT t xi) v p2 p2 eq_refl).
exact (H p2).
reflexivity.
Defined.

End Lem1.

Theorem SomeInj {foo} :forall (a b : foo), Some a = Some b -> a = b.
Proof.
  intros a b H.
  inversion H.
  reflexivity.
Defined.

Theorem eq_equ (A B:Prop) : A=B -> (A <-> B).
Proof.
intro p. 
destruct p.
firstorder.
Defined. (* rewrite p. firstorder. *)

Theorem conj_eq (A0 B0 A1 B1:Prop)(pA:A0=A1)(pB:B0=B1): (A0 /\ B0) = (A1 /\ B1).
Proof. destruct pA, pB; reflexivity. Defined.
Theorem disj_eq (A0 B0 A1 B1:Prop)(pA:A0=A1)(pB:B0=B1): (A0 \/ B0) = (A1 \/ B1).
Proof. destruct pA, pB; reflexivity. Defined.
Theorem impl_eq (A0 B0 A1 B1:Prop)(pA:A0=A1)(pB:B0=B1): (A0 -> B0) = (A1 -> B1).
Proof. destruct pA, pB; reflexivity. Defined.
Lemma dbl_cng pi xi m1 m2: forall q,(cng (cng pi xi m1) xi m2) q = (cng pi xi m2) q.
Proof. intro q. unfold cng. destruct (Nat.eqb q xi); reflexivity. Defined.


Theorem l01 h n v :
Vector.fold_left orb false (Vector.cons bool h n v) = Vector.fold_left orb (orb false h) v.
Proof.
simpl. reflexivity.
Defined.

Check all_then_someV.

Lemma all_then_someP (A:Type)(n:nat)(p:Fin.t (n)) (v:Vector.t A (n)) (P:A->bool)
(H : Vector.fold_left orb false (Vector.map P v) = false)
 : (P (Vector.nth v p)) = false.
Proof.
Check nth_map P v p p eq_refl.
rewrite <- (nth_map P v p p eq_refl).
apply all_then_someV. trivial.
Defined.

(* Not a parameter then not changed afted substitution (for Terms) *)
Lemma NPthenNCAST (u:Terms)(xi:SetVars)(t:Terms) (H:(isParamT xi u=false))
: (substT t xi u) = u.
Proof. induction u.
+ simpl in * |- *.
  rewrite H. reflexivity.
+ simpl in * |- *.
  apply ap.
apply eq_nth_iff.
intros p1 p2 ppe.
Check nth_map _ _ _ p2 ppe.
rewrite (nth_map _ _ _ p2 ppe).
apply H0.
simpl.
apply all_then_someP.
trivial.
Defined.

Lemma NPthenNCAST_vec:forall p xi t ts (H:(isParamF xi (Atom p ts)=false)), 
  (Vector.map (substT t xi) ts) = ts.
Proof.
  intros p xi t1 ts H.
  apply eq_nth_iff.
  intros p1 p2 H0.
  Check nth_map (substT t1 xi) ts p1 p2 H0.
  rewrite -> (nth_map (substT t1 xi) ts p1 p2 H0).
  apply NPthenNCAST.
  apply all_then_someP.
  simpl in H.
  exact H.
Defined.


(* Not a parameter then not changed afted substitution (for Formulas) *)
Fixpoint NPthenNCASF (mu:Fo) : forall (xi:SetVars)(t:Terms) (H:(isParamF xi mu=false))
   , substF t xi mu = Some mu .
Proof. (*induction mu eqn:u0.*)
destruct mu eqn:u0.
Check t.
* intros xi t0 H.
  simpl.
  rewrite -> NPthenNCAST_vec; (trivial || assumption).
* intros xi t H.
  simpl; trivial.
* intros xi t H.
  simpl.
  simpl in H.
  (*pose (Q:=A1 _ _ H).*)
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF .
  rewrite -> NPthenNCASF .
  (*rewrite -> IHf1 with xi t.
  rewrite -> IHf2 with xi t.*)
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF .
  rewrite -> NPthenNCASF .
  (*rewrite -> IHmu1 with xi t.
  rewrite -> IHmu2 with xi t.*)
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF .
  rewrite -> NPthenNCASF .
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (PeanoNat.Nat.eqb x xi) eqn:u2.
  trivial.
  destruct (isParamF xi f) eqn:u1.
  inversion H.
  trivial.
* simpl.
  intros xi t H.
  destruct (PeanoNat.Nat.eqb x xi) eqn:u2.
  trivial.
  destruct (isParamF xi f) eqn:u1.
  inversion H.
  trivial.
Defined.

(* p.137 *)
Section Lem2.

Lemma mqd x t pi m (H:isParamT x t = false): (teI (cng pi x m) t) = (teI pi t).
Proof.
induction t.
 simpl.
simpl in H.
unfold cng.
rewrite -> H.
reflexivity.
 simpl.
simpl in H.
apply ap.
apply eq_nth_iff.
intros.
Check nth_map (teI (cng pi x m)) v p1 p1 eq_refl.
rewrite -> (nth_map (teI (cng pi x m)) v p1 p1 eq_refl).
rewrite -> (nth_map (teI pi) v p2 p2 eq_refl).
rewrite <- H1.
apply H0.
exact (all_then_someP _ _ p1 _ (isParamT x) H).
Defined.

Lemma IOF xi : PeanoNat.Nat.eqb xi xi = true.
Proof.
induction xi.
simpl. trivial.
simpl. exact IHxi.
Defined.

(* USELESS THEOREM *)
Lemma cng_commT  x xi m0 m1 pi t :
PeanoNat.Nat.eqb x xi = false -> 
teI (cng (cng pi x m0) xi m1) t = teI (cng (cng pi xi m1) x m0) t.
Proof. intro i.
revert pi.
induction t; intro pi.
simpl.
unfold cng.
(*destruct (Nat.eqb x xi) eqn:j.
inversion i. NO*)
Check not_iff_compat (PeanoNat.Nat.eqb_eq x xi).
pose (n3:= proj1 (not_iff_compat (PeanoNat.Nat.eqb_eq x xi)) ).
Check proj2 (not_true_iff_false (PeanoNat.Nat.eqb x xi)).
pose (n4:= n3 (proj2 (not_true_iff_false (PeanoNat.Nat.eqb x xi)) i)).
Require Import Arith.Peano_dec.
Check eq_nat_dec.
destruct (PeanoNat.Nat.eq_dec sv xi).
rewrite -> e.
rewrite -> IOF.
destruct (PeanoNat.Nat.eq_dec x xi).
destruct (n4 e0).
pose (hi := (not_eq_sym n)).

Check not_true_iff_false .
pose (ih:= not_true_is_false _ (proj2 (not_iff_compat (PeanoNat.Nat.eqb_eq xi x)) hi)).
rewrite ih.
reflexivity.
pose (ih:= not_true_is_false _ (proj2 (not_iff_compat (PeanoNat.Nat.eqb_eq sv xi)) n)).
rewrite -> ih.
reflexivity.
simpl.
apply ap.
apply eq_nth_iff.
intros p1 p2 HU.

Check nth_map (teI (cng (cng pi x m0) xi m1)) v p1 p2 HU.
rewrite -> (nth_map (teI (cng (cng pi x m0) xi m1)) v p1 p2 HU).
Check nth_map.
rewrite -> (nth_map (teI (cng (cng pi xi m1) x m0)) v p2 p2 eq_refl).
apply H.
Defined.

Lemma EqualThenEquiv A B: A=B -> (A<->B). intro H. rewrite H. exact (iff_refl B). Defined.

Lemma ix W (P Q:W->Prop) (H: P = Q):(forall x, P x) =(forall y, Q y).
Proof.
rewrite H.
reflexivity.
Defined.

Lemma weafunT pi mu (q: forall z, pi z = mu z) t : teI pi t = teI mu t.
Proof.
induction t.
+ simpl. exact (q sv).
+ simpl. apply ap.
  apply eq_nth_iff.
  intros p1 p2 HU.
  rewrite -> (nth_map (teI pi) v p1 p2 HU).
  rewrite -> (nth_map (teI mu) v p2 p2 eq_refl).
  apply H.
Defined.
Print Omega.
Locate "<->". (* iff *)
Lemma weafunF pi mu (q: forall z, pi z = mu z) fi : foI pi fi <-> foI mu fi.
Proof.
revert pi mu q.
induction fi.
intros pi mu q.
+ simpl.
  apply EqualThenEquiv.
  apply ap.
  apply eq_nth_iff.
  intros p1 p2 HU.
  rewrite -> (nth_map (teI pi) t p1 p2 HU).
  rewrite -> (nth_map (teI mu) t p2 p2 eq_refl).
  apply weafunT.
  apply q.
+ simpl. reflexivity.
+ simpl. intros. 
  rewrite -> (IHfi1 pi mu q) (*weafunF pi mu q fi1*).
  rewrite -> (IHfi2 pi mu q) (*weafunF pi mu q fi2*).
  reflexivity.
+ simpl. intros. 
  rewrite -> (IHfi1 pi mu q) (*weafunF pi mu q fi1*).
  rewrite -> (IHfi2 pi mu q) (*weafunF pi mu q fi2*).
  reflexivity.
+ simpl.
  unfold OImp.
  split;
  intros;
  apply (IHfi2 pi mu q (*pi m0 m1 xe xi i*));
  apply H;
  apply (IHfi1 pi mu q (*pi m0 m1 xe xi i*));
  apply H0. (*twice*)
+ simpl.
  split.
  * intros.
    rewrite IHfi. (*weafunF.*)
    apply H.
    intro z.
    unfold cng.
    destruct (Nat.eqb z x).
    reflexivity.
    symmetry.
    apply q.
  * intros.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (Nat.eqb z x).
    reflexivity.
    apply q.
+ simpl.
  split.
  * intros.
destruct H as [m H].
exists m.
    rewrite IHfi. (*weafunF.*)
    apply H.
    intro z.
    unfold cng.
    destruct (Nat.eqb z x).
    reflexivity.
    symmetry.
    apply q.
  * intros.
destruct H as [m H].
exists m.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (Nat.eqb z x).
    reflexivity.
    apply q.
Defined.

Lemma cng_commF_EQV  xe xi m0 m1 pi fi :
PeanoNat.Nat.eqb xe xi = false -> 
(foI (cng (cng pi xe m0) xi m1) fi <-> foI (cng (cng pi xi m1) xe m0) fi).
Proof.
intros H.
apply weafunF.
intros z.
unfold cng.
destruct (PeanoNat.Nat.eqb z xi) eqn:e0, (PeanoNat.Nat.eqb z xe) eqn:e1.
pose (U0:= proj1 (PeanoNat.Nat.eqb_eq z xi) e0).
rewrite U0 in e1.
pose (U1:= proj1 (PeanoNat.Nat.eqb_eq xi xe) e1).
symmetry in U1.
pose (U2:= proj2 (PeanoNat.Nat.eqb_eq xe xi) U1).
rewrite U2 in H.
inversion H.
reflexivity. reflexivity. reflexivity.
Defined.

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
Lemma FORALL_EQV : forall A0 A1 : X -> Prop, 
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


Lemma lem2caseAtom : forall (p : PSV) (t0 : Vector.t Terms (psv p))
(t : Terms) (xi : SetVars) (pi : SetVars->X)
(r:Fo) (H:(substF t xi (Atom p t0)) = Some r) ,
foI pi r <-> foI (cng pi xi (teI pi t)) (Atom p t0).
Proof.
intros.
+  (*simpl in *|-*; intros r H.*)
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
apply EqualThenEquiv.
  (*apply eq_equ.*)
  apply ap.
  apply 
    (proj1 (
      eq_nth_iff X (psv p) 
      (Vector.map (teI pi) (Vector.map (substT t xi) t0))
      (Vector.map (teI (cng pi xi (teI pi t))) t0)
    )).
  rename t0 into v.
  intros p1 p2 H0.
  rewrite -> (nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0).
  rewrite -> (nth_map (teI (cng pi xi (teI pi t))) v p2 p2 ).
  rewrite -> (nth_map (substT t xi) v p2 p2 eq_refl).
  apply lem1. reflexivity.
Defined.

Lemma twice_the_same pi x m0 m1 : 
forall u, (cng (cng pi x m0) x m1) u = (cng pi x m1) u.
Proof.
intro u.
unfold cng.
destruct (PeanoNat.Nat.eqb u x).
reflexivity.
reflexivity.
Defined.

(*Lemma eqb_comm x xi : PeanoNat.Nat.eqb xi x =  PeanoNat.Nat.eqb x xi.
unfold PeanoNat.Nat.eqb.
Admitted.*)

Lemma NPthenNCACVT x t m pi: 
 isParamT x t = false -> (teI (cng pi x m) t) = (teI pi t).
Proof.
intros H.
induction t.
unfold cng.
simpl in * |- *.
rewrite H.
reflexivity.
simpl in * |- *.
apply ap.
apply eq_nth_iff.
intros.
Check nth_map .
Check nth_map (teI (cng pi x m)) v p1 p2 H1.
rewrite -> (nth_map (teI (cng pi x m)) v p1 p2 H1).
Check nth_map (teI pi) v p1 p2 H1.
rewrite -> (nth_map (teI pi) v p2 p2 eq_refl).
apply H0.
Check all_then_someP.

Check all_then_someP Terms (fsv f) p2 v (isParamT x) H.
apply (all_then_someP Terms (fsv f) p2 v (isParamT x) H).
Defined.

Lemma orb_elim (a b:bool): ((a||b)=false)->((a=false)/\(b=false)).
Proof.
intros. destruct a,b. 
simpl in H. inversion H.
simpl in H. inversion H.
firstorder.
firstorder.
Defined.

Lemma EXISTS_EQV : forall A0 A1 : X -> Prop, 
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

Lemma NPthenNCACVF xi fi m mu :  isParamF xi fi = false ->
foI (cng mu xi m) fi <-> foI mu fi.
Proof.
revert mu.
induction fi; intro mu;
intro H;
simpl in * |- *.
* apply EqualThenEquiv.
  apply ap.
  apply eq_nth_iff.
  intros p1 p2 H0.
  Check eq_nth_iff.
  Check nth_map (teI (cng mu xi m)) t p1 p2 H0.
  rewrite -> (nth_map (teI (cng mu xi m)) t p1 p2 H0).
  Check nth_map (teI mu) t p2 p2 eq_refl.
  rewrite -> (nth_map (teI mu) t p2 p2 eq_refl).
  Check NPthenNCACVT. 
  apply NPthenNCACVT.
  Check all_then_someP Terms (psv p) p2 t (isParamT xi) H.
  apply (all_then_someP Terms (psv p) p2 t (isParamT xi) H).
  (*1st done *)
* firstorder.
* apply AND_EQV.
  apply IHfi1. destruct (orb_elim _ _ H). apply H0.
  apply IHfi2. destruct (orb_elim _ _ H). apply H1.
* apply OR_EQV.
  apply IHfi1. destruct (orb_elim _ _ H). apply H0.
  apply IHfi2. destruct (orb_elim _ _ H). apply H1.
* apply IMP_EQV.
  apply IHfi1. destruct (orb_elim _ _ H). apply H0.
  apply IHfi2. destruct (orb_elim _ _ H). apply H1.
* apply FORALL_EQV. intro m0.
  destruct (PeanoNat.Nat.eqb x xi) eqn:e1.
  pose (C:=proj1 (PeanoNat.Nat.eqb_eq x xi) e1).
  rewrite <- C.
  pose (D:= twice_the_same mu x m m0).
  exact (weafunF _ _ D fi).
Check cng_commF_EQV x xi m0 m.
  rewrite cng_commF_EQV.
(* here inductive IHfi*)
apply IHfi.
exact H.
rewrite <-(eqb_comm xi x).
exact e1.
* 

apply EXISTS_EQV. intro m0.
fold (cng (cng mu xi m) x m0).
fold (cng mu x m0). (* Print cng. Check cng mu xi m. *)

  destruct (PeanoNat.Nat.eqb x xi) eqn:e1.
  pose (C:=proj1 (PeanoNat.Nat.eqb_eq x xi) e1).
  rewrite <- C.
  pose (D:= twice_the_same mu x m m0).
  exact (weafunF _ _ D fi).
Check cng_commF_EQV x xi m0 m.
  rewrite cng_commF_EQV.
(* here inductive IHfi*)
apply IHfi.
exact H.
rewrite <-(eqb_comm xi x).
exact e1.
Defined.

Definition lem2 (t : Terms) : forall (fi : Fo) (xi : SetVars) (pi : SetVars->X)
(r:Fo) (H:(substF t xi fi) = Some r), (*(SH:sig (fun(r:Fo)=>(substF t xi fi) = Some r)),*)
(foI pi r)<->(foI (cng pi xi (teI pi t)) fi).
Proof.
fix lem2 1.
(*H depends on t xi fi r *)
intros fi xi pi r H.
revert pi r H.
induction fi;
intros pi r H.
+ apply lem2caseAtom.
  exact H.
+  (*simpl in *|-*; intros r H.*)
   inversion H. simpl. reflexivity.
+  simpl in *|-*; (*intros r H.*)
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
(* here! *)
Check conj_eq.
simpl.
unfold OAnd.
apply AND_EQV.
  simpl in * |- *.
  * apply (IHfi1 pi f1 eq_refl).
  * apply (IHfi2 pi f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in *|-*. (*; intros r H.*)
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl in * |- *.
apply OR_EQV.
  (*apply disj_eq ;   fold foI.*)
  * apply (IHfi1 pi f1 eq_refl).
  * apply (IHfi2 pi f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in *|-*. (*; intros r H.*)
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl in * |- *.
  apply IMP_EQV. (*apply impl_eq ;   fold foI.*)
  * apply (IHfi1 pi f1 eq_refl).
  * apply (IHfi2 pi f2 eq_refl).
  * inversion H.
  * inversion H.
+
simpl in * |- *.

destruct (PeanoNat.Nat.eqb x xi) eqn:l2.
pose (Q:=SomeInj _ _ H).
rewrite <- Q.
simpl.
apply FORALL_EQV.
intro m.
assert (RA : x = xi).
apply (PeanoNat.Nat.eqb_eq x xi ).
exact l2.
rewrite <- RA.
Check weafunF (cng (cng pi x (teI pi t)) x m) (cng pi x m) 
(twice_the_same pi x (teI pi t) m) fi.
rewrite -> (weafunF (cng (cng pi x (teI pi t)) x m) (cng pi x m) 
(twice_the_same pi x (teI pi t) m) fi).
firstorder.

destruct (isParamF xi fi) eqn:l1.
pose(xint := (isParamT x t)).
destruct (isParamT x t) eqn:l3.
inversion H.
destruct (substF t xi fi) eqn:l4.
 pose (Q:=SomeInj _ _ H).
rewrite <- Q.
simpl.
apply FORALL_EQV.
intro m.
Check cng_commF_EQV.
rewrite cng_commF_EQV.
2 : {
rewrite -> eqb_comm .
exact l2. }

Check IHfi (cng pi x m) f eq_refl.

Check IHfi (cng pi x m) f eq_refl.
Check NPthenNCACVT x t m pi l3.
rewrite <- (NPthenNCACVT x t m pi l3).
Check IHfi (cng pi x m) f eq_refl.
exact (IHfi (cng pi x m) f eq_refl).
inversion H.
 pose (Q:=SomeInj _ _ H).
rewrite <- Q.
simpl.
apply FORALL_EQV.
intro m.
Check cng_commF_EQV.
Check IHfi (cng pi x m) fi.

rewrite cng_commF_EQV.
Check NPthenNCACVF.
symmetry.
exact (NPthenNCACVF xi fi (teI pi t) (cng pi x m) l1).
rewrite -> (eqb_comm x xi).
exact l2.
(* end of FORALL case*)
+
simpl in * |- *.

destruct (PeanoNat.Nat.eqb x xi) eqn:l2.
pose (Q:=SomeInj _ _ H).
rewrite <- Q.
simpl.
apply EXISTS_EQV.
intro m.
assert (RA : x = xi).
apply (PeanoNat.Nat.eqb_eq x xi ).
exact l2.
rewrite <- RA.
Check weafunF (cng (cng pi x (teI pi t)) x m) (cng pi x m) 
(twice_the_same pi x (teI pi t) m) fi.
rewrite -> (weafunF (cng (cng pi x (teI pi t)) x m) (cng pi x m) 
(twice_the_same pi x (teI pi t) m) fi).
firstorder.

destruct (isParamF xi fi) eqn:l1.
pose(xint := (isParamT x t)).
destruct (isParamT x t) eqn:l3.
inversion H.
destruct (substF t xi fi) eqn:l4.
 pose (Q:=SomeInj _ _ H).
rewrite <- Q.
simpl.
apply EXISTS_EQV.
intro m.
Check cng_commF_EQV.
fold (cng  pi x m ).
fold (cng  (cng pi xi (teI pi t)) x m ).

rewrite cng_commF_EQV.
2 : {
rewrite -> eqb_comm .
exact l2. }

Check IHfi (cng pi x m) f eq_refl.

Check IHfi (cng pi x m) f eq_refl.
Check NPthenNCACVT x t m pi l3.
rewrite <- (NPthenNCACVT x t m pi l3).
Check IHfi (cng pi x m) f eq_refl.
exact (IHfi (cng pi x m) f eq_refl).
inversion H.
 pose (Q:=SomeInj _ _ H).
rewrite <- Q.
simpl.
apply EXISTS_EQV.
intro m.
Check cng_commF_EQV.
Check IHfi (cng pi x m) fi.
fold (cng  pi x m ).
fold (cng  (cng pi xi (teI pi t)) x m ).

rewrite cng_commF_EQV.
Check NPthenNCACVF.
symmetry.
exact (NPthenNCACVF xi fi (teI pi t) (cng pi x m) l1).
rewrite -> (eqb_comm x xi).
exact l2.
Defined. (* END OF LEM2 *)
End Lem2.

Lemma UnivInst : forall (fi:Fo) (pi:SetVars->X) (x:SetVars) (t:Terms)
(r:Fo) (H:(substF t x fi)=Some r), foI pi (Impl (Fora x fi) r).
Proof.
intros fi pi x t r H.
simpl.
intro H0.
apply (lem2 t fi x pi r H).
apply H0.
Defined.

Lemma ExisGene : forall (fi:Fo) (pi:SetVars->X) (x:SetVars) (t:Terms)
(r:Fo) (H:(substF t x fi)=Some r), foI pi (Impl r (Exis x fi)).
Proof.
intros fi pi x t r H.
simpl.
intro H0.
exists (teI pi t).
fold (cng pi x (teI pi t)).
apply (lem2 t fi x pi r H).
apply H0.
Defined.
(* PROOF OF THE SOUNDNESS *)
Theorem correct (f:Fo) (l:list Fo) (m:PR l f) 
(lfi : forall  (h:Fo), (InL h l)-> forall (val:SetVars->X), (foI val h)) : 
forall (val:SetVars->X), foI val f.
Proof.
revert lfi.
induction m (* eqn: meq *); intros lfi val.
+ exact (lfi A i _).
+ simpl.
  intros a b.
  exact a.
+ simpl.
  intros a b c.
  exact (a c (b c)).
+ simpl in *|-*.
  destruct (substF t xi ph) eqn: j.
  apply (UnivInst ph val xi t f j).
  simpl. firstorder.
+ simpl in *|-*.
  unfold OImp.
  intros H0 H1 m.
  apply H0.
  rewrite -> (NPthenNCACVF xi ps0 m val H).
  exact H1.
+ simpl in * |- *.
  unfold OImp in IHm2.
apply IHm2.
apply lfi.
apply IHm1.
apply lfi. (*  exact (IHm2 IHm1).*)
+ simpl in * |- *.
  intro m0.
apply IHm.
intros h B.
intro val2.
apply lfi.
exact B.
Defined.
(** SOUNDNESS IS PROVED **)
Check PR.
Print Fo.
Check Atom.
Print PSV.
Check Atom (MPSV 0 2).
Print Terms.
Check Atom (MPSV 0 2).
Print Vector.t.
Check Vector.cons _ (FVC 1) _ (Vector.cons _ (FVC 0) _ (Vector.nil _ )).
Check Atom (MPSV 0 2) 
(Vector.cons _ (FVC 1) _ (Vector.cons _ (FVC 0) _ (Vector.nil _ ))).
Definition xeqy := Atom (MPSV 0 2) 
(Vector.cons _ (FVC 1) _ (Vector.cons _ (FVC 0) _ (Vector.nil _ ))).

Theorem upr : PR (xeqy::nil) (Fora 2 xeqy).
Proof.
apply GEN.
apply hyp.
simpl. (*Print "+"%type.*) 
apply inl.
reflexivity.
Defined.
(* PR is from provability, but it is better to call it derivability.*)

Theorem badcorrect (x1 x2 : X) (nequ : ~(x1=x2))
(f:Fo) (l:list Fo) (m:PR l f) :
~ (forall(val:SetVars->X) (lfi : forall h:Fo, (InL h l)->(foI val h)), foI val f).
Proof.
intro H.
assert (val:SetVars->X).
 intro n. destruct n eqn:nn. exact x1.
          destruct s eqn:ss. exact x2. exact x2.
Abort.
End cor.
End sec0.
End VS.

(* IT IS NOT POSSIBLE TO PROVE THIS THEOREM:
Fixpoint correct (f:Fo) (l:list Fo) (val:SetVars->X) (m:PR l f) 
(lfi : forall h:Fo, (InL h l)->(foI val h)) {struct m}: foI val f.
Proof.
revert val lfi.
induction m (* eqn: meq *); intros val lfi.
+ exact (lfi A i).
+ simpl.
  intros a b.
  exact a.
+ simpl.
  intros a b c.
  exact (a c (b c)).
+ simpl in *|-*.
  destruct (substF t xi ph) eqn: j.
  apply (UnivInst ph val xi t f j).
  simpl. firstorder.
+ simpl in *|-*.
  unfold OImp.
  intros H0 H1 m.
  apply H0.
  rewrite -> (NPthenNCACVF xi ps0 m val H).
  exact H1.
+ simpl in * |- *.
  unfold OImp in IHm2.
apply IHm2.
apply lfi.
apply IHm1.
apply lfi. (*  exact (IHm2 IHm1).*)
+ simpl in * |- *.
  intro m0.
apply IHm.
intros h B.
unfold InL in B.
(*Check correct A l val m lfi.*)
Check NPthenNCACVF xi ps0 m val H.
  destruct (substF t xi ph) eqn: j.
  apply (UnivInst ph val xi t f j).
  simpl. firstorder.

*)


(* old trash
unfold InL in B.
(*Check correct A l val m lfi.*)
Check NPthenNCACVF xi ps0 m val H.
  destruct (substF t xi ph) eqn: j.
  apply (UnivInst ph val xi t f j).
  simpl. firstorder.



  2 : { simpl. trivial. unfold OImp. firstorder. }
  apply (correct _ l).
  2 : {assumption. }
  simpl.
Check fun pi => UnivInst ph pi xi t f j. 
(*forall pi : SetVars -> X, foI pi (Impl (Fora xi ph) f)*)
Show Proof.
Check PR.
pose (Z:=(@Ded (Fora xi ph) f l )).
simple refine (Z _ _ ).
Check correct.
apply correct.
2 : { 
intros.
Check notGenWith.
simpl.
(*
  pose (W:= lfi f).
  destruct (Nat.eqb r xi).
  simpl in H.
  exact H.
  unfold foI. 
  simpl.
*)
Abort. *)
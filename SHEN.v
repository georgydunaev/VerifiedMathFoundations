Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.

Module VS.
Section sec0.
Definition SetVars  := nat.
Definition FuncSymb := nat.
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
Definition A1Type:=Set.
Inductive Term : A1Type :=
| FVC :> SetVars -> Term
| FSC (f:FSV) : (Vector.t Term (fsv f)) -> Term.

(*Formulas*)
Inductive Fo :=
|Atom (p:PSV) : (Vector.t Term (psv p)) ->  Fo
|Bot :Fo
|Conj:Fo->Fo->Fo
|Disj:Fo->Fo->Fo
|Impl:Fo->Fo->Fo
|Fora(x:SetVars)(f:Fo): Fo
|Exis(x:SetVars)(f:Fo): Fo
.
(* Substitution *)

Fixpoint substT (t:Term) (xi: SetVars) (u:Term): Term. 
Proof.
destruct u.
2 : { refine (FSC _ _). exact ( Vector.map (substT t xi) t0 ). }
{
(*Check my.beq_natP s xi.*)
destruct (PeanoNat.Nat.eqb s xi).
Print bool.
exact t.
exact s. }
(*Show Proof.*)
Defined.


Fixpoint isParamT (xi : SetVars) (t : Term) {struct t} : bool :=
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

Fixpoint substF (t:Term) (xi: SetVars) (u : Fo): option Fo. 
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
          | true => match substF t xi u with
                    | Some q => Some (Fora x q)
                    | None => None
                    end
          | false => None
          end
| false => Some u end).
refine (match (isParamF xi (Fora x u)) with 
| true => match (isParamT x t) with 
          | true => match substF t xi u with
                    | Some q => Some (Exis x q)
                    | None => None
                    end
          | false => None
          end
| false => Some u end).
Defined.


Definition Top:Fo := Impl Bot Bot.

Notation " x --> y ":=(Impl x y) (at level 80).
(*
Notation " u '[' t >> xi ] ":=(substT t xi u ) (at level 10).
Set Warnings "-notation-overridden".
Notation " ph [ t | xi ] ":=(substF t xi ph ) (at level 10).
(*Set Warnings "default".*)
Check fun (t:Term) (x:SetVars) => ( t [ t >> x ]).
Check fun (t:Term) (x:SetVars) (ph:Fo) => ( ph [ t | x ] ).
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
| a12 (ph: Fo) (t:Term) (xi:SetVars)
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

(*Export List Notations.*)
(* \u0448\u044b\u0417\u0444\u043a\u0444*)
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

Fixpoint Ded (A B:Fo)(m:(PR (cons A nil) B)) 
(H:forall xi:SetVars, (true = isParamF xi A)->(true=notGenWith xi _ _ m))
{struct m}:(PR nil (A-->B)).
Proof.
destruct m. (*as [i|i|i|i|i|i|i].*)
 unfold In in i.
  simpl in i .
  destruct i .
  rewrite <- e.

exact (AtoA A ).
exfalso.
assumption. (*exact H. (*destruct H.*)*)
apply a1i.
apply a1.
apply a1i.
apply a2.
apply a1i.
apply a12.
apply a1i.
apply b1.
trivial.
apply (MP _ (A-->A0)).
+ simple refine (@Ded _ _ _ _ ).
  exact m1.
  intros xi H0.
  pose (W:=H xi H0).
  simpl in W.
  pose (J:=notGenWith xi (A :: Datatypes.nil) A0 m1).
  try reflexivity.
  fold J.
  fold J in W.
  apply (lm _ _ W).
+
apply (MP _ (A-->(A0-->B))).
simple refine (@Ded _ _ _ _ ).
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
simple refine (@Ded _ _ _ _ ).
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

Fixpoint SimplDed (A B:Fo)(m:(PR (cons A nil) B))
(NP:forall xi:SetVars, (false = isParamF xi A)) 
{struct m}:(PR nil (A-->B)).
Proof.
simple refine (Ded _ _ _ _ ).
exact m.
intros xi H.
rewrite <- NP in H.
inversion H.
Defined.

(* Definition ACK : list Fo := . *)
End sec0.
End VS.



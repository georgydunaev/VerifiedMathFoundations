Require List.
Require Bool.
Require Import Coq.Structures.Equalities.

Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Import Misc.
Require Export Provability.

Module Deduction_mod (SetVars FuncSymb PredSymb: UsualDecidableTypeFull).
Module X := Provability_mod SetVars FuncSymb PredSymb.
Export X.
Export Coq.Lists.List.
Import Bool.Bool.
Notation SetVars := SetVars.t (only parsing).
Notation FuncSymb := FuncSymb.t (only parsing).
Notation PredSymb := PredSymb.t (only parsing).

Module Facts := BoolEqualityFacts SetVars.

Lemma ZX (xi:SetVars) :true = negb (SetVars.eqb xi xi) -> False.
Proof.
intro q.
rewrite Facts.eqb_refl in q.
inversion q.
Defined.

Definition B1 (ps ph:Fo) (xi:SetVars) (H:isParamF xi ps = false): 
 PR nil (ps --> ph) -> PR nil (ps --> Fora xi ph).
Proof.
intro q.
apply MP with (A:=(Fora xi (ps --> ph))).
(*apply (MP nil (Fora xi (ps --> ph))).*)
+ apply GEN.
  exact q.
+ apply (b1 _).
  exact H.
Defined.

Definition gen (A:Fo) (xi:SetVars) (*Generalization from Bernay's rule*)
: PR nil (A) -> PR nil (Fora xi A).
Proof.
intro q.
apply MP with (A:= Top).
unfold Top.
exact (AtoA Bot).
apply MP with (A:= (Fora xi (Top --> A))).
* apply GEN.
  apply MP with (A:= A).
  + exact q.
  + apply a1.
* apply b1.
  trivial.
Defined.

Definition neg (f:Fo):= (Impl f Bot).

Definition a1i (A B : Fo)(l : list Fo):(PR l B)->(PR l (Impl A B)).
Proof.
intros x.
apply MP with (A:= B).
exact x.
apply a1.
Defined.

Fixpoint weak (A F:Fo) (l :list Fo) (x: (PR l F)) : (PR (A::l) F).
Proof.
destruct x as [a b|a b|a b|a b].
+ apply hyp.
  right. (* apply inr. or_intror *)
  exact b.
+ apply Hax,b.
(*apply a1.
apply a2.
apply a12.
apply b1.
assumption. *)
+ apply MP with (A:= a).
  * apply weak.
    exact x1.
  * apply weak.
    exact x2.
+ apply GEN. (* Order is not important! *)
  apply weak. (* Order is not important! *)
  exact x.
Show Proof.
Abort.

Fixpoint weak (A F : Fo) (l : list Fo) (x : PR l F) {struct x} :
   PR (A :: l) F :=
   match x in (GPR _ _ f) return (PR (A :: l) f) with
   | hyp _ _ a b => hyp PRECA (A :: l) a (inr b)
   | Hax _ _ a b => Hax PRECA (A :: l) a b
   | MP _ _ a b x1 x2 =>
       MP PRECA (A :: l) a b (weak A a l x1) (weak A (a --> b) l x2)
   | GEN _ _ a b x0 => GEN PRECA (A :: l) a b (weak A a l x0)
   end.

Fixpoint weaken (F:Fo) (li l :list Fo) (x: (PR l F)) {struct li}: (PR (li ++ l) F).
Proof.
destruct li.
simpl.
exact x.
simpl.
simple refine (@weak f F (li ++ l) _).
apply weaken.
exact x.
Show Proof.
Abort.

Fixpoint weaken (F : Fo) (li l : list Fo) (x : PR l F) {struct li} :
   PR (li ++ l) F :=
   match li as l0 return (PR (l0 ++ l) F) with
   | Datatypes.nil => x
   | f :: li0 => weak f F (li0 ++ l) (weaken F li0 l x)
   end.

(*Export List Notations.*)
Fixpoint notGenWith (xi:SetVars)(l:list Fo)(B:Fo)(m:(PR l B)){struct m}:bool.
Proof.
destruct m eqn: o.
exact true.
destruct p eqn:j.
exact true.
exact true.
exact true.
exact (andb (notGenWith xi l _ p1) (notGenWith xi l _ p2)).
exact (andb (negb (SetVars.eqb xi xi0)) (notGenWith xi l _ p) ).
Defined.

Fixpoint HA xi : true = PeanoNat.Nat.eqb (xi) (xi).
Proof.
destruct xi.
reflexivity.
simpl.
exact (HA xi).
Defined.

Theorem lm (a b :bool)(G:true = (a && b) ): true = a.
Proof.
destruct a.
trivial.
inversion G.
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
  * simpl in H.
    apply a1i.
    exact (hyp _ il _ i).
+ apply a1i.
  apply Hax, p.
+ apply MP with (A:= (A-->A0)).
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
- apply MP with (A:= (A-->(A0-->B))).
  simple refine (@Ded _ _ _ _ _).
  exact m2.
  intros xi H0.
  pose (W:=H xi H0).
  simpl in W.
  apply (lm2 _ _ W).
 (*Last part about GEN*)
  apply a2.
  + apply MP with (A:= (Fora xi (A-->A0))).
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
      exact (ZX xi C).
      exact H0.
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
destruct m. simpl. try reflexivity.
destruct p eqn:j.
simpl. try reflexivity.
simpl. try reflexivity.
simpl. try reflexivity.
simpl. try reflexivity.
+ apply lm3.
  simple refine (@forClosed _ _ _ _ _ _); assumption.
  simple refine (@forClosed _ _ _ _ _ _); assumption.
+ apply lm3.
  2 : simple refine (@forClosed _ _ _ _ _ _); assumption.
  pose (U:=H xi).
  rewrite <- Q in U.
  exfalso.
  inversion U.
Defined.

Fixpoint SimplDed (A B:Fo) (il: list Fo)(m:(PR (cons A il) B))
(NP:forall xi:SetVars, (isParamF xi A = false)) 
{struct m}:(PR il (A-->B)).
Proof.
(*unshelve eapply Ded.*)
simple refine (Ded _ _ _ _ _).
exact m.
intros xi H.
rewrite -> NP in H.
inversion H.
Defined.
Check orb_elim.

Definition swapSIMPL ctx A B C
(HA : forall xi : SetVars.t, isParamF xi A = false)
(HB : forall xi : SetVars.t, isParamF xi B = false)
(HC : forall xi : SetVars.t, isParamF xi C = false) :
(PR ctx (A --> (B --> C) --> (B --> (A --> C)) )).
Proof.
unshelve eapply SimplDed.
2 : { intro xi. simpl.
apply orb_intro. split. apply HA.
apply orb_intro. split. apply HB. apply HC.
}
unshelve eapply SimplDed. 2 : apply HB.
unshelve eapply SimplDed. 2 : apply HA.
apply MP with (A:=B). apply hyp.
simpl. firstorder. (*apply inr.*)
apply MP with (A:=A).
apply hyp; firstorder.
apply hyp; firstorder.
Defined.

Definition swap ctx A B C :
(PR ctx (A --> (B --> C) --> (B --> (A --> C)) )).
Proof.
unshelve eapply SimplDed.

Admitted.


End Deduction_mod.
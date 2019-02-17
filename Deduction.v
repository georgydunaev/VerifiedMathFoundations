Require List.
Require Bool.
Require Import Coq.Structures.Equalities.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Import Misc.
(*From VerifiedMathFoundations.library Require Import Misc.*)
Require Export Provability.

Module Deduction_mod (SetVars FuncSymb PredSymb: UsualDecidableTypeFull).
Module X := Provability_mod SetVars FuncSymb PredSymb.
Export X.

Import PredFormulasNotationsASCII.
Local Open Scope pretxtnot.

Export Coq.Lists.List.
Import Bool.Bool.
Notation SetVars := SetVars.t (only parsing).
Notation FuncSymb := FuncSymb.t (only parsing).
Notation PredSymb := PredSymb.t (only parsing).

Module Facts := BoolEqualityFacts SetVars.

Definition B1 (ps ph:Fo) (xi:SetVars) (H:isParamF xi ps = false): 
 PREPR nil (ps --> ph) -> PREPR nil (ps --> Fora xi ph).
Proof.
intro q.
apply MP_E with (A:=(Fora xi (ps --> ph))).
(*apply (MP_E nil (Fora xi (ps --> ph))).*)
+ apply (GEN_E).
  exact q.
+ apply (b1 _).
  exact H.
Defined.

Definition gen (A:Fo) (xi:SetVars) ctx
(*Generalization from Bernay's rule*)
: PREPR ctx (A) -> PREPR ctx (Fora xi A).
Proof.
intro q.
apply MP_E with (A:= Top).
unfold Top.
(*fold PREPR.*)
exact (@AtoA ctx Bot).
apply MP_E with (A:= (Fora xi (Top --> A))).
* apply GEN_E.
  apply MP_E with (A:= A).
  + exact q.
  + apply a1. (*apply subcalc, a1.*)
* apply b1.
  trivial.
Defined.

Definition neg (f:Fo):= (Impl f Bot).

Definition a1i (A B : Fo)(l : list Fo):(PREPR l B)->(PREPR l (Impl A B)).
Proof.
intros x.
apply MP_E with (A:= B).
exact x.
apply (*subcalc,*) a1.
Defined.

Fixpoint weak (A F:Fo) (l :list Fo) (x: (PREPR l F)) : (PREPR (A::l) F).
Proof.
destruct x as [a b|a b|i a b|a b].
+ apply hyp_E.
  right. (* apply inr. or_intror *)
  exact b.
+ apply Hax_E,b.
(*apply a1.
apply a2.
apply a12.
apply b1.
assumption. *)
+ apply MP_E with (A:= i).
  * apply weak.
    exact b.
  * apply weak.
    exact x1.
+ apply GEN_E. (* Order is not important! *)
  apply weak. (* Order is not important! *)
  exact x.
Defined.

(*Fixpoint weak (A F : Fo) (l : list Fo) (x : PREPR l F) {struct x} :
   PREPR (A :: l) F :=
   match x in (GPR _ _ _ f) return (PREPR (A :: l) f) with
   | hyp _ _ _ a b => hyp dcb PRECA (A :: l) a (inr b)
   | Hax _ _ _ a b => Hax dcb PRECA (A :: l) a b
   | MP_E _ _ _ _ a b x1 x2 =>
       MP_E dcb PRECA (A :: l) I a b (weak A a l x1) (weak A (a --> b) l x2)
   | GEN_E _ _ _ _ a b x0 => GEN_E dcb PRECA (A :: l) I a b (weak A a l x0)
   end.*)

Fixpoint weaken (F:Fo) (li l :list Fo) (x: (PREPR l F)) {struct li}: (PREPR (li ++ l) F).
Proof.
destruct li.
simpl.
exact x.
simpl.
simple refine (@weak f F (li ++ l) _).
apply weaken.
exact x.
(*Show Proof.*)
Abort.

Fixpoint weaken (F : Fo) (li l : list Fo) (x : PREPR l F) {struct li} :
   PREPR (li ++ l) F :=
   match li as l0 return (PREPR (l0 ++ l) F) with
   | Datatypes.nil => x
   | f :: li0 => weak f F (li0 ++ l) (weaken F li0 l x)
   end.

(*Export List Notations.*)
Fixpoint notGenWith (xi:SetVars)(l:list Fo)
(B:Fo)(m:(PREPR l B)){struct m}:bool.
Proof.
(*induction m.  eqn: o.*)
destruct m  eqn: o.
(*Show Proof.*)
exact true.
destruct p eqn:j.
exact true.
exact true.
exact true.
exact true.
exact true.
(*exact (andb IHm1 IHm2).
exact (andb (negb (SetVars.eqb xi xi0)) IHm).*)
exact (andb (notGenWith xi l _ p1) (notGenWith xi l _ p2)).
exact (andb (negb (SetVars.eqb xi xi0)) (notGenWith xi l _ p) ). 
Defined.

(*Fixpoint HA xi : true = PeanoNat.Nat.eqb (xi) (xi).
Proof.
destruct xi.
reflexivity.
simpl.
exact (HA xi).
Defined.*)

Theorem lm (a b :bool)(G:true = (a && b) ): true = a.
Proof.
destruct a.
trivial.
inversion G.
Defined.

Fixpoint Ded (A B:Fo)(il:list Fo)(m:(PREPR (cons A il) B)) 
(H:forall xi:SetVars, (true = isParamF xi A)->(true=notGenWith xi _ _ m))
{struct m}:(PREPR il (A-->B)).
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
    apply hyp_E with (ctx:=il) (1:=i).
    (*exact (hyp _ il _ i).*)
+ apply a1i.
  apply Hax_E, p.
+ apply MP_E with (A:= (A-->A0)).
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
- apply MP_E with (A:= (A-->(A0-->B))).
  simple refine (@Ded _ _ _ _ _).
  exact m2.
  intros xi H0.
  pose (W:=H xi H0).
  simpl in W.
  apply (lm2 _ _ W).
 (*Last part about GEN*)
  apply a2.
  + apply MP_E with (A:= (Fora xi (A-->A0))).
    apply GEN_E.
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
      - pose (C:= lm _ _(U H0)).
        exfalso.
        rewrite Facts.eqb_refl in C.
        inversion C.
      - exact H0.
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


Fixpoint forClosed (A B:Fo)(m:(PREPR (cons A nil) B)):
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

Fixpoint SimplDed (A B:Fo) (il: list Fo)(m:(PREPR (cons A il) B))
(NP:forall xi:SetVars, (isParamF xi A = false)) 
{struct m}:(PREPR il (A-->B)).
Proof.
(*unshelve eapply Ded.*)
simple refine (Ded _ _ _ _ _).
exact m.
intros xi H.
rewrite -> NP in H.
inversion H.
Defined.

Definition swapSIMPL ctx A B C
(HA : forall xi : SetVars.t, isParamF xi A = false)
(HB : forall xi : SetVars.t, isParamF xi B = false)
(HC : forall xi : SetVars.t, isParamF xi C = false) :
(PREPR ctx ((A --> (B --> C)) --> (B --> (A --> C)) )).
Proof.
unshelve eapply SimplDed.
2 : { intro xi. simpl.
apply orb_intro. split. apply HA.
apply orb_intro. split. apply HB. apply HC.
}
unshelve eapply SimplDed. 2 : apply HB.
unshelve eapply SimplDed. 2 : apply HA.
apply MP_E with (A:=B) . apply hyp_E.
simpl. firstorder. (*apply inr.*)
apply MP_E with (A:=A) .
apply hyp_E; firstorder.
apply hyp_E; firstorder.
Defined.

Definition swap ctx A B C :
(PREPR ctx ((A --> (B --> C)) --> (B --> (A --> C)) )).
Proof.
unshelve eapply SimplDed.
Admitted.


End Deduction_mod.
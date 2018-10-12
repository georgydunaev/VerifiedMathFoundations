Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Require Formulas.
Export Formulas.
Export Coq.Lists.List.

Module Provability_mod (SetVars FuncSymb PredSymb: UsualDecidableTypeFull).
Module XPro := Formulas.Formulas_mod SetVars FuncSymb PredSymb.
Export XPro.


(*Local Notation SetVars := SetVars.t (*only parsing*).
Local Notation FuncSymb := FuncSymb.t (*only parsing*). 
Local Notation PredSymb := PredSymb.t (*only parsing*).*)

(*Notation " x --> y ":=(Impl x y) (at level 80).*)

(*Open Scope list_scope.*)
Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.

(* PROpositional Calculus Axioms *)
Inductive PROCA : Fo -> Type :=
| Ha1  : forall A B, PROCA (A-->(B-->A))
| Ha2  : forall A B C, PROCA ((A-->(B-->C))-->((A-->B)-->(A-->C)))
.

(* PREdicate Calculus Axioms *)
Inductive PRECA : Fo -> Type :=
| OtoE  :> forall A, (PROCA A) -> (PRECA A)
| Ha12 : forall (ph: Fo) (t:Terms) (xi:SetVars.t)
 (r:Fo) (s:(substF t xi ph)=Some r), PRECA (Impl (Fora xi ph) r)
| Hb1  : forall (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false),
PRECA (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
.

(* Type of the rules of inference. *)
Record IR := {
(*n : nat;*)
paramT : Type;
(*premi : Vector.t (paramT -> Fo) n;*)
premi : list (paramT -> Fo);
result : (paramT -> Fo);
condi : Prop;
}.

Check fst.
(*Import VectorNotations.*)
Import ListNotations.
Definition IR_MP := Build_IR (Fo*Fo) [fst ; fun x=>(fst x --> snd x)]
snd True
.

(*Coercion PRO : PROCA >-> PRECA.*)

Section GRP_sec.
Record checks := {
useMP:Prop;
useGEN:Prop;
}.

(*Context (useGEN:Prop).*)
(*Context (c:checks).*)
Context (rules : list IR).
Context (axs : Fo -> Type).
Check map.

Definition proof (PR : Fo -> Type) 
(r:IR) (p : paramT r)
:=
fold_left prod 
(map (fun f => PR (f p)) (premi r))
True.
Definition rtype (PR : Fo -> Type):= forall (A:Fo) (r:IR) (u: InL r rules) (p : paramT r) 
(Q: forall u:Fo, InL u (map (fun f => (f p)) (premi r)) -> PR u)
, PR A.

Inductive PR : Fo -> Type :=
| Hax_O :> forall (A : Fo), (axs A) -> PR A
| Hrule_PR : rtype PR
.
(*| MP_O (q:useMP c) (A B: Fo) : (PR A)->(PR (Impl A B))->(PR B)
| GEN_O (q:useGEN c) (A : Fo) (xi:SetVars.t): (PR A)->(PR (Fora xi A))
.*)
Class CHRULE (X : Fo -> Type) : Type :=
  Hrule : rtype X.
Instance CHRULE_1 : CHRULE  PR := Hrule_PR.



Context (ctx:list Fo).
(* Derivation from a context. *)
Inductive CPR : Fo -> Type :=
| hyp (A : Fo): (InL A ctx) -> CPR A
| Hax_C :> forall (A : Fo), (axs A) -> CPR A
| Hrule_CPR : rtype CPR
.

Instance CHRULE_2 : CHRULE CPR := Hrule_CPR.

(*Inductive GPR : Fo -> Type :=
| hyp (A : Fo): (InL A ctx) -> GPR A
(*| HPR :> forall (A : Fo), (PR A) -> GPR A*)
| Hax :> forall (A : Fo), (axs A) -> GPR A
| MP (q:useMP c) (A B: Fo) : (GPR A)->(GPR (Impl A B))
                 ->(GPR B)
| GEN (q:useGEN c) (A : Fo) (xi:SetVars.t): (GPR A)->(GPR (Fora xi A))
.*)
End GRP_sec.

Class CHAX (X : Fo -> Type) (axs : Fo -> Type): Type :=
  Hax :> forall (A : Fo), (axs A) -> X A.


Record Rules fo := {
premises : list fo;
conclusion : fo;
condition : Prop;
}.

Import ListNotations.

(* Provability in the propositional calculus. *)
(*Definition PROPR := GPR {|useMP:=True;useGEN:=False|} PROCA.*)
Definition PROPR := PR [IR_MP] PROCA.
Instance CHAX_1 : CHAX (PR [IR_MP] PROCA) PROCA := Hax_O [IR_MP] PROCA.


(*Instance CHAX_2 : CHAX CPR := Hax_C./*)
Class CMP (X : Fo -> Type) : Type :=
  MP A B :X A -> X (A-->B) -> X B.
(* Instance CMP_1 : CMP PROPR. intros A B.*)
Definition MP_1 A B :PROPR A -> PROPR (A-->B) -> PROPR B.
Proof.
intros X0 X1.
pose(t:= Hrule_PR [IR_MP] PROCA B).
unshelve eapply t.
exact IR_MP.
exact (pair A B).
left;reflexivity.
intros u H.
simpl in H.
destruct H.
rewrite <- e.
exact X0.
destruct s.
rewrite <- e.
exact X1.
destruct f.
Show Proof.
Defined.
Instance CMP_1 : CMP PROPR := MP_1.

(*trivial.
unfold paramT.
unfold rtype in t.
apply Hrule_PR.*)

Class CA1 (X : Fo -> Type) : Type :=
{  a1 : forall (A B: Fo), X (A-->(B-->A));
   a2 : forall (A B C: Fo), X ((A-->(B-->C))-->((A-->B)-->(A-->C)))
}.

Instance CHA1_1 : CA1 PROPR.
Proof.
apply Build_CA1.
(*unfold CA1.*)
intros.
apply Hax, Ha1.
intros.
apply Hax, Ha2.
Defined.

Definition AtoA (A:Fo) : PROPR (A-->A).
Proof.
apply MP with (A-->(A-->A)).
apply a1. (* apply (Hax _ _ (Ha1 _ _)).*)
apply MP with (A-->((A-->A)-->A)) (*1:=I*).
apply a1.
apply a2.
Defined.


(* Provability in predicate calculus. *)
(*Definition PREPR := GPR {|useMP:=True;useGEN:=True|} PRECA.*)
Check True.
Definition IR_GEN := Build_IR (Fo * SetVars.t) [fst]
(fun x => (Fora (snd x) (fst x))) True
.

Definition PREPR := PR [IR_MP;IR_GEN] PRECA.
Instance CHAX_2 : CHAX (PR [IR_MP;IR_GEN] PRECA) PRECA.
Proof.
unfold CHAX.
intros.
eapply Hax_O.
exact X.
Defined.
(*:= Hax_O [IR_MP] PRECA.*)

Instance CHA1_2 : CA1 PREPR.
Proof.
apply Build_CA1.
(*unfold CA1.*)
+ intros. apply Hax_O, OtoE, Ha1.
+ intros. apply Hax, OtoE, Ha2.
Defined.

(*useless*)
Definition Ma1 A B : PREPR (Impl A (Impl B A)).
Proof. apply a1. Defined.
Definition Ma2 A B C : PREPR ((A-->(B-->C))-->((A-->B)-->(A-->C))).
Proof. apply a2. Defined.
Definition b1 (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false):
PREPR(Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) ).
Proof. apply Hax, Hb1, H. Defined.

Theorem subcalc (*{ctx}*) (A:Fo) : PROPR (*ctx *)A -> PREPR (*ctx*) A.
Proof.
intro p.
try apply PRO.
induction p.
(*+ apply hyp, i.*)
+ apply  Hax, OtoE. exact a.
+ apply MP with (A0:=A) .
  apply IHp1. apply IHp2.
+ destruct q.
Defined.

Coercion subcalc : PROPR >-> PREPR.

(*Arguments GPR {axs}.*)
(*Notation newMP := (MP (1:=I)).*)
Definition AtoA {ctx} (A:Fo) : PROPR ctx (A-->A).
Proof.
apply MP with (A:=(A-->(A-->A))) (1:=I).  (*(MP ctx (A-->(A-->A)) _).*)
apply Hax, Ha1. (* apply (Hax _ _ (Ha1 _ _)).*)
apply MP with (A:= A-->((A-->A)-->A)) (1:=I).
apply Hax, Ha1.
apply Hax, Ha2.
Defined.




Definition a12 axi ph t xi : @PREPR axi (match (substF t xi ph) with 
      | Some q => (Impl (Fora xi ph) q)
      | None => Top
      end).
Proof. induction (substF t xi ph) eqn:g. eapply Hax, Ha12, g.
unfold Top.
exact (AtoA  Bot).
Defined.

End Provability_mod.
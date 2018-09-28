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
| PRO  :> forall {A}, (PROCA A) -> (PRECA A)
| Ha12 : forall (ph: Fo) (t:Terms) (xi:SetVars.t)
 (r:Fo) (s:(substF t xi ph)=Some r), PRECA (Impl (Fora xi ph) r)
| Hb1  : forall (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false),
PRECA (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
.

(*Coercion PRO : PROCA >-> PRECA.*)

(*
Inductive AxiomH : Fo -> Type :=
| Ha1  : forall A B, AxiomH (A-->(B-->A))
| Ha2  : forall A B C, AxiomH ((A-->(B-->C))-->((A-->B)-->(A-->C)))
| Ha12 : forall (ph: Fo) (t:Terms) (xi:SetVars.t)
 (r:Fo) (s:(substF t xi ph)=Some r), AxiomH (Impl (Fora xi ph) r)
| Hb1  : forall (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false),
AxiomH (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
.*)
Section GRP_sec.
Context (axs : Fo -> Type).
Context (ctx:list Fo).
Inductive GPR : Fo -> Type :=
| hyp (A : Fo): (InL A ctx)-> GPR A
| Hax :> forall (A : Fo), (axs A) -> GPR A
| MP (A B: Fo) : (GPR A)->(GPR (Impl A B))
                 ->(GPR B)
| GEN (A : Fo) (xi:SetVars.t): (GPR A)->(GPR (Fora xi A))
.
Print All.

End GRP_sec.

Check Hax.
(*Coercion Hax : axs >-> GPR.*)
(* Provability in predicate calculus *)
Definition PR := GPR PRECA. (*here*)
(*Definition NHax := Hax PRECA.*)
(*Coercion NHax : PRECA >-> PR.*)
(*Inductive PR (axi:list Fo) : Fo -> Type :=
| hyp (A : Fo): (InL A axi)-> @PR axi A
| Hax (A : Fo): (AxiomH A) -> @PR axi A
(*| a1 (A B: Fo) : @PR axi (Impl A (Impl B A))
| a2 (A B C: Fo) : @PR axi ((A-->(B-->C))-->((A-->B)-->(A-->C)))*)
(*| a12 (ph: Fo) (t:Terms) (xi:SetVars)
: @PR axi (match (substF t xi ph) with 
      | Some q => (Impl (Fora xi ph) q)
      | None => Top
      end)
| b1 (ps ph: Fo) (xi:SetVars) (H:isParamF xi ps = false):
@PR axi (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) ) *)
| MP (A B: Fo) : (@PR axi A)->(@PR axi (Impl A B))->(@PR axi B)
| GEN (A : Fo) (xi:SetVars): (@PR axi A)->(@PR axi (Fora xi A))
.*)

Definition a1 axi A B : @PR axi (Impl A (Impl B A)).
Proof. apply Hax.
(*
(*rapply Ha1.*)
Check Ha1 A B : PROCA (A --> (B --> A)).
Check Ha1 A B : PRECA (A --> (B --> A)).
(*Check (Ha1 A B: PRECA (A --> (B --> A))) : @PR axi (A --> (B --> A)).*)
*)
refine (Ha1 _ _). Defined.
Definition a2 axi A B C : @PR axi ((A-->(B-->C))-->((A-->B)-->(A-->C))).
Proof. apply Hax, PRO, Ha2. Defined.
Definition b1 axi (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false):
@PR axi (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) ).
Proof. apply Hax, Hb1, H. Defined.

(*Arguments GPR {axs}.*)
Definition AtoA {ctx} (A:Fo) : PR ctx (A-->A).
Proof.
apply MP with (A:=(A-->(A-->A))).  (*(MP ctx (A-->(A-->A)) _).*)
apply a1. (* apply (Hax _ _ (Ha1 _ _)).*)
apply MP with (A:= A-->((A-->A)-->A)).
apply a1.
apply a2.
Defined.

Definition a12 axi ph t xi : @PR axi (match (substF t xi ph) with 
      | Some q => (Impl (Fora xi ph) q)
      | None => Top
      end).
Proof. induction (substF t xi ph) eqn:g. eapply Hax, Ha12, g.
unfold Top.
exact (AtoA  Bot).
Defined.

End Provability_mod.
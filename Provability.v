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
| PRO  :> forall A, (PROCA A) -> (PRECA A)
| Ha12 : forall (ph: Fo) (t:Terms) (xi:SetVars.t)
 (r:Fo) (s:(substF t xi ph)=Some r), PRECA (Impl (Fora xi ph) r)
| Hb1  : forall (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false),
PRECA (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
.

(*Coercion PRO : PROCA >-> PRECA.*)

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

Record Rules fo := {
premises : list fo;
conclusion : fo;
condition : Prop;
}.

Import ListNotations.
Definition rMP A B := Build_Rules Fo [A ; A-->B] B.
Definition rGEN A xi := Build_Rules Fo [A] (Fora xi A).
Definition RulesScheme fo := list fo * list SetVars.t -> Rules fo.
Print all.
Section GRP2_sec.
Context (axs : Fo -> Type).
Context (ctx:list Fo).
Context (lrules:list (Rules Fo)).
Inductive DER : Fo -> Type :=
| Hyp (A : Fo): (InL A ctx)-> DER A
| Axi :> forall (A : Fo), (axs A) -> DER A
(*| Infer R (A : Fo): (InL R lrules) -> DER A   bad*)
(*| MPD (A B: Fo) : (DER A)->(DER (Impl A B))
                 ->(DER B)
| GEND (A : Fo) (xi:SetVars.t): (DER A)->(DER (Fora xi A))*)
.
(*Print All.*)
End GRP2_sec.

(* Provability in predicate calculus *)
Definition PR := GPR PRECA. (*here*)

Definition a1 axi A B : @PR axi (Impl A (Impl B A)).
Proof. apply Hax.
(*
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

Theorem subcalc {ctx} (A:Fo) : GPR PROCA ctx A -> GPR  PRECA ctx A.
Proof.
intro p.
try apply PRO.
induction p.
apply hyp, i.
apply Hax, PRO, a.
apply MP with (A:=A). apply IHp1. apply IHp2.
Abort. (* how to separate rules of inference?*)

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
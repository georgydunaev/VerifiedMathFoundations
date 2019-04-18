Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Require Formulas.
Export Formulas.
Export Coq.Lists.List.

Module Provability_mod (SetVars FuncSymb PredSymb: UsualDecidableTypeFull).
Module PRE := Formulas.Formulas_mod SetVars FuncSymb PredSymb.
Export PRE.

Import PredFormulasNotationsASCII.
Local Open Scope pretxtnot.

Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.

(* intuitionistic "PROpositional" Calculus Axioms *)
Inductive PROCA : Fo -> Type :=
| Ha1  : forall A B, PROCA (A-->(B-->A))
| Ha2  : forall A B C, PROCA ((A-->(B-->C))-->((A-->B)-->(A-->C)))
| Ha3  : forall A B, PROCA (Conj A B --> A)
| Ha4  : forall A B, PROCA (Conj A B --> B)
| Ha5  : forall A B, PROCA (A --> (B --> Conj A B))
| Ha6  : forall A B, PROCA (A --> Disj A B)
| Ha7  : forall A B, PROCA (B --> Disj A B)
| Ha8  : forall A B C, PROCA ((A --> C) --> ((B --> C) --> (Disj A B --> C)))
| Ha9  : forall A B, PROCA (Neg A --> (A --> B))
| Ha10  : forall A B, PROCA ((A --> B) --> ((A --> Neg B) --> Neg A))
.

(* intuitionistic PREdicate Calculus Axioms *)
Inductive PRECA : Fo -> Type :=
| PRO  :> forall A, (PROCA A) -> (PRECA A)
| Ha12 : forall (ph: Fo) (t:Terms) (xi:SetVars.t)
 (r:Fo) (s:(substF t xi ph)=Some r), PRECA ((Fora xi ph) --> r)
| Ha13 : forall (ph: Fo) (t:Terms) (xi:SetVars.t)
 (r:Fo) (s:(substF t xi ph)=Some r), PRECA (r --> (Exis xi ph) )
| Hb1  : forall (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false),
PRECA (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
| Hb2  : forall (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false),
PRECA (Impl (Fora xi (Impl ph ps)) (Impl (Exis xi ph) ps ) )
.

(***** MISLEADING THING! Do NOT use! *****)
(* IT WORKS:
Section PROPR.
(*Context (axs : Fo -> Type).*)
Context (ctx:list Fo).
Inductive PROPR : Fo -> Type :=
| hyp_O (A : Fo): (InL A ctx)-> PROPR A
| Hax_O :> forall (A : Fo), (PROCA A) -> PROPR A
| MP_O (A B: Fo) : (PROPR A)->(PROPR (Impl A B))
                 ->(PROPR B)
.
End PROPR.
*)

Section PREPR.
(*Context (axs : Fo -> Type).*)
Context (ctx:list Fo).
Inductive PREPR : Fo -> Type :=
| hyp_E (A : Fo): (InL A ctx)-> PREPR A
| Hax_E :> forall (A : Fo), (PRECA A) -> PREPR A
| MP_E (A B: Fo) : (PREPR A)->(PREPR (Impl A B))
                 ->(PREPR B)
| GEN_E (A : Fo) (xi :SetVars.t)
 (nic:forall A : Fo, (InL A ctx)-> (isParamF xi A = false))
: (PREPR A)->(PREPR (Fora xi A))
.
(*Instance cMPe : (cMP PREPR) := MP_E.*)
End PREPR.
(* IT WORKS:
Definition a1 ctx A B : @PROPR ctx (Impl A (Impl B A)).
Proof. apply Hax_O.
(*
Check Ha1 A B : PROCA (A --> (B --> A)).
Check Ha1 A B : PRECA (A --> (B --> A)).
(*Check (Ha1 A B: PRECA (A --> (B --> A))) : @PR axi (A --> (B --> A)).*)
*)
refine (Ha1 _ _). Defined.
*)
Definition a1 ctx A B : @PREPR ctx (Impl A (Impl B A)).
Proof. apply Hax_E.
refine (Ha1 _ _). 
Defined.

Definition a2 axi A B C : @PREPR axi ((A-->(B-->C))-->((A-->B)-->(A-->C))).
Proof. apply Hax_E, PRO, Ha2. Defined.
Definition b1 axi (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false):
@PREPR axi (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) ).
Proof. apply Hax_E, Hb1, H. Defined.

(* IT WORKS:
Theorem subcalc {ctx} (A:Fo) : PROPR ctx A -> PREPR ctx A.
Proof.
intro p.
try apply PRO.
induction p.
apply hyp_E, i.
apply Hax_E, PRO, p.
apply @MP_E with (A:=A).
(* unfold cMP. exact (MP_E ctx). intros. *)
apply IHp1. apply IHp2.
Defined.

Coercion subcalc : PROPR >-> PREPR.
*)

(*Arguments GPR {axs}.*)
(*Notation newMP := (MP (1:=I)).*)
(* IT WORKS:
Definition AtoA {ctx} (A:Fo) : PROPR ctx (A-->A).
Proof.
apply MP_O with (A:=(A-->(A-->A))).  (*(MP ctx (A-->(A-->A)) _).*)
apply Hax_O, Ha1. (* apply (Hax _ _ (Ha1 _ _)).*)
apply MP_O with (A:= A-->((A-->A)-->A)).
apply Hax_O, Ha1.
apply Hax_O, Ha2.
Defined.
*)

(* IT WORKS:
Definition a12 axi ph t xi : @PREPR axi (match (substF t xi ph) with 
      | Some q => (Impl (Fora xi ph) q)
      | None => Top
      end).
Proof. induction (substF t xi ph) eqn:g. eapply Hax_E, Ha12, g.
unfold Top.
exact (AtoA  Bot).
Defined.
*)

Definition AtoA {ctx} (A:Fo) : PREPR ctx (A-->A).
Proof.
apply MP_E with (A:=(A-->(A-->A))).  (*(MP ctx (A-->(A-->A)) _).*)
apply Hax_E, PRO, Ha1. (* apply (Hax _ _ (Ha1 _ _)).*)
apply MP_E with (A:= A-->((A-->A)-->A)).
apply Hax_E, PRO, Ha1.
apply Hax_E, PRO, Ha2.
Defined.

(* page 155 *)
Theorem reverse_subst (xi eta:SetVars.t) (ph ps:Fo)
(H: (substF eta xi ph) = Some ps) : (substF xi eta ps) = Some ph.
Proof.
unfold substF in H.
Abort.

End Provability_mod.
Require Export Coq.Lists.List.
Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.

Require Import Coq.Structures.Equalities.
Module Lang (PropVars : UsualDecidableTypeFull).
 Inductive Fo :=
 |Atom (p:PropVars.t) :> Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
 .

 Notation " x --> y ":=(Impl x y) (at level 80, right associativity).
 Notation " x -/\ y ":=(Conj x y) (at level 80).
 Notation " x -\/ y ":=(Disj x y) (at level 80).
 Notation " -. x " :=(Impl x Bot) (at level 80).
 Definition Neg (A:Fo):Fo := Impl A Bot.
 Definition Top:Fo := Neg Bot.

 (* Proposional calculus' axioms (Intuitionistic) *)
 Inductive PROCAI : Fo -> Type :=
 | Ha1  : forall A B, PROCAI (A-->(B-->A))
 | Ha2  : forall A B C, PROCAI ((A-->(B-->C))-->((A-->B)-->(A-->C)))
 | Ha3  : forall A B, PROCAI ((A-/\ B)--> A)
 | Ha4  : forall A B, PROCAI ((A-/\ B)--> B)
 | Ha5  : forall A B, PROCAI (A-->(B-->(A-/\B)))
 | Ha6  : forall A B, PROCAI (A-->(A-\/ B))
 | Ha7  : forall A B, PROCAI (B-->(A-\/ B))
 | Ha8  : forall A B C, PROCAI ((A-->C)-->((B-->C)-->((A-\/ B)-->C)))
 | Ha9  : forall A B, PROCAI (-.A --> A --> B )
 .

End Lang.
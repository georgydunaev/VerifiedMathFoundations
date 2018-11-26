(* Here I will prove that substitution doesn't change validity. *)
(*Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".*)
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
 Definition Top:Fo := Impl Bot Bot.
End Lang.
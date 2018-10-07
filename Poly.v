Require Import List.
(*Import ListNotations.*)
Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.

Class PolyClass (Omega:Type) : Type :=
{ 
  OFalse: Omega;
  OImpl : Omega->Omega->Omega;
  OConj : Omega->Omega->Omega;
  ODisj : Omega->Omega->Omega;
}.
Instance ClassProp : PolyClass Prop := 
 Build_PolyClass Prop False (fun x y:Prop => x->y) and or.
Instance ClassType : PolyClass Type := 
 Build_PolyClass Type False (fun x y => x->y) prod sum.
Instance ClassBool : PolyClass bool := 
 Build_PolyClass bool false implb andb orb.

Notation " x =-> y ":=(OImpl x y) (at level 80).
Notation " x =/\ y ":=(OConj x y) (at level 80).
Notation " x =\/ y ":=(ODisj x y) (at level 80).


Module Type PolyMod.
Parameter Omega : Type.
Axiom OImpl OConj ODisj : Omega->Omega->Omega.
(* This just doesn't work properly.
Notation " x =-> y ":=(OImpl x y) (at level 80).
Notation " x =/\ y ":=(OConj x y) (at level 80).
Notation " x =\/ y ":=(ODisj x y) (at level 80).
*)
End PolyMod.

Module ModProp <: PolyMod.
(*Notation Omega := Prop (only parsing).*)
Definition Omega := Prop.
Definition OFalse := False.
Definition OConj := and.
Definition ODisj := or.
Definition OImpl := (fun x y:Omega => x->y).
Notation Osig := ex.
End ModProp.

Module ModType <: PolyMod.
(*Notation Omega := Type (only parsing).*)
Definition Omega := Type.
Definition OFalse := False.
Definition OConj := prod.
Definition ODisj := sum.
Definition OImpl := (fun x y:Omega => x->y).
Notation Osig := sigT.
End ModType.

Module ModBool<: PolyMod.
(*Notation Omega := bool (only parsing).*)
Definition Omega := bool.
Definition OFalse := false.
Definition OConj := andb.
Definition ODisj := orb.
Definition OImpl := implb.
End ModBool.
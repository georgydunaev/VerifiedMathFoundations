Module Type PolyMod.
Parameter Omega : Type.
Axiom OImp : Omega->Omega->Omega.
Axiom OAnd OOr : Omega->Omega->Omega.
Notation " x =-> y ":=(OImp x y) (at level 80).
Notation " x =/\ y ":=(OAnd x y) (at level 80).
Notation " x =\/ y ":=(OOr x y) (at level 80).
End PolyMod.

Module ModProp <: PolyMod.
(*Notation Omega := Prop (only parsing).*)
Definition Omega := Prop.
Definition OFalse := False.
Definition OAnd := and.
Definition OOr := or.
Definition OImp := (fun x y:Omega => x->y).
Notation Osig := ex.
End ModProp.

Module ModType <: PolyMod.
(*Notation Omega := Type (only parsing).*)
Definition Omega := Type.
Definition OFalse := False.
Definition OAnd := prod.
Definition OOr := sum.
Definition OImp := (fun x y:Omega => x->y).
Notation Osig := sigT.
End ModType.

Module ModBool<: PolyMod.
(*Notation Omega := bool (only parsing).*)
Definition Omega := bool.
Definition OFalse := false.
Definition OAnd := andb.
Definition OOr := orb.
Definition OImp := implb.
End ModBool.
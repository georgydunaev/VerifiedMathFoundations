Module ModProp.
Definition Omega := Prop.
Definition OFalse := False.
Definition OAnd := and.
Definition OOr := or.
Definition OImp := (fun x y:Omega => x->y).
Notation Osig := ex.
End ModProp.

Module ModType.
Notation Omega := Type.
Definition OFalse := False. (*Print "+"%type.*)
Definition OAnd := prod.
Definition OOr := sum.
Definition OImp := (fun x y:Omega => x->y).
Notation Osig := sigT.
End ModType.


Module ModBool.
Definition Omega := bool.
Definition OFalse := false.
Definition OAnd := andb.
Definition OOr := orb.
Definition OImp := implb.
End ModBool.
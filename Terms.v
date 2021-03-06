(* PUBLIC DOMAIN *)
(* Author: Georgy Dunaev, georgedunaev@gmail.com *)
Require Coq.Vectors.Vector.
Require Coq.Structures.Equalities.
Import Coq.Structures.Equalities.
Module Terms_mod (SetVars FuncSymb: UsualDecidableTypeFull).
(*Local Notation SetVars := SetVars.t (*only parsing*).
Local Notation FuncSymb := FuncSymb.t (*only parsing*).*)

Record FSV := {
 fs : FuncSymb.t;
 fsv : nat;
}.

Unset Elimination Schemes.
Inductive Terms : Type :=
| FVC :> SetVars.t -> Terms
| FSC (f:FSV) : (Vector.t Terms (fsv f)) -> Terms.
Set Elimination Schemes.

Definition Terms_rect (T : Terms -> Type)
                      (H_FVC : forall sv, T (FVC sv))
                      (H_FSC : forall f v, (forall n, T (Vector.nth v n)) -> T (FSC f v)) :=
  fix loopt (t : Terms) : T t :=
    match t with
    | FVC sv  => H_FVC sv
    | FSC f v =>
      let fix loopv s (v : Vector.t Terms s) : forall n, T (Vector.nth v n) :=
        match v with
        | @Vector.nil _ => Fin.case0 _
        | @Vector.cons _ t _ v => fun n => Fin.caseS' n (fun n => T (Vector.nth (Vector.cons _ t _ v) n))
                                                      (loopt t)
                                                      (loopv _ v)
        end in
      H_FSC f v (loopv _ v)
    end.

Definition Terms_ind (T : Terms -> Prop)
                      (H_FVC : forall sv, T (FVC sv))
                      (H_FSC : forall f v, (forall n, T (Vector.nth v n)) -> T (FSC f v)) :=
  fix loopt (t : Terms) : T t :=
    match t with
    | FVC sv  => H_FVC sv
    | FSC f v =>
      let fix loopv s (v : Vector.t Terms s) : forall n, T (Vector.nth v n) :=
        match v with
        | @Vector.nil _ => Fin.case0 _
        | @Vector.cons _ t _ v => fun n => Fin.caseS' n (fun n => T (Vector.nth (Vector.cons _ t _ v) n))
                                                      (loopt t)
                                                      (loopv _ v)
        end in
      H_FSC f v (loopv _ v)
    end.
(*Check Terms_ind.*)

Fixpoint substT (t:Terms) (xi: SetVars.t) (u:Terms): Terms.
Proof.
destruct u as [s|f t0].
2 : {
 refine (FSC _ _).
 exact ( @Vector.map _ _ (substT t xi) _ t0 ).
}
{
 destruct (SetVars.eqb s xi).
 exact t.
 exact s.
}
(*Show Proof.*)
Defined.

Fixpoint isParamT (xi : SetVars.t) (t : Terms) {struct t} : bool :=
   match t with
   | FVC s => SetVars.eqb s xi
   | FSC f t0 => Vector.fold_left orb false (Vector.map (isParamT xi) t0)
   end.

Section Interpretation.
Context {X} {fsI:forall(q:FSV),(Vector.t X (fsv q))->X}.
Fixpoint teI
   (val:SetVars.t->X) (t:Terms): X :=
   match t with
   | FVC s => val s
   | FSC f t0 => fsI f (Vector.map (teI val) t0)
   end.
End Interpretation.
End Terms_mod.
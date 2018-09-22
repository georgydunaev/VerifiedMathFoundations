(* PUBLIC DOMAIN *)
(* Author: Georgy Dunaev, georgedunaev@gmail.com *)
Require Export Coq.Vectors.Vector.
Require Import Coq.Structures.Equalities.
(*Type*)
Module  terms_mod (SetVars FuncSymb: UsualDecidableTypeFull).
Notation SetVars := SetVars.t.
Notation FuncSymb := FuncSymb.t.
(*Parameter FuncSymb : Set.*)

Record FSV := {
 fs : FuncSymb;
 fsv : nat;
}.

Unset Elimination Schemes.
Inductive Terms : Type :=
| FVC :> SetVars -> Terms
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

(*Print SetVars.eqb.*)
Fixpoint substT (t:Terms) (xi: SetVars) (u:Terms): Terms. 
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
Defined.

Fixpoint isParamT (xi : SetVars) (t : Terms) {struct t} : bool :=
   match t with
   | FVC s => SetVars.eqb s xi
   | FSC f t0 => Vector.fold_left orb false (Vector.map (isParamT xi) t0)
   end.


End terms_mod.
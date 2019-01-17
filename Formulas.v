Require Export Coq.Vectors.Vector.
Require Import Coq.Structures.Equalities.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Terms.
Require Poly.
Require Valuation.
Export Terms.
Export Valuation.
Export Poly.ModProp.

Module  Formulas_mod (SetVars FuncSymb PredSymb: UsualDecidableTypeFull).
Module cn := Valuation_mod SetVars.
Module XFo := Terms_mod SetVars FuncSymb.
Export cn.
Export XFo.

Record PSV := MPSV{
 ps : PredSymb.t;
 psv : nat;
}.

Inductive Fo :=
 |Atom (p:PSV) : (Vector.t Terms (psv p)) -> Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
 |Fora(x:SetVars.t)(f:Fo): Fo
 |Exis(x:SetVars.t)(f:Fo): Fo
.

Definition Neg (A:Fo):Fo := Impl A Bot.
Definition Top:Fo := Neg Bot.

Module FormulasNotationsUnicode.
 Notation " '⊥' "   :=(Bot) (at level 80).
 Notation " x '∧' y ":=(Conj x y) (at level 80).
 Notation " x '∨' y ":=(Disj x y) (at level 80).
 Notation " x '→' y ":=(Impl x y) (at level 80, right associativity).
 Notation "'∀' x f " :=(Fora x f) (at level 80).
 Notation "'∃' x f " :=(Exis x f) (at level 80).
 Notation " ¬ x "   :=(Neg x) (at level 80).
End FormulasNotationsUnicode.

Module FormulasNotationsASCII.
 Notation " x --> y ":=(Impl x y) (at level 80, right associativity).
 Notation " x -/\ y ":=(Conj x y) (at level 80).
 Notation " x -\/ y ":=(Disj x y) (at level 80).
(*
 Notation " '(A.' x ')(' f ')' " :=(Fora x f) (at level 80).
 Notation " '(E.' x ')(' f ')' " :=(Exis x f) (at level 80).
*)
 Notation " -. x "   :=(Neg x) (at level 80).
End FormulasNotationsASCII.

(* Substitution *)
Fixpoint isParamF (xi : SetVars.t) (f : Fo) {struct f} : bool :=
   match f with
   | Atom p t0 => Vector.fold_left orb false (Vector.map (isParamT xi) t0)
   | Bot => false
   | Conj f1 f2 | Disj f1 f2 | Impl f1 f2 => isParamF xi f1 || isParamF xi f2
   | Fora x f0 | Exis x f0 =>
       if SetVars.eqb x xi then false else isParamF xi f0
   end.

Fixpoint substF (t : Terms) (xi : SetVars.t) (u : Fo)
 {struct u} : option Fo
 :=let f := (substF t xi) in
   match u with
   | Atom p t0 => Some (Atom p (map (substT t xi) t0))
   | Bot => Some Bot
   | Conj u1 u2 =>
     match (f u1),(f u2) with
     | Some f0,Some f1 => (Some (Conj f0 f1))
     | _,_ => None
     end
   | Disj u1 u2 =>
     match (f u1),(f u2) with
     | Some f0,Some f1 => (Some (Disj f0 f1))
     | _,_ => None
     end
   | Impl u1 u2 =>
     match (f u1),(f u2) with
     | Some f0,Some f1 => (Some (Impl f0 f1))
     | _,_ => None
     end
   | Fora x psi =>
       if isParamF xi (Fora x psi)
       then
        if isParamT x t
        then None
        else
         match f psi with
         | Some q => Some (Fora x q)
         | None => None
         end
       else Some (Fora x psi)
   | Exis x psi =>
       if isParamF xi (Exis x psi)
       then
        if isParamT x t
        then None
        else
         match f psi with
         | Some q => Some (Exis x q)
         | None => None
         end
       else Some (Exis x psi)
   end.

Section Interpretation.
Context {X} {fsI:forall(q:FSV),(Vector.t X (fsv q))->X}.
Context {prI:forall(q:PSV),(Vector.t X (psv q))->Omega}.

Fixpoint foI (val : SetVars.t -> X) (f : Fo) {struct f} : Omega :=
   match f with
   | Atom p t0 => prI p (map (@teI _ fsI val) t0)
   | Bot => OFalse
   | Conj f1 f2 => OAnd (foI val f1) (foI val f2)
   | Disj f1 f2 => OOr (foI val f1) (foI val f2)
   | Impl f1 f2 => OImp (foI val f1) (foI val f2)
   | Fora x f0 => forall m : X, foI (cng val x m) f0
   | Exis x f0 => exists m : X, foI (cng val x m) f0
   end.

End Interpretation.

End Formulas_mod.
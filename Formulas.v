Require Export Coq.Vectors.Vector.
Require Import Coq.Structures.Equalities.
Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Export Terms.

Module  Formulas_mod (SetVars FuncSymb PredSymb: UsualDecidableTypeFull).
Module X := terms_mod SetVars FuncSymb.
Export X.

Notation SetVars := SetVars.t.
Notation PredSymb := PredSymb.t.
Notation FuncSymb := FuncSymb.t.

Record PSV := MPSV{
 ps : PredSymb;
 psv : nat;
}.
(*Check Terms.
Check terms_mod.Terms.
Check Formulas_mod.Terms.*)
(*Formulas*)
Inductive Fo :=
 |Atom (p:PSV) : (Vector.t Terms (psv p)) ->  Fo
 |Bot :Fo
 |Conj:Fo->Fo->Fo
 |Disj:Fo->Fo->Fo
 |Impl:Fo->Fo->Fo
 |Fora(x:SetVars)(f:Fo): Fo
 |Exis(x:SetVars)(f:Fo): Fo
.

(* Substitution *)
Fixpoint isParamF (xi : SetVars) (f : Fo) {struct f} : bool :=
   match f with
   | Atom p t0 => Vector.fold_left orb false (Vector.map (isParamT xi) t0)
   | Bot => false
   | Conj f1 f2 | Disj f1 f2 | Impl f1 f2 => isParamF xi f1 || isParamF xi f2
   | Fora x f0 | Exis x f0 =>
       if SetVars.eqb x xi then false else isParamF xi f0
   end.

Fixpoint substF (t:Terms) (xi: SetVars) (u : Fo): option Fo. 
Proof.
pose(g := substT t xi).
pose(f := substF t xi).
destruct u.
refine (Some (Atom p _)).
exact (Vector.map g t0).
exact (Some Bot).
 exact (
 match (f u1),(f u2) with
 | Some f0,Some f1 => (Some (Conj f0 f1))
 | _,_ => None
 end).
 exact (
 match (f u1),(f u2) with
 | Some f0,Some f1 => (Some (Disj f0 f1))
 | _,_ => None
 end).
 exact (
 match (f u1),(f u2) with
 | Some f0,Some f1 => (Some (Impl f0 f1))
 | _,_ => None
 end).
(*destruct (isParamF xi (Fora x0 u)).*)
refine (match (isParamF xi (Fora x u)) with 
| true => match (isParamT x t) with 
          | false => match substF t xi u with
                    | Some q => Some (Fora x q)
                    | None => None
                    end
          | true => None
          end
| false => Some (Fora x u) end).
refine (match (isParamF xi (Exis x u)) with 
| true => match (isParamT x t) with 
          | false => match substF t xi u with
                    | Some q => Some (Exis x q)
                    | None => None
                    end
          | true => None
          end
| false => Some (Exis x u) end).
Show Proof.
Defined.


Definition Top:Fo := Impl Bot Bot.

Notation " x --> y ":=(Impl x y) (at level 80).
(*
Notation " u '[' t >> xi ] ":=(substT t xi u ) (at level 10).
Set Warnings "-notation-overridden".
Notation " ph [ t | xi ] ":=(substF t xi ph ) (at level 10).
(*Set Warnings "default".*)
Check fun (t:Terms) (x:SetVars) => ( t [ t >> x ]).
Check fun (t:Terms) (x:SetVars) (ph:Fo) => ( ph [ t | x ] ).
*)


End Formulas_mod.
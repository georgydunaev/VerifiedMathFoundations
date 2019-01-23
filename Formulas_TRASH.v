(* This file is not for compilation! *)

========
(*Local Notation SetVars := SetVars.t (*only parsing*).
Local Notation FuncSymb := FuncSymb.t (*only parsing*).
Local Notation PredSymb := PredSymb.t (*only parsing*).*)
(*Notation PredSymbQQ := PredSymb.t.*)
========


Fixpoint substF (t:Terms) (xi: SetVars.t) (u : Fo): option Fo.
Proof.
pose(f := substF t xi).
destruct u.
refine (Some (Atom p _)).
exact (Vector.map (substT t xi) t0).
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
Abort.

========

(*
Notation " u '[' t >> xi ] ":=(substT t xi u ) (at level 10).
Set Warnings "-notation-overridden".
Notation " ph [ t | xi ] ":=(substF t xi ph ) (at level 10).
(*Set Warnings "default".*)
Check fun (t:Terms) (x:SetVars) => ( t [ t >> x ]).
Check fun (t:Terms) (x:SetVars) (ph:Fo) => ( ph [ t | x ] ).
*)

========

(*
Fixpoint foI (val:SetVars->X) (f:Fo): Omega.
Proof.
destruct f.
+ refine (prI p _).
  apply (Vector.map  (teI val)).
  exact t.
+ exact false.
+ exact ( andb (foI val f1) (foI val f2)).
+ exact (  orb (foI val f1) (foI val f2)).
+ exact (implb (foI val f1) (foI val f2)).
+  (*Infinite conjunction!!!*)
 Show Proof.
*)

========

(*Import FormulasNotationsUnicode.*)
Fixpoint foI (val:SetVars.t->X) (f:Fo): Omega.
Proof.
destruct f.
+ refine (prI p _).
  eapply (@Vector.map Terms X (@teI _ fsI val)).
  exact t.
+ exact OFalse.
+ exact ( OAnd (foI val f1) (foI val f2)).
+ exact (  OOr (foI val f1) (foI val f2)).
+ exact ( OImp (foI val f1) (foI val f2)).
+ exact (forall m:X, foI (cng val x m) f).
+ exact (exists m:X, foI (cng val x m) f).
Show Proof.
Abort.
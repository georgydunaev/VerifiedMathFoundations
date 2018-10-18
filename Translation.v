Add LoadPath "/home/user/0my/GITHUB/VerifiedMathFoundations/library".
Require Propositional.
Require Import PredicateCalculus.
Check Propositional.InL.
Module O.
Import Propositional.
Export Propositional.
End O.
Module E.
Import PredicateCalculus.
End E.

(*
Import O.
Check InL.
Export O.
Check InL.
*)
(*
Fail Check InL.*)
(*Check Propositional.Prop_mod.Fo. *)
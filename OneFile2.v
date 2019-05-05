(* Author: Georgy Dunaev, georgedunaev@gmail.com *)
Require Import Bool.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import Coq.Structures.Equalities.

(* Firstly I prove some lemmas, then the module "ALL_mod" contains
the soundness theorem of the predicate logic. *)

(** 1. NOTATIONS **)
Notation Omega := Prop.
Definition OFalse := False.
Definition OAnd := and.
Definition OOr := or.
Definition OImp := (fun x y:Omega => x->y).

(** 2. TRIVIAL LEMMAS **)
Lemma my_andb_true_eq :
  forall a b:bool, a && b = true -> a = true /\ b = true.
Proof.
  destr_bool. auto.
Defined.

Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.

Theorem contraposition : forall p q:Prop, (p->q)->(~q->~p).
Proof. intros. intro. apply H0. apply H. exact H1. Defined.

(** 3. ALL THEN SOME (VECTOR) **)
Import VectorNotations.

Fixpoint ATS_B2 (n:nat) (l:t bool n) :fold_left orb true l = true.
Proof.
destruct l; simpl.
reflexivity.
apply ATS_B2.
Defined.

Fixpoint ATS_B0 b (n:nat) (l:t bool n) : 
fold_left orb false (b :: l)  = orb b (fold_left orb false l) .
Proof.
destruct l.
simpl. firstorder.
simpl.
destruct b.
simpl.
apply ATS_B2.
simpl.
reflexivity.
Defined.

Definition ATS_G h (n:nat) (l:Vector.t bool n) : Prop :=
 @eq bool (@fold_left bool bool orb false (S n) (cons bool h n l)) false.

Lemma vp1 (n:nat) (l : t bool (S n)) : exists (q:bool) (m:t bool n), l = (q::m).
Proof.
apply (@caseS bool (fun n => 
fun (l : t bool (S n)) => exists (q : bool) (m : t bool n), l = q :: m)).
intros.
exists h.
exists t.
reflexivity.
Defined.

Fixpoint all_then_someV (n:nat) (l:Vector.t bool n) {struct l} :
(Vector.fold_left orb false l ) = false ->
(forall p, (Vector.nth l p  ) = false).
Proof.
intros.
destruct l.
{ inversion p. }
{ (*fold G in H.*)
  assert (vari : ATS_G h n l).
  { exact H. }
  clear H.
  revert h l vari.
  set (P := fun n p => forall (h : bool) (l : t bool n) (_ :ATS_G h n l),
    @eq bool (@nth bool (S n) (cons bool h n l) p) false).
  revert n p.
  fix loop 1.
  intros n;revert n.
  unshelve eapply (@Fin.rectS P).
  { unfold P.
    intros.
    simpl.
    unfold ATS_G in H.
    rewrite -> (ATS_B0 h n l) in H.
    apply orb_false_elim in H as [H _]; exact H.
  }
  { unfold P.
    intros.
    unfold ATS_G in H0.
    simpl in  |- *.
    rewrite -> (ATS_B0 h (S n) l) in H0.
    apply orb_false_elim in H0 as [_ HH1].
    assert (YO := vp1 n l).
    destruct YO as [YO1 [YO2 YO3]].
    rewrite -> YO3.
    apply H.
    unfold ATS_G.
    rewrite <- YO3.
    exact HH1. }
}
Defined.

(** 4. MISC **)
Definition ap {A B}{a0 a1:A} (f:A->B) (h:a0=a1):((f a0)=(f a1))
:= match h in (_ = y) return (f a0 = f y) with
   | eq_refl => eq_refl
   end.

Theorem SomeInj {foo} :forall (a b : foo), Some a = Some b -> a = b.
Proof.
  intros a b H.
  inversion H.
  reflexivity.
Defined.

Lemma EqualThenEquiv A B: A=B -> (A<->B).
Proof. intro H. rewrite H. exact (iff_refl B). Defined.

(* Lemmas START *)
Lemma AND_EQV : forall A0 B0 A1 B1 : Prop,
 (A0 <-> A1) -> (B0 <-> B1) -> ((A0 /\ B0) <-> (A1 /\ B1)).
Proof.
intros A0 B0 A1 B1 H0 H1.
rewrite H0.
rewrite H1.
reflexivity.
Defined.

Lemma OR_EQV : forall A0 B0 A1 B1 : Prop,
 (A0 <-> A1) -> (B0 <-> B1) -> ((A0 \/ B0) <-> (A1 \/ B1)).
Proof.
intros A0 B0 A1 B1 H0 H1.
rewrite H0.
rewrite H1.
reflexivity.
Defined.

Lemma IMP_EQV : forall A0 B0 A1 B1 : Prop,
 (A0 <-> A1) -> (B0 <-> B1) -> ((A0 -> B0) <-> (A1 -> B1)).
Proof.
intros A0 B0 A1 B1 H0 H1.
rewrite H0.
rewrite H1.
reflexivity.
Defined.

Lemma FORALL_EQV {X}: forall A0 A1 : X -> Prop,
 (forall m, A0 m <-> A1 m) -> ((forall m:X, A0 m) <-> (forall m:X, A1 m)).
Proof.
intros A0 A1 H0.
split.
+ intros.
  rewrite <- H0.
  exact (H m).
+ intros.
  rewrite -> H0.
  exact (H m).
Defined.

Lemma EXISTS_EQV {X}: forall A0 A1 : X -> Prop,
 (forall m, A0 m <-> A1 m) -> ((exists m:X, A0 m) <-> (exists m:X, A1 m)).
Proof.
intros A0 A1 H0.
split.
+ intros.
  destruct H as [x Hx].
  exists x.
  rewrite <- H0.
  exact (Hx).
+ intros.
  destruct H as [x Hx].
  exists x.
  rewrite -> H0.
  exact (Hx).
Defined.
(* Lemmas END *)

(*** PREDICATE CALCULUS ***)
Module ALL_mod (SetVars FuncSymb PredSymb : UsualDecidableTypeFull).
Module Facts := BoolEqualityFacts SetVars.

(** 5. TERMS **)
Record FSV := {
 fs : FuncSymb.t;
 fsv : nat;
}.

Unset Elimination Schemes.
Inductive Terms : Type :=
| FVC :> SetVars.t -> Terms
| FSC (f:FSV) : (Vector.t Terms (fsv f)) -> Terms.
Set Elimination Schemes.

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

(* the next is useless for our aim *)
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

(* the next is useless for our aim *)
Definition Terms_rec (T : Terms -> Set)
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


Fixpoint substT (t:Terms) (xi: SetVars.t) (u:Terms): Terms
:=
   match u with
   | FVC s => if (SetVars.eqb s xi) then t else FVC s
   | FSC f t0 => FSC f (Vector.map (substT t xi) t0)
   end.

Fixpoint isParamT (xi : SetVars.t) (t : Terms) {struct t} : bool :=
   match t with
   | FVC s => SetVars.eqb s xi
   | FSC f t0 => Vector.fold_left orb false (Vector.map (isParamT xi) t0)
   end.

Section Interpretation1.
Context {X} {fsI:forall(q:FSV),(Vector.t X (fsv q))->X}.
Fixpoint teI
   (val:SetVars.t->X) (t:Terms): X :=
   match t with
   | FVC s => val s
   | FSC f t0 => fsI f (Vector.map (teI val) t0)
   end.
End Interpretation1.

(** 6. VALUATIONS **)
Section a.
Context {X:Type}.

Definition cng (val:SetVars.t -> X) (xi:SetVars.t) (m:X) :=
 (fun r:SetVars.t =>
 match SetVars.eqb r xi with
 | true => m
 | false => (val r)
 end).

Lemma dbl_cng (pi:SetVars.t->X) x m0 m1 :
 forall u, (cng (cng pi x m0) x m1) u = (cng pi x m1) u.
Proof.
intro u.
unfold cng.
destruct (SetVars.eqb u x).
reflexivity.
reflexivity.
Defined.

End a.

(** 7. FORMULAS **)
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

Module PredFormulasNotationsUnicode.
 Notation " '⊥' "   :=(Bot) (at level 80) : preuninot.
 Notation " x '∧' y ":=(Conj x y) (at level 80) : preuninot.
 Notation " x '∨' y ":=(Disj x y) (at level 80) : preuninot.
 Notation " x '→' y ":=(Impl x y) (at level 80, right associativity) : preuninot.
 Notation " '∀' x f " :=(Fora x f) (at level 80) : preuninot.
 Notation " '∃' x f " :=(Exis x f) (at level 80) : preuninot.
 Notation " '¬' x "   :=(Neg x) (at level 80)  : preuninot.
Delimit Scope preuninot with eud.
(* Example :
Fail Check (¬ ⊥).
Check (¬ ⊥)%unidel.
Local Open Scope uninot.
Check (¬ ⊥).
Local Close Scope uninot.
*)
End PredFormulasNotationsUnicode.

Module PredFormulasNotationsASCII.
 Notation " x --> y ":=(Impl x y) (at level 80, right associativity) : pretxtnot.
 Notation " x -/\ y ":=(Conj x y) (at level 80) : pretxtnot.
 Notation " x -\/ y ":=(Disj x y) (at level 80) : pretxtnot.
 Notation " -. x "   :=(Neg x) (at level 80) : pretxtnot.
 Delimit Scope pretxtnot with etd.
End PredFormulasNotationsASCII.

Fixpoint isParamF (xi : SetVars.t) (f : Fo) {struct f} : bool :=
   match f with
   | Atom p t0 => Vector.fold_left orb false (Vector.map (isParamT xi) t0)
   | Bot => false
   | Conj f1 f2 | Disj f1 f2 | Impl f1 f2 => isParamF xi f1 || isParamF xi f2
   | Fora x f0 | Exis x f0 =>
       if SetVars.eqb x xi then false else isParamF xi f0
   end.

(* Substitution *)
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

Section Interpretation2.
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

End Interpretation2.

(** 8. PROVABILITY **)
Import PredFormulasNotationsASCII.
Local Open Scope pretxtnot.

(* intuitionistic "PROpositional" Calculus Axioms *)
Inductive PROCA : Fo -> Type :=
| Ha1  : forall A B, PROCA (A-->(B-->A))
| Ha2  : forall A B C, PROCA ((A-->(B-->C))-->((A-->B)-->(A-->C)))
| Ha3  : forall A B, PROCA (Conj A B --> A)
| Ha4  : forall A B, PROCA (Conj A B --> B)
| Ha5  : forall A B, PROCA (A --> (B --> Conj A B))
| Ha6  : forall A B, PROCA (A --> Disj A B)
| Ha7  : forall A B, PROCA (B --> Disj A B)
| Ha8  : forall A B C, PROCA ((A --> C) --> ((B --> C) --> (Disj A B --> C)))
| Ha9  : forall A B, PROCA (Neg A --> (A --> B))
| Ha10  : forall A B, PROCA ((A --> B) --> ((A --> Neg B) --> Neg A))
.

(* intuitionistic PREdicate Calculus Axioms *)
Inductive PRECA : Fo -> Type :=
| PRO  :> forall A, (PROCA A) -> (PRECA A)
| Ha12 : forall (ph: Fo) (t:Terms) (xi:SetVars.t)
 (r:Fo) (s:(substF t xi ph)=Some r), PRECA ((Fora xi ph) --> r)
| Ha13 : forall (ph: Fo) (t:Terms) (xi:SetVars.t)
 (r:Fo) (s:(substF t xi ph)=Some r), PRECA (r --> (Exis xi ph) )
| Hb1  : forall (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false),
PRECA (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
| Hb2  : forall (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false),
PRECA (Impl (Fora xi (Impl ph ps)) (Impl (Exis xi ph) ps ) )
.

Definition NotParamC xi ctx :=
 forall F : Fo, ctx F -> isParamF xi F = false.

Section PREPR.
Context (ctx:Fo->Type).
(*Context (ctx:list Fo).*)
Inductive PREPR : Fo -> Type :=
| hyp_E (A : Fo) : (ctx A) -> (PREPR A)
| Hax_E :> forall (A : Fo), (PRECA A) -> (PREPR A)
| MP_E (A B: Fo) : (PREPR A) -> (PREPR (Impl A B)) -> (PREPR B)
| GEN_E (A: Fo) (xi :SetVars.t) (nic:NotParamC xi ctx)
  : (PREPR A) -> (PREPR (Fora xi A))
.
End PREPR.

Definition a1 ctx A B : @PREPR ctx (Impl A (Impl B A)).
Proof. apply Hax_E, PRO, Ha1. Defined.
Definition a2 axi A B C : @PREPR axi ((A-->(B-->C))-->((A-->B)-->(A-->C))).
Proof. apply Hax_E, PRO, Ha2. Defined.
Definition b1 axi (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false):
@PREPR axi (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) ).
Proof. apply Hax_E, Hb1, H. Defined.

Definition AtoA {ctx} (A:Fo) : PREPR ctx (A-->A).
Proof.
apply MP_E with (A := (A-->(A-->A))).
apply Hax_E, PRO, Ha1.
apply MP_E with (A := A-->((A-->A)-->A)).
apply Hax_E, PRO, Ha1.
apply Hax_E, PRO, Ha2.
Defined.

(* Another style of the proof:
Definition AtoA {ctx} (A:Fo) : PREPR ctx (A-->A).
Proof.
eapply MP_E.
2 : { eapply MP_E.
  2 : { apply Hax_E, PRO, Ha2. }
  apply Hax_E, PRO, Ha1. }
apply Hax_E, PRO, Ha1.
Unshelve. exact A.
Defined.
*)

Notation SetVars := SetVars.t (only parsing).
Notation FuncSymb := FuncSymb.t (only parsing).
Notation PredSymb := PredSymb.t (only parsing).

Import Coq.Lists.List.

(* Example: 1st Bernays Rule is admissable *)
Definition B1 (ps ph:Fo) (xi:SetVars) ctx 
 (H:isParamF xi ps = false)
 (T:NotParamC xi ctx) :
 PREPR ctx (ps --> ph) -> PREPR ctx (ps --> Fora xi ph).
Proof.
intro q.
apply MP_E with (A:=(Fora xi (ps --> ph))).
+ apply (GEN_E).
  exact T.
  exact q.
+ apply (b1 _).
  exact H.
Defined.

Definition a1i (A B : Fo)(l : Fo -> Type):(PREPR l B)->(PREPR l (Impl A B)).
Proof.
intros x.
apply MP_E with (A:= B).
exact x.
apply a1.
Defined.

(* Example: Generalization from 1st Bernay's rule*)
Definition gen (A:Fo) (xi:SetVars) ctx
 (T:NotParamC xi ctx)
 : PREPR ctx (A) -> PREPR ctx (Fora xi A).
Proof.
intro q.
apply MP_E with (A:= Top).
unfold Top.
exact (@AtoA ctx Bot).
apply B1.
+ trivial.
+ exact T.
+ apply a1i.
  exact q.
Defined.

(* Contexts *)
 Inductive empctx : Fo -> Type :=. (* empty context *)

 Definition add2ctx (A:Fo) (l:Fo->Type) : Fo->Type 
 := fun f=> sum (A=f) (l f). (* add head *)
Definition CTX := Fo->Type.
(* Deduction theorem *)
Fixpoint Ded (A B:Fo)(il:CTX)(m:(PREPR (add2ctx A il) B))
{struct m}:(PREPR il (A-->B)).
Proof.
destruct m.
+ rename a into i.
 simpl in i.
  destruct i.
  - rewrite <- e.
    exact (AtoA A).
  - apply a1i.
    apply hyp_E with (ctx:=il) (1:=i).
+ apply a1i.
  apply Hax_E, p.
+ apply MP_E with (A:= (A-->A0)).
  - simple refine (@Ded _ _ _ _).
    1 : exact m1.
  - apply MP_E with (A:= (A-->(A0-->B))).
    * simple refine (@Ded _ _ _ _).
      exact m2.
    * apply a2.
+ (*Last part about GEN*)
  apply MP_E with (A:= (Fora xi (A-->A0))).
  - eapply GEN_E.
    { intros A1 M. apply nic. right. exact M. }
    simple refine (@Ded _ _ _ _ ).
    * exact m.
  - simpl.
    eapply Hax_E.
    eapply Hb1.
    apply nic. left. trivial.
Defined.

Definition swap_args ctx A B C :
(PREPR ctx ((A --> (B --> C)) --> (B --> (A --> C)) )).
Proof.
unshelve eapply Ded.
unshelve eapply Ded.
unshelve eapply Ded.
apply MP_E with (A:=B) .
+ apply hyp_E.
  simpl. firstorder.
+ apply MP_E with (A:=A) .
  apply hyp_E; firstorder.
  apply hyp_E; firstorder.
Defined.

(** 9. SOUNDNESS **)
(* Soundness theorem section *)
Section cor.
Context (X:Type).
Context (fsI:forall(q:FSV),(Vector.t X (fsv q))->X).
Context (prI:forall(q:PSV),(Vector.t X (psv q))->Omega).

Section Lem1.
(* page 136 of the book *)
Definition lem1 (t : Terms) : forall (u :Terms) 
(xi : SetVars.t) (pi : SetVars.t->X) ,
(@teI X fsI pi (substT t xi u))=(@teI X fsI (cng pi xi (@teI X fsI pi t)) u).
Proof.
fix lem1 1.
intros.
induction u as [s|f].
+ simpl.
  unfold cng.
  destruct (SetVars.eqb s xi) eqn:ek.
  * reflexivity.
  * simpl.
    reflexivity.
+ simpl.
  destruct f.
  simpl.
  apply ap.
  simpl in * |- *.
  apply (proj1 (
   eq_nth_iff X fsv0
   (Vector.map (teI pi) (Vector.map (substT t xi) v))
   (Vector.map (teI (cng pi xi (teI pi t))) v)
  )).
  intros.
  simpl in * |- *.
  rewrite -> (nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0).
  rewrite -> (nth_map (teI (cng pi xi (teI pi t))) v p2 p2 ).
  rewrite -> (nth_map (substT t xi) v p2 p2 eq_refl).
  exact (H p2).
  reflexivity.
Defined.
End Lem1.

Lemma all_then_someP (A:Type)(n:nat)(p:Fin.t (n)) (v:Vector.t A (n)) (P:A->bool)
(H : Vector.fold_left orb false (Vector.map P v) = false)
 : (P (Vector.nth v p)) = false.
Proof.
rewrite <- (nth_map P v p p eq_refl).
apply all_then_someV. trivial.
Defined.

(* Not a parameter then not changed afted substitution (for Terms) *)
Lemma NPthenNCAST (u:Terms)(xi:SetVars.t)(t:Terms) (H:(isParamT xi u=false))
: (substT t xi u) = u.
Proof. induction u.
+ simpl in * |- *.
  rewrite H. reflexivity.
+ simpl in * |- *.
  apply ap.
  apply eq_nth_iff.
  intros p1 p2 ppe.
  rewrite (nth_map _ _ _ p2 ppe).
  apply H0.
  simpl.
  apply all_then_someP.
  trivial.
Defined.

Lemma NPthenNCAST_vec:forall p xi t ts (H:(isParamF xi (Atom p ts)=false)),
  (Vector.map (substT t xi) ts) = ts.
Proof.
intros p xi t1 ts H.
apply eq_nth_iff.
intros p1 p2 H0.
rewrite -> (nth_map (substT t1 xi) ts p1 p2 H0).
apply NPthenNCAST.
apply all_then_someP.
simpl in H.
exact H.
Defined.

(* Not a parameter then not changed afted substitution (for Formulas) *)
Fixpoint NPthenNCASF (mu:Fo) : forall (xi:SetVars.t)(t:Terms) (H:(isParamF xi mu=false))
   , substF t xi mu = Some mu .
Proof. (*induction mu eqn:u0.*)
destruct mu eqn:u0 ; simpl; intros xi t0 H.
* rewrite -> NPthenNCAST_vec; (trivial || assumption).
* trivial.
* simpl in H.
  apply orb_false_elim in H as [H0 H1].
  rewrite -> NPthenNCASF .
  rewrite -> NPthenNCASF .
  trivial.
  trivial.
  trivial.
* apply orb_false_elim in H as [H0 H1].
  rewrite -> NPthenNCASF.
  rewrite -> NPthenNCASF.
  trivial.
  trivial.
  trivial.
* apply orb_false_elim in H as [H0 H1].
  rewrite -> NPthenNCASF.
  rewrite -> NPthenNCASF.
  trivial.
  trivial.
  trivial.
* destruct (SetVars.eqb x xi) eqn:u2.
  trivial.
  destruct (isParamF xi f) eqn:u1.
  inversion H.
  trivial.
* destruct (SetVars.eqb x xi) eqn:u2.
  trivial.
  destruct (isParamF xi f) eqn:u1.
  inversion H.
  trivial.
Defined.

(* p.137 *)
Section Lem2.
Lemma weafunT pi mu (q: forall z, pi z = mu z) t :
@teI X fsI pi t = @teI X fsI mu t.
Proof.
induction t.
+ simpl. exact (q sv).
+ simpl. apply ap.
  apply eq_nth_iff.
  intros p1 p2 HU.
  rewrite -> (nth_map (teI pi) v p1 p2 HU).
  rewrite -> (nth_map (teI mu) v p2 p2 eq_refl).
  apply H.
Defined.

Lemma weafunF (pi mu:SetVars.t->X) (q: forall z, pi z = mu z) fi :
 @foI X fsI prI pi fi <-> @foI X fsI prI mu fi.
Proof.
revert pi mu q.
induction fi.
intros pi mu q.
+ simpl.
  apply EqualThenEquiv.
  apply ap.
  apply eq_nth_iff.
  intros p1 p2 HU.
  rewrite -> (nth_map (teI pi) t p1 p2 HU).
  rewrite -> (nth_map (teI mu) t p2 p2 eq_refl).
  apply weafunT.
  apply q.
+ simpl. reflexivity.
+ simpl. intros. 
  rewrite -> (IHfi1 pi mu q).
  rewrite -> (IHfi2 pi mu q).
  reflexivity.
+ simpl. intros. 
  rewrite -> (IHfi1 pi mu q).
  rewrite -> (IHfi2 pi mu q).
  reflexivity.
+ simpl.
  unfold OImp.
  split;
  intros;
  apply (IHfi2 pi mu q);
  apply H;
  apply (IHfi1 pi mu q);
  apply H0.
+ simpl.
  split.
  * intros.
    rewrite IHfi.
    apply H with (m:=m).
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    symmetry.
    apply q.
  * intros.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    apply q.
+ simpl.
  split.
  * intros.
    destruct H as [m H].
    exists m.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    symmetry.
    apply q.
  * intros.
    destruct H as [m H].
    exists m.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    apply q.
Defined.

(** weak weafun theorems BEGIN **)
(* it's for Torelsta's systems *)

Lemma some_then_trueV
     : forall (n : nat) (l : t bool n) (p : Fin.t n), l[@p] = true ->
       Vector.fold_left orb false l = true.
Proof.
intros.
apply not_false_is_true.
eapply contraposition.
refine (all_then_someV _ _).
intro W.
assert (Q:=W p).
rewrite Q in H.
inversion H.
Defined.

Lemma wweafunT pi mu t
 (q: forall z, isParamT z t=true -> pi z = mu z) :
 @teI X fsI pi t = @teI X fsI mu t.
Proof.
induction t.
+ simpl. apply q. simpl. exact (Facts.eqb_refl sv).
+ simpl. apply ap.
  apply eq_nth_iff.
  intros p1 p2 HU.
  rewrite -> (nth_map (teI pi) v p1 p2 HU).
  rewrite -> (nth_map (teI mu) v p2 p2 eq_refl).
  apply H.
  { intros z S. apply q. simpl.
eapply some_then_trueV.
rewrite ( nth_map (isParamT z) v p2 p2 eq_refl).
exact S. }
Defined.

Lemma fleft (fi1 fi2 : Fo) (C:SetVars.t->Omega) (q:forall z : SetVars.t, 
isParamF z fi1 || isParamF z fi2 = true -> C z):
 forall z : SetVars.t, isParamF z fi1  = true -> C z.
Proof.
{ intros z J. apply q. rewrite orb_true_iff. left. exact J. }
Defined.

Lemma fright (fi1 fi2 : Fo) (C:SetVars.t->Omega) (q:forall z : SetVars.t, 
isParamF z fi1 || isParamF z fi2 = true -> C z):
 forall z : SetVars.t, isParamF z fi2 = true -> C z.
Proof.
{ intros z J. apply q. rewrite orb_true_iff. right. exact J. }
Defined.

Lemma wweafunF (pi mu:SetVars.t->X) fi (q: forall z, isParamF z fi=true -> pi z = mu z) :
 @foI X fsI prI pi fi <-> @foI X fsI prI mu fi.
Proof.
revert pi mu q.
induction fi.
intros pi mu q.
+ simpl.
  apply EqualThenEquiv.
  apply ap.
  apply eq_nth_iff.
  intros p1 p2 HU.
  rewrite -> (nth_map (teI pi) t p1 p2 HU).
  rewrite -> (nth_map (teI mu) t p2 p2 eq_refl).
destruct HU.
  apply wweafunT.
  simpl in q.
intros z Q.
eapply q.
eapply some_then_trueV.
  rewrite -> (nth_map (isParamT z) t p1 p1 eq_refl).
  exact Q.
+ simpl. reflexivity.
+ simpl. intros.
assert (q1:=fleft fi1 fi2 (fun z=>pi z = mu z) q).
assert (q2:=fright fi1 fi2 (fun z=>pi z = mu z) q).
(*  eapply fright in q.
  rewrite -> (IHfi1 pi mu q1).
rewrite orb_true_iff in q.
assert (q1: forall z : SetVars.t,
    isParamF z fi1  = true ->
    pi z = mu z).
{ intros z J. apply q. rewrite orb_true_iff. left. exact J. } *)
  rewrite -> (IHfi1 pi mu q1).
  rewrite -> (IHfi2 pi mu q2).
  reflexivity.
+ simpl. intros.
assert (q1:=fleft fi1 fi2 (fun z=>pi z = mu z) q).
assert (q2:=fright fi1 fi2 (fun z=>pi z = mu z) q).
  rewrite -> (IHfi1 pi mu q1).
  rewrite -> (IHfi2 pi mu q2).
  reflexivity.
+ simpl.
  unfold OImp.
  intros.
assert (q1:=fleft fi1 fi2 (fun z=>pi z = mu z) q).
assert (q2:=fright fi1 fi2 (fun z=>pi z = mu z) q).
  split;
   intros;
   eapply (IHfi2 pi mu q2);
   apply H;
   apply (IHfi1 pi mu q1);
   apply H0.
+ simpl.
  intros.

(*assert (q1:=fleft fi1 fi2 (fun z=>pi z = mu z) q).
  assert (q2:=fright fi1 fi2 (fun z=>pi z = mu z) q).*)
  split.
  * intros.
    rewrite IHfi.
    apply H with (m:=m).
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    symmetry.
(*
    apply q.
  * intros.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    apply q.
+ simpl.
  split.
  * intros.
    destruct H as [m H].
    exists m.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    symmetry.
    apply q.
  * intros.
    destruct H as [m H].
    exists m.
    rewrite IHfi.
    apply H.
    intro z.
    unfold cng.
    destruct (SetVars.eqb z x).
    reflexivity.
    apply q.
Defined.
*)
Admitted.
(** weak weafun theorems END **)

Lemma cng_commF_EQV  xe xi m0 m1 pi fi :
SetVars.eqb xe xi = false -> 
(@foI X fsI prI (cng (cng pi xe m0) xi m1) fi <-> @foI X fsI prI (cng (cng pi xi m1) xe m0) fi).
Proof.
intros H.
apply weafunF.
intros z.
unfold cng.
destruct (SetVars.eqb z xi) eqn:e0, (SetVars.eqb z xe) eqn:e1.
assert (U0:= proj1 (SetVars.eqb_eq z xi) e0).
rewrite U0 in e1.
assert (U1:= proj1 (SetVars.eqb_eq xi xe) e1).
symmetry in U1.
assert (U2:= proj2 (SetVars.eqb_eq xe xi) U1).
rewrite U2 in H.
inversion H.
reflexivity. reflexivity. reflexivity.
Defined.

Lemma lem2caseAtom : forall (p : PSV) (t0 : Vector.t Terms (psv p))
(t : Terms) (xi : SetVars.t) (pi : SetVars.t->X)
(r:Fo) (H:(substF t xi (Atom p t0)) = Some r) ,
@foI X fsI prI pi r <-> @foI X fsI prI (cng pi xi (@teI X fsI pi t)) (Atom p t0).
Proof.
intros.
+ simpl in H.
  assert (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply EqualThenEquiv.
  apply ap.
  apply 
    (proj1 (
      eq_nth_iff X (psv p) 
      (Vector.map (teI pi) (Vector.map (substT t xi) t0))
      (Vector.map (teI (cng pi xi (teI pi t))) t0)
    )).
  rename t0 into v.
  intros p1 p2 H0.
  rewrite -> (nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0).
  rewrite -> (nth_map (teI (cng pi xi (teI pi t))) v p2 p2 ).
  rewrite -> (nth_map (substT t xi) v p2 p2 eq_refl).
  apply lem1. reflexivity.
Defined.

Lemma NPthenNCACVT x t m pi :
 isParamT x t = false ->
 (@teI X fsI (cng pi x m) t) = (@teI X fsI pi t).
Proof.
intros H.
induction t.
unfold cng.
simpl in * |- *.
rewrite H.
reflexivity.
simpl in * |- *.
apply ap.
apply eq_nth_iff.
intros.
rewrite -> (nth_map (teI (cng pi x m)) v p1 p2 H1).
rewrite -> (nth_map (teI pi) v p2 p2 eq_refl).
apply H0.
apply (all_then_someP Terms (fsv f) p2 v (isParamT x) H).
Defined.

Lemma eqb_comm x xi : SetVars.eqb xi x = SetVars.eqb x xi.
Proof.
destruct (SetVars.eqb xi x) eqn:e1.
symmetry.
assert (Y:= proj1 (SetVars.eqb_eq xi x) e1).
rewrite -> Y at 1.
rewrite <- Y at 1.
exact e1.
symmetry.
assert (n3:= proj2 (not_iff_compat (SetVars.eqb_eq x xi)) ).
apply not_true_iff_false.
apply n3.
intro q.
symmetry in q.
revert q.
fold (xi <> x).
assert (n5:= proj1 (not_iff_compat (SetVars.eqb_eq xi x)) ).
apply n5.
apply not_true_iff_false.
exact e1.
Defined.

Lemma NPthenNCACVF xi fi m mu : isParamF xi fi = false ->
 @foI X fsI prI (cng mu xi m) fi <-> @foI X fsI prI mu fi.
Proof.
revert mu.
induction fi; intro mu;
intro H;
simpl in * |- *.
* apply EqualThenEquiv.
  apply ap.
  apply eq_nth_iff.
  intros p1 p2 H0.
  rewrite -> (nth_map (teI (cng mu xi m)) t p1 p2 H0).
  rewrite -> (nth_map (teI mu) t p2 p2 eq_refl).
  apply NPthenNCACVT.
  apply (all_then_someP Terms (psv p) p2 t (isParamT xi) H).
  (*1st done *)
* firstorder.
* apply AND_EQV.
  apply IHfi1. destruct (orb_false_elim _ _ H). apply H0.
  apply IHfi2. destruct (orb_false_elim _ _ H). apply H1.
* apply OR_EQV.
  apply IHfi1. destruct (orb_false_elim _ _ H). apply H0.
  apply IHfi2. destruct (orb_false_elim _ _ H). apply H1.
* apply IMP_EQV.
  apply IHfi1. destruct (orb_false_elim _ _ H). apply H0.
  apply IHfi2. destruct (orb_false_elim _ _ H). apply H1.
* apply FORALL_EQV. intro m0.
  destruct (SetVars.eqb x xi) eqn:e1.
  assert (C:=proj1 (SetVars.eqb_eq x xi) e1).
  rewrite <- C.
  pose (D:= dbl_cng mu x m m0).
  exact (weafunF _ _ D fi).
  rewrite cng_commF_EQV.
  (* IHfi is an inductive hypotheis *)
  apply IHfi.
  exact H.
  rewrite <-(eqb_comm xi x).
  exact e1.
* apply EXISTS_EQV. intro m0.
  fold (cng (cng mu xi m) x m0).
  fold (cng mu x m0).
  destruct (SetVars.eqb x xi) eqn:e1.
  assert (C:=proj1 (SetVars.eqb_eq x xi) e1).
  rewrite <- C.
  assert (D:= dbl_cng mu x m m0).
  exact (weafunF _ _ D fi).
  rewrite cng_commF_EQV.
  (* IHfi is an inductive hypothesis*)
  apply IHfi.
  exact H.
  rewrite <-(eqb_comm xi x).
  exact e1.
Defined.

Definition lem2 (t : Terms) : forall (fi : Fo) (xi : SetVars.t) (pi : SetVars.t->X)
 (r:Fo) (H:(substF t xi fi) = Some r),
 (@foI X fsI prI pi r)<->(@foI X fsI prI (cng pi xi (@teI X fsI pi t)) fi).
Proof.
fix lem2 1.
(*H depends on t xi fi r *)
intros fi xi pi r H.
revert pi r H.
induction fi;
intros pi r H.
+ apply lem2caseAtom.
  exact H.
+ inversion H. simpl. reflexivity.
+ simpl in *|-*.
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  assert (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  unfold OAnd.
  apply AND_EQV.
  simpl in * |- *.
  * apply (IHfi1 pi f1 eq_refl).
  * apply (IHfi2 pi f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in *|-*.
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  assert (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl in * |- *.
  apply OR_EQV.
  * apply (IHfi1 pi f1 eq_refl).
  * apply (IHfi2 pi f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in *|-*.
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  assert (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl in * |- *.
  apply IMP_EQV.
  * apply (IHfi1 pi f1 eq_refl).
  * apply (IHfi2 pi f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in * |- *.
  destruct (SetVars.eqb x xi) eqn:l2.
  assert (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply FORALL_EQV.
  intro m.
  assert (RA : x = xi).
  apply (SetVars.eqb_eq x xi ).
  exact l2.
  rewrite <- RA.
  rewrite -> (weafunF (cng (cng pi x (teI pi t)) x m) (cng pi x m) 
   (dbl_cng pi x (teI pi t) m) fi).
  firstorder.
  destruct (isParamF xi fi) eqn:l1.
  destruct (isParamT x t) eqn:l3.
  inversion H.
  destruct (substF t xi fi) eqn:l4.
  assert (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply FORALL_EQV.
  intro m.
  rewrite cng_commF_EQV.
  2 : {
    rewrite -> eqb_comm .
    exact l2.
  }
  rewrite <- (NPthenNCACVT x t m pi l3).
  exact (IHfi (cng pi x m) f eq_refl).
  inversion H.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply FORALL_EQV.
  intro m.
  rewrite cng_commF_EQV.
  symmetry.
  exact (NPthenNCACVF xi fi (teI pi t) (cng pi x m) l1).
  rewrite -> (eqb_comm x xi).
  exact l2. (* end of FORALL case*)
+ simpl in * |- *.
  destruct (SetVars.eqb x xi) eqn:l2.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply EXISTS_EQV.
  intro m.
  assert (RA : x = xi).
  apply (SetVars.eqb_eq x xi ).
  exact l2.
  rewrite <- RA.
  rewrite -> (weafunF (cng (cng pi x (@teI X fsI pi t)) x m) (cng pi x m) 
   (dbl_cng pi x (@teI X fsI pi t) m) fi).
  firstorder.
  destruct (isParamF xi fi) eqn:l1.
  pose(xint := (isParamT x t)).
  destruct (isParamT x t) eqn:l3.
  inversion H.
  destruct (substF t xi fi) eqn:l4.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply EXISTS_EQV.
  intro m.
  fold (cng  pi x m ).
  fold (cng  (cng pi xi (@teI X fsI pi t)) x m ).
  rewrite cng_commF_EQV.
  2 : {
    rewrite -> eqb_comm .
    exact l2.
  }
  rewrite <- (NPthenNCACVT x t m pi l3).
  exact (IHfi (cng pi x m) f eq_refl).
  inversion H.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply EXISTS_EQV.
  intro m.
  fold (cng  pi x m ).
  fold (cng  (cng pi xi (@teI X fsI pi t)) x m ).
  rewrite cng_commF_EQV.
  symmetry.
  exact (NPthenNCACVF xi fi (teI pi t) (cng pi x m) l1).
  rewrite -> (eqb_comm x xi).
  exact l2.
Defined. (* END OF LEM2 *)
End Lem2.

Lemma UnivInst : forall (fi:Fo) (pi:SetVars.t->X) (x:SetVars.t) (t:Terms)
(r:Fo) (H:(substF t x fi)=Some r), @foI X fsI prI pi (Impl (Fora x fi) r).
Proof.
intros fi pi x t r H.
simpl.
intro H0.
apply (lem2 t fi x pi r H).
apply H0.
Defined.

Lemma ExisGene : forall (fi:Fo) (pi:SetVars.t->X) (x:SetVars.t) (t:Terms)
(r:Fo) (H:(substF t x fi)=Some r), @foI X fsI prI pi (Impl r (Exis x fi)).
Proof.
intros fi pi x t r H.
simpl.
intro H0.
exists (@teI X fsI pi t).
fold (cng pi x (@teI X fsI pi t)).
apply (lem2 t fi x pi r H).
apply H0.
Defined.

(* SOUNDNESS OF THE PREDICATE CALCULUS *)
Theorem soundness (f:Fo) (l:CTX) (m : PREPR l f) :
 forall (val:SetVars.t->X),
 (forall h:Fo, (l h) -> (@foI X fsI prI val h)) ->
  @foI X fsI prI val f.
Proof.
induction m; intros val lfi.
+ rename c into i.
  exact (lfi A i).
+ destruct p eqn:k.
  ++ destruct p0.
     * simpl.
       intros a0 b.
       exact a0.
     * simpl.
       intros a0 b c.
       exact (a0 c (b c)).
     * simpl. intros [i0 i1]. assumption.
     * simpl. intros [i0 i1]. assumption.
     * simpl. intros m1 m2. split; assumption.
     * simpl. intros n. left. assumption.
     * simpl. intros n. right. assumption.
     * simpl. intros f1 f2 [h|h]. exact (f1 h). exact (f2 h).
     * simpl. intros i0 i1. destruct (i0 i1).
     * simpl. intros i0 i1 i2. apply (i1 i2). apply (i0 i2).
  ++ simpl in *|-*.
     apply (UnivInst ph val xi t r s).
  ++ simpl in *|-*.
     apply (ExisGene ph val xi t r s).
  ++ simpl in *|-*.
     unfold OImp.
     intros H0 H1 m.
     apply H0.
     rewrite -> (NPthenNCACVF xi ps0 m val H).
     exact H1.
  ++ simpl in *|-*.
     unfold OImp.
     intros H0 [m H1].
     rewrite <- (NPthenNCACVF xi ps0 m val H).
     eapply H0.
     exact H1.
+ simpl in * |- *.
  unfold OImp in IHm2.
  apply IHm2.
  apply lfi.
  apply IHm1.
  apply lfi.
+ simpl in * |- *.
  intro m0.
  eapply IHm. (* IHm is a (soundness A l) *)
  intros h J.
  apply <- NPthenNCACVF.
  2 : { apply nic. exact J. }
  apply lfi. exact J.
Defined.

End cor.

(* ============ END OF THE TEXT ============ *)

(* Completeness theorem section *)
Section Completeness.
Theorem completeness (f:Fo) (l:CTX)
 (m : forall 
   (X:Type)
   (fsI:forall(q:FSV),(Vector.t X (fsv q))->X)
   (prI:forall(q:PSV),(Vector.t X (psv q))->Omega)
   (val:SetVars.t->X),
      (forall h:Fo, (l h) -> (@foI X fsI prI val h)) ->
      @foI X fsI prI val f)
 : PREPR l f.
Proof.
Admitted.
End Completeness.

(*Include replace_variable_with_itself.*)
Fixpoint replxixiF (xi:SetVars.t) A: substF xi xi A = Some A.
Proof.
Admitted.

(* Troelstra's "Hilbert calculus" section *)
Section Troelstra.
Context (X:Type).
Context (fsI:forall(q:FSV),(Vector.t X (fsv q))->X).
Context (prI:forall(q:PSV),(Vector.t X (psv q))->Omega).
Lemma fresh_variable
(A r : Fo)
(y x : SetVars.t)
(H1:isParamF y A = false)
(Hr : substF y x A = Some r)
(v : SetVars.t -> X):
@foI X fsI prI v A <-> @foI X fsI prI (cng v y (v x)) r.
Proof.
(*remember (SetVars.eqb x y) as c.
destruct c.*)
destruct (SetVars.eq_dec x y).
*
destruct e.
rewrite replxixiF in Hr.
apply SomeInj in Hr.
destruct Hr.
eapply weafunF.
intro z. unfold cng.
remember (SetVars.eqb z x) as c.
destruct c.
2 : reflexivity.
{ symmetry in Heqc.
  apply SetVars.eqb_eq in Heqc.
  destruct Heqc.
  reflexivity. }

*

split.
+ intro j.
  assert (Q:=lem2 X fsI prI y A x (cng v y (v x)) r Hr).
  apply Q. clear Q.
simpl.
rewrite -> (weafunF X fsI prI 
((cng (cng v y (v x)) x (cng v y (v x) y)))
v
).
exact j.
{ intro z.
unfold cng.
rewrite Facts.eqb_refl.
remember (SetVars.eqb z x) as u.
destruct u.
{ symmetry in Hequ.
  apply SetVars.eqb_eq in Hequ.
  destruct Hequ.
  reflexivity. }
remember (SetVars.eqb z y) as uu.
destruct uu.
2 : reflexivity.
(* weafunF is too strong!
 valuations should be the same at FV of the formula *)

(*
destruct SetVars.eqb z y
Check Facts.eqb_refl.
Check BoolEqualityFacts
 simpl.
reflexivity.

unshelve eapply lem2.
  Check lem2 X fsI prI y A x v r Hr.
*)

(*
induction A.
+ simpl in *|-*.
  apply SomeInj in Hr.
  rewrite <- Hr.
  simpl.
  apply EqualThenEquiv.
  apply f_equal.
*)

Admitted.

Definition Satisf val f := (@foI X fsI prI val f).
Definition SatisfC val l :=
(forall h:Fo, (l h) -> Satisf val h).
Definition Entails l f :=
 forall val, SatisfC val l -> Satisf val f.
Section thm.
Context (A D r:Fo) (y x:SetVars) (Gamma:CTX)
(Hr:substF y x A = Some r) (j:Entails (add2ctx r Gamma) D).
Context (H1:isParamF y A = false).
Context (H2:isParamF y D = false).
Context (H3:NotParamC y Gamma).
Theorem renam : Entails (add2ctx A Gamma) D.
Proof.
intros v H.
unfold Satisf.
(* pose(w:=(fun m : SetVars.t =>
 if SetVars.eqb m y then v x else v m)). *)
unshelve eapply NPthenNCACVF.
exact y.
exact (v x).
exact H2.
eapply j.
intros e Q.
destruct Q.
+ unfold Satisf.
destruct e0.
unfold SatisfC in H.
assert (Y:Satisf v A).
{ apply H. left. reflexivity. }
rewrite <- fresh_variable.
exact Y.
exact H1.
exact Hr.
+ unfold Satisf.
unshelve rewrite -> NPthenNCACVF.
apply H.
right.
exact g.
apply H3.
exact g.
Defined.
(* Check NPthenNCASF.
unfold Satisf in Y. *)
(*unshelve rewrite <- NPthenNCACVF in Y.
exact y.
exact (v x).*)

(* end *)

(*!
(* Check lem2 X fsI prI y A x v r Hr. *)
rewrite <- lem2 in Y.
pose (HA:=H A ).

- unfold 
(*unshelve eapply weafunF.
+ intro m.
  exact (if (SetVars.eqb m y) then (v x) else (v m)).
+*)
simpl in H.
Abort.
*)
End thm.
End Troelstra.




Lemma forall_swap A x y :
 PREPR empctx (Fora y (Fora x A) --> Fora y (Fora x A)).
Proof.
apply Ded.
apply GEN_E.
+ intros B [H1|H2].
  - rewrite <- H1.
    simpl.
    rewrite Facts.eqb_refl. trivial.
  - destruct H2.
+ apply GEN_E.
  - intros B [H1|H2].
    * rewrite <- H1.
      simpl.
      rewrite Facts.eqb_refl.
      destruct (SetVars.eqb y x); trivial.
    * destruct H2.
  - eapply MP_E.
    2 : { apply Hax_E.
          eapply (Ha12 A x x).
          apply replxixiF. }
  * eapply MP_E.
    2 : { apply Hax_E.
          eapply (Ha12 (Fora x A) y y).
          apply replxixiF. }
  apply hyp_E. left. trivial.
Defined.




(*** BEGIN EXPERIMENTAL ***)

Check PREPR. (*(NotParamC ctx)*)
Theorem extension A B r (x y:SetVars.t)
(ss : (substF y x A) = Some r)
(ww1 : isParamF y A = false)
(ww2 : isParamF x B = false)
: PREPR empctx ((Fora x (B --> A)) -->
   (B --> Fora y r)).
Proof.
apply Ded.
apply Ded.
Abort.

Lemma uio1 (x y:SetVars.t) A r
(ss : substF y x A = Some r)
(ww1 : isParamF y A = false) :
PREPR empctx ((Fora x A)-->(Fora y r)).
apply Ded.
destruct A.
+ simpl in *|-*.
  apply SomeInj in ss. (*!*)
(*!
eapply GEN_E.
+ intros fo H.
  simpl in H.
  destruct H.
  - destruct e. impossible
*)
    
simpl.
(*
destruct A eqn:b.
Gen

+ simpl in ss. apply SomeInj in ss.
eapply f_equal in ss.
*)
(*destruct (substF y x A) eqn:q.*)
Abort.
(*Check eqb_refl.
(*Import Facts.*)
Check Facts.eqb_refl.
SetVars.eqb_refl.
_refl.*)

Section notation.
(*Context ()*)
Inductive NTerms : Type :=
  | NFVC : SetVars.t -> NTerms
  | NFSC : forall f : FSV, t NTerms (fsv f) -> NTerms
.
Inductive NFo :=
 |NAtom (p:PSV) : (Vector.t NTerms (psv p)) -> NFo
 |NBot :NFo
 |NConj:NFo->NFo->NFo
 |NDisj:NFo->NFo->NFo
 |NImpl:NFo->NFo->NFo
 |NFora(x:SetVars.t)(f:NFo): NFo
 |NExis(x:SetVars.t)(f:NFo): NFo
.
End notation.
(*** END EXPERIMENTAL ***)

End ALL_mod.

(* Author: Georgy Dunaev, georgedunaev@gmail.com *)
Require Import Bool.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import Coq.Structures.Equalities.

(* Firstly I prove some lemmas, then the module "ALL_mod" contains
the soundness theorem of predicate logic.
*)

Lemma my_andb_true_eq :
  forall a b:bool, a && b = true -> a = true  /\ b = true.
Proof.
  destr_bool. auto.
Defined.

Notation Omega := Prop.
Definition OFalse := False.
Definition OAnd := and.
Definition OOr := or.
Definition OImp := (fun x y:Omega => x->y).

Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.
(*
Lemma orb_intro (a b:bool): ((a=false)/\(b=false))->((a||b)=false).
Proof.
intros. firstorder.
Defined.
orb_false_intro
*)
(*Import Bool.*)
(*
Lemma orb_elim (a b:bool): ((a||b)=false)->((a=false)/\(b=false)).
Proof.
intros. destruct a,b. 
simpl in H. inversion H.
simpl in H. inversion H.
firstorder.
firstorder.
Defined.
Check orb_false_elim.
*)

(** 4. ALL THEN SOME (VECTOR) **)
Import VectorNotations.

Fixpoint B2 (n:nat) (l:t bool n) :fold_left orb true l  = true.
Proof.
destruct l; simpl.
reflexivity.
apply B2.
Defined.

Fixpoint B0 b (n:nat) (l:t bool n) : 
fold_left orb false (b :: l)  = orb b (fold_left orb false l) .
Proof.
destruct l.
simpl. firstorder.
simpl.
destruct b.
simpl.
apply B2.
simpl.
reflexivity.
Defined.

Definition G h (n:nat) (l:Vector.t bool n) : Prop :=
 @eq bool (@fold_left bool bool orb false (S n) (cons bool h n l)) false.

(*Definition mIDProp : Prop := (forall A : Prop, A -> A).*)
(*Check False_ind (@IDProp).*)

Definition McaseS {A} (P : forall {n}, t A (S n) -> Prop)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with
  |h :: t => H h t
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

(*
Check McaseS.
Definition McaseSs {A} (P : forall {n}, t A (S n) -> Prop)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v.
induction v.
destruct v.
Check @IDProp.
Check False_ind.
*)
(* useless
Definition McaseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Prop)
  (H : forall h t, P (h :: t)), P v :=
  match v with
  | h :: t => fun P H => H h t
  | _ => fun devil => False_ind (@IDProp) devil
  end.
*)

Lemma vp1 (n:nat) (l : t bool (S n)) : exists (q:bool) (m:t bool n), l = (q::m).
Proof.
apply (@McaseS bool (fun n => 
fun (l : t bool (S n)) => exists (q : bool) (m : t bool n), l = q :: m)).
intros.
exists h.
exists t.
reflexivity.
Defined.

Theorem A1 (x y:bool): (orb x y = false)->(x=false)/\(y=false).
Proof. intro H. destruct x, y; firstorder || inversion H. Defined.

Fixpoint all_then_someV (n:nat) (l:Vector.t bool n) {struct l}:
(Vector.fold_left orb false l ) = false ->
(forall p, (Vector.nth l p  ) = false).
Proof.
intros.
(*induction*)
destruct l (*eqn:equa*).
inversion p. (* simpl. destruct p; trivial.*)
fold G in H.
assert (vari : G h n l).
exact H.
clear H.
revert h l vari.
set (P := fun n p => forall (h : bool) (l : t bool n) (_ : G h n l),
@eq bool (@nth bool (S n) (cons bool h n l) p) false).
revert n p.
fix loop 1.
intros n;revert n.
unshelve eapply (@Fin.rectS P).
unfold P.
intros.
simpl.
unfold G in H.
rewrite -> (B0 h n l) in H.
assert (Q:=A1 _ _ H).
destruct Q as [H0 H1].
exact H0.
(* OK!! *)
unfold P.
intros.
unfold G in H0.
simpl in  |- *.
rewrite -> (B0 h (S n) l) in H0.
assert (Q:=A1 _ _ H0).
destruct Q as [HH0 HH1].
assert (YO := vp1 n l).
destruct YO as [YO1 [YO2 YO3]].
rewrite -> YO3.
apply H.
unfold G.
rewrite <- YO3.
exact HH1.
Defined.

(** 5. MISC **)
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



(*Lemma orb_intro (a b:bool): ((a=false)/\(b=false))->((a||b)=false).
Proof.
intros. firstorder.
Defined.*)

(*lm2*)
(*Theorem conj_true_then_right (a b :bool)(G:true = (a && b) ): true = b.
Proof.
destruct a.
trivial.
inversion G.
Defined.*)
(* Lemmas END *)




Module ALL_mod (SetVars FuncSymb PredSymb 
 : UsualDecidableTypeFull).

(** Terms **)
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

(** 2. VALUATIONS **)

Section a.
Context {X:Type}.

Definition cng (val:SetVars.t -> X) (xi:SetVars.t) (m:X) :=
 (fun r:SetVars.t =>
 match SetVars.eqb r xi with
 | true => m
 | false => (val r)
 end).
(*
Lemma dbl_cng  pi xi m1 m2: forall q,(cng (cng pi xi m1) xi m2) q = (cng pi xi m2) q.
Proof. intro q. unfold cng. destruct (SetVars.eqb q xi); reflexivity. Defined.
*)

Lemma twice_the_same (pi:SetVars.t->X) x m0 m1 : 
forall u, (cng (cng pi x m0) x m1) u = (cng pi x m1) u.
Proof.
intro u.
unfold cng.
destruct (SetVars.eqb u x).
reflexivity.
reflexivity.
Defined.

End a.
 
(** FORMULAS **)

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
(*
 Notation " '(A.' x ')(' f ')' " :=(Fora x f) (at level 80) : pretxtnot.
 Notation " '(E.' x ')(' f ')' " :=(Exis x f) (at level 80) : pretxtnot.
*)
 Notation " -. x "   :=(Neg x) (at level 80) : pretxtnot.
 Delimit Scope pretxtnot with etd.
End PredFormulasNotationsASCII.

(* FFI *)
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

(** 3. PROVABILITY **)

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

| Hb1  : forall (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false)
(*(r:Fo) (s:(substF t xi ph)=Some r) (*D:sum ()*) *),
PRECA (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
| Hb2  : forall (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false),
PRECA (Impl (Fora xi (Impl ph ps)) (Impl (Exis xi ph) ps ) )
.

Section PREPR.
(*Context (axs : Fo -> Type).*)
Context (ctx:list Fo).
Inductive PREPR : Fo -> Type :=
| hyp_E (A : Fo): (InL A ctx)-> PREPR A
| Hax_E :> forall (A : Fo), (PRECA A) -> PREPR A
| MP_E (A B: Fo) : (PREPR A)->(PREPR (Impl A B))
                 ->(PREPR B)
| GEN_E (A: Fo) (xi :SetVars.t)
 (nic:forall A : Fo, (InL A ctx)-> (isParamF xi A = false))
 (*(side: sum (yi=xi) (isParamF yi A = false))*)
: (PREPR A)->(PREPR (Fora xi A))
(*| GEN_E (A r: Fo) (xi yi :SetVars.t) (s:(substF yi xi A)=Some r)
 (nic:forall A : Fo, (InL A ctx)-> (isParamF xi A = false))
 (side: sum (yi=xi) (isParamF yi A = false))
: (PREPR A)->(PREPR (Fora yi r))*)
.
(*Instance cMPe : (cMP PREPR) := MP_E.*)
End PREPR.
(* IT WORKS:
Definition a1 ctx A B : @PROPR ctx (Impl A (Impl B A)).
Proof. apply Hax_O.
(*
Check Ha1 A B : PROCA (A --> (B --> A)).
Check Ha1 A B : PRECA (A --> (B --> A)).
(*Check (Ha1 A B: PRECA (A --> (B --> A))) : @PR axi (A --> (B --> A)).*)
*)
refine (Ha1 _ _). Defined.
*)
Definition a1 ctx A B : @PREPR ctx (Impl A (Impl B A)).
Proof. apply Hax_E.
refine (Ha1 _ _). 
Defined.

Definition a2 axi A B C : @PREPR axi ((A-->(B-->C))-->((A-->B)-->(A-->C))).
Proof. apply Hax_E, PRO, Ha2. Defined.
Definition b1 axi (ps ph: Fo) (xi:SetVars.t) (H:isParamF xi ps = false):
@PREPR axi (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) ).
Proof. apply Hax_E, Hb1, H. Defined.

(* IT WORKS:
Theorem subcalc {ctx} (A:Fo) : PROPR ctx A -> PREPR ctx A.
Proof.
intro p.
try apply PRO.
induction p.
apply hyp_E, i.
apply Hax_E, PRO, p.
apply @MP_E with (A:=A).
(* unfold cMP. exact (MP_E ctx). intros. *)
apply IHp1. apply IHp2.
Defined.

Coercion subcalc : PROPR >-> PREPR.
*)

(*Arguments GPR {axs}.*)
(*Notation newMP := (MP (1:=I)).*)
(* IT WORKS:
Definition AtoA {ctx} (A:Fo) : PROPR ctx (A-->A).
Proof.
apply MP_O with (A:=(A-->(A-->A))).  (*(MP ctx (A-->(A-->A)) _).*)
apply Hax_O, Ha1. (* apply (Hax _ _ (Ha1 _ _)).*)
apply MP_O with (A:= A-->((A-->A)-->A)).
apply Hax_O, Ha1.
apply Hax_O, Ha2.
Defined.
*)

(* IT WORKS:
Definition a12 axi ph t xi : @PREPR axi (match (substF t xi ph) with 
      | Some q => (Impl (Fora xi ph) q)
      | None => Top
      end).
Proof. induction (substF t xi ph) eqn:g. eapply Hax_E, Ha12, g.
unfold Top.
exact (AtoA  Bot).
Defined.
*)

Definition AtoA {ctx} (A:Fo) : PREPR ctx (A-->A).
Proof.
apply MP_E with (A:=(A-->(A-->A))).  (*(MP ctx (A-->(A-->A)) _).*)
apply Hax_E, PRO, Ha1. (* apply (Hax _ _ (Ha1 _ _)).*)
apply MP_E with (A:= A-->((A-->A)-->A)).
apply Hax_E, PRO, Ha1.
apply Hax_E, PRO, Ha2.
Defined.

Notation SetVars := SetVars.t (only parsing).
Notation FuncSymb := FuncSymb.t (only parsing).
Notation PredSymb := PredSymb.t (only parsing).

Module Facts := BoolEqualityFacts SetVars.


Lemma yui (xi sv:SetVars.t) : (if SetVars.eqb sv xi then xi else sv) = sv.
Proof.
remember (SetVars.eqb sv xi) as w eqn:t.
destruct w.
+ symmetry in t.
  apply SetVars.eqb_eq in t.
  symmetry. exact t.
+ reflexivity.
Defined.

Lemma yui2 (xi sv:SetVars.t) : substT xi xi sv = sv.
Proof.
remember (SetVars.eqb sv xi) as w eqn:t.
destruct w.
+ symmetry in t.
  apply SetVars.eqb_eq in t.
simpl.
assert (t2:=t).
rewrite <- SetVars.eqb_eq in t2.
rewrite t2.
rewrite t.
reflexivity.
(*rewrite (yui sv xi).
simpl.
  symmetry. exact t.*)
+ simpl. rewrite <- t.
 reflexivity.
Defined.

(* "@eq Terms (if SetVars.eqb sv xi then FVC xi else FVC sv)
    (FVC sv)"*)

Theorem replxixiT (xi:SetVars.t) (q:Terms)
 : (substT xi xi) q = q.
Proof.
apply (Terms_ind (fun q=>substT xi xi q = q)).
+ simpl.
  apply (yui2 xi).
+ simpl.
  intros.
  apply f_equal.
  apply eq_nth_iff.
  intros p1 _ [].
  rewrite (nth_map (substT xi xi) v p1 p1 eq_refl).
  apply H.
Defined.

Theorem replxixiT_vec (xi:SetVars.t) n (v : Vector.t Terms n)
 : Vector.map (substT xi xi) v = v.
Proof.
 apply eq_nth_iff.
 intros p1 _ [].
 rewrite (nth_map (substT xi xi) v p1 p1 eq_refl).
 apply replxixiT.
Defined.
(*
induction w.
2 : {
simpl.
reflexivity.
  destruct w eqn:b.
simpl.
*)
Module Y:= (BoolEqualityFacts SetVars). (*for eqb_sym*)
Import Y.
Fixpoint replxixiF (xi:SetVars.t) A: substF xi xi A = Some A.
Proof.
induction A; simpl.
+ repeat apply f_equal.
  apply replxixiT_vec.
+ trivial.
+ rewrite -> IHA1.
  rewrite -> IHA2.
  trivial.
+ rewrite -> IHA1.
  rewrite -> IHA2.
  trivial.
+ rewrite -> IHA1.
  rewrite -> IHA2.
  trivial.
+ rewrite -> IHA.
  destruct (SetVars.eqb x xi) eqn:h.
  - trivial.
  - rewrite eqb_sym.
    rewrite h.
    destruct (isParamF xi A); reflexivity.
+ rewrite -> IHA.
  destruct (SetVars.eqb x xi) eqn:h.
  - trivial.
  - rewrite eqb_sym.
    rewrite h.
    destruct (isParamF xi A); reflexivity.
Defined.

(* TODO
Definition B1 (ps ph:Fo) (xi:SetVars) (H:isParamF xi ps = false): 
 PREPR nil (ps --> ph) -> PREPR nil (ps --> Fora xi ph).
Proof.
intro q.
apply MP_E with (A:=(Fora xi (ps --> ph))).
(*apply (MP_E nil (Fora xi (ps --> ph))).*)
+ eapply (GEN_E).
  - reflexivity. 
  - intros A [].
  - exact q.
+ apply (b1 _).
  exact H.
Defined.
*)

(* OBSOLETE
Definition gen (A:Fo) (xi:SetVars) ctx
(*Generalization from Bernay's rule*)
: PREPR ctx (A) -> PREPR ctx (Fora xi A).
Proof.
intro q.
apply MP_E with (A:= Top).
unfold Top.
(*fold PREPR.*)
exact (@AtoA ctx Bot).
apply MP_E with (A:= (Fora xi (Top --> A))).
* apply GEN_E.
  apply MP_E with (A:= A).
  + exact q.
  + apply a1. (*apply subcalc, a1.*)
* apply b1.
  trivial.
Defined.
*)

Definition neg (f:Fo):= (Impl f Bot).

Definition a1i (A B : Fo)(l : list Fo):(PREPR l B)->(PREPR l (Impl A B)).
Proof.
intros x.
apply MP_E with (A:= B).
exact x.
apply (*subcalc,*) a1.
Defined.
(*TODO
Fixpoint weak (A F:Fo) (l :list Fo) (x: (PREPR l F)) : (PREPR (A::l) F).
Proof.
destruct x as [a b|a b|i a b|a b].
+ apply hyp_E.
  right. (* apply inr. or_intror *)
  exact b.
+ apply Hax_E,b.
(*apply a1.
apply a2.
apply a12.
apply b1.
assumption. *)
+ apply MP_E with (A:= i).
  * apply weak.
    exact b.
  * apply weak.
    exact x1.
+ apply GEN_E. (* Order is not important! *)
  - intros F IL.
    destruct IL as [C1|C2].
  apply weak. (* Order is not important! *)
  exact x.
Defined.
*)
(*Fixpoint weak (A F : Fo) (l : list Fo) (x : PREPR l F) {struct x} :
   PREPR (A :: l) F :=
   match x in (GPR _ _ _ f) return (PREPR (A :: l) f) with
   | hyp _ _ _ a b => hyp dcb PRECA (A :: l) a (inr b)
   | Hax _ _ _ a b => Hax dcb PRECA (A :: l) a b
   | MP_E _ _ _ _ a b x1 x2 =>
       MP_E dcb PRECA (A :: l) I a b (weak A a l x1) (weak A (a --> b) l x2)
   | GEN_E _ _ _ _ a b x0 => GEN_E dcb PRECA (A :: l) I a b (weak A a l x0)
   end.*)
(*TODO
Fixpoint weaken (F:Fo) (li l :list Fo) (x: (PREPR l F)) {struct li}: (PREPR (li ++ l) F).
Proof.
destruct li.
simpl.
exact x.
simpl.
simple refine (@weak f F (li ++ l) _).
apply weaken.
exact x.
(*Show Proof.*)
Abort.

Fixpoint weaken (F : Fo) (li l : list Fo) (x : PREPR l F) {struct li} :
   PREPR (li ++ l) F :=
   match li as l0 return (PREPR (l0 ++ l) F) with
   | Datatypes.nil => x
   | f :: li0 => weak f F (li0 ++ l) (weaken F li0 l x)
   end.
*)
(*Export List Notations.*)
Fixpoint notGenWith (xi:SetVars)(l:list Fo)
(B:Fo)(m:(PREPR l B)){struct m}:bool.
Proof.
(*induction m.  eqn: o.*)
destruct m  eqn: o.
(*Show Proof.*)
exact true.
destruct p eqn:j.
exact true.
exact true.
exact true.
exact true.
exact true.
(*exact (andb IHm1 IHm2).
exact (andb (negb (SetVars.eqb xi xi0)) IHm).*)
exact (andb (notGenWith xi l _ p1) (notGenWith xi l _ p2)).
exact (andb (negb (SetVars.eqb xi xi0)) (notGenWith xi l _ p) ). 
Defined.

(*Fixpoint HA xi : true = PeanoNat.Nat.eqb (xi) (xi).
Proof.
destruct xi.
reflexivity.
simpl.
exact (HA xi).
Defined.*)
Import Bool.Bool.
Export Coq.Lists.List.

(*
Theorem lm (a b :bool)(G:true = (a && b) ): true = a.
Proof.
destruct a.
trivial.
inversion G.
Defined.

Theorem conj_true_then_right (a b :bool)(G:true = (a && b) ): true = b.
Proof.
destruct a.
trivial.
inversion G.
Defined.
*)
Fixpoint Ded (A B:Fo)(il:list Fo)(m:(PREPR (cons  A il) B)) 
(H:forall xi:SetVars, (isParamF xi A = true) ->(notGenWith xi _ _ m = true))
{struct m}:(PREPR il (A-->B)).
Proof.
destruct m. (*as [i|i|i|i|i|i|i].*)
+ unfold In in i.
  simpl in i .
  destruct i .
  * rewrite <- e.
    exact (AtoA A).
  * simpl in H.
    apply a1i.
    apply hyp_E with (ctx:=il) (1:=i).
+ apply a1i.
  apply Hax_E, p.
+ apply MP_E with (A:= (A-->A0)).
- simple refine (@Ded _ _ _ _ _).
  exact m1.
  intros xi H0.
  assert (W:=H xi H0).
  simpl in W.
  assert (J:=notGenWith xi (A :: il) A0 m1).
  try reflexivity.
(*  fold J. 
  fold J in W. *)
  apply my_andb_true_eq in W as [W _].
  exact W.
  (*apply (lm _ _ W).*)
- apply MP_E with (A:= (A-->(A0-->B))).
  simple refine (@Ded _ _ _ _ _).
  exact m2.
  intros xi H0.
  assert (W:=H xi H0).
  simpl in W.
  apply my_andb_true_eq in W as [_ W].
  exact W.
  (* apply (conj_true_then_right _ _ W). *)
 (*Last part about GEN*)
  apply a2.
+ apply MP_E with (A:= (Fora xi (A-->A0))).
    eapply GEN_E.

(*{ instantiate (2 := yi).
  instantiate (1 := A-->A0).
  destruct side.
  - rewrite -> e.
    simpl.
    repeat rewrite -> replxixiF.
    reflexivity.
  -
    admit.
}*)
(*    { intros A1 M.
destruct side.
- rewrite e.
 eapply (nic A1). 
simpl. right. exact M. 
- admit.
} *)
{ intros A1 M. apply nic. right. exact M. }
(*{ admit. }*)
    simple refine (@Ded _ _ _ _ _).
    exact m.
    intros xi0 H0.
    assert (W:=H xi0 H0).
    simpl in W.
    * apply my_andb_true_eq in W as [_ W]; exact W.
(*exact (conj_true_then_right _ _ W).*)
    * 
     simpl.
(*
{ destruct side as [q1|q2].
Fail rewrite q1 in s |- *.
admit. 
*)

eapply Hax_E.
eapply Hb1.
apply nic. left. trivial.
Defined.
(*
      apply b1.
*)
(*
      pose (r := isParamF xi A).
      pose (U := H xi).
      fold r in U |- *.
      simpl in U.
      destruct (bool_eq_true_or_false r).
      - pose (C:= lm _ _(U H0)).
        exfalso.
        rewrite Facts.eqb_refl in C.
        inversion C.
      - exact H0.
*)
(*Defined.*)

(* USELESS
Definition lm3 (a b :bool)(A: true = a)(B: true = b):true = (a && b) 
:=
 (if a as a0 return (true = a0 -> true = a0 && b)
  then
   fun _ : true = true =>
   (if b as b0 return (true = b0 -> true = true && b0)
    then fun _ : true = true => eq_refl
    else fun B0 : true = false => B0) B
  else
   fun A0 : true = false =>
   (if b as b0 return (true = b0 -> true = false && b0)
    then fun _ : true = true => A0
    else fun _ : true = false => A0) B) A.
(*destruct a,b.
reflexivity.
simpl.
exact B.
simpl.
exact A.
simpl.
exact A.
Show Proof.
Defined.*)
*)

Fixpoint forClosed (A B:Fo)(m:(PREPR (cons A nil) B)):
(forall xi:SetVars, (false = isParamF xi A))
->
(forall xi:SetVars, (true = isParamF xi A)->(true=notGenWith xi _ _ m)).
Proof.
intros H xi Q.
rewrite <- H in Q.
inversion Q.
(*unfold notGenWith.
simpl.
destruct m. simpl. try reflexivity.
destruct p eqn:j.
simpl. try reflexivity.
simpl. try reflexivity.
simpl. try reflexivity.
simpl. try reflexivity.
simpl. try reflexivity.
+ apply lm3.
  simple refine (@forClosed _ _ _ _ _ _); assumption.
  simple refine (@forClosed _ _ _ _ _ _); assumption.
+ apply lm3.
  2 : simple refine (@forClosed _ _ _ _ _ _); assumption.
  pose (U:=H xi).
  rewrite <- Q in U.
  exfalso.
  inversion U.*)
Defined.

Fixpoint SimplDed (A B:Fo) (il: list Fo)(m:(PREPR (cons A il) B))
(NP:forall xi:SetVars, (isParamF xi A = false)) 
{struct m}:(PREPR il (A-->B)).
Proof.
(*unshelve eapply Ded.*)
simple refine (Ded _ _ _ _ _).
exact m.
intros xi H.
rewrite -> NP in H.
inversion H.
Defined.



(* Examples of *)
Definition swapSIMPL ctx A B C
(HA : forall xi : SetVars.t, isParamF xi A = false)
(HB : forall xi : SetVars.t, isParamF xi B = false)
(HC : forall xi : SetVars.t, isParamF xi C = false) :
(PREPR ctx ((A --> (B --> C)) --> (B --> (A --> C)) )).
Proof.
unshelve eapply SimplDed.
2 : { intro xi. simpl.
apply orb_false_intro. apply HA.
apply orb_false_intro. apply HB. apply HC.
}
unshelve eapply SimplDed. 2 : apply HB.
unshelve eapply SimplDed. 2 : apply HA.
apply MP_E with (A:=B) . apply hyp_E.
simpl. firstorder. (*apply inr.*)
apply MP_E with (A:=A) .
apply hyp_E; firstorder.
apply hyp_E; firstorder.
Defined.

(* It is also true:
Definition swap ctx A B C :
(PREPR ctx ((A --> (B --> C)) --> (B --> (A --> C)) )).
Proof.
unshelve eapply SimplDed.
Admitted.
*)

(** 6. SOUNDNESS **)
(** Soundness theorem section **)
Section cor.
Context (X:Type).
Context (fsI:forall(q:FSV),(Vector.t X (fsv q))->X).
Context (prI:forall(q:PSV),(Vector.t X (psv q))->Omega).

Section Lem1.
Definition ap {A B}{a0 a1:A} (f:A->B) (h:a0=a1):((f a0)=(f a1))
:= match h in (_ = y) return (f a0 = f y) with
   | eq_refl => eq_refl
   end.

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
destruct mu eqn:u0.
* intros xi t0 H.
  simpl.
  rewrite -> NPthenNCAST_vec; (trivial || assumption).
* intros xi t H.
  simpl; trivial.
* intros xi t H.
  simpl.
  simpl in H.
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF .
  rewrite -> NPthenNCASF .
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF.
  rewrite -> NPthenNCASF.
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF.
  rewrite -> NPthenNCASF.
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (SetVars.eqb x xi) eqn:u2.
  trivial.
  destruct (isParamF xi f) eqn:u1.
  inversion H.
  trivial.
* simpl.
  intros xi t H.
  destruct (SetVars.eqb x xi) eqn:u2.
  trivial.
  destruct (isParamF xi f) eqn:u1.
  inversion H.
  trivial.
Defined.

(* p.137 *)
Section Lem2.
(*
Lemma mqd x t pi m (H:isParamT x t = false): 
(@teI X fsI (cng pi x m) t) = (@teI X fsI pi t).
Proof.
induction t.
simpl.
simpl in H.
unfold cng.
rewrite -> H.
reflexivity.
simpl.
simpl in H.
apply ap.
apply eq_nth_iff.
intros.
rewrite -> (nth_map (teI (cng pi x m)) v p1 p1 eq_refl).
rewrite -> (nth_map (teI pi) v p2 p2 eq_refl).
rewrite <- H1.
apply H0.
exact (all_then_someP _ _ p1 _ (isParamT x) H).
Defined.*)
(*
(* USELESS THEOREM *)
Lemma cng_commT  x xi m0 m1 pi t :
SetVars.eqb x xi = false -> 
@teI X fsI (cng (cng pi x m0) xi m1) t = @teI X fsI (cng (cng pi xi m1) x m0) t.
Proof. intro i.
revert pi.
induction t; intro pi.
simpl.
unfold cng.
pose (n3:= proj1 (not_iff_compat (SetVars.eqb_eq x xi)) ).
pose (n4:= n3 (proj2 (not_true_iff_false (SetVars.eqb x xi)) i)).
destruct (SetVars.eq_dec sv xi).
rewrite -> e.
rewrite -> (Facts.eqb_refl xi).
destruct (SetVars.eq_dec x xi).
destruct (n4 e0).
pose (hi := (not_eq_sym n)).
pose (ih:= not_true_is_false _ (proj2 (not_iff_compat (SetVars.eqb_eq xi x)) hi)).
rewrite ih.
reflexivity.
pose (ih:= not_true_is_false _ (proj2 (not_iff_compat (SetVars.eqb_eq sv xi)) n)).
rewrite -> ih.
reflexivity.
simpl.
apply ap.
apply eq_nth_iff.
intros p1 p2 HU.
rewrite -> (nth_map (teI (cng (cng pi x m0) xi m1)) v p1 p2 HU).
rewrite -> (nth_map (teI (cng (cng pi xi m1) x m0)) v p2 p2 eq_refl).
apply H.
Defined.
*)
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

Lemma EqualThenEquiv A B: A=B -> (A<->B). 
Proof. intro H. rewrite H. exact (iff_refl B). Defined.

Lemma weafunF (pi mu:SetVars.t->X) (q: forall z, pi z = mu z) fi
: @foI X fsI prI pi fi <-> @foI X fsI prI mu fi.
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
  apply H0. (*twice*)
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

Theorem SomeInj {foo} :forall (a b : foo), Some a = Some b -> a = b.
Proof.
  intros a b H.
  inversion H.
  reflexivity.
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

Lemma NPthenNCACVT x t m pi: 
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

Lemma eqb_comm x xi : SetVars.eqb xi x =  SetVars.eqb x xi.
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

Lemma NPthenNCACVF xi fi m mu :  isParamF xi fi = false ->
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
  pose (D:= twice_the_same mu x m m0).
  exact (weafunF _ _ D fi).
  rewrite cng_commF_EQV.
  (*here inductive IHfi*)
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
  assert (D:= twice_the_same mu x m m0).
  exact (weafunF _ _ D fi).
  rewrite cng_commF_EQV.
  (*here inductive IHfi*)
  apply IHfi.
  exact H.
  rewrite <-(eqb_comm xi x).
  exact e1.
Defined.

Definition lem2 (t : Terms) : forall (fi : Fo) (xi : SetVars.t) 
(pi : SetVars.t->X)
(r:Fo) (H:(substF t xi fi) = Some r), (*(SH:sig (fun(r:Fo)=>(substF t xi fi) = Some r)),*)
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
  pose (Q:=SomeInj _ _ H).
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
  pose (Q:=SomeInj _ _ H).
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
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl in * |- *.
  apply IMP_EQV.
  * apply (IHfi1 pi f1 eq_refl).
  * apply (IHfi2 pi f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in * |- *.
  destruct (SetVars.eqb x xi) eqn:l2.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  apply FORALL_EQV.
  intro m.
  assert (RA : x = xi).
  apply (SetVars.eqb_eq x xi ).
  exact l2.
  rewrite <- RA.
  rewrite -> (weafunF (cng (cng pi x (teI pi t)) x m) (cng pi x m) 
   (twice_the_same pi x (teI pi t) m) fi).
  firstorder.
  destruct (isParamF xi fi) eqn:l1.
  pose(xint := (isParamT x t)).
  destruct (isParamT x t) eqn:l3.
  inversion H.
  destruct (substF t xi fi) eqn:l4.
  pose (Q:=SomeInj _ _ H).
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
   (twice_the_same pi x (@teI X fsI pi t) m) fi).
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

(* PROOF OF THE (WRONG!) SOUNDNESS *)
Theorem correct (f:Fo) (l:list Fo) (m : PREPR l f) 
(lfi : forall  (h:Fo), (InL h l)-> forall (val:SetVars.t->X), 
(@foI X fsI prI val h)) : 
forall (val:SetVars.t->X), @foI X fsI prI val f.
Proof.
revert lfi.
induction m (* eqn: meq *); intros lfi val.
+ exact (lfi A i _).
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
  (*destruct (substF t xi ph) eqn: j.*)
  apply (UnivInst ph val xi t r s).
  ++ simpl in *|-*.
  (*destruct (substF t xi ph) eqn: j.*)
  apply (ExisGene ph val xi t r s).
  (*simpl. firstorder.*)
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
  apply lfi. (*  exact (IHm2 IHm1).*)
+ simpl in * |- *.
  intro m0.
  apply IHm.
  intros h B.
  intro val2.
  apply lfi.
  exact B.
Defined.


(* SOUNDNESS OF THE PREDICATE CALCULUS *)
Fixpoint strong_correct (f:Fo) (l:list Fo) (m : PREPR l f) 
(val:SetVars.t->X)
(lfi : forall  (h:Fo), (InL h l)->
(@foI X fsI prI val h)) {struct m}: @foI X fsI prI val f.
Proof.
revert lfi.
induction m (* eqn: meq *); intros lfi (*val*).
+ exact (lfi A i).
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
  (*destruct (substF t xi ph) eqn: j.*)
  apply (UnivInst ph val xi t r s).
  ++ simpl in *|-*.
  (*destruct (substF t xi ph) eqn: j.*)
  apply (ExisGene ph val xi t r s).
  (*simpl. firstorder.*)
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
  apply lfi. (*  exact (IHm2 IHm1).*)
+ simpl in * |- *.
  intro m0.
eapply strong_correct.
exact m.
intros h J.
apply <- NPthenNCACVF.
2 : { apply nic. exact J. }
apply lfi. exact J.
Defined.

(*(* simpl. *)
apply <- NPthenNCACVF.
  apply IHm.
(*  intros h B.
  intro val2.*)
  apply lfi.
induction m eqn:b.
- apply nic. exact i.
- induction p.
  * induction p; simpl in *|-*.
Abort.*)

(** SOUNDNESS IS PROVED **)
Section test.
Context (x y z w:SetVars.t).
Context (NEps:PredSymb.t). (* not equal sign*)
Definition NE := MPSV NEps 2. (* valence = 2 *)
Import VectorNotations.
Check Terms.
Definition zw : t Terms (psv NE) :=[FVC z;FVC w].
Definition xx : t Terms (psv NE) :=[FVC x;FVC x].
Import ListNotations.
Theorem BAD : PREPR [Exis z (Exis w (Atom NE zw))]
(Fora x (Atom NE xx)).
Proof.
apply GEN_E.
Print PREPR.
Print PRECA.
(*???*)
Abort.
End test.
(*PSV
Theorem completeness (f:Fo)
(H : forall (val:SetVars.t->X), @foI X fsI prI val f)
 : 
exists  (l:list Fo)
(lfi : forall  (h:Fo), (InL h l)-> forall (val:SetVars.t->X), 
(@foI X fsI prI val h)), PREPR l f
.
Proof.
Defined. *)
End cor.


End ALL_mod.

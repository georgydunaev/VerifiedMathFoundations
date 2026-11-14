(* ========================================================================= *)
(* Sequent.v -- Gentzen's Sequent Calculus (LK and LJ) for Propositional    *)
(* Logic, Invertible Rules, Semantic Soundness, and Hilbert Bridge Theorems *)
(*                                                                           *)
(* Part of VerifiedMathFoundations. Integrates with PropLang.v.             *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Structures.Equalities.
Require Import Logic.Classical_Prop.

Require Import PropLang.
Export ListNotations.

Module Sequent_mod (PropVars : UsualDecidableTypeFull).
  Module XLang := Lang PropVars.
  Import XLang.

  Open Scope protxtnot.

  (** =====================================================================
      1. Sequent Data Type and Structural Permutations
      ===================================================================== *)

  Definition Sequent : Type := (list Fo * list Fo)%type.

  (** Basic lemmas on membership and permutation *)
  Lemma in_perm_head : forall (A : Fo) (l : list Fo),
    In A l -> exists l', Permutation l (A :: l').
  Proof.
    intros A l Hin.
    apply in_split in Hin as [l1 [l2 Heq]].
    subst l.
    exists (l1 ++ l2).
    apply Permutation_sym.
    apply Permutation_middle.
  Qed.

  Lemma perm_in : forall (A : Fo) (l1 l2 : list Fo),
    Permutation l1 l2 -> In A l1 -> In A l2.
  Proof.
    intros A l1 l2 Hperm Hin.
    eapply Permutation_in; eassumption.
  Qed.

  (** =====================================================================
      2. Classical Sequent Calculus LK (Cut-Free)
      ===================================================================== *)

  Inductive LK : list Fo -> list Fo -> Type :=
  (** Identity and False on the left *)
  | LK_Ax : forall (Gamma Delta : list Fo) (A : Fo),
      LK (A :: Gamma) (A :: Delta)
  | LK_L_Bot : forall (Gamma Delta : list Fo),
      LK (Bot :: Gamma) Delta

  (** Structural rules: Weakening *)
  | LK_Weak_L : forall (Gamma Delta : list Fo) (A : Fo),
      LK Gamma Delta -> LK (A :: Gamma) Delta
  | LK_Weak_R : forall (Gamma Delta : list Fo) (A : Fo),
      LK Gamma Delta -> LK Gamma (A :: Delta)

  (** Structural rules: Contraction *)
  | LK_Contr_L : forall (Gamma Delta : list Fo) (A : Fo),
      LK (A :: A :: Gamma) Delta -> LK (A :: Gamma) Delta
  | LK_Contr_R : forall (Gamma Delta : list Fo) (A : Fo),
      LK Gamma (A :: A :: Delta) -> LK Gamma (A :: Delta)

  (** Structural rules: Exchange / Permutation *)
  | LK_Perm_L : forall (Gamma Gamma' Delta : list Fo),
      Permutation Gamma Gamma' -> LK Gamma Delta -> LK Gamma' Delta
  | LK_Perm_R : forall (Gamma Delta Delta' : list Fo),
      Permutation Delta Delta' -> LK Gamma Delta -> LK Gamma Delta'

  (** Logical introduction rules: Conjunction *)
  | LK_L_Conj : forall (Gamma Delta : list Fo) (A B : Fo),
      LK (A :: B :: Gamma) Delta -> LK (Conj A B :: Gamma) Delta
  | LK_R_Conj : forall (Gamma Delta : list Fo) (A B : Fo),
      LK Gamma (A :: Delta) -> LK Gamma (B :: Delta) -> LK Gamma (Conj A B :: Delta)

  (** Logical introduction rules: Disjunction *)
  | LK_L_Disj : forall (Gamma Delta : list Fo) (A B : Fo),
      LK (A :: Gamma) Delta -> LK (B :: Gamma) Delta -> LK (Disj A B :: Gamma) Delta
  | LK_R_Disj : forall (Gamma Delta : list Fo) (A B : Fo),
      LK Gamma (A :: B :: Delta) -> LK Gamma (Disj A B :: Delta)

  (** Logical introduction rules: Implication *)
  | LK_L_Impl : forall (Gamma Delta : list Fo) (A B : Fo),
      LK Gamma (A :: Delta) -> LK (B :: Gamma) Delta -> LK (Impl A B :: Gamma) Delta
  | LK_R_Impl : forall (Gamma Delta : list Fo) (A B : Fo),
      LK (A :: Gamma) (B :: Delta) -> LK Gamma (Impl A B :: Delta)
  .

  (** Derived exchange rules: adjacent swap *)
  Lemma LK_Swap_L : forall (Gamma Delta : list Fo) (A B : Fo),
    LK (A :: B :: Gamma) Delta -> LK (B :: A :: Gamma) Delta.
  Proof.
    intros Gamma Delta A B H.
    eapply LK_Perm_L.
    - apply perm_swap.
    - exact H.
  Defined.

  Lemma LK_Swap_R : forall (Gamma Delta : list Fo) (A B : Fo),
    LK Gamma (A :: B :: Delta) -> LK Gamma (B :: A :: Delta).
  Proof.
    intros Gamma Delta A B H.
    eapply LK_Perm_R.
    - apply perm_swap.
    - exact H.
  Defined.

  (** Derived negation introduction rules *)
  Lemma LK_L_Neg : forall (Gamma Delta : list Fo) (A : Fo),
    LK Gamma (A :: Delta) -> LK ((-. A) :: Gamma) Delta.
  Proof.
    intros Gamma Delta A H.
    unfold Neg.
    apply LK_L_Impl.
    - exact H.
    - apply LK_L_Bot.
  Defined.

  Lemma LK_R_Neg : forall (Gamma Delta : list Fo) (A : Fo),
    LK (A :: Gamma) Delta -> LK Gamma ((-. A) :: Delta).
  Proof.
    intros Gamma Delta A H.
    unfold Neg.
    apply LK_R_Impl.
    apply LK_Weak_R.
    exact H.
  Defined.

  (** InL permutation lemma in Type *)
  Lemma inL_perm_head : forall (A : Fo) (l : list Fo),
    InL A l -> sig (fun l' => Permutation l (A :: l')).
  Proof.
    intros A l.
    induction l as [| b m IH].
    - intros [].
    - intros [Heq | Htail].
      + subst b. exists m. apply Permutation_refl.
      + destruct (IH Htail) as [m' Hperm].
        exists (b :: m').
        eapply Permutation_trans with (l' := b :: A :: m').
        * apply Permutation_cons; [reflexivity | exact Hperm].
        * apply perm_swap.
  Defined.

  (** Identity rule for general InL membership *)
  Lemma LK_Ax_In : forall (Gamma Delta : list Fo) (A : Fo),
    InL A Gamma -> InL A Delta -> LK Gamma Delta.
  Proof.
    intros Gamma Delta A HinG HinD.
    destruct (inL_perm_head A Gamma HinG) as [Gamma' HpG].
    destruct (inL_perm_head A Delta HinD) as [Delta' HpD].
    eapply LK_Perm_L.
    - apply Permutation_sym. exact HpG.
    - eapply LK_Perm_R.
      + apply Permutation_sym. exact HpD.
      + apply LK_Ax.
  Defined.

  (** =====================================================================
      3. Intuitionistic Sequent Calculus LJ (Single-Succedent Restriction)
      ===================================================================== *)

  Inductive LJ : list Fo -> list Fo -> Type :=
  | LJ_Ax : forall (Gamma : list Fo) (A : Fo),
      LJ (A :: Gamma) [A]
  | LJ_L_Bot : forall (Gamma Delta : list Fo),
      length Delta <= 1 -> LJ (Bot :: Gamma) Delta

  | LJ_Weak_L : forall (Gamma Delta : list Fo) (A : Fo),
      LJ Gamma Delta -> LJ (A :: Gamma) Delta
  | LJ_Contr_L : forall (Gamma Delta : list Fo) (A : Fo),
      LJ (A :: A :: Gamma) Delta -> LJ (A :: Gamma) Delta
  | LJ_Perm_L : forall (Gamma Gamma' Delta : list Fo),
      Permutation Gamma Gamma' -> LJ Gamma Delta -> LJ Gamma' Delta

  | LJ_L_Conj : forall (Gamma Delta : list Fo) (A B : Fo),
      LJ (A :: B :: Gamma) Delta -> LJ (Conj A B :: Gamma) Delta
  | LJ_R_Conj : forall (Gamma : list Fo) (A B : Fo),
      LJ Gamma [A] -> LJ Gamma [B] -> LJ Gamma [Conj A B]

  | LJ_L_Disj : forall (Gamma Delta : list Fo) (A B : Fo),
      LJ (A :: Gamma) Delta -> LJ (B :: Gamma) Delta -> LJ (Disj A B :: Gamma) Delta
  | LJ_R_Disj1 : forall (Gamma : list Fo) (A B : Fo),
      LJ Gamma [A] -> LJ Gamma [Disj A B]
  | LJ_R_Disj2 : forall (Gamma : list Fo) (A B : Fo),
      LJ Gamma [B] -> LJ Gamma [Disj A B]

  | LJ_L_Impl : forall (Gamma Delta : list Fo) (A B : Fo),
      LJ Gamma [A] -> LJ (B :: Gamma) Delta -> LJ (Impl A B :: Gamma) Delta
  | LJ_R_Impl : forall (Gamma : list Fo) (A B : Fo),
      LJ (A :: Gamma) [B] -> LJ Gamma [Impl A B]
  .

  (** Right weakening by a list *)
  Lemma LK_weaken_R_list : forall (Delta Gamma : list Fo) (A : Fo),
    LK Gamma [A] -> LK Gamma (A :: Delta).
  Proof.
    induction Delta as [| d Delta' IHd].
    - intros Gamma A H. exact H.
    - intros Gamma A H.
      apply LK_Swap_R.
      apply LK_Weak_R.
      apply IHd.
      exact H.
  Defined.

  (** Embedding of LJ into LK *)
  Theorem lj_to_lk : forall (Gamma Delta : list Fo),
    LJ Gamma Delta -> LK Gamma Delta.
  Proof.
    intros Gamma Delta H.
    induction H.
    - apply LK_Ax.
    - apply LK_L_Bot.
    - apply LK_Weak_L; assumption.
    - apply LK_Contr_L; assumption.
    - eapply LK_Perm_L; eassumption.
    - apply LK_L_Conj; assumption.
    - apply LK_R_Conj; assumption.
    - apply LK_L_Disj; assumption.
    - apply LK_R_Disj. apply LK_Swap_R. apply LK_Weak_R. assumption.
    - apply LK_R_Disj. apply LK_Weak_R. assumption.
    - apply LK_L_Impl.
      + apply LK_weaken_R_list. exact IHLJ1.
      + exact IHLJ2.
    - apply LK_R_Impl; assumption.
  Defined.

  (** =====================================================================
      4. Classical Semantic Soundness of LK
      ===================================================================== *)

  Definition val_Gamma (val : PropVars.t -> Prop) (Gamma : list Fo) : Prop :=
    forall A, In A Gamma -> foI_cl val A.

  Definition val_Delta (val : PropVars.t -> Prop) (Delta : list Fo) : Prop :=
    exists B, In B Delta /\ foI_cl val B.

  Definition seq_sem (val : PropVars.t -> Prop) (Gamma Delta : list Fo) : Prop :=
    val_Gamma val Gamma -> val_Delta val Delta.

  Lemma val_Gamma_nil : forall val,
    val_Gamma val [].
  Proof.
    intros val A Hin. inversion Hin.
  Qed.

  Lemma val_Gamma_cons : forall val A Gamma,
    val_Gamma val (A :: Gamma) <-> (foI_cl val A /\ val_Gamma val Gamma).
  Proof.
    intros val A Gamma.
    unfold val_Gamma. split.
    - intros H. split.
      + apply H. left. reflexivity.
      + intros B Hin. apply H. right. exact Hin.
    - intros [HA HG] B [Heq | Hin].
      + subst B. exact HA.
      + apply HG. exact Hin.
  Qed.

  Lemma val_Delta_cons : forall val B Delta,
    val_Delta val (B :: Delta) <-> (foI_cl val B \/ val_Delta val Delta).
  Proof.
    intros val B Delta.
    unfold val_Delta. split.
    - intros [C [[Heq | Hin] Hsat]].
      + subst C. left. exact Hsat.
      + right. exists C. split; assumption.
    - intros [HB | [C [Hin Hsat]]].
      + exists B. split. left. reflexivity. exact HB.
      + exists C. split. right. exact Hin. exact Hsat.
  Qed.

  Lemma val_Gamma_perm : forall val Gamma Gamma',
    Permutation Gamma Gamma' -> (val_Gamma val Gamma <-> val_Gamma val Gamma').
  Proof.
    intros val Gamma Gamma' Hperm.
    unfold val_Gamma. split; intros H A Hin.
    - apply H. eapply Permutation_in. apply Permutation_sym. exact Hperm. exact Hin.
    - apply H. eapply Permutation_in. exact Hperm. exact Hin.
  Qed.

  Lemma val_Delta_perm : forall val Delta Delta',
    Permutation Delta Delta' -> (val_Delta val Delta <-> val_Delta val Delta').
  Proof.
    intros val Delta Delta' Hperm.
    unfold val_Delta. split; intros [B [Hin Hsat]]; exists B; split; try assumption.
    - eapply Permutation_in. exact Hperm. exact Hin.
    - eapply Permutation_in. apply Permutation_sym. exact Hperm. exact Hin.
  Qed.

  (** Soundness of Cut-Free LK Derivations with respect to Classical Valuations *)
  Theorem lk_sound : forall (Gamma Delta : list Fo),
    LK Gamma Delta -> forall (val : PropVars.t -> Prop), seq_sem val Gamma Delta.
  Proof.
    intros Gamma Delta H.
    induction H; intros val HGamma.
    - (** LK_Ax *)
      rewrite val_Gamma_cons in HGamma. destruct HGamma as [HA HG].
      rewrite val_Delta_cons. left. exact HA.
    - (** LK_L_Bot *)
      rewrite val_Gamma_cons in HGamma. destruct HGamma as [Hbot _].
      simpl in Hbot. contradiction.
    - (** LK_Weak_L *)
      rewrite val_Gamma_cons in HGamma. destruct HGamma as [_ HG].
      apply IHLK. exact HG.
    - (** LK_Weak_R *)
      rewrite val_Delta_cons. right. apply IHLK. exact HGamma.
    - (** LK_Contr_L *)
      rewrite val_Gamma_cons in HGamma. destruct HGamma as [HA HG].
      apply IHLK.
      rewrite val_Gamma_cons. split. exact HA.
      rewrite val_Gamma_cons. split; assumption.
    - (** LK_Contr_R *)
      pose proof (IHLK val HGamma) as HD.
      rewrite val_Delta_cons in HD.
      destruct HD as [HA1 | HD2].
      + rewrite val_Delta_cons. left. exact HA1.
      + rewrite val_Delta_cons in HD2.
        destruct HD2 as [HA2 | HD3].
        * rewrite val_Delta_cons. left. exact HA2.
        * rewrite val_Delta_cons. right. exact HD3.
    - (** LK_Perm_L *)
      apply IHLK.
      eapply (proj2 (val_Gamma_perm val Gamma Gamma' p)).
      exact HGamma.
    - (** LK_Perm_R *)
      eapply (proj1 (val_Delta_perm val Delta Delta' p)).
      apply IHLK. exact HGamma.
    - (** LK_L_Conj *)
      rewrite val_Gamma_cons in HGamma. destruct HGamma as [Hconj HG].
      simpl in Hconj. destruct Hconj as [HA HB].
      apply IHLK.
      rewrite val_Gamma_cons. split. exact HA.
      rewrite val_Gamma_cons. split; assumption.
    - (** LK_R_Conj *)
      pose proof (IHLK1 val HGamma) as HD1.
      pose proof (IHLK2 val HGamma) as HD2.
      rewrite val_Delta_cons in HD1.
      rewrite val_Delta_cons in HD2.
      rewrite val_Delta_cons.
      destruct HD1 as [HA | HDA].
      + destruct HD2 as [HB | HDB].
        * left. simpl. split; assumption.
        * right. exact HDB.
      + right. exact HDA.
    - (** LK_L_Disj *)
      rewrite val_Gamma_cons in HGamma. destruct HGamma as [Hdisj HG].
      simpl in Hdisj. destruct Hdisj as [HA | HB].
      + apply IHLK1. rewrite val_Gamma_cons. split; assumption.
      + apply IHLK2. rewrite val_Gamma_cons. split; assumption.
    - (** LK_R_Disj *)
      pose proof (IHLK val HGamma) as HD.
      rewrite val_Delta_cons in HD.
      rewrite val_Delta_cons.
      destruct HD as [HA | HD2].
      + left. simpl. left. exact HA.
      + rewrite val_Delta_cons in HD2.
        destruct HD2 as [HB | HD3].
        * left. simpl. right. exact HB.
        * right. exact HD3.
    - (** LK_L_Impl *)
      rewrite val_Gamma_cons in HGamma. destruct HGamma as [Himpl HG].
      simpl in Himpl.
      pose proof (IHLK1 val HG) as HD1.
      rewrite val_Delta_cons in HD1.
      destruct HD1 as [HA | HDA].
      + apply IHLK2. rewrite val_Gamma_cons. split.
        * apply Himpl. exact HA.
        * exact HG.
      + exact HDA.
    - (** LK_R_Impl *)
      rewrite val_Delta_cons.
      destruct (classic (foI_cl val A)) as [HA | HnotA].
      + assert (HGA : val_Gamma val (A :: Gamma)).
        { rewrite val_Gamma_cons. split; assumption. }
        pose proof (IHLK val HGA) as HD.
        rewrite val_Delta_cons in HD.
        destruct HD as [HB | HD].
        * left. simpl. intros _. exact HB.
        * right. exact HD.
      + left. simpl. intros HA. contradiction.
  Defined.

  (** =====================================================================
      5. Sequent Calculus with Cut (LKC) and Cut Soundness
      ===================================================================== *)

  Inductive LKC : list Fo -> list Fo -> Type :=
  | LKC_embed : forall (Gamma Delta : list Fo),
      LK Gamma Delta -> LKC Gamma Delta
  | LKC_Cut : forall (Gamma Delta : list Fo) (A : Fo),
      LKC Gamma (A :: Delta) -> LKC (A :: Gamma) Delta -> LKC Gamma Delta
  | LKC_Weak_L : forall (Gamma Delta : list Fo) (A : Fo),
      LKC Gamma Delta -> LKC (A :: Gamma) Delta
  | LKC_Weak_R : forall (Gamma Delta : list Fo) (A : Fo),
      LKC Gamma Delta -> LKC Gamma (A :: Delta)
  | LKC_Perm_L : forall (Gamma Gamma' Delta : list Fo),
      Permutation Gamma Gamma' -> LKC Gamma Delta -> LKC Gamma' Delta
  | LKC_Perm_R : forall (Gamma Delta Delta' : list Fo),
      Permutation Delta Delta' -> LKC Gamma Delta -> LKC Gamma Delta'
  .

  (** Soundness of LKC *)
  Theorem lkc_sound : forall (Gamma Delta : list Fo),
    LKC Gamma Delta -> forall (val : PropVars.t -> Prop), seq_sem val Gamma Delta.
  Proof.
    intros Gamma Delta H.
    induction H; intros val HGamma.
    - eapply lk_sound; eassumption.
    - destruct (classic (foI_cl val A)) as [HA | HnotA].
      + apply IHLKC2. rewrite val_Gamma_cons. split; assumption.
      + pose proof (IHLKC1 val HGamma) as HD1.
        rewrite val_Delta_cons in HD1.
        destruct HD1 as [HA | HD]; [contradiction | exact HD].
    - rewrite val_Gamma_cons in HGamma. destruct HGamma as [_ HG].
      apply IHLKC. exact HG.
    - rewrite val_Delta_cons. right. apply IHLKC. exact HGamma.
    - apply IHLKC.
      eapply (proj2 (val_Gamma_perm val Gamma Gamma' p)).
      exact HGamma.
    - eapply (proj1 (val_Delta_perm val Delta Delta' p)).
      apply IHLKC. exact HGamma.
  Defined.

  (** =====================================================================
      6. Cut-Free Proofs of Classical Theorems and Hilbert Axioms in LK
      ===================================================================== *)

  (** Identity on any formula A *)
  Theorem lk_id : forall A, LK [A] [A].
  Proof.
    intro A.
    apply (LK_Ax [] []).
  Defined.

  (** Law of Excluded Middle: |- A \/ -.A *)
  Theorem lk_em : forall A, LK [] [A -\/ -.A].
  Proof.
    intro A.
    apply LK_R_Disj.
    unfold Neg.
    eapply LK_Perm_R.
    - apply perm_swap.
    - apply LK_R_Impl.
      eapply LK_Perm_R.
      + apply perm_swap.
      + apply (LK_Ax [] [Bot]).
  Defined.

  (** Double Negation Elimination: -. -. A |- A *)
  Theorem lk_dne : forall A, LK [-. -. A] [A].
  Proof.
    intro A.
    unfold Neg.
    apply LK_L_Impl.
    - apply LK_R_Impl.
      apply LK_Swap_R.
      apply (LK_Ax [] [Bot]).
    - apply LK_L_Bot.
  Defined.

  (** Peirce's Law: |- ((A --> B) --> A) --> A *)
  Theorem lk_peirce : forall A B, LK [] [((A --> B) --> A) --> A].
  Proof.
    intros A B.
    apply LK_R_Impl.
    apply LK_L_Impl.
    - apply LK_R_Impl.
      apply LK_Swap_R.
      apply (LK_Ax [] [B] A).
    - apply (LK_Ax [] [] A).
  Defined.

  (** Contraposition: A --> B |- -.B --> -.A *)
  Theorem lk_contra : forall A B, LK [A --> B] [(-. B) --> (-. A)].
  Proof.
    intros A B.
    unfold Neg.
    apply LK_R_Impl.
    apply LK_Swap_L.
    apply LK_L_Impl.
    - apply LK_Swap_R.
      apply LK_R_Impl.
      apply LK_Swap_R.
      apply (LK_Ax [B --> Bot] [Bot] A).
    - apply LK_Swap_L.
      apply LK_L_Impl.
      + apply (LK_Ax [] [A --> Bot] B).
      + apply LK_L_Bot.
  Defined.

  (** Hilbert Axiom Ha1: A --> (B --> A) *)
  Theorem lk_Ha1 : forall A B, LK [] [A --> (B --> A)].
  Proof.
    intros A B.
    apply LK_R_Impl.
    apply LK_R_Impl.
    apply LK_Swap_L.
    apply (LK_Ax [B] [] A).
  Defined.

  (** Cyclic permutation of 3 elements on the left *)
  Lemma perm_3_1 : forall (Gamma : list Fo) (X Y Z : Fo),
    Permutation (X :: Y :: Z :: Gamma) (Z :: X :: Y :: Gamma).
  Proof.
    intros.
    eapply Permutation_trans with (l' := Y :: X :: Z :: Gamma).
    - apply perm_swap.
    - eapply Permutation_trans with (l' := Y :: Z :: X :: Gamma).
      + apply perm_skip. apply perm_swap.
      + eapply Permutation_trans with (l' := Z :: Y :: X :: Gamma).
        * apply perm_swap.
        * apply perm_skip. apply perm_swap.
  Defined.

  (** Cyclic permutation bringing 3rd element to head *)
  Lemma perm_cycle_to_head : forall (Gamma : list Fo) (X Y Z : Fo),
    Permutation (Z :: X :: Y :: Gamma) (X :: Y :: Z :: Gamma).
  Proof.
    intros.
    apply Permutation_sym.
    apply perm_3_1.
  Defined.

  (** Hilbert Axiom Ha2: (A --> B --> C) --> (A --> B) --> (A --> C) *)
  Theorem lk_Ha2 : forall A B C,
    LK [] [(A --> B --> C) --> (A --> B) --> (A --> C)].
  Proof.
    intros A B C.
    apply LK_R_Impl.
    apply LK_R_Impl.
    apply LK_R_Impl.
    apply LK_Swap_L.
    apply LK_L_Impl.
    - apply (LK_Ax [A --> B --> C] [C] A).
    - eapply LK_Perm_L; [apply perm_cycle_to_head | ].
      apply LK_L_Impl.
      + apply LK_Swap_L.
        apply (LK_Ax [B] [C] A).
      + apply LK_L_Impl.
        * apply (LK_Ax [A] [C] B).
        * apply (LK_Ax [B; A] [] C).
  Defined.

  (** Hilbert Axiom Ha3: (A -/\ B) --> A *)
  Theorem lk_Ha3 : forall A B, LK [] [(A -/\ B) --> A].
  Proof.
    intros A B.
    apply LK_R_Impl.
    apply LK_L_Conj.
    apply (LK_Ax [B] [] A).
  Defined.

  (** Hilbert Axiom Ha4: (A -/\ B) --> B *)
  Theorem lk_Ha4 : forall A B, LK [] [(A -/\ B) --> B].
  Proof.
    intros A B.
    apply LK_R_Impl.
    apply LK_L_Conj.
    apply LK_Swap_L.
    apply (LK_Ax [A] [] B).
  Defined.

  (** Hilbert Axiom Ha5: A --> B --> (A -/\ B) *)
  Theorem lk_Ha5 : forall A B, LK [] [A --> B --> (A -/\ B)].
  Proof.
    intros A B.
    apply LK_R_Impl.
    apply LK_R_Impl.
    apply LK_R_Conj.
    - apply LK_Swap_L.
      apply (LK_Ax [B] [] A).
    - apply (LK_Ax [A] [] B).
  Defined.

  (** Hilbert Axiom Ha6: A --> (A -\/ B) *)
  Theorem lk_Ha6 : forall A B, LK [] [A --> (A -\/ B)].
  Proof.
    intros A B.
    apply LK_R_Impl.
    apply LK_R_Disj.
    apply (LK_Ax [] [B] A).
  Defined.

  (** Hilbert Axiom Ha7: B --> (A -\/ B) *)
  Theorem lk_Ha7 : forall A B, LK [] [B --> (A -\/ B)].
  Proof.
    intros A B.
    apply LK_R_Impl.
    apply LK_R_Disj.
    apply LK_Swap_R.
    apply (LK_Ax [] [A] B).
  Defined.

  (** Hilbert Axiom Ha8: (A --> C) --> (B --> C) --> ((A -\/ B) --> C) *)
  Theorem lk_Ha8 : forall A B C,
    LK [] [(A --> C) --> (B --> C) --> ((A -\/ B) --> C)].
  Proof.
    intros A B C.
    apply LK_R_Impl.
    apply LK_R_Impl.
    apply LK_R_Impl.
    apply LK_L_Disj.
    - eapply LK_Perm_L; [apply perm_cycle_to_head | ].
      apply LK_L_Impl.
      + apply (LK_Ax [B --> C] [C] A).
      + apply (LK_Ax [A; B --> C] [] C).
    - apply LK_Swap_L.
      apply LK_L_Impl.
      + apply (LK_Ax [A --> C] [C] B).
      + apply (LK_Ax [B; A --> C] [] C).
  Defined.

  (** Hilbert Axiom Ha9: (-.A) --> (A --> B) *)
  Theorem lk_Ha9 : forall A B, LK [] [(-.A) --> (A --> B)].
  Proof.
    intros A B.
    unfold Neg.
    apply LK_R_Impl.
    apply LK_R_Impl.
    apply LK_Swap_L.
    apply LK_L_Impl.
    - apply (LK_Ax [] [B] A).
    - apply LK_L_Bot.
  Defined.

  (** Hilbert Axiom Ha10: (A --> B) --> (A --> -.B) --> -.A *)
  Theorem lk_Ha10 : forall A B,
    LK [] [(A --> B) --> (A --> -.B) --> -.A].
  Proof.
    intros A B.
    unfold Neg.
    apply LK_R_Impl.
    apply LK_R_Impl.
    apply LK_R_Impl.
    eapply LK_Perm_L; [apply perm_cycle_to_head | ].
    apply LK_L_Impl.
    - apply (LK_Ax [A --> B --> Bot] [Bot] A).
    - eapply LK_Perm_L; [apply perm_cycle_to_head | ].
      apply LK_L_Impl.
      + apply LK_Swap_L.
        apply (LK_Ax [B] [Bot] A).
      + apply LK_L_Impl.
        * apply (LK_Ax [A] [Bot] B).
        * apply LK_L_Bot.
  Defined.

  (** Hilbert Axiom Ha11: A -\/ -.A *)
  Theorem lk_Ha11 : forall A, LK [] [A -\/ -.A].
  Proof.
    apply lk_em.
  Defined.

  (** =====================================================================
      7. Hilbert Deduction to Sequent Calculus Equivalence
      ===================================================================== *)

  Lemma lkc_ax_inst : forall A, PROCA A -> LKC [] [A].
  Proof.
    intros A Hax.
    apply LKC_embed.
    destruct Hax as [f H_intui | A_lem].
    - destruct H_intui.
      + apply lk_Ha1.
      + apply lk_Ha2.
      + apply lk_Ha3.
      + apply lk_Ha4.
      + apply lk_Ha5.
      + apply lk_Ha6.
      + apply lk_Ha7.
      + apply lk_Ha8.
      + apply lk_Ha9.
      + apply lk_Ha10.
    - apply lk_Ha11.
  Defined.

  Theorem lkc_mp_nil : forall A B,
    LKC [] [A] -> LKC [] [A --> B] -> LKC [] [B].
  Proof.
    intros A B HA HAB.
    assert (HL_impl : LK [A; A --> B] [B]).
    {
      apply LK_Swap_L.
      apply LK_L_Impl.
      - apply (LK_Ax [] [B] A).
      - apply (LK_Ax [A] [] B).
    }
    pose proof (LKC_embed _ _ HL_impl) as HLKC_impl.
    assert (Hcut1 : LKC [A] [B]).
    {
      eapply LKC_Cut with (A := A --> B).
      - apply LKC_Weak_L.
        eapply LKC_Perm_R.
        + apply perm_swap.
        + apply LKC_Weak_R.
          exact HAB.
      - eapply LKC_Perm_L; [apply perm_swap | exact HLKC_impl].
    }
    eapply LKC_Cut with (A := A).
    - eapply LKC_Perm_R.
      + apply perm_swap.
      + apply LKC_Weak_R.
        exact HA.
    - exact Hcut1.
  Defined.

  (** Bridge Theorem: Any classical Hilbert proof translates to an LKC derivation *)
  Theorem hilbert_to_lkc : forall A,
    PR PROCA empctx A -> LKC [] [A].
  Proof.
    intros A H.
    remember empctx as ctx eqn:Heq.
    induction H.
    - subst ctx. inversion c.
    - subst ctx. apply lkc_ax_inst. exact a.
    - subst ctx.
      eapply (lkc_mp_nil A B).
      + apply IHPR1; reflexivity.
      + apply IHPR2; reflexivity.
  Defined.

End Sequent_mod.

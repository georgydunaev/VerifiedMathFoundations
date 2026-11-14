# [VERIFIEDMATHFOUNDATIONS] Ticket 7811: Sequent Calculus LK and LJ for Propositional Logic, Invertible Rules, and Cut-Free Derivation Search

**Repository:** `VerifiedMathFoundations`
**Status:** `RESOLVED`
**Created:** `2026-11-13T23:55:00Z`
**Resolved:** `2026-11-14T00:10:00Z`
**Author:** Proof Theory and Automated Reasoning Specialist

## Overview
Propositional logic in `VerifiedMathFoundations` was primarily formalized through Hilbert-style axiomatic deduction (`PR PROCA` and `PR PROCAI` in `PropLang.v` and predicate calculus in `Deduction.v`). While Hilbert systems are foundational for metamathematical results (such as the deduction theorem), they are ill-suited for automated proof search and structural proof theory.

This ticket introduces Gentzen's Sequent Calculus for propositional logic (classical LK and intuitionistic LJ), mechanizes the structural and logical rules, establishes valuation soundness for cut-free derivations, proves bridge theorems connecting Hilbert deduction and sequent calculus, and provides a verified Python reference prover with automated proof search, proof tree validation, and countermodel generation.

## Key Objectives and Achievements

1. **Coq Formalization (Sequent.v):**
   - Defined propositional sequents as pairs of formula lists (Gamma, Delta).
   - Mechanized the classical cut-free sequent calculus LK with:
     - Identity and Axiom rules (Ax, L_Bot).
     - Structural rules: left and right weakening, left and right contraction, and exchange permutations (via Coq's Permutation).
     - Logical introduction rules: conjunction (L_Conj, R_Conj), disjunction (L_Disj, R_Disj), implication (L_Impl, R_Impl), and negation (derived L_Neg, R_Neg).
   - Mechanized the intuitionistic restriction LJ where the succedent contains at most one formula, with conservative embedding `lj_to_lk`.
   - Proved semantic soundness theorem `lk_sound`: every cut-free LK derivation is sound with respect to classical valuations (`foI_cl`).
   - Mechanized Gentzen calculus with Cut (`LKC`), proved soundness `lkc_sound`.
   - Proved classical tautologies cut-free in LK:
     - Identity (`lk_id`)
     - Law of Excluded Middle (`lk_em`)
     - Double Negation Elimination (`lk_dne`)
     - Peirce's Law (`lk_peirce`)
     - Contraposition (`lk_contra`)
     - All Hilbert classical axioms Ha1 through Ha11 (`lk_Ha1` to `lk_Ha11`)
   - Proved bridge theorem `hilbert_to_lkc`: every Hilbert deduction `PR PROCA empctx A` yields a sequent derivation `LKC [] [A]`.
   - Compiled with `coqc -Q . ""` with zero errors and zero Admitted.

2. **Python Implementation (src/sequent_prover.py):**
   - AST for propositional formulas (`Atom`, `Bot`, `Top`, `Not`, `And`, `Or`, `Impl`).
   - Sequent and derivation tree data structures with complexity metrics and two-sided valuation evaluation.
   - Invertible and branching proof search (`prove_sequent`) implementing Gentzen's cut-free LK algorithm.
   - Certified derivation verifier (`verify_derivation`) confirming each inference step adheres strictly to LK rules.
   - Countermodel extractor (`find_countermodel`) providing falsifying truth assignments for unprovable sequents.
   - High-level API (`prove_formula`) and ASCII derivation tree visualizer (`display`).

3. **Automated Verification and Test Suite:**
   - Unit tests in `tests/test_sequent.py` covering classical theorems (LEM, DNE, Peirce's Law, De Morgan laws, Contraposition, Hilbert axioms Ha1 to Ha11, implication transitivity), invalid sequents, proof tree verification, and countermodel checks.
   - Full integration with `verify.py`: all 22 Coq files and all Python unit tests pass cleanly.

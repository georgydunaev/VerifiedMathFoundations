"""Unit tests for Propositional Sequent Calculus (LK) Prover and Proof Search."""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.sequent_prover import (
    And,
    Atom,
    Bot,
    Derivation,
    Formula,
    Impl,
    Not,
    Or,
    Sequent,
    Top,
    find_countermodel,
    prove_formula,
    prove_sequent,
    verify_derivation,
)


class TestFormulaAST(unittest.TestCase):
    """Test AST representation, valuation, and complexity of formulas."""

    def test_formula_atoms(self):
        a = Atom("P")
        b = Atom("Q")
        f = Impl(And(a, b), Or(a, Not(b)))
        self.assertEqual(f.atoms(), {"P", "Q"})
        self.assertEqual(f.complexity(), 4)

    def test_formula_eval(self):
        p = Atom("P")
        q = Atom("Q")
        val_tt = {"P": True, "Q": True}
        val_tf = {"P": True, "Q": False}
        val_ft = {"P": False, "Q": True}
        val_ff = {"P": False, "Q": False}

        f_and = And(p, q)
        self.assertTrue(f_and.evaluate(val_tt))
        self.assertFalse(f_and.evaluate(val_tf))

        f_impl = Impl(p, q)
        self.assertTrue(f_impl.evaluate(val_tt))
        self.assertFalse(f_impl.evaluate(val_tf))
        self.assertTrue(f_impl.evaluate(val_ft))
        self.assertTrue(f_impl.evaluate(val_ff))

        self.assertTrue(Top().evaluate(val_ff))
        self.assertFalse(Bot().evaluate(val_tt))

    def test_formula_str(self):
        p = Atom("P")
        q = Atom("Q")
        self.assertEqual(str(p), "P")
        self.assertEqual(str(Not(p)), "(-.P)")
        self.assertEqual(str(And(p, q)), "(P -/\\ Q)")
        self.assertEqual(str(Or(p, q)), "(P -\\/ Q)")
        self.assertEqual(str(Impl(p, q)), "(P --> Q)")


class TestSequentSemantics(unittest.TestCase):
    """Test Sequent evaluation against valuations."""

    def test_sequent_eval(self):
        p = Atom("P")
        q = Atom("Q")
        seq = Sequent([p, Impl(p, q)], [q])
        # In any valuation, if P and P ==> Q hold, then Q holds
        for p_val in [True, False]:
            for q_val in [True, False]:
                val = {"P": p_val, "Q": q_val}
                self.assertTrue(seq.evaluate(val))

    def test_invalid_sequent_eval(self):
        p = Atom("P")
        q = Atom("Q")
        seq = Sequent([Or(p, q)], [And(p, q)])
        val_tf = {"P": True, "Q": False}
        self.assertFalse(seq.evaluate(val_tf))


class TestSequentProofSearch(unittest.TestCase):
    """Test cut-free LK proof search on classical tautologies."""

    def setUp(self):
        self.p = Atom("P")
        self.q = Atom("Q")
        self.r = Atom("R")

    def assertDerivationValid(self, node):
        self.assertIsNotNone(node)
        valid, msg = verify_derivation(node)
        self.assertTrue(valid, msg)

    def test_identity(self):
        seq = Sequent([self.p], [self.p])
        node = prove_sequent(seq)
        self.assertDerivationValid(node)

    def test_excluded_middle(self):
        # |- P \/ ~P
        f = Or(self.p, Not(self.p))
        is_valid, der, cm = prove_formula(f)
        self.assertTrue(is_valid)
        self.assertIsNone(cm)
        self.assertDerivationValid(der)

    def test_double_negation_elimination(self):
        # ~~P |- P
        seq = Sequent([Not(Not(self.p))], [self.p])
        node = prove_sequent(seq)
        self.assertDerivationValid(node)

    def test_peirce_law(self):
        # |- ((P ==> Q) ==> P) ==> P
        f = Impl(Impl(Impl(self.p, self.q), self.p), self.p)
        is_valid, der, cm = prove_formula(f)
        self.assertTrue(is_valid)
        self.assertIsNone(cm)
        self.assertDerivationValid(der)

    def test_contraposition(self):
        # P ==> Q |- ~Q ==> ~P
        seq = Sequent([Impl(self.p, self.q)], [Impl(Not(self.q), Not(self.p))])
        node = prove_sequent(seq)
        self.assertDerivationValid(node)

    def test_de_morgan_1(self):
        # ~(P /\ Q) |- ~P \/ ~Q
        seq = Sequent([Not(And(self.p, self.q))], [Or(Not(self.p), Not(self.q))])
        node = prove_sequent(seq)
        self.assertDerivationValid(node)

    def test_de_morgan_2(self):
        # ~P \/ ~Q |- ~(P /\ Q)
        seq = Sequent([Or(Not(self.p), Not(self.q))], [Not(And(self.p, self.q))])
        node = prove_sequent(seq)
        self.assertDerivationValid(node)

    def test_de_morgan_3(self):
        # ~(P \/ Q) |- ~P /\ ~Q
        seq = Sequent([Not(Or(self.p, self.q))], [And(Not(self.p), Not(self.q))])
        node = prove_sequent(seq)
        self.assertDerivationValid(node)

    def test_de_morgan_4(self):
        # ~P /\ ~Q |- ~(P \/ Q)
        seq = Sequent([And(Not(self.p), Not(self.q))], [Not(Or(self.p, self.q))])
        node = prove_sequent(seq)
        self.assertDerivationValid(node)

    def test_hilbert_axioms(self):
        axioms = [
            # Ha1: A ==> B ==> A
            Impl(self.p, Impl(self.q, self.p)),
            # Ha2: (A ==> B ==> C) ==> (A ==> B) ==> (A ==> C)
            Impl(
                Impl(self.p, Impl(self.q, self.r)),
                Impl(Impl(self.p, self.q), Impl(self.p, self.r)),
            ),
            # Ha3: A /\ B ==> A
            Impl(And(self.p, self.q), self.p),
            # Ha4: A /\ B ==> B
            Impl(And(self.p, self.q), self.q),
            # Ha5: A ==> B ==> A /\ B
            Impl(self.p, Impl(self.q, And(self.p, self.q))),
            # Ha6: A ==> A \/ B
            Impl(self.p, Or(self.p, self.q)),
            # Ha7: B ==> A \/ B
            Impl(self.q, Or(self.p, self.q)),
            # Ha8: (A ==> C) ==> (B ==> C) ==> (A \/ B ==> C)
            Impl(
                Impl(self.p, self.r),
                Impl(Impl(self.q, self.r), Impl(Or(self.p, self.q), self.r)),
            ),
            # Ha9: (A ==> B) ==> (A ==> ~B) ==> ~A
            Impl(
                Impl(self.p, self.q),
                Impl(Impl(self.p, Not(self.q)), Not(self.p)),
            ),
            # Ha10: ~A ==> A ==> B (ex falso)
            Impl(Not(self.p), Impl(self.p, self.q)),
            # Ha11: A \/ ~A (LEM)
            Or(self.p, Not(self.p)),
        ]
        for ax in axioms:
            is_valid, der, cm = prove_formula(ax)
            self.assertTrue(is_valid, f"Failed to prove axiom: {ax}")
            self.assertIsNone(cm)
            self.assertDerivationValid(der)

    def test_implication_transitivity(self):
        # P ==> Q, Q ==> R |- P ==> R
        seq = Sequent([Impl(self.p, self.q), Impl(self.q, self.r)], [Impl(self.p, self.r)])
        node = prove_sequent(seq)
        self.assertDerivationValid(node)


class TestInvalidSequentsAndCountermodels(unittest.TestCase):
    """Test countermodel generation for unprovable sequents."""

    def setUp(self):
        self.p = Atom("P")
        self.q = Atom("Q")

    def test_atomic_fallacy(self):
        # |- P is not valid
        seq = Sequent([], [self.p])
        self.assertIsNone(prove_sequent(seq))
        cm = find_countermodel(seq)
        self.assertIsNotNone(cm)
        self.assertFalse(seq.evaluate(cm))
        self.assertFalse(cm["P"])

    def test_affirming_consequent(self):
        # (P ==> Q), Q |- P is not valid
        seq = Sequent([Impl(self.p, self.q), self.q], [self.p])
        self.assertIsNone(prove_sequent(seq))
        cm = find_countermodel(seq)
        self.assertIsNotNone(cm)
        self.assertFalse(seq.evaluate(cm))
        self.assertFalse(cm["P"])
        self.assertTrue(cm["Q"])

    def test_disjunction_conjunction_fallacy(self):
        # P \/ Q |- P /\ Q is not valid
        seq = Sequent([Or(self.p, self.q)], [And(self.p, self.q)])
        self.assertIsNone(prove_sequent(seq))
        cm = find_countermodel(seq)
        self.assertIsNotNone(cm)
        self.assertFalse(seq.evaluate(cm))


class TestDerivationValidation(unittest.TestCase):
    """Test derivation tree structural verification."""

    def test_tampered_derivation_rejected(self):
        p = Atom("P")
        # Build an illegitimate leaf
        bad_leaf = Derivation(
            rule="Ax",
            sequent=Sequent([p], [Atom("Q")]),
            premises=[],
            principal=p,
        )
        valid, _ = verify_derivation(bad_leaf)
        self.assertFalse(valid)

    def test_display_derivation(self):
        p = Atom("P")
        seq = Sequent([p], [p])
        node = prove_sequent(seq)
        self.assertIsNotNone(node)
        text = node.display()
        self.assertIn("Ax", text)


if __name__ == "__main__":
    unittest.main()

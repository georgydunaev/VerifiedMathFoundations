#!/usr/bin/env python3
"""Propositional Sequent Calculus LK Prover and Proof Tree Verifier.

Part of VerifiedMathFoundations.
Formalized in Coq in Sequent.v.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Optional


# ============================================================================
# 1. Formula Abstract Syntax Tree
# ============================================================================


class Formula(ABC):
    """Abstract base class for propositional formulas."""

    @abstractmethod
    def evaluate(self, val: dict[str, bool]) -> bool:
        """Evaluate formula under a boolean valuation."""
        pass

    @abstractmethod
    def complexity(self) -> int:
        """Measure formula complexity for termination metrics."""
        pass

    @abstractmethod
    def atoms(self) -> set[str]:
        """Collect all propositional variable names."""
        pass


@dataclass(frozen=True)
class Atom(Formula):
    name: str

    def evaluate(self, val: dict[str, bool]) -> bool:
        return val.get(self.name, False)

    def complexity(self) -> int:
        return 0

    def atoms(self) -> set[str]:
        return {self.name}

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return f"Atom('{self.name}')"


@dataclass(frozen=True)
class Bot(Formula):
    def evaluate(self, val: dict[str, bool]) -> bool:
        return False

    def complexity(self) -> int:
        return 0

    def atoms(self) -> set[str]:
        return set()

    def __str__(self) -> str:
        return "Bot"

    def __repr__(self) -> str:
        return "Bot()"


@dataclass(frozen=True)
class Top(Formula):
    def evaluate(self, val: dict[str, bool]) -> bool:
        return True

    def complexity(self) -> int:
        return 0

    def atoms(self) -> set[str]:
        return set()

    def __str__(self) -> str:
        return "Top"

    def __repr__(self) -> str:
        return "Top()"


@dataclass(frozen=True)
class Not(Formula):
    inner: Formula

    def evaluate(self, val: dict[str, bool]) -> bool:
        return not self.inner.evaluate(val)

    def complexity(self) -> int:
        return 1 + self.inner.complexity()

    def atoms(self) -> set[str]:
        return self.inner.atoms()

    def __str__(self) -> str:
        return f"(-.{self.inner})"

    def __repr__(self) -> str:
        return f"Not({self.inner!r})"


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula

    def evaluate(self, val: dict[str, bool]) -> bool:
        return self.left.evaluate(val) and self.right.evaluate(val)

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def atoms(self) -> set[str]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return f"({self.left} -/\\ {self.right})"

    def __repr__(self) -> str:
        return f"And({self.left!r}, {self.right!r})"


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula

    def evaluate(self, val: dict[str, bool]) -> bool:
        return self.left.evaluate(val) or self.right.evaluate(val)

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def atoms(self) -> set[str]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return f"({self.left} -\\/ {self.right})"

    def __repr__(self) -> str:
        return f"Or({self.left!r}, {self.right!r})"


@dataclass(frozen=True)
class Impl(Formula):
    left: Formula
    right: Formula

    def evaluate(self, val: dict[str, bool]) -> bool:
        return (not self.left.evaluate(val)) or self.right.evaluate(val)

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def atoms(self) -> set[str]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return f"({self.left} --> {self.right})"

    def __repr__(self) -> str:
        return f"Impl({self.left!r}, {self.right!r})"


# ============================================================================
# 2. Sequent Data Structure
# ============================================================================


@dataclass(frozen=True)
class Sequent:
    """A two-sided Gentzen sequent Gamma |- Delta."""

    gamma: tuple[Formula, ...]
    delta: tuple[Formula, ...]

    def __init__(self, gamma: tuple[Formula, ...] | list[Formula], delta: tuple[Formula, ...] | list[Formula]):
        object.__setattr__(self, "gamma", tuple(gamma))
        object.__setattr__(self, "delta", tuple(delta))

    def evaluate(self, val: dict[str, bool]) -> bool:
        gamma_true = all(f.evaluate(val) for f in self.gamma)
        if not gamma_true:
            return True
        return any(f.evaluate(val) for f in self.delta)

    def complexity(self) -> int:
        return sum(f.complexity() for f in self.gamma) + sum(f.complexity() for f in self.delta)

    def all_atoms(self) -> set[str]:
        res: set[str] = set()
        for f in self.gamma:
            res |= f.atoms()
        for f in self.delta:
            res |= f.atoms()
        return res

    def __str__(self) -> str:
        g_str = ", ".join(str(f) for f in self.gamma) if self.gamma else "[empty]"
        d_str = ", ".join(str(f) for f in self.delta) if self.delta else "[empty]"
        return f"{g_str} |- {d_str}"


# ============================================================================
# 3. Derivation Tree
# ============================================================================


@dataclass
class Derivation:
    """A node in a sequent calculus proof tree."""

    rule: str
    sequent: Sequent
    premises: list[Derivation]
    principal: Optional[Formula] = None

    def display(self, indent: int = 0) -> str:
        prefix = "  " * indent
        prin_str = f" [{self.principal}]" if self.principal is not None else ""
        lines = [f"{prefix}{self.rule}{prin_str}: {self.sequent}"]
        for p in self.premises:
            lines.append(p.display(indent + 1))
        return "\n".join(lines)


# ============================================================================
# 4. Proof Search Algorithm (Cut-Free LK)
# ============================================================================


def prove_sequent(sequent: Sequent) -> Optional[Derivation]:
    """Automated derivation search in cut-free LK."""
    # Axiom: Gamma, A |- Delta, A
    for f in sequent.gamma:
        if f in sequent.delta:
            return Derivation(rule="Ax", sequent=sequent, premises=[], principal=f)

    # L_Bot: Gamma, Bot |- Delta
    for f in sequent.gamma:
        if isinstance(f, Bot):
            return Derivation(rule="L_Bot", sequent=sequent, premises=[], principal=f)

    # R_Top: Gamma |- Delta, Top
    for f in sequent.delta:
        if isinstance(f, Top):
            return Derivation(rule="R_Top", sequent=sequent, premises=[], principal=f)

    # Invertible rules on Gamma (Antecedent)
    # L_And: (A -/\ B), Gamma |- Delta  from  A, B, Gamma |- Delta
    for i, f in enumerate(sequent.gamma):
        if isinstance(f, And):
            new_gamma = list(sequent.gamma[:i] + sequent.gamma[i + 1 :])
            new_gamma.extend([f.left, f.right])
            prem_seq = Sequent(new_gamma, sequent.delta)
            prem_der = prove_sequent(prem_seq)
            if prem_der is not None:
                return Derivation(rule="L_And", sequent=sequent, premises=[prem_der], principal=f)
            return None

    # L_Not: (-.A), Gamma |- Delta  from  Gamma |- Delta, A
    for i, f in enumerate(sequent.gamma):
        if isinstance(f, Not):
            new_gamma = list(sequent.gamma[:i] + sequent.gamma[i + 1 :])
            new_delta = list(sequent.delta) + [f.inner]
            prem_seq = Sequent(new_gamma, new_delta)
            prem_der = prove_sequent(prem_seq)
            if prem_der is not None:
                return Derivation(rule="L_Not", sequent=sequent, premises=[prem_der], principal=f)
            return None

    # Invertible rules on Delta (Succedent)
    # R_Or: Gamma |- Delta, (A -\/ B)  from  Gamma |- Delta, A, B
    for i, f in enumerate(sequent.delta):
        if isinstance(f, Or):
            new_delta = list(sequent.delta[:i] + sequent.delta[i + 1 :])
            new_delta.extend([f.left, f.right])
            prem_seq = Sequent(sequent.gamma, new_delta)
            prem_der = prove_sequent(prem_seq)
            if prem_der is not None:
                return Derivation(rule="R_Or", sequent=sequent, premises=[prem_der], principal=f)
            return None

    # R_Impl: Gamma |- Delta, (A --> B)  from  A, Gamma |- Delta, B
    for i, f in enumerate(sequent.delta):
        if isinstance(f, Impl):
            new_delta = list(sequent.delta[:i] + sequent.delta[i + 1 :]) + [f.right]
            new_gamma = list(sequent.gamma) + [f.left]
            prem_seq = Sequent(new_gamma, new_delta)
            prem_der = prove_sequent(prem_seq)
            if prem_der is not None:
                return Derivation(rule="R_Impl", sequent=sequent, premises=[prem_der], principal=f)
            return None

    # R_Not: Gamma |- Delta, (-.A)  from  A, Gamma |- Delta
    for i, f in enumerate(sequent.delta):
        if isinstance(f, Not):
            new_delta = list(sequent.delta[:i] + sequent.delta[i + 1 :])
            new_gamma = list(sequent.gamma) + [f.inner]
            prem_seq = Sequent(new_gamma, new_delta)
            prem_der = prove_sequent(prem_seq)
            if prem_der is not None:
                return Derivation(rule="R_Not", sequent=sequent, premises=[prem_der], principal=f)
            return None

    # Branching invertible rules on Delta (Succedent)
    # R_And: Gamma |- Delta, (A -/\ B)  from  Gamma |- Delta, A  and  Gamma |- Delta, B
    for i, f in enumerate(sequent.delta):
        if isinstance(f, And):
            base_delta = list(sequent.delta[:i] + sequent.delta[i + 1 :])
            prem1_seq = Sequent(sequent.gamma, base_delta + [f.left])
            prem2_seq = Sequent(sequent.gamma, base_delta + [f.right])
            p1 = prove_sequent(prem1_seq)
            if p1 is None:
                return None
            p2 = prove_sequent(prem2_seq)
            if p2 is None:
                return None
            return Derivation(rule="R_And", sequent=sequent, premises=[p1, p2], principal=f)

    # Branching invertible rules on Gamma (Antecedent)
    # L_Or: (A -\/ B), Gamma |- Delta  from  A, Gamma |- Delta  and  B, Gamma |- Delta
    for i, f in enumerate(sequent.gamma):
        if isinstance(f, Or):
            base_gamma = list(sequent.gamma[:i] + sequent.gamma[i + 1 :])
            prem1_seq = Sequent(base_gamma + [f.left], sequent.delta)
            prem2_seq = Sequent(base_gamma + [f.right], sequent.delta)
            p1 = prove_sequent(prem1_seq)
            if p1 is None:
                return None
            p2 = prove_sequent(prem2_seq)
            if p2 is None:
                return None
            return Derivation(rule="L_Or", sequent=sequent, premises=[p1, p2], principal=f)

    # L_Impl: (A --> B), Gamma |- Delta  from  Gamma |- Delta, A  and  B, Gamma |- Delta
    for i, f in enumerate(sequent.gamma):
        if isinstance(f, Impl):
            base_gamma = list(sequent.gamma[:i] + sequent.gamma[i + 1 :])
            prem1_seq = Sequent(base_gamma, list(sequent.delta) + [f.left])
            prem2_seq = Sequent(base_gamma + [f.right], sequent.delta)
            p1 = prove_sequent(prem1_seq)
            if p1 is None:
                return None
            p2 = prove_sequent(prem2_seq)
            if p2 is None:
                return None
            return Derivation(rule="L_Impl", sequent=sequent, premises=[p1, p2], principal=f)

    # If all formulas are atomic and no atom is shared, the sequent is invalid.
    return None


# ============================================================================
# 5. Countermodel Generator
# ============================================================================


def find_countermodel(sequent: Sequent) -> Optional[dict[str, bool]]:
    """Compute a falsifying boolean valuation if sequent is invalid."""
    if prove_sequent(sequent) is not None:
        return None

    # Decompose sequent until an irreducible atomic branch is reached
    return _decompose_countermodel(sequent)


def _decompose_countermodel(sequent: Sequent) -> Optional[dict[str, bool]]:
    # Identity or False on left implies valid on this branch
    for f in sequent.gamma:
        if f in sequent.delta:
            return None
        if isinstance(f, Bot):
            return None
    for f in sequent.delta:
        if isinstance(f, Top):
            return None

    # L_And
    for i, f in enumerate(sequent.gamma):
        if isinstance(f, And):
            rem = list(sequent.gamma[:i] + sequent.gamma[i + 1 :]) + [f.left, f.right]
            return _decompose_countermodel(Sequent(rem, sequent.delta))

    # L_Not
    for i, f in enumerate(sequent.gamma):
        if isinstance(f, Not):
            rem = list(sequent.gamma[:i] + sequent.gamma[i + 1 :])
            return _decompose_countermodel(Sequent(rem, list(sequent.delta) + [f.inner]))

    # R_Or
    for i, f in enumerate(sequent.delta):
        if isinstance(f, Or):
            rem = list(sequent.delta[:i] + sequent.delta[i + 1 :]) + [f.left, f.right]
            return _decompose_countermodel(Sequent(sequent.gamma, rem))

    # R_Impl
    for i, f in enumerate(sequent.delta):
        if isinstance(f, Impl):
            rem_d = list(sequent.delta[:i] + sequent.delta[i + 1 :]) + [f.right]
            rem_g = list(sequent.gamma) + [f.left]
            return _decompose_countermodel(Sequent(rem_g, rem_d))

    # R_Not
    for i, f in enumerate(sequent.delta):
        if isinstance(f, Not):
            rem_d = list(sequent.delta[:i] + sequent.delta[i + 1 :])
            rem_g = list(sequent.gamma) + [f.inner]
            return _decompose_countermodel(Sequent(rem_g, rem_d))

    # R_And: branching (falsified if either premise is falsified)
    for i, f in enumerate(sequent.delta):
        if isinstance(f, And):
            rem = list(sequent.delta[:i] + sequent.delta[i + 1 :])
            cm1 = _decompose_countermodel(Sequent(sequent.gamma, rem + [f.left]))
            if cm1 is not None:
                return cm1
            return _decompose_countermodel(Sequent(sequent.gamma, rem + [f.right]))

    # L_Or: branching (falsified if either premise is falsified)
    for i, f in enumerate(sequent.gamma):
        if isinstance(f, Or):
            rem = list(sequent.gamma[:i] + sequent.gamma[i + 1 :])
            cm1 = _decompose_countermodel(Sequent(rem + [f.left], sequent.delta))
            if cm1 is not None:
                return cm1
            return _decompose_countermodel(Sequent(rem + [f.right], sequent.delta))

    # L_Impl: branching (falsified if either premise is falsified)
    for i, f in enumerate(sequent.gamma):
        if isinstance(f, Impl):
            rem = list(sequent.gamma[:i] + sequent.gamma[i + 1 :])
            cm1 = _decompose_countermodel(Sequent(rem, list(sequent.delta) + [f.left]))
            if cm1 is not None:
                return cm1
            return _decompose_countermodel(Sequent(rem + [f.right], sequent.delta))

    # Irreducible atomic sequent
    val: dict[str, bool] = {}
    for f in sequent.all_atoms():
        val[f] = False
    for f in sequent.gamma:
        if isinstance(f, Atom):
            val[f.name] = True
    for f in sequent.delta:
        if isinstance(f, Atom):
            val[f.name] = False

    return val


# ============================================================================
# 6. Derivation Verifier
# ============================================================================


def verify_derivation(tree: Derivation) -> tuple[bool, str]:
    """Verify that a derivation tree is structurally valid according to LK rules."""
    rule = tree.rule
    seq = tree.sequent
    prin = tree.principal
    prems = tree.premises

    if rule == "Ax":
        if len(prems) != 0:
            return False, "Ax rule must have 0 premises"
        if prin is None:
            return False, "Ax rule requires principal formula"
        if prin not in seq.gamma or prin not in seq.delta:
            return False, f"Ax principal {prin} must be in both antecedent and succedent"
        return True, "Valid Ax"

    if rule == "L_Bot":
        if len(prems) != 0:
            return False, "L_Bot must have 0 premises"
        if not any(isinstance(f, Bot) for f in seq.gamma):
            return False, "L_Bot requires Bot in antecedent"
        return True, "Valid L_Bot"

    if rule == "R_Top":
        if len(prems) != 0:
            return False, "R_Top must have 0 premises"
        if not any(isinstance(f, Top) for f in seq.delta):
            return False, "R_Top requires Top in succedent"
        return True, "Valid R_Top"

    if rule == "L_And":
        if len(prems) != 1:
            return False, "L_And must have 1 premise"
        if not isinstance(prin, And) or prin not in seq.gamma:
            return False, "L_And requires principal And in antecedent"
        p_seq = prems[0].sequent
        if prin.left not in p_seq.gamma or prin.right not in p_seq.gamma:
            return False, "L_And premise must contain both conjuncts in antecedent"
        return verify_derivation(prems[0])

    if rule == "R_And":
        if len(prems) != 2:
            return False, "R_And must have 2 premises"
        if not isinstance(prin, And) or prin not in seq.delta:
            return False, "R_And requires principal And in succedent"
        if prin.left not in prems[0].sequent.delta:
            return False, "R_And premise 1 must contain left conjunct"
        if prin.right not in prems[1].sequent.delta:
            return False, "R_And premise 2 must contain right conjunct"
        v1, m1 = verify_derivation(prems[0])
        if not v1:
            return False, m1
        return verify_derivation(prems[1])

    if rule == "L_Or":
        if len(prems) != 2:
            return False, "L_Or must have 2 premises"
        if not isinstance(prin, Or) or prin not in seq.gamma:
            return False, "L_Or requires principal Or in antecedent"
        if prin.left not in prems[0].sequent.gamma:
            return False, "L_Or premise 1 must contain left disjunct"
        if prin.right not in prems[1].sequent.gamma:
            return False, "L_Or premise 2 must contain right disjunct"
        v1, m1 = verify_derivation(prems[0])
        if not v1:
            return False, m1
        return verify_derivation(prems[1])

    if rule == "R_Or":
        if len(prems) != 1:
            return False, "R_Or must have 1 premise"
        if not isinstance(prin, Or) or prin not in seq.delta:
            return False, "R_Or requires principal Or in succedent"
        p_seq = prems[0].sequent
        if prin.left not in p_seq.delta or prin.right not in p_seq.delta:
            return False, "R_Or premise must contain both disjuncts in succedent"
        return verify_derivation(prems[0])

    if rule == "L_Impl":
        if len(prems) != 2:
            return False, "L_Impl must have 2 premises"
        if not isinstance(prin, Impl) or prin not in seq.gamma:
            return False, "L_Impl requires principal Impl in antecedent"
        if prin.left not in prems[0].sequent.delta:
            return False, "L_Impl premise 1 must contain antecedent formula in succedent"
        if prin.right not in prems[1].sequent.gamma:
            return False, "L_Impl premise 2 must contain consequent formula in antecedent"
        v1, m1 = verify_derivation(prems[0])
        if not v1:
            return False, m1
        return verify_derivation(prems[1])

    if rule == "R_Impl":
        if len(prems) != 1:
            return False, "R_Impl must have 1 premise"
        if not isinstance(prin, Impl) or prin not in seq.delta:
            return False, "R_Impl requires principal Impl in succedent"
        p_seq = prems[0].sequent
        if prin.left not in p_seq.gamma or prin.right not in p_seq.delta:
            return False, "R_Impl premise must have antecedent in gamma and consequent in delta"
        return verify_derivation(prems[0])

    if rule == "L_Not":
        if len(prems) != 1:
            return False, "L_Not must have 1 premise"
        if not isinstance(prin, Not) or prin not in seq.gamma:
            return False, "L_Not requires principal Not in antecedent"
        if prin.inner not in prems[0].sequent.delta:
            return False, "L_Not premise must have inner formula in succedent"
        return verify_derivation(prems[0])

    if rule == "R_Not":
        if len(prems) != 1:
            return False, "R_Not must have 1 premise"
        if not isinstance(prin, Not) or prin not in seq.delta:
            return False, "R_Not requires principal Not in succedent"
        if prin.inner not in prems[0].sequent.gamma:
            return False, "R_Not premise must have inner formula in antecedent"
        return verify_derivation(prems[0])

    return False, f"Unknown rule: {rule}"


# ============================================================================
# 7. High-Level Formula Prover API
# ============================================================================


def prove_formula(f: Formula) -> tuple[bool, Optional[Derivation], Optional[dict[str, bool]]]:
    """Test validity of a formula: |- f.

    Returns (is_valid, derivation, countermodel).
    """
    seq = Sequent([], [f])
    der = prove_sequent(seq)
    if der is not None:
        return True, der, None
    cm = find_countermodel(seq)
    return False, None, cm

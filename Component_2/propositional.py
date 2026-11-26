"""C2: propositional tautology checking for rule R1.

Uses formula decomposition and exhaustive truth-table evaluation.
Temporal expressions are treated as opaque Boolean units.
Optional valuation limits apply per subproblem.
"""
from itertools import product
from Component_1.formula import Atom, Not, And, Imp, Iff, Next, Always, Eventually, Until, Formula

OPAQUE = (Atom, Next, Always, Eventually, Until)
BOOLEAN_BINARY = (And, Imp, Iff)
VALUATION_LIMIT = 5000  # Maximum valuations per subproblem


class SolverResourceLimit(RuntimeError):
    """Raised when the valuation budget is exhausted."""


def propositional_atoms(f: Formula) -> frozenset[Formula]:
    """Collect distinct propositional units."""
    if isinstance(f, Not):
        return propositional_atoms(f.p)
    if isinstance(f, BOOLEAN_BINARY):
        return propositional_atoms(f.p) | propositional_atoms(f.q)
    if isinstance(f, OPAQUE):
        return frozenset({f})
    raise TypeError(f"unsupported formula: {f!r}")


def evaluate(f: Formula, valuation: dict[Formula, bool]) -> bool:
    """Evaluate a formula under a given valuation."""
    if isinstance(f, Not):
        return not evaluate(f.p, valuation)
    if isinstance(f, And):
        return evaluate(f.p, valuation) and evaluate(f.q, valuation)
    if isinstance(f, Imp):
        return not evaluate(f.p, valuation) or evaluate(f.q, valuation)
    if isinstance(f, Iff):
        return evaluate(f.p, valuation) == evaluate(f.q, valuation)
    if isinstance(f, OPAQUE):
        return valuation[f]
    raise TypeError(f"unsupported formula: {f!r}")


def reference_counterexample(f: Formula, node_limit: int | None = None) -> dict[Formula, bool] | None:
    """Return a falsifying valuation, or None if tautological."""
    units = sorted(propositional_atoms(f), key=repr)
    for i, values in enumerate(product((False, True), repeat=len(units))):
        if node_limit is not None and i >= node_limit:
            raise SolverResourceLimit("valuation budget exhausted")
        valuation = dict(zip(units, values))
        if not evaluate(f, valuation):
            return valuation
    return None


def _split_goal(f: Formula) -> tuple[Formula, ...] | None:
    """Decompose the conclusion while preserving its hypotheses.

    A & B   -> A, B
    A <-> B -> A -> B, B -> A
    ~~A     -> A

    Return None if no decomposition applies.
    """
    hypotheses = []
    conclusion = f
    while isinstance(conclusion, Imp):
        hypotheses.append(conclusion.p)
        conclusion = conclusion.q
    if isinstance(conclusion, And):
        pieces = (conclusion.p, conclusion.q)
    elif isinstance(conclusion, Iff):
        pieces = (Imp(conclusion.p, conclusion.q), Imp(conclusion.q, conclusion.p))
    elif isinstance(conclusion, Not) and isinstance(conclusion.p, Not):
        pieces = (conclusion.p.p,)
    else:
        return None

    def under_hypotheses(piece: Formula) -> Formula:
        for hypothesis in reversed(hypotheses):
            piece = Imp(hypothesis, piece)
        return piece

    return tuple(under_hypotheses(piece) for piece in pieces)


def _complete_witness(witness: dict[Formula, bool], f: Formula) -> dict[Formula, bool]:
    """Assign False to missing propositional units."""
    return {unit: witness.get(unit, False) for unit in propositional_atoms(f)}


def counterexample(f: Formula, *,
                   node_limit: int | None = VALUATION_LIMIT) -> dict[Formula, bool] | None:
    """Find a counterexample using decomposition and exhaustive evaluation.

    Raise SolverResourceLimit if a subproblem exceeds its budget.
    """
    if node_limit is not None and (type(node_limit) is not int or node_limit < 0):
        raise ValueError("node_limit must be a nonnegative integer or None")
    if isinstance(f, (Imp, Iff)) and f.p == f.q:
        return None  # A -> A and A <-> A are propositional tautologies.
    parts = _split_goal(f)
    if parts is not None:
        for part in parts:
            witness = counterexample(part, node_limit=node_limit)
            if witness is not None:
                completed = _complete_witness(witness, f)
                # Splitting rules guarantee the full formula is falsified.
                assert not evaluate(f, completed)
                return completed
        return None
    return reference_counterexample(f, node_limit)


def is_tautology(f: Formula, *, node_limit: int | None = VALUATION_LIMIT) -> bool:
    """Check whether a formula is a propositional tautology."""
    return counterexample(f, node_limit=node_limit) is None


"""C2: two exact decision procedures for rule R1.

A temporal expression (Next/Always/Eventually/Until) is an opaque Boolean
unit; only Not/And/Imp/Iff are interpreted propositionally, as in
Rules.dfy's PropEval. Both algorithms decide validity by searching for a
valuation that makes the formula false.

* bits: bit-parallel exhaustive truth table (fast for modest unit counts).
* dpll: Tseitin CNF for the negation of the formula, then DPLL SAT solving.
* reference: the original Python truth table, retained as a test oracle.

No external SAT solver is trusted. These algorithms are tested, not formally
verified; Dafny C0 verification does not certify the Python implementation.
"""
from functools import lru_cache
from itertools import product
from Component_1.formula import Atom, Not, And, Imp, Iff, Next, Always, Eventually, Until, Formula

OPAQUE = (Atom, Next, Always, Eventually, Until)
BOOLEAN_BINARY = (And, Imp, Iff)
BIT_LIMIT = 26  # bounded bit-mask size; 2**26 bits per full mask
DPLL_NODE_LIMIT = 5000  # default node cap; None disables the cap


class SolverResourceLimit(RuntimeError):
    """SAT status UNKNOWN: search budget exhausted (never interpret as UNSAT)."""



def propositional_atoms(f: Formula) -> frozenset[Formula]:
    if isinstance(f, Not):
        return propositional_atoms(f.p)
    if isinstance(f, BOOLEAN_BINARY):
        return propositional_atoms(f.p) | propositional_atoms(f.q)
    if isinstance(f, OPAQUE):
        return frozenset({f})
    raise TypeError(f"unsupported formula: {f!r}")


def evaluate(f: Formula, valuation: dict[Formula, bool]) -> bool:
    """Single-valuation specification/reference evaluator."""
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


def reference_counterexample(f: Formula) -> dict[Formula, bool] | None:
    """Slow exhaustive oracle, used to cross-check optimized implementations."""
    units = sorted(propositional_atoms(f), key=repr)
    for values in product((False, True), repeat=len(units)):
        valuation = dict(zip(units, values))
        if not evaluate(f, valuation):
            return valuation
    return None


def _bit_counterexample(f: Formula, units: tuple[Formula, ...]) -> dict[Formula, bool] | None:
    """Each bit position corresponds to a valuation. No Python loop over rows."""
    n = len(units)
    rows = 1 << n
    all_ones = (1 << rows) - 1
    # For unit i, bit k encodes bit i of assignment index k.
    def unit_mask(i: int) -> int:
        block = 1 << i
        pattern = ((1 << block) - 1) << block
        period = 2 * block
        while period < rows:
            pattern |= pattern << period
            period *= 2
        return pattern

    unit_masks = {u: unit_mask(i) for i, u in enumerate(units)}

    def mask(x: Formula) -> int:
        if isinstance(x, Not):
            return all_ones ^ mask(x.p)
        if isinstance(x, And):
            return mask(x.p) & mask(x.q)
        if isinstance(x, Imp):
            return (all_ones ^ mask(x.p)) | mask(x.q)
        if isinstance(x, Iff):
            return all_ones ^ (mask(x.p) ^ mask(x.q))
        if isinstance(x, OPAQUE):
            return unit_masks[x]
        raise TypeError(f"unsupported formula: {x!r}")

    false_rows = all_ones ^ mask(f)
    if false_rows == 0:
        return None
    # Lowest set bit gives a concrete falsifying valuation.
    k = (false_rows & -false_rows).bit_length() - 1
    return {u: bool((k >> i) & 1) for i, u in enumerate(units)}


class _Tseitin:
    """Equisatisfiable CNF encoding with a variable for every Boolean node."""
    def __init__(self, units: tuple[Formula, ...]):
        self.var = {u: i + 1 for i, u in enumerate(units)}
        self.next_var = len(units) + 1
        self.clauses: list[tuple[int, ...]] = []

    def encode(self, f: Formula) -> int:
        if f in self.var:
            return self.var[f]
        if isinstance(f, Not):
            return -self.encode(f.p)
        if not isinstance(f, BOOLEAN_BINARY):
            raise TypeError(f"unsupported formula: {f!r}")
        a, b = self.encode(f.p), self.encode(f.q)
        if isinstance(f, And) and a == b:
            self.var[f] = a
            return a
        v = self.next_var
        self.next_var += 1
        self.var[f] = v
        if isinstance(f, And):
            self.clauses.extend(((-v, a), (-v, b), (v, -a, -b)))
        elif isinstance(f, Imp):
            if a == b:
                self.clauses.append((v,))
            else:
                self.clauses.extend(((-v, -a, b), (v, a), (v, -b)))
        else:  # Iff
            if a == b:
                self.clauses.append((v,))
                return v
            self.clauses.extend(((-v, -a, b), (-v, a, -b), (v, a, b), (v, -a, -b)))
        return v


def _simplify(clauses: list[tuple[int, ...]], lit: int) -> list[tuple[int, ...]]:
    """Assign lit=True: discard satisfied clauses and remove false literals."""
    return [tuple(x for x in c if x != -lit) for c in clauses if lit not in c]


def _dpll(clauses: list[tuple[int, ...]], assignment: dict[int, bool],
          budget: list[int | None]) -> dict[int, bool] | None:
    if budget[0] is not None:
        budget[0] -= 1
    if budget[0] is not None and budget[0] < 0:
        raise SolverResourceLimit("DPLL search budget exhausted; tautology status unknown")
    while True:
        if not clauses:
            return assignment
        if any(len(c) == 0 for c in clauses):
            return None
        unit = next((c[0] for c in clauses if len(c) == 1), None)
        if unit is None:
            # Pure-literal elimination is satisfiability preserving.
            literals = {lit for clause in clauses for lit in clause}
            unit = next((lit for lit in sorted(literals, key=lambda x: (abs(x), x))
                         if -lit not in literals), None)
        if unit is None:
            break
        var, value = abs(unit), unit > 0
        if var in assignment and assignment[var] != value:
            return None
        assignment[var] = value
        clauses = _simplify(clauses, unit)

    # Deterministic branching. If either branch satisfies CNF, return a model.
    var = abs(clauses[0][0])
    for value in (True, False):
        lit = var if value else -var
        extended = dict(assignment)
        extended[var] = value
        result = _dpll(_simplify(clauses, lit), extended, budget)
        if result is not None:
            return result
    return None


def _dpll_counterexample(f: Formula, units: tuple[Formula, ...],
                         node_limit: int | None) -> dict[Formula, bool] | None:
    encoder = _Tseitin(units)
    top = encoder.encode(f)
    encoder.clauses.append((-top,))  # SAT(¬f) iff f is not a tautology
    model = _dpll(encoder.clauses, {}, [node_limit])
    if model is None:
        return None
    # Unassigned unit variables can be arbitrarily completed: all CNF
    # clauses are already satisfied by the partial assignment.
    return {u: model.get(i + 1, False) for i, u in enumerate(units)}


def _split_goal(f: Formula) -> tuple[Formula, ...] | None:
    """Exact propositional reductions, including curried hypotheses.

    A & B                 -> A, B
    A <-> B               -> A -> B, B -> A
    ~~A                   -> A
    H1 -> ... -> Hk -> C  -> H1 -> ... -> Hk -> Ci for each reduction Ci of C

    A split only occurs if the final consequent actually has a reducible
    outermost form. Rebuilding the *same* chain without a reduction would
    cause nontermination. The hypotheses remain unchanged, so each returned
    formula is logically implied by the original and the original is a
    tautology exactly when every returned formula is a tautology.
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
    """Fill units not mentioned in a split proof (arbitrary truth values)."""
    return {unit: witness.get(unit, False) for unit in propositional_atoms(f)}


def counterexample(f: Formula, method: str = "auto", *,
                   node_limit: int | None = DPLL_NODE_LIMIT) -> dict[Formula, bool] | None:
    """Return a falsifying valuation, or None if tautological.

    A raised SolverResourceLimit means UNKNOWN, never 'tautological'.
    `node_limit=None` makes DPLL exhaustive (but potentially very slow).
    Auto mode first applies exact, sound splitting to conjunctions,
    equivalences and double negations, including under curried implications.
    """
    if method not in {"auto", "bits", "dpll", "reference"}:
        raise ValueError(f"unknown tautology-checking method: {method!r}")
    if node_limit is not None and (type(node_limit) is not int or node_limit < 0):
        raise ValueError("node_limit must be a nonnegative integer or None")
    if method == "auto" and isinstance(f, (Imp, Iff)) and f.p == f.q:
        return None  # A -> A and A <-> A are propositional tautologies.
    if method == "auto":
        parts = _split_goal(f)
        if parts is not None:
            for part in parts:
                witness = counterexample(part, method="auto", node_limit=node_limit)
                if witness is not None:
                    completed = _complete_witness(witness, f)
                    # Splitting rules guarantee the full formula is falsified.
                    assert not evaluate(f, completed)
                    return completed
            return None
    units = tuple(sorted(propositional_atoms(f), key=repr))
    if method == "reference":
        return reference_counterexample(f)
    if method == "auto":
        method = "bits" if len(units) <= BIT_LIMIT else "dpll"
    if method == "bits":
        if len(units) > BIT_LIMIT:
            raise ValueError(f"bit-parallel method limited to {BIT_LIMIT} units; use dpll")
        return _bit_counterexample(f, units)
    return _dpll_counterexample(f, units, node_limit)


@lru_cache(maxsize=4096)
def _cached_tautology_status(f: Formula, method: str, node_limit: int | None) -> bool | None:
    """Cache True / False / UNKNOWN (None) rather than exceptions."""
    try:
        return counterexample(f, method=method, node_limit=node_limit) is None
    except SolverResourceLimit:
        return None


def is_tautology(f: Formula, method: str = "auto", *,
                 node_limit: int | None = DPLL_NODE_LIMIT) -> bool:
    """C2 tautology predicate; an UNKNOWN result raises SolverResourceLimit."""
    if node_limit is not None and (type(node_limit) is not int or node_limit < 0):
        raise ValueError("node_limit must be a nonnegative integer or None")
    status = _cached_tautology_status(f, method, node_limit)
    if status is None:
        raise SolverResourceLimit("DPLL search budget exhausted; tautology status unknown")
    return status


# Preserve the standard cache inspection API used by tests and diagnostics.
is_tautology.cache_clear = _cached_tautology_status.cache_clear
is_tautology.cache_info = _cached_tautology_status.cache_info

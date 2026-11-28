
"""Component 4: Benchmark suite for evaluating the LTL theorem prover."""

from dataclasses import dataclass

from Component_1.formula import (
    Formula, Atom, Not, And, Imp, Iff,
    Next, Always, Eventually, Until
)


@dataclass(frozen=True)
class Benchmark:
    name: str
    formula: Formula
    valid: bool
    category: str
    difficulty: str
    justification: str
    in_fragment: bool = True


# atomic propositions
p = Atom(0)
q = Atom(1)
r = Atom(2)

# encode a OR b as (NOT a) -> b.
def Or(a: Formula, b: Formula) -> Formula:
    return Imp(Not(a), b)


# count all nodes in the formula's abstract syntax tree and repeated subformulas are counted separately
def formula_size(f: Formula) -> int:
    if isinstance(f, Atom):
        return 1

    if isinstance(f, (Not, Next, Always, Eventually)):
        return 1 + formula_size(f.p)

    if isinstance(f, (And, Imp, Iff, Until)):
        return 1 + formula_size(f.p) + formula_size(f.q)

    raise TypeError(f"Unknown formula: {f!r}")


BENCHMARKS = [

    # 1. propositional logic (10 formulas)

    Benchmark(
        "P01", Imp(p, p), True,
        "Propositional", "Easy",
        "Reflexivity of implication."
    ),

    Benchmark(
        "P02", Or(p, Not(p)), True,
        "Propositional", "Easy",
        "Law of excluded middle."
    ),

    Benchmark(
        "P03", Imp(And(p, q), p), True,
        "Propositional", "Easy",
        "Conjunction elimination."
    ),

    Benchmark(
        "P04", Iff(Not(Not(p)), p), True,
        "Propositional", "Easy",
        "Double negation elimination."
    ),

    Benchmark(
        "P05",
        Imp(And(Imp(p, q), Imp(q, r)), Imp(p, r)),
        True, "Propositional", "Medium",
        "Transitivity of implication."
    ),

    Benchmark(
        "P06", Imp(p, q), False,
        "Propositional", "Easy",
        "Counterexample: p=true, q=false."
    ),

    Benchmark(
        "P07", And(p, Not(p)), False,
        "Propositional", "Easy",
        "Contradiction under every valuation."
    ),

    Benchmark(
        "P08", Iff(p, q), False,
        "Propositional", "Easy",
        "Counterexample: p=true, q=false."
    ),

    Benchmark(
        "P09", Imp(p, And(p, q)), False,
        "Propositional", "Easy",
        "Counterexample: p=true, q=false."
    ),

    Benchmark(
        "P10", Imp(Imp(p, q), Imp(q, p)), False,
        "Propositional", "Medium",
        "Counterexample: p=false, q=true."
    ),

    # 2. basic temporal operators (12 formulas)

    Benchmark(
        "T01", Imp(Always(p), p), True,
        "Basic Temporal", "Easy",
        "Always includes the current time."
    ),

    Benchmark(
        "T02", Imp(p, Eventually(p)), True,
        "Basic Temporal", "Easy",
        "Eventually includes the current time."
    ),

    Benchmark(
        "T03", Imp(Always(p), Next(p)), True,
        "Basic Temporal", "Easy",
        "Always includes the next time step."
    ),

    Benchmark(
        "T04", Imp(Always(p), Eventually(p)), True,
        "Basic Temporal", "Easy",
        "If p always holds, it eventually holds."
    ),

    Benchmark(
        "T05", Imp(Next(p), Eventually(p)), True,
        "Basic Temporal", "Easy",
        "Time t+1 is a witness for Eventually."
    ),

    Benchmark(
        "T06", Iff(Eventually(p), Not(Always(Not(p)))),
        True, "Basic Temporal", "Easy",
        "Duality of Eventually and Always (A1)."
    ),

    Benchmark(
        "T07", Iff(Next(Not(p)), Not(Next(p))),
        True, "Basic Temporal", "Easy",
        "Next commutes with negation (A3)."
    ),

    Benchmark(
        "T08", Imp(Always(p), Next(Always(p))),
        True, "Basic Temporal", "Medium",
        "If p always holds now, it always holds from t+1."
    ),

    Benchmark(
        "T09", Imp(p, Always(p)), False,
        "Basic Temporal", "Easy",
        "p holds at t=0 but is false thereafter."
    ),

    Benchmark(
        "T10", Imp(Eventually(p), Always(p)), False,
        "Basic Temporal", "Easy",
        "p is false at t=0 and true thereafter."
    ),

    Benchmark(
        "T11", Imp(Next(p), p), False,
        "Basic Temporal", "Easy",
        "p is false at t=0 and true at t=1."
    ),

    Benchmark(
        "T12", Imp(p, Next(p)), False,
        "Basic Temporal", "Easy",
        "p is true at t=0 and false at t=1."
    ),

    # 3. temporal distribution (12 formulas)

    Benchmark(
        "D01",
        Imp(Always(And(p, q)), And(Always(p), Always(q))),
        True, "Distribution", "Medium",
        "If both hold at every time, each holds at every time."
    ),

    Benchmark(
        "D02",
        Imp(And(Always(p), Always(q)), Always(And(p, q))),
        True, "Distribution", "Medium",
        "Both propositions hold at every time."
    ),

    Benchmark(
        "D03",
        Iff(Always(And(p, q)), And(Always(p), Always(q))),
        True, "Distribution", "Medium",
        "Always distributes over conjunction."
    ),

    Benchmark(
        "D04",
        Iff(Next(And(p, q)), And(Next(p), Next(q))),
        True, "Distribution", "Medium",
        "Next distributes over conjunction."
    ),

    Benchmark(
        "D05",
        Iff(Next(Or(p, q)), Or(Next(p), Next(q))),
        True, "Distribution", "Medium",
        "Next distributes over disjunction."
    ),

    Benchmark(
        "D06",
        Iff(Eventually(Or(p, q)),
            Or(Eventually(p), Eventually(q))),
        True, "Distribution", "Medium",
        "Eventually distributes over disjunction."
    ),

    Benchmark(
        "D07",
        Imp(Always(Imp(p, q)),
            Imp(Eventually(p), Eventually(q))),
        True, "Distribution", "Medium",
        "Any future witness for p is also a witness for q."
    ),

    Benchmark(
        "D08",
        Iff(Next(Imp(p, q)), Imp(Next(p), Next(q))),
        True, "Distribution", "Medium",
        "Both sides evaluate the implication at t+1."
    ),

    Benchmark(
        "D09",
        Imp(Always(Or(p, q)), Or(Always(p), Always(q))),
        False, "Distribution", "Medium",
        "p and q alternate, so neither holds forever."
    ),

    Benchmark(
        "D10",
        Imp(And(Eventually(p), Eventually(q)),
            Eventually(And(p, q))),
        False, "Distribution", "Medium",
        "p and q alternate and never hold simultaneously."
    ),

    Benchmark(
        "D11",
        Imp(Always(Imp(p, q)),
            Imp(Eventually(q), Eventually(p))),
        False, "Distribution", "Medium",
        "p is always false and q is always true."
    ),

    Benchmark(
        "D12",
        Imp(Imp(Always(p), Always(q)),
            Always(Imp(p, q))),
        False, "Distribution", "Hard",
        "p holds only at t=0; q is always false."
    ),

    # 4. nested temporal operators (10 formulas)

    Benchmark(
        "N01", Imp(Always(p), Always(Always(p))),
        True, "Nested Temporal", "Hard",
        "Every suffix of an always-p trace satisfies always p."
    ),

    Benchmark(
        "N02", Imp(Eventually(Eventually(p)), Eventually(p)),
        True, "Nested Temporal", "Hard",
        "A future witness of a future witness is a future witness."
    ),

    Benchmark(
        "N03", Imp(Always(Always(p)), Always(p)),
        True, "Nested Temporal", "Medium",
        "Always includes the current time."
    ),

    Benchmark(
        "N04", Imp(Next(Eventually(p)), Eventually(p)),
        True, "Nested Temporal", "Medium",
        "A witness after t+1 is also a witness after t."
    ),

    Benchmark(
        "N05", Imp(Eventually(Always(p)), Always(Eventually(p))),
        True, "Nested Temporal", "Hard",
        "If p eventually holds forever, every suffix contains p."
    ),

    Benchmark(
        "N06", Imp(Always(Next(p)), Next(Always(p))),
        True, "Nested Temporal", "Hard",
        "Both sides require p at every time from t+1 onward."
    ),

    Benchmark(
        "N07", Imp(Always(Eventually(p)), Eventually(Always(p))),
        False, "Nested Temporal", "Hard",
        "p alternates forever between true and false."
    ),

    Benchmark(
        "N08", Imp(Next(Always(p)), Always(p)),
        False, "Nested Temporal", "Medium",
        "p is false initially but true from t=1 onward."
    ),

    Benchmark(
        "N09", Imp(Eventually(p), Next(Eventually(p))),
        False, "Nested Temporal", "Medium",
        "p holds only at t=0."
    ),

    Benchmark(
        "N10", Imp(Eventually(Always(p)), Always(p)),
        False, "Nested Temporal", "Medium",
        "p is false initially but true from t=1 onward."
    ),

    # 5. induction and complex formulas (10)

    Benchmark(
        "I01",
        Imp(Always(Imp(p, Next(p))), Imp(p, Always(p))),
        True, "Induction and Complex", "Hard",
        "Temporal induction axiom (A6)."
    ),

    Benchmark(
        "I02",
        Imp(And(p, Always(Imp(p, Next(p)))), Always(p)),
        True, "Induction and Complex", "Hard",
        "Base case and persistent induction step imply Always(p)."
    ),

    Benchmark(
        "I03",
        Imp(And(p, Next(Always(p))), Always(p)),
        True, "Induction and Complex", "Hard",
        "p holds now and at every subsequent time."
    ),

    Benchmark(
        "I04", Imp(Always(p), Always(Next(p))),
        True, "Induction and Complex", "Hard",
        "Always(p) implies p at every successor time."
    ),

    Benchmark(
        "I05",
        Imp(And(Always(p), And(Always(q), Always(r))),
            Always(And(p, And(q, r)))),
        True, "Induction and Complex", "Hard",
        "All three propositions hold at every time."
    ),

    Benchmark(
        "I06",
        Imp(Always(Imp(p, q)),
            Imp(Always(p), Always(q))),
        True, "Induction and Complex", "Medium",
        "Distribution of Always over implication (A2)."
    ),

    Benchmark(
        "I07",
        Imp(And(p, Imp(p, Next(p))), Always(p)),
        False, "Induction and Complex", "Hard",
        "p holds at t=0 and t=1, but not at t=2."
    ),

    Benchmark(
        "I08",
        Imp(Always(Imp(p, Next(p))), Always(p)),
        False, "Induction and Complex", "Hard",
        "p is always false; the induction step is vacuously true."
    ),

    Benchmark(
        "I09",
        Imp(And(p, Next(p)), Always(p)),
        False, "Induction and Complex", "Medium",
        "p holds at t=0 and t=1, but is false thereafter."
    ),

    Benchmark(
        "I10",
        Imp(And(Always(p), Eventually(q)), Always(And(p, q))),
        False, "Induction and Complex", "Hard",
        "p is always true; q holds only at t=0."
    ),

    # 6. weak until (6 formulas)

    Benchmark(
        "U01", Imp(Always(p), Until(p, q)),
        True, "Weak Until", "Medium",
        "Weak until permits p to hold forever (A7).",
        in_fragment=False
    ),

    Benchmark(
        "U02", Imp(q, Until(p, q)),
        True, "Weak Until", "Medium",
        "q holds now, so the until condition is satisfied.",
        in_fragment=False
    ),

    Benchmark(
        "U03",
        Iff(Until(p, q), Or(q, And(p, Next(Until(p, q))))),
        True, "Weak Until", "Hard",
        "Recursive expansion of weak until (A8).",
        in_fragment=False
    ),

    Benchmark(
        "U04", Imp(Until(p, q), Eventually(q)),
        False, "Weak Until", "Medium",
        "p is always true and q is always false.",
        in_fragment=False
    ),

    Benchmark(
        "U05", Imp(Until(p, q), p),
        False, "Weak Until", "Medium",
        "q is true initially while p is false.",
        in_fragment=False
    ),

    Benchmark(
        "U06", Imp(Eventually(q), Until(p, q)),
        False, "Weak Until", "Hard",
        "p is always false and q first holds at t=1.",
        in_fragment=False
    ),
]


# print a summary when this module is run directly
if __name__ == "__main__":
    from collections import Counter

    print(f"Total benchmarks: {len(BENCHMARKS)}")
    print(f"Valid: {sum(b.valid for b in BENCHMARKS)}")
    print(f"Invalid: {sum(not b.valid for b in BENCHMARKS)}")
    print(f"In fragment: {sum(b.in_fragment for b in BENCHMARKS)}")
    print(f"Outside fragment: {sum(not b.in_fragment for b in BENCHMARKS)}")

    print("\nBy category:")
    for category, count in Counter(
        b.category for b in BENCHMARKS
    ).items():
        print(f"  {category}: {count}")

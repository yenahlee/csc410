# CSC410 — Axiomatic LTL Theorem Prover (C0, C1, C2, C3)

This folder packages the verified soundness foundation (C0) and executable
proof-checking (C1) / propositional reasoning (C2) implementation. All Python
commands below are run **from this repository root**, using Python 3.10+.
No additional Python packages are required.

## Layout

```
CSC410_project/
├── Component_0/
│   ├── LTL.dfy                # LTL syntax and semantic validity
│   ├── Axioms.dfy             # soundness proofs of A1–A8
│   ├── Rules.dfy              # R1–R3 and PropTautology specification
│   └── Soundness.dfy          # derivation tree and soundness theorem
├── Component_1/
│   ├── __init__.py
│   ├── formula.py             # immutable Python LTL AST / JSON format
│   ├── axioms.py              # instances of A1–A8
│   ├── checker.py             # numbered derivation validator / CLI
│   └── examples/              # JSON proofs for acceptance and rejection
├── Component_2/
│   ├── __init__.py
│   └── propositional.py       # decomposition and exhaustive truth-table evaluation
├── Component_3/
│   ├── search.py              # proof search, writes proofs in the C1 format
│   └── test_search.py         # search tests
└── README.md
```

Folders `Component_1` and `Component_2` are Python packages; their `__init__.py`
files are present. Both import the same `Component_1.formula` classes. Do not
run Python scripts from inside a component folder; run them as **modules**
from the project root to ensure imports resolve consistently.

## Verify and run

Run the proof checker from the repository root.

Check a valid derivation:

```bash
python3 -m Component_1.checker Component_1/examples/02_valid_r3.json
```

Expected result: `ACCEPT`.

Check an invalid derivation:

```bash
python3 -m Component_1.checker Component_1/examples/12_invalid_r1.json
```

Expected result: `REJECT`.

The `Component_1/examples/` directory contains 18 example derivations covering A1–A8, R1–R3, and incorrect proof steps.

Check all C0 files from the `Component_0` folder (Dafny 4.x):

```bash
cd Component_0
dafny verify --verify-included-files Soundness.dfy
cd ..
```

If Dafny is installed only through VS Code, invoke its DLL with `dotnet` in place of `dafny`.

## C1 proof format

`checker.py` expects JSON with a `goal` and a list of `lines`:

```json
{
  "goal": {"op":"Always", "p":{"op":"Imp", "p":{"op":"Atom","id":0}, "q":{"op":"Atom","id":0}}},
  "lines": [
    {"rule":"R1", "formula":{"op":"Imp", "p":{"op":"Atom","id":0}, "q":{"op":"Atom","id":0}}},
    {"rule":"R3", "refs":[0], "formula":{"op":"Always", "p":{"op":"Imp", "p":{"op":"Atom","id":0}, "q":{"op":"Atom","id":0}}}}
  ]
}
```

References are **zero-based** and must point to strictly earlier lines.
Axiom lines have `params` in the precise metavariable order of the schema.
R2 has `refs:[antecedent_index, implication_index]`; R3 has one reference.
The last line must be structurally identical to `goal`. CLI examples may
contain an `expected_accept` annotation, ignored by the CLI.

## C2 backend design

- Atomic propositions and distinct outermost temporal expressions are
  treated as opaque Boolean units. Structurally identical units share
  the same Boolean value.

- C2 decomposes conclusions of the form `And(A,B)`, `Iff(A,B)`, and
  `Not(Not(A))`, including under curried hypotheses
  `H1 -> ... -> Hk -> conclusion`. Trivial `Imp(X,X)` / `Iff(X,X)`
  are recognized directly. Each piece is checked recursively.
  The decompositions preserve validity and counterexamples.

- Each remaining subproblem is checked using exhaustive truth-table
  evaluation. A falsifying valuation establishes that the formula is
  not a propositional tautology. If all valuations satisfy the formula,
  it is a tautology. Counterexamples from decomposed subproblems are
  extended to the original formula by assigning False to missing units.

- C1 runs **exact checking by default**, with `node_limit=None`.
  C3 uses a limit of **5,000 valuations per subproblem** during proof
  search. Budget exhaustion raises `SolverResourceLimit` rather than
  returning a Boolean result. The limit applies only to exhaustive
  evaluation, not to the identity shortcut or the entire proof search.

- The C1 CLI performs unlimited truth-table evaluation by default.
  Optional valuation limits remain available through the Python API.

CLI verdict exit codes: `0` = ACCEPT; `1` = REJECT.

The C1 checker returns **exactly two verification outcomes**:

- `ACCEPT`: every line is justified and the last line matches
  the requested goal.
- `REJECT`: an invalid proof step, malformed proof, goal mismatch,
  or handled resource limitation prevents successful verification.

When a handled resource limitation prevents verification from
completing, C1 conservatively rejects the derivation and reports
the reason. This preserves soundness but may result in the rejection
of a valid derivation.

**Limitations:** A resource-related rejection does not establish
that the formula or derivation is mathematically invalid.
Exhaustive truth-table evaluation may require 2^n valuations for a
subproblem with n distinct propositional units. Decomposition can
reduce this cost, but worst-case time remains exponential.
The default exact mode does not guarantee verification within a
practical amount of time or memory, and Python recursion limits may
still be exceeded. Handled recursion errors result in conservative
rejection rather than acceptance. Performance varies by formula shape.

## Verification boundaries and integration

C0's Dafny specifications prove soundness for the **formal**
derivation tree. The Python implementations of C1 and C2 are
not themselves formally verified.

They were tested during development using example derivations,
propositional reasoning and decomposition tests, counterexample
reconstruction tests, resource-limit tests, and integration tests.
The submitted examples demonstrate acceptance and rejection of
candidate derivations.

In particular, translating the Dafny formula datatype, axiom
instance descriptions, and derivation tree into Python objects
and a flat numbered proof is a manual trust boundary.

C2 implements R1 by treating atomic propositions and distinct
outermost temporal expressions as opaque propositional variables,
matching C0's `PropEval` semantics. Axioms follow `Soundness.dfy`,
with A8's logically equivalent implication formulation and
**weak until**.

C3 imports `check_derivation` and `ProofLine` from C1.
It uses `node_limit=5000` for propositional tautology checks during
proof search, now limiting valuations per subproblem. If the budget
is exceeded, the corresponding tautology check fails for search purposes.

Final candidate proofs are checked using the default
`node_limit=None`. Resource-related rejections should be
distinguished from logically incorrect derivations in evaluation
using the reported rejection reason.

Dafny verification of C0 does **not** certify the Python checker
or establish the completeness of the implementation.

The runtime checker's key intended safety invariant is:
no R1 line is accepted unless C2 has completed a check establishing
propositional tautologicity.

## C3 search

Takes a goal and finds a proof for it in the C1 format. Every proof it finds
gets rechecked by C1 before it's printed, so the search can fail to find a
proof but it never outputs a wrong one.

```bash
python -m Component_3.search goal.json --show --out proof.json
python -m unittest Component_3.test_search
```

`goal.json` is either `{"goal": FORMULA}` or just the formula, same format as
C1. `--show` prints the lines, `--out` saves the proof JSON. Exit code is 0 if
it found a proof and C1 accepted it, 1 if nothing was found.

From python:

```python
from Component_3.search import search
from Component_1.checker import check_derivation

lines = search(goal)   # list of ProofLine, or None if not found
check_derivation(goal, lines)
```

Below, `->` is implies, `&` is and, `~` is not.

### How it works

- Works backwards from the goal. For a goal `H -> C` it looks at the top
  symbol of each side and picks a recipe for that shape, which turns the goal
  into smaller goals. Everything inside each side is treated as one
  proposition until we strip down to it, same idea as how C2 handles R1.
- A goal is done when it's a tautology (one R1 line, checked by C2).
- On the way back up each recipe writes the lines for its step. Every line is
  one rule, and plain logic steps join at most 2 earlier lines (an R1
  tautology then R2s), so nothing gets compressed into one line.
- Rewrites, one way so they can't undo each other:
  - `eventually x` becomes `~ always ~x` (A1)
  - `~ next x` becomes `next ~x` (A3)
  - `~~x` becomes `x`
  - `~(a -> b)` becomes `a & ~b`
- Strips:
  - `always a -> always b` needs `a -> b` (A2)
  - `next a -> next b` needs `a -> b` (A4)
  - `~a -> ~b` flips to `b -> a`
  - conjunctions and iff split into two goals, and an arrow on the left (a
    disjunction) splits into two cases
- Chains of hypotheses like `always p -> (always q -> always (p & q))` get
  merged from the inside out while both sides have the same operator, and
  stop when they don't.
- A5 is used when we have `always x` and need something about next
  (`next x & next always x`) or about now (`x`). Only the part we need gets
  added.
- A6 (induction) is the last thing tried for `H -> always C`. The invariant
  is `C` or `H`, and it's only used once per branch.
- Three caches: goals already proved, goals that failed, and goals on the
  current path so it never loops.

### Boundary

The fragment we target is propositional plus always, eventually and next, no
until. Induction is used at most once per branch and the invariant has to be
the conclusion or the hypothesis.

On our test set it proves 26/26 valid formulas that don't need induction, 5/7
that do, and 0/10 invalid ones. The two it misses:

- `(p & next always p) -> always p`: the right invariant is a candidate, but
  proving its step needs splitting a `&` inside a next, and we only look at
  the outer layer.
- `always next p -> next always p`: the conclusion starts with next not
  always, so induction never gets tried. The induction would have to happen
  one step in the future.

### Tradeoff

We picked convergence over completeness. The search always stops: goals stay
under a size bound that comes from the input, the loop guard stops a path from
repeating a goal, and every node only has finitely many options, so the search
tree is finite. Valid goals take a few ms, failing goals are the slow case
(around 1s for a chain of 10 hypotheses that doesn't hold).

What we gave up for that:

- Induction once per branch with only 2 invariant candidates, so goals that
  need a different invariant or nested induction aren't found.
- Only looking at the outer layer, so reasoning inside a next or always
  without stripping it first is out of reach.
- Merging `always a -> always b` into `always (a -> b)` proves something
  stronger, so in theory it can miss a proof.
- Remembering failures can rarely hide a proof, if the failure only happened
  because the loop guard cut a branch.
- Tautology checks during search use C2's limit of 5,000 valuations per
  subproblem. Budget exhaustion counts as a failed search attempt.

None of these let a wrong proof through, they only mean some valid goals
come back as not found.

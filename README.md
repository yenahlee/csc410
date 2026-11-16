# CSC410 — Axiomatic LTL Theorem Prover (C0, C1, C2)

This folder packages the verified soundness foundation (C0) and executable
proof-checking (C1) / propositional reasoning (C2) implementation. All Python
commands below are run **from this repository root**, using Python 3.10+.
No additional Python packages are required.

## Layout

```
CSC410_project_v5/
├── Component_0/
│   ├── LTL.dfy                # LTL syntax and semantic validity
│   ├── Axioms.dfy             # soundness proofs of A1–A8
│   ├── Rules.dfy              # R1–R3 and PropTautology specification
│   └── Soundness.dfy          # derivation tree and soundness theorem
├── Component_1/
│   ├── formula.py             # immutable Python LTL AST / JSON format
│   ├── axioms.py              # instances of A1–A8
│   ├── checker.py             # numbered derivation validator / CLI
│   ├── test_checker.py        # checker tests
│   ├── generate_examples.py   # regenerate example proofs
│   └── examples/              # JSON proofs for acceptance and rejection
├── Component_2/
│   ├── propositional.py       # reference, bit-parallel, and DPLL backends
│   ├── test_propositional.py  # basic propositional tests
│   ├── test_backends.py       # differential, splitting, and budget tests
│   └── benchmark_c2.py       # reproducible basic timing benchmark
└── README.md
```

Folders `Component_1` and `Component_2` are Python packages; their `__init__.py`
files are present. Both import the same `Component_1.formula` classes. Do not
run Python scripts from inside a component folder; run them as **modules**
from the project root to ensure imports resolve consistently.

## Verify and run

```bash
python3 -m unittest discover -v
python3 -m Component_1.checker Component_1/examples/02_valid_r3.json
python3 -m Component_1.checker Component_1/examples/12_invalid_r1.json
python3 -m Component_2.benchmark_c2
python3 -m Component_1.generate_examples
```

Check all C0 files from the `Component_0` folder (Dafny 4.x):

```bash
cd Component_0
dafny verify --verify-included-files Soundness.dfy
```

If Dafny is installed only through VS Code, invoke its DLL with `dotnet`
in place of `dafny`, as done during your earlier verification.

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

## C2 v5 improvements

- `auto`: exact decomposition of `And(A,B)`, `Iff(A,B)`, and `Not(Not(A))`, including under curried hypotheses `H1 -> ... -> Hk -> conclusion`;
  trivial `Imp(X,X)` / `Iff(X,X)` are recognized. Each piece is checked
  recursively. The decompositions preserve validity and counterexamples.
- Each remaining formula with <= **26** distinct propositional units uses
  bit-parallel exhaustive checking. Larger pieces use Tseitin CNF + DPLL.
- DPLL has a default **5,000 search-node budget**. Exhaustion is `UNKNOWN`,
  never `True` or false acceptance. `is_tautology` caches True, False **and
  UNKNOWN** (UNKNOWN is re-raised as `SolverResourceLimit`). Cached results
  are scoped by formula, method and node limit.
- The CLI exposes `--no-limit` for exhaustive DPLL and
  `--dpll-node-limit N` for a custom limit. An unlimited search may be very
  slow; it is not a wall-clock guarantee.

```bash
python3 -m Component_1.checker Component_1/examples/02_valid_r3.json
python3 -m Component_1.checker Component_1/examples/02_valid_r3.json --no-limit
python3 -m Component_1.checker Component_1/examples/02_valid_r3.json --dpll-node-limit 1000
```

CLI exit codes: `0` = ACCEPT; `1` = REJECT; `2` = UNKNOWN.

Three *reported* outcomes:

- `ACCEPT`: every line proven legitimate and last line matches goal.
- `REJECT`: a genuinely invalid step, malformed proof, or goal mismatch.
- `UNKNOWN`: a resource limit prevented deciding a step. The `accepted`
  Boolean remains `False` to ensure UNKNOWN is never mistaken for acceptance.

**Limitations:** An UNKNOWN result does not prove the formula or proof is
invalid. Disabling the DPLL node budget with `--no-limit` allows exhaustive
search on formulas within runtime constraints; it does not guarantee
a decision for arbitrarily deep inputs because Python recursion limits
can still result in UNKNOWN, nor does it guarantee termination within
a practical amount of time or memory. The default DPLL solver has no clause learning and
can be exponential on some easy tautologies; the 26-unit bit-parallel limit
also has exponential memory cost and potentially large transient masks.
Deep input recursion is safely reported as UNKNOWN, not silently accepted.
Performance varies significantly by formula shape. Benchmarks of
conjunctions of `(p_i -> p_i)` are not representative of DPLL worst cases.

## Verification boundaries and integration

C0's Dafny specifications prove soundness for the **formal** derivation tree.
The Python implementations of C1 and C2 are extensively tested but are
**not themselves formally verified**. In particular, translating the Dafny
formula datatype, axiom instance descriptions, and derivation tree into Python
objects and a flat numbered proof is a manual trust boundary.

C2 implements R1 by treating each distinct temporal expression as an opaque
propositional variable, matching C0's `PropEval` semantics. Axioms follow
`Soundness.dfy`, with A8's logically equivalent implication formulation
and **weak until**. C3 should import `check_derivation` and the `ProofLine`
class and should distinguish `UNKNOWN` from `REJECT` during evaluation.

Dafny verification of C0 does **not** certify the Python checker or prove
that all reported outcomes are complete. The runtime checker's key safety
invariant is: no R1 line is accepted unless the selected backend has
completed a proof of propositional tautologicity.

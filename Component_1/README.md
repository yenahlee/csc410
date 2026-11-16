# Component 1 — Executable derivation checker

Run from the **repository root**:
`python3 -m Component_1.checker Component_1/examples/02_valid_r3.json`

`formula.py` defines the shared immutable formula AST and JSON serialization;
`axioms.py` constructs and checks axiom instances; `checker.py` checks numbered
proofs, delegating R1 to Component 2. `test_checker.py` covers valid/invalid
proofs; `examples/` contains sample proofs.

Exact checking (unbudgeted DPLL) is the default for final derivations.
Use `--dpll-node-limit N` only to opt in to resource-limited checking
for C3/search experiments. `--no-limit` explicitly selects the default.
See the top-level README for the detailed data contract and verdict semantics.

Checker CLI exit statuses: 0 for ACCEPT, 1 for REJECT. Exit 2 (UNKNOWN) is reserved for budget exhaustion or execution resource failure, never interpreted as an invalid proof.

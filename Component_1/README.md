# Component 1 — Executable derivation checker

Run from the **repository root**:
`python3 -m Component_1.checker Component_1/examples/02_valid_r3.json`

`formula.py` defines the shared immutable formula AST and JSON serialization;
`axioms.py` constructs and checks axiom instances; `checker.py` checks numbered
proofs, delegating R1 to Component 2. `test_checker.py` covers valid/invalid
proofs; `examples/` contains sample proofs.

Use `--no-limit` or `--dpll-node-limit N` for C2 DPLL search configuration.
See the top-level README for the detailed data contract and verdict semantics.

Checker CLI exit statuses: 0 for ACCEPT, 1 for REJECT, and 2 for UNKNOWN (e.g. C2 resource exhaustion).

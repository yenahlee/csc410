# Component 2 — Propositional backend

Run from the **repository root**:
`python3 -m unittest discover -v`
`python3 -m Component_2.benchmark_c2`

`propositional.py` contains the reference exhaustive truth table, bit-parallel
truth tables, and a budgeted DPLL with Tseitin CNF. Automatic checking splits
conjunctions, certain implications, and equivalences into equivalent
subproblems. `test_backends.py` differential-tests all backends and failure
modes. `test_propositional.py` exercises basic logic; `benchmark_c2.py`
illustrates runtime on a simple formula family.

C2 retains a 5,000-node default for **direct backend calls** and C3 experiments.
The **C1 checker deliberately overrides it with `node_limit=None`**, so final proof
validation is exact by default. Passing `--dpll-node-limit N` to the C1 CLI
opts into a resource-limited search mode. UNKNOWN is not a valid R1 justification.

The backend supports exact decomposition under curried implication hypotheses and double negation. CLI exit statuses are 0 (ACCEPT), 1 (REJECT), 2 (UNKNOWN). Unlimited DPLL is subject to Python recursion and available computational resources.

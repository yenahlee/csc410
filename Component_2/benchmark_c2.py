"""Small, reproducible C2 performance and robustness benchmark.

Run from repository root: python3 -m Component_2.benchmark_c2
Figures depend on formula structure, hardware, Python version and caching.
We avoid deliberately unbounded DPLL calls on adversarial formulas.
"""
import time
from Component_1.formula import Atom, And, Imp, Not
from Component_2.propositional import is_tautology, SolverResourceLimit, BIT_LIMIT


def identity_conjunction(n):
    f = Imp(Atom(0), Atom(0))
    for i in range(1, n):
        a = Atom(i)
        f = And(f, Imp(a, a))
    return f


def contradiction_conjunction(n):
    f = Imp(Atom(0), Atom(0))
    for i in range(1, n):
        a = Atom(i)
        f = And(f, Not(And(a, Not(a))))
    return f


def implication_chain(n):
    f = Atom(0)
    for i in range(1, n):
        f = Imp(Atom(i), f)
    return f


def time_case(label, f, method="auto", node_limit=5000):
    start = time.perf_counter()
    try:
        result = "TRUE" if is_tautology(f, method=method, node_limit=node_limit) else "FALSE"
    except SolverResourceLimit:
        result = "UNKNOWN"
    elapsed = time.perf_counter() - start
    print(f"{label:<34} {method:<6} {result:<8} {elapsed:>9.4f} s")


def main():
    print('Example workload                  method verdict    elapsed')
    print('-' * 64)
    for n in (12, 20, 26, 27):
        time_case(f'Identity conjunction, n={n}', identity_conjunction(n))
    for n in (20, 26, 27):
        time_case(f'Contradiction conjunction, n={n}', contradiction_conjunction(n))
    time_case('Unsplit chain, n=27 (limit 100)', implication_chain(27), node_limit=100)
    time_case('Unsplit chain, n=27 (unlimited)', implication_chain(27), node_limit=None)
    print('\nThe first two families now split into small formulas; this benchmark')
    print('does not characterize worst-case DPLL complexity or memory usage.')


if __name__ == '__main__':
    main()

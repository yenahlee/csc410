"""Cross-validation of bit-parallel and DPLL C2 against exhaustive oracle."""
import random
import unittest
from Component_1.formula import Atom, Not, And, Imp, Iff, Next, Always, Eventually, Until, from_dict
from Component_2.propositional import (
    propositional_atoms, evaluate, reference_counterexample, counterexample,
    is_tautology, BIT_LIMIT,
)
from Component_1.checker import check_json


class TestBackendAgreement(unittest.TestCase):
    def test_random_formulas_against_reference(self):
        rng = random.Random(410)
        p, q, r = Atom(0), Atom(1), Atom(2)
        leaves = [p, q, r, Next(p), Always(q), Eventually(r), Until(p, q)]

        def make(depth):
            if depth == 0 or rng.random() < .30:
                return rng.choice(leaves)
            op = rng.choice([Not, And, Imp, Iff])
            return op(make(depth - 1)) if op is Not else op(make(depth - 1), make(depth - 1))

        for _ in range(400):
            f = make(4)
            expected = reference_counterexample(f) is None
            for method in ('bits', 'dpll', 'auto'):
                with self.subTest(formula=repr(f), method=method):
                    witness = counterexample(f, method)
                    self.assertEqual(witness is None, expected)
                    if witness is not None:
                        self.assertFalse(evaluate(f, witness))
                    self.assertEqual(is_tautology(f, method), expected)

    def test_larger_shared_and_distinct_units(self):
        atoms = [Atom(i) for i in range(21)]
        # Many units but a short proof of tautology: all p_i imply themselves.
        conjunction = Imp(atoms[0], atoms[0])
        for x in atoms[1:]:
            conjunction = And(conjunction, Imp(x, x))
        self.assertEqual(len(propositional_atoms(conjunction)), 21)
        self.assertTrue(is_tautology(conjunction, 'bits'))
        self.assertTrue(is_tautology(conjunction, 'dpll'))
        non_tautology = And(conjunction, atoms[0])
        for method in ('bits', 'dpll'):
            witness = counterexample(non_tautology, method)
            self.assertIsNotNone(witness)
            self.assertFalse(evaluate(non_tautology, witness))

    def test_bit_limit_and_dpll_fallback(self):
        atoms = [Atom(i) for i in range(BIT_LIMIT + 1)]
        f = atoms[0]
        for x in atoms[1:]:
            f = And(f, x)
        self.assertFalse(is_tautology(f, 'auto'))
        with self.assertRaises(ValueError):
            counterexample(f, 'bits')
        self.assertFalse(is_tautology(f, 'dpll'))

    def test_cache(self):
        is_tautology.cache_clear()
        f = Imp(Atom(1), Atom(1))
        self.assertTrue(is_tautology(f))
        self.assertTrue(is_tautology(f))
        self.assertGreaterEqual(is_tautology.cache_info().hits, 1)

    def test_deep_json_rejected(self):
        f = {'op':'Atom', 'id':0}
        for _ in range(1200):
            f = {'op':'Not', 'p':f}
        result = check_json({'goal':f, 'lines': []})
        self.assertFalse(result.accepted)
        self.assertEqual(result.status, 'UNKNOWN')

    def test_empty_or_invalid_method(self):
        with self.assertRaises(ValueError):
            is_tautology(Atom(0), 'bad')


if __name__ == '__main__':
    unittest.main()

class TestResourceSafety(unittest.TestCase):
    def test_budget_exhaustion_is_unknown_not_tautology(self):
        from Component_2.propositional import SolverResourceLimit
        f = Imp(Atom(0), Atom(0))  # tautology, but forced DPLL budget = 0
        with self.assertRaises(SolverResourceLimit):
            counterexample(f, 'dpll', node_limit=0)
        # No accidental ACCEPT when the solver has returned UNKNOWN.
        from Component_1.checker import check_derivation, ProofLine
        from unittest.mock import patch
        with patch('Component_1.checker.is_tautology',
                                 side_effect=SolverResourceLimit('budget')):
            result = check_derivation(f, [ProofLine(f, 'R1')])
        self.assertEqual(result.status, 'UNKNOWN')
        self.assertFalse(result.accepted)

    def test_checker_library_deep_formula_does_not_crash(self):
        from Component_1.checker import check_derivation, ProofLine
        deep = Atom(0)
        for _ in range(1600):
            deep = Not(deep)
        formula = Imp(deep, deep)
        outcome = check_derivation(formula, [ProofLine(formula, 'R1')])
        self.assertFalse(outcome.accepted)
        self.assertIn('resource limit', outcome.reason)
        self.assertEqual(outcome.status, 'UNKNOWN')

    def test_checker_rejects_unknown_dpll_status(self):
        from unittest.mock import patch
        from Component_1.checker import check_derivation, ProofLine
        from Component_2.propositional import SolverResourceLimit
        f = Imp(Atom(0), Atom(0))
        with patch('Component_1.checker.is_tautology', side_effect=SolverResourceLimit('budget')):
            outcome = check_derivation(f, [ProofLine(f, 'R1')])
        self.assertFalse(outcome.accepted)
        self.assertIn('resource limit', outcome.reason)
        self.assertEqual(outcome.status, 'UNKNOWN')

    def test_adversarial_dpll_reports_unknown(self):
        from Component_2.propositional import SolverResourceLimit
        f = Imp(Atom(0), Atom(0))
        for i in range(1, 18):
            a = Atom(i)
            f = And(f, Not(And(a, Not(a))))
        with self.assertRaises(SolverResourceLimit):
            counterexample(f, 'dpll')
        # Bit-parallel exhaustively verifies it within the unit limit.
        self.assertTrue(is_tautology(f, 'bits'))


class TestFormulaSplitting(unittest.TestCase):
    def test_split_27_unit_tautology(self):
        atoms = [Atom(i) for i in range(27)]
        f = Imp(atoms[0], atoms[0])
        for a in atoms[1:]:
            f = And(f, Not(And(a, Not(a))))
        self.assertEqual(len(propositional_atoms(f)), 27)
        self.assertTrue(is_tautology(f, 'auto', node_limit=0))
        with self.assertRaises(Exception):
            is_tautology(f, 'dpll', node_limit=0)

    def test_iff_and_implication_splits(self):
        atoms = [Atom(i) for i in range(28)]
        big = Imp(atoms[0], atoms[0])
        for a in atoms[1:]:
            big = And(big, Imp(a, a))
        self.assertTrue(is_tautology(Imp(atoms[0], big), 'auto', node_limit=0))
        self.assertTrue(is_tautology(Iff(big, big), 'auto', node_limit=0))
        not_valid = Iff(big, atoms[0])
        witness = counterexample(not_valid, 'auto')
        self.assertIsNotNone(witness)
        self.assertFalse(evaluate(not_valid, witness))

    def test_unknown_cache_and_unlimited_mode(self):
        from Component_2.propositional import SolverResourceLimit
        is_tautology.cache_clear()
        f = Imp(Atom(0), Atom(0))
        with self.assertRaises(SolverResourceLimit):
            is_tautology(f, 'dpll', node_limit=0)
        before = is_tautology.cache_info().hits
        with self.assertRaises(SolverResourceLimit):
            is_tautology(f, 'dpll', node_limit=0)
        self.assertEqual(is_tautology.cache_info().hits, before + 1)
        self.assertTrue(is_tautology(f, 'dpll', node_limit=None))

    def test_three_verdicts(self):
        from Component_1.checker import ProofLine, check_derivation
        f = Imp(Atom(0), Atom(0))
        self.assertEqual(check_derivation(f, [ProofLine(f, 'R1')]).status, 'ACCEPT')
        self.assertEqual(check_derivation(Atom(0), [ProofLine(Atom(0), 'R1')]).status, 'REJECT')
        self.assertEqual(check_derivation(f, [ProofLine(f, 'R1')], node_limit=0).status, 'ACCEPT')

class TestAutoBudgetFromChecker(unittest.TestCase):
    def test_large_unsplit_r1_reports_unknown(self):
        from Component_1.checker import check_derivation, ProofLine
        f = Atom(0)
        for i in range(1, 27):
            f = Imp(Atom(i), f)
        self.assertEqual(len(propositional_atoms(f)), 27)
        result = check_derivation(f, [ProofLine(f, 'R1')], node_limit=0)
        self.assertEqual(result.status, 'UNKNOWN')
        self.assertFalse(result.accepted)
        self.assertEqual(result.line_index, 0)

class TestCurriedSplitting(unittest.TestCase):
    def test_curried_conjunction_with_42_units(self):
        atoms = [Atom(i) for i in range(42)]
        big = Imp(atoms[2], atoms[2])
        for a in atoms[3:]:
            big = And(big, Imp(a, a))
        f = Imp(atoms[0], Imp(atoms[1], big))
        self.assertEqual(len(propositional_atoms(f)), 42)
        self.assertTrue(is_tautology(f, 'auto', node_limit=0))

    def test_curried_equivalence(self):
        p, q = Atom(0), Atom(1)
        good = Imp(p, Imp(q, Iff(p, p)))
        bad = Imp(p, Imp(q, Iff(p, Not(q))))
        self.assertTrue(is_tautology(good, 'auto', node_limit=0))
        witness = counterexample(bad, 'auto')
        self.assertIsNotNone(witness)
        self.assertFalse(evaluate(bad, witness))

    def test_double_negation_large_conjunction(self):
        atoms = [Atom(i) for i in range(40)]
        big = Imp(atoms[0], atoms[0])
        for a in atoms[1:]:
            big = And(big, Imp(a, a))
        self.assertTrue(is_tautology(Not(Not(big)), 'auto', node_limit=0))
        self.assertTrue(is_tautology(Imp(Atom(100), Not(Not(big))), 'auto', node_limit=0))

    def test_double_negation_non_tautology_witness(self):
        f = Not(Not(Imp(Atom(0), Atom(1))))
        witness = counterexample(f, 'auto')
        self.assertIsNotNone(witness)
        self.assertFalse(evaluate(f, witness))

    def test_cli_exit_codes(self):
        import json
        import subprocess
        import sys
        import tempfile
        from pathlib import Path
        from Component_1.formula import to_dict
        from Component_1.checker import ProofLine, check_derivation
        accepted = Imp(Atom(0), Atom(0))
        rejected = Atom(0)
        unknown = Atom(0)
        for i in range(1, 27):
            unknown = Imp(Atom(i), unknown)
        cases = [(accepted, 0), (rejected, 1), (unknown, 2)]
        with tempfile.TemporaryDirectory() as directory:
            for i, (formula, expected_code) in enumerate(cases):
                path = Path(directory) / f'{i}.json'
                path.write_text(json.dumps({'goal': to_dict(formula), 'lines': [
                    {'rule': 'R1', 'formula': to_dict(formula)}]}))
                proc = subprocess.run([sys.executable, '-m', 'Component_1.checker',
                                       str(path), '--dpll-node-limit', '0'],
                                      capture_output=True, text=True, timeout=10)
                self.assertEqual(proc.returncode, expected_code, proc.stdout + proc.stderr)
                self.assertIn(('ACCEPT', 'REJECT', 'UNKNOWN')[i], proc.stdout)

class TestExactDefault(unittest.TestCase):
    def test_cli_defaults_to_exact(self):
        import json
        import subprocess
        import sys
        import tempfile
        from pathlib import Path
        from Component_1.formula import to_dict
        tautology = Imp(Atom(26), Atom(26))
        for i in range(25, -1, -1):
            tautology = Imp(Atom(i), tautology)
        non_tautology = Atom(0)
        for i in range(1, 27):
            non_tautology = Imp(Atom(i), non_tautology)
        with tempfile.TemporaryDirectory() as folder:
            for name, f, expected in [('valid', tautology, 0), ('invalid', non_tautology, 1)]:
                path = Path(folder) / (name + '.json')
                path.write_text(json.dumps({'goal': to_dict(f), 'lines': [{'rule': 'R1', 'formula': to_dict(f)}]}))
                command = [sys.executable, '-m', 'Component_1.checker', str(path)]
                run = subprocess.run(command, capture_output=True, text=True, timeout=15)
                self.assertEqual(run.returncode, expected, run.stdout + run.stderr)
                self.assertIn('ACCEPT' if expected == 0 else 'REJECT', run.stdout)
                if name == 'invalid':
                    limited = subprocess.run(command + ['--dpll-node-limit', '0'], capture_output=True, text=True, timeout=15)
                    self.assertEqual(limited.returncode, 2)
                    self.assertIn('UNKNOWN', limited.stdout)

class TestSplittingRandomized(unittest.TestCase):
    def test_curried_and_double_negation_against_reference(self):
        rng = random.Random(4115)
        atoms = [Atom(i) for i in range(4)]
        ops = (And, Imp, Iff)

        def generate(depth):
            if depth == 0 or rng.random() < .28:
                return rng.choice(atoms)
            if rng.random() < .25:
                return Not(generate(depth - 1))
            return rng.choice(ops)(generate(depth - 1), generate(depth - 1))

        for _ in range(600):
            h1, h2 = generate(2), generate(2)
            a, b = generate(2), generate(2)
            conclusion = rng.choice((And(a, b), Iff(a, b), Not(Not(a))))
            f = Imp(h1, Imp(h2, conclusion))
            expected = reference_counterexample(f) is None
            witness = counterexample(f, method='auto')
            self.assertEqual(witness is None, expected)
            if witness is not None:
                self.assertFalse(evaluate(f, witness))

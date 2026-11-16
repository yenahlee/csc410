import json
from pathlib import Path
import unittest
from Component_1.formula import Atom, And, Imp, Not, Always, Next, Until, Iff, Eventually
from Component_1.axioms import axiom_instance, AXIOM_ARITY, is_axiom_instance
from Component_1.checker import ProofLine, check_derivation, check_json, proof_from_dict

p, q = Atom(0), Atom(1)

class TestChecker(unittest.TestCase):
    def test_all_axioms(self):
        for name, arity in AXIOM_ARITY.items():
            with self.subTest(name=name):
                params = (p,) if arity == 1 else (p, q)
                f = axiom_instance(name, params)
                self.assertTrue(check_derivation(f, [ProofLine(f, name, params)]).accepted)

    def test_axiom_wrong_instantiation(self):
        f = Iff(Next(Not(p)), Not(Next(q)))
        self.assertFalse(is_axiom_instance('A3', f, (p,)))
        self.assertFalse(check_derivation(f, [ProofLine(f, 'A3', (p,))]).accepted)

    def test_r1_r3(self):
        t = Imp(p, p)
        proof = [ProofLine(t, 'R1'), ProofLine(Always(t), 'R3', refs=(0,))]
        self.assertTrue(check_derivation(Always(t), proof).accepted)

    def test_r2(self):
        # R1 can prove p -> (q -> p), and (p -> (q -> p)) -> (p -> (q -> p)).
        # For actual MP: first prove tautology w, then tautology w -> (q -> w).
        w = Imp(p, p)
        conditional = Imp(w, Imp(q, w))
        target = Imp(q, w)
        proof = [ProofLine(w, 'R1'), ProofLine(conditional, 'R1'),
                 ProofLine(target, 'R2', refs=(0, 1))]
        self.assertTrue(check_derivation(target, proof).accepted)
        self.assertFalse(check_derivation(target, proof[:-1]).accepted)

    def test_bad_reference(self):
        f = Imp(p, p)
        self.assertFalse(check_derivation(Always(f), [ProofLine(f, 'R1'), ProofLine(Always(f), 'R3', refs=(1,))]).accepted)
        self.assertFalse(check_derivation(Always(f), [ProofLine(f, 'R1'), ProofLine(Always(f), 'R3', refs=(-1,))]).accepted)
        self.assertFalse(check_derivation(Always(f), [ProofLine(f, 'R1'), ProofLine(Always(f), 'R3', refs=(True,))]).accepted)

    def test_wrong_rule(self):
        f = Imp(p, Always(p))
        self.assertFalse(check_derivation(f, [ProofLine(f, 'R1')]).accepted)
        self.assertFalse(check_derivation(p, [ProofLine(p, 'R9')]).accepted)
        self.assertFalse(check_derivation(Always(p), [ProofLine(p, 'R1'), ProofLine(Always(p), 'R3', refs=(0,))]).accepted)

    def test_empty_and_wrong_goal(self):
        f = Imp(p, p)
        self.assertFalse(check_derivation(f, []).accepted)
        self.assertFalse(check_derivation(p, [ProofLine(f, 'R1')]).accepted)

    def test_malformed_json(self):
        self.assertFalse(check_json({"goal": {"op":"Atom", "id":0}, "lines": [{"rule":"R3", "formula":{"op":"Atom","id":0}, "refs":["0"]}]}).accepted)
        self.assertFalse(check_json({"lines": []}).accepted)

    def test_example_corpus(self):
        examples = list((Path(__file__).parent / 'examples').glob('*.json'))
        self.assertGreaterEqual(len(examples), 10)
        for path in examples:
            with self.subTest(file=path.name):
                data = json.loads(path.read_text())
                expected = data.pop('expected_accept')
                self.assertEqual(check_json(data).accepted, expected)

if __name__ == '__main__':
    unittest.main()

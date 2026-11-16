import unittest
from Component_1.formula import Atom, Not, And, Imp, Iff, Next, Always, Eventually, Until, to_dict, from_dict
from Component_2.propositional import propositional_atoms, evaluate, is_tautology, counterexample

p, q = Atom(0), Atom(1)

class TestPropositional(unittest.TestCase):
    def test_basic_tautologies(self):
        self.assertTrue(is_tautology(Imp(p, p)))
        self.assertTrue(is_tautology(Imp(And(p, q), p)))
        self.assertTrue(is_tautology(Iff(Not(Not(p)), p)))

    def test_non_tautologies(self):
        self.assertFalse(is_tautology(p))
        self.assertFalse(is_tautology(Imp(p, q)))
        self.assertFalse(is_tautology(Imp(p, Always(p))))
        self.assertFalse(is_tautology(Imp(Always(p), p)))

    def test_temporal_units_indivisible(self):
        t = Until(p, q)
        self.assertEqual(propositional_atoms(Imp(t, t)), {t})
        self.assertTrue(is_tautology(Imp(t, t)))
        self.assertTrue(is_tautology(Imp(Next(p), Next(p))))
        self.assertFalse(is_tautology(Imp(Next(p), p)))
        self.assertFalse(is_tautology(Iff(Eventually(p), Not(Always(Not(p))))))

    def test_counterexample(self):
        f = Imp(p, q)
        v = counterexample(f)
        self.assertIsNotNone(v)
        self.assertFalse(evaluate(f, v))
        self.assertIsNone(counterexample(Imp(p, p)))

    def test_immutability_and_roundtrip(self):
        f = Iff(Always(Imp(p, q)), Until(p, Not(q)))
        self.assertEqual(from_dict(to_dict(f)), f)
        with self.assertRaises(Exception):
            p.id = 10
        with self.assertRaises(ValueError):
            Atom(-1)
        with self.assertRaises(ValueError):
            Atom(True)
        with self.assertRaises(ValueError):
            from_dict({"op": "Imp", "p": {"op": "Atom", "id": 0}})

if __name__ == '__main__':
    unittest.main()

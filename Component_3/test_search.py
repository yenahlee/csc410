import unittest
from Component_1.formula import Atom, Not, And, Imp, Iff, Next, Always, Eventually
from Component_1.checker import check_derivation
from Component_3.search import search

p, q, r = Atom(0), Atom(1), Atom(2)


def Or(a, b):
    return Imp(Not(a), b)


PROVABLE = [
    Imp(Always(p), p),
    Imp(Always(p), Next(p)),
    Imp(Always(p), Eventually(p)),
    Imp(p, Eventually(p)),
    Iff(Eventually(p), Not(Always(Not(p)))),
    Iff(Next(Not(p)), Not(Next(p))),
    Imp(Eventually(p), Eventually(Or(p, q))),
    Imp(Always(And(p, q)), And(Always(p), Always(q))),
    Imp(Next(And(p, q)), And(Next(p), Next(q))),
    Imp(And(Always(p), Always(q)), Always(And(p, q))),
    Iff(Always(And(p, q)), And(Always(p), Always(q))),
    Iff(Next(And(p, q)), And(Next(p), Next(q))),
    Imp(Always(Imp(p, q)), Imp(Eventually(p), Eventually(q))),
    Imp(Always(p), Imp(Always(q), Always(And(p, q)))),
    Imp(And(Always(p), And(Always(q), Always(r))), Always(And(p, And(q, r)))),
    Imp(Always(p), Imp(Always(q), Imp(Always(r), Always(And(p, And(q, r)))))),
    Imp(And(Next(p), And(Next(q), Next(r))), Next(And(p, And(q, r)))),
    Imp(Or(Always(p), Always(q)), Always(Or(p, q))),
    Iff(Next(Or(p, q)), Or(Next(p), Next(q))),
    Iff(Next(Imp(p, q)), Imp(Next(p), Next(q))),
    Imp(Or(Eventually(p), Eventually(q)), Eventually(Or(p, q))),
    Imp(Next(p), Eventually(p)),
    Imp(Next(Eventually(p)), Eventually(p)),
    Imp(Always(p), Imp(Next(q), Next(And(p, q)))),
    Imp(Always(p), Next(Eventually(p))),
    Imp(Always(p), Next(Next(Always(p)))),
    Imp(Or(p, Next(Eventually(p))), Eventually(p)),
    Iff(Eventually(Or(p, q)), Or(Eventually(p), Eventually(q))),
    # these need one induction with A6
    Imp(Always(p), Always(Always(p))),
    Imp(Eventually(Eventually(p)), Eventually(p)),
    Imp(Always(p), Always(Next(p))),
    Imp(And(p, Always(Imp(p, Next(p)))), Always(p)),
    Imp(Next(Always(p)), Always(Next(p))),
]

# valid but the invariant or the step is out of reach
OUT_OF_REACH = [
    Imp(And(p, Next(Always(p))), Always(p)),
    Imp(Always(Next(p)), Next(Always(p))),
]

INVALID = [
    Imp(p, Always(p)),
    Imp(Eventually(p), Always(p)),
    Imp(Next(p), p),
]


class TestSearch(unittest.TestCase):
    def test_found_proofs_pass_the_checker(self):
        for goal in PROVABLE:
            with self.subTest(goal=goal):
                lines = search(goal)
                self.assertIsNotNone(lines)
                self.assertEqual(check_derivation(goal, lines).status, "ACCEPT")

    def test_out_of_reach_goals_are_not_found(self):
        for goal in OUT_OF_REACH:
            with self.subTest(goal=goal):
                self.assertIsNone(search(goal))

    def test_invalid_goals_are_not_found(self):
        for goal in INVALID:
            with self.subTest(goal=goal):
                self.assertIsNone(search(goal))


if __name__ == "__main__":
    unittest.main()

import argparse
import json
from pathlib import Path
from Component_1.formula import Atom, Not, And, Imp, Iff, Next, Always, Eventually, Until, from_dict, to_dict
from Component_1.axioms import axiom_instance
from Component_1.checker import ProofLine, check_derivation
from Component_2.propositional import is_tautology, SolverResourceLimit

NODE_LIMIT = 5000


class Proof:
    def __init__(self):
        # proof lines written so far
        self.lines = []
        # formula to the line that proves it
        self.index = {}
        # goals on the current path so we never loop
        self.active = set()
        # goals that led nowhere so no branch retries them
        self.failed = set()
        # true while inside an induction so it happens once per branch
        self.in_induction = False

    def add(self, formula, rule, params=(), refs=()):
        # reuse the earlier line if this formula is already proved
        if formula in self.index:
            return self.index[formula]
        self.lines.append(ProofLine(formula, rule, tuple(params), tuple(refs)))
        self.index[formula] = len(self.lines) - 1
        return self.index[formula]

    def formula(self, line):
        return self.lines[line].formula

    def mark(self):
        return len(self.lines)

    def rollback(self, mark):
        # forget the lines a failed branch added
        del self.lines[mark:]
        self.index = {f: i for f, i in self.index.items() if i < mark}


# rules that write one proof line each


def tautology(f):
    # running out of budget just means this branch fails
    try:
        return is_tautology(f, node_limit=NODE_LIMIT)
    except SolverResourceLimit:
        return False


def axiom(proof, name, *params):
    return proof.add(axiom_instance(name, params), name, params)


def r1(proof, tautology_formula):
    return proof.add(tautology_formula, "R1")


def r2(proof, premise, implication):
    return proof.add(proof.formula(implication).q, "R2", refs=(premise, implication))


def r3(proof, line):
    return proof.add(Always(proof.formula(line)), "R3", refs=(line,))


def chain(proof, facts, goal):
    # one or two proved lines give the goal by plain logic
    # written as one R1 tautology then one R2 per fact
    # example with facts a -> b and b -> c and goal a -> c
    #   R1  (a -> b) -> ((b -> c) -> (a -> c))
    #   R2  (b -> c) -> (a -> c)
    #   R2  a -> c
    # all three lines go into the proof and we return the number of the last one
    # nothing to write if the goal is already proved
    if goal in proof.index:
        return proof.index[goal]
    bridge = goal
    for fact in reversed(facts):
        bridge = Imp(proof.formula(fact), bridge)
    if not tautology(bridge):
        return None
    line = r1(proof, bridge)
    for fact in facts:
        line = r2(proof, fact, line)
    return line


def attempt(proof, step, *args):
    # undo whatever a failed step left behind
    mark = proof.mark()
    line = step(*args)
    if line is None:
        proof.rollback(mark)
    return line


# one way rewrites of the visible layer one spot at a time


def rewrite_once(f):
    # eventually becomes not always not by A1
    if isinstance(f, Eventually):
        return Not(Always(Not(f.p))), ("A1", f.p)
    if isinstance(f, Not):
        inner = f.p
        # double negation disappears
        if isinstance(inner, Not):
            return inner.p, None
        # next moves to the outside by A3
        if isinstance(inner, Next):
            return Next(Not(inner.p)), ("A3", inner.p)
        # a negated arrow is its hypothesis and the negated conclusion
        if isinstance(inner, Imp):
            return And(inner.p, Not(inner.q)), None
        # otherwise look further inside the negation
        step = rewrite_once(inner)
        if step is None:
            return None
        return Not(step[0]), step[1]
    if isinstance(f, (And, Imp, Iff)):
        # left side first then right side
        step = rewrite_once(f.p)
        if step is not None:
            return type(f)(step[0], f.q), step[1]
        step = rewrite_once(f.q)
        if step is not None:
            return type(f)(f.p, step[0]), step[1]
    return None


def prove_rewritten(goal, rewritten, fact, proof):
    child = prove(rewritten, proof)
    if child is None:
        return None
    # the axiom fact if any turns the rewritten goal back into the original
    if fact is None:
        return chain(proof, [child], goal)
    return chain(proof, [axiom(proof, *fact), child], goal)


# recipes that strip one layer


def strip_always_r3(goal, proof):
    child = prove(goal.p, proof)
    if child is None:
        return None
    return r3(proof, child)


def strip_always_a2(goal, proof):
    a, b = goal.p.p, goal.q.p
    child = prove(Imp(a, b), proof)
    if child is None:
        return None
    # make the step hold always then push always through with A2
    boxed = r3(proof, child)
    return r2(proof, boxed, axiom(proof, "A2", a, b))


def strip_next_a4(goal, proof):
    a, b = goal.p.p, goal.q.p
    step = Imp(a, b)
    child = prove(step, proof)
    if child is None:
        return None
    # no rule adds next directly so go through always and A5
    boxed = r3(proof, child)
    unfolded = r2(proof, boxed, axiom(proof, "A5", step))
    nexted = chain(proof, [unfolded], Next(step))
    # A4 pushes next through the implication
    return r2(proof, nexted, axiom(proof, "A4", a, b))


def strip_not_r1(goal, proof):
    # ~a -> ~b flips to b -> a
    child = prove(Imp(goal.q.p, goal.p.p), proof)
    if child is None:
        return None
    return chain(proof, [child], goal)


# recipes that split into two parts


def join(first, second, goal, proof):
    # both parts must be proved before joining them
    a = prove(first, proof)
    if a is None:
        return None
    b = prove(second, proof)
    if b is None:
        return None
    return chain(proof, [a, b], goal)


def split_r1(goal, proof):
    if isinstance(goal, Iff):
        return join(Imp(goal.p, goal.q), Imp(goal.q, goal.p), goal, proof)
    return join(goal.p, goal.q, goal, proof)


def split_under_r1(goal, proof):
    # h -> (a & b) needs h -> a and h -> b
    h, both = goal.p, goal.q
    return join(Imp(h, both.p), Imp(h, both.q), goal, proof)


def split_cases_r1(goal, proof):
    # (x -> y) -> c is (~x or y) -> c so both cases must give c
    either, c = goal.p, goal.q
    return join(Imp(Not(either.p), c), Imp(either.q, c), goal, proof)


# A5 and moving a hidden always across the arrow


def unfold(h, c):
    # always as a hypothesis gives only the part the conclusion needs
    if not isinstance(h, Always):
        return None
    x = h.p
    if isinstance(c, Next):
        return And(Next(x), Next(Always(x)))
    if not isinstance(c, (Always, Next, Eventually, Until)):
        return x
    return None


def unfold_a5(goal, proof):
    h, c = goal.p, goal.q
    child = prove(Imp(unfold(h, c), c), proof)
    if child is None:
        return None
    # A5 gives the replacement from the original hypothesis
    return chain(proof, [axiom(proof, "A5", h.p), child], goal)


def swap_always_r1(goal, proof):
    # h -> ~[]y says the same as []y -> ~h
    h, boxed = goal.p, goal.q.p
    child = prove(Imp(boxed, Not(h)), proof)
    if child is None:
        return None
    return chain(proof, [child], goal)


def swap_hypothesis_r1(goal, proof):
    # ~[]x -> c says the same as ~c -> []x
    boxed, c = goal.p.p, goal.q
    child = prove(Imp(Not(c), boxed), proof)
    if child is None:
        return None
    return chain(proof, [child], goal)


# chains of hypotheses on the right


def merges(inner):
    # every way to rewrite this arrow in the order we try them
    a, b = inner.p, inner.q
    options = []
    # same operator on both sides merges into one
    if isinstance(a, Always) and isinstance(b, Always):
        options.append((Always(Imp(a.p, b.p)), ("A2", a.p, b.p)))
    if isinstance(a, Next) and isinstance(b, Next):
        options.append((Next(Imp(a.p, b.p)), ("A4", a.p, b.p)))
    # not on both sides flips which is plain R1
    if isinstance(a, Not) and isinstance(b, Not):
        options.append((Imp(b.p, a.p), None))
    # always as a hypothesis unfolds with A5
    replacement = unfold(a, b)
    if replacement is not None:
        options.append((Imp(replacement, b), ("A5", a.p)))
    # or keep the always and move a hidden always across instead
    if isinstance(b, Not) and isinstance(b.p, Always):
        options.append((Imp(b.p, Not(a)), None))
    return options


def spine_steps(f):
    # every rewrite down the chain of arrows deepest first
    if not isinstance(f, Imp):
        return []
    h, rest = f.p, f.q
    # a conjunction hypothesis splits into two hypotheses
    if isinstance(h, And):
        return [(Imp(h.p, Imp(h.q, rest)), None)]
    if not isinstance(rest, Imp):
        return []
    steps = spine_steps(rest) + merges(rest)
    return [(Imp(h, inner), fact) for inner, fact in steps]


def rewrite_spine_a2_a4(goal, proof):
    # try each rewrite until one leads to a proof
    for rewritten, fact in spine_steps(goal):
        line = attempt(proof, prove_rewritten, goal, rewritten, fact, proof)
        if line is not None:
            return line
    return None


# induction with A6


def induct_a6(goal, proof):
    # induction is allowed once per branch
    if proof.in_induction:
        return None
    h, c = goal.p, goal.q.p
    # the invariant is what we prove or what we are given
    for x in dict.fromkeys([c, h]):
        proof.in_induction = True
        line = attempt(proof, induct_with, h, x, c, proof)
        proof.in_induction = False
        if line is not None:
            return line
    return None


def induct_with(h, x, c, proof):
    # base case x holds now
    base = prove(Imp(h, x), proof)
    if base is None:
        return None

    # induction gives x forever then base and induction give h -> []x
    forever = induction(h, x, proof)
    if forever is None:
        return None
    held = chain(proof, [base, forever], Imp(h, Always(x)))
    if x == c:
        return held

    # x must be strong enough to give c and A2 lifts that under always
    enough = prove(Imp(x, c), proof)
    if enough is None:
        return None
    lifted = r2(proof, r3(proof, enough), axiom(proof, "A2", x, c))
    return chain(proof, [held, lifted], Imp(h, Always(c)))


def induction(h, x, proof):
    # usually the step x -> Xx holds on its own so R3 and A6 give x -> []x
    step = attempt(proof, prove, Imp(x, Next(x)), proof)
    if step is not None:
        return r2(proof, r3(proof, step), axiom(proof, "A6", x))

    # otherwise the hypothesis supplies the step and we get h -> (x -> []x)
    step = prove(Imp(h, Always(Imp(x, Next(x)))), proof)
    if step is None:
        return None
    return chain(proof, [step, axiom(proof, "A6", x)], Imp(h, Imp(x, Always(x))))


# choosing what to try at each node


def final_conclusion(f):
    # follow the arrows on the right to the end
    while isinstance(f, Imp):
        f = f.q
    return f


def recipes_for(goal):
    # the top symbol of each side picks the recipes in the order we try them
    if isinstance(goal, Always):
        return [strip_always_r3]
    if isinstance(goal, (And, Iff)):
        return [split_r1]
    if not isinstance(goal, Imp):
        return []
    left, right = goal.p, goal.q
    if isinstance(right, And):
        return [split_under_r1]
    # an arrow on the left is a disjunction in disguise
    if isinstance(left, Imp):
        return [split_cases_r1]

    found = []
    # more arrows on the right or a conjunction on the left
    if isinstance(left, And) or isinstance(right, Imp):
        found.append(rewrite_spine_a2_a4)
    if isinstance(left, Always) and isinstance(right, Always):
        found.append(strip_always_a2)
    if isinstance(left, Next) and isinstance(right, Next):
        found.append(strip_next_a4)
    if isinstance(left, Not) and isinstance(right, Not):
        found.append(strip_not_r1)
    # always on the left and the conclusion needs next or now
    if unfold(left, right) is not None:
        found.append(unfold_a5)
    # a hidden always in the conclusion moves to the hypothesis
    if isinstance(right, Not) and isinstance(right.p, Always):
        found.append(swap_always_r1)
    # a negated always hypothesis moves to the conclusion unless it already ends in always
    if isinstance(left, Not) and isinstance(left.p, Always) and not isinstance(right, Not):
        if not isinstance(final_conclusion(right), Always):
            found.append(swap_hypothesis_r1)
    # induction is the last resort when the conclusion is always
    if isinstance(right, Always):
        found.append(induct_a6)
    return found


def prove(goal, proof):
    if goal in proof.index:
        return proof.index[goal]
    # a goal we are already working on would only loop
    # failures inside an induction may succeed outside one so they are kept apart
    key = (goal, proof.in_induction)
    if goal in proof.active or key in proof.failed:
        return None

    proof.active.add(goal)
    line = prove_node(goal, proof)
    proof.active.discard(goal)
    # remember failures so other branches do not redo them
    if line is None:
        proof.failed.add(key)
    return line


def prove_node(goal, proof):
    # cheapest leaf first
    if tautology(goal):
        return r1(proof, goal)

    # a rewritten goal becomes the new node
    step = rewrite_once(goal)
    if step is not None:
        rewritten, fact = step
        return attempt(proof, prove_rewritten, goal, rewritten, fact, proof)

    # try each recipe that fits until one works
    for recipe in recipes_for(goal):
        line = attempt(proof, recipe, goal, proof)
        if line is not None:
            return line
    return None


def search(goal):
    proof = Proof()
    if prove(goal, proof) is None:
        return None
    return proof.lines


# printing and the command line


SYMBOLS = {Not: "~", Next: "X", Always: "[]", Eventually: "<>"}
INFIX = {And: "&", Imp: "->", Iff: "<->", Until: "U"}


def show(f):
    if isinstance(f, Atom):
        return f"p{f.id}"
    if type(f) in SYMBOLS:
        return SYMBOLS[type(f)] + show(f.p)
    return f"({show(f.p)} {INFIX[type(f)]} {show(f.q)})"


def show_line(i, line):
    extra = ""
    if line.params:
        extra += " params [" + ", ".join(show(p) for p in line.params) + "]"
    if line.refs:
        extra += f" refs {list(line.refs)}"
    return f"{i:>3}. {show(line.formula)}    {line.rule}{extra}"


def line_to_dict(line):
    data = {"formula": to_dict(line.formula), "rule": line.rule}
    if line.params:
        data["params"] = [to_dict(p) for p in line.params]
    if line.refs:
        data["refs"] = list(line.refs)
    return data


def main():
    parser = argparse.ArgumentParser(description="Search for an LTL derivation")
    parser.add_argument("goal", type=Path, help="JSON file holding a goal formula")
    parser.add_argument("--out", type=Path, help="write the proof JSON here")
    parser.add_argument("--show", action="store_true", help="print the proof lines")
    args = parser.parse_args()

    data = json.loads(args.goal.read_text(encoding="utf-8"))
    goal = from_dict(data["goal"] if "goal" in data else data)
    lines = search(goal)
    if lines is None:
        print("NOT FOUND")
        return 1

    # never trust the search so recheck with the exact checker
    result = check_derivation(goal, lines)
    print(f"{result.status}: {len(lines)} lines")
    if args.show:
        for i, line in enumerate(lines):
            print(show_line(i, line))
    if args.out:
        proof = {"goal": to_dict(goal), "lines": [line_to_dict(l) for l in lines]}
        args.out.write_text(json.dumps(proof, indent=2), encoding="utf-8")
    return 0 if result.accepted else 2


if __name__ == "__main__":
    raise SystemExit(main())

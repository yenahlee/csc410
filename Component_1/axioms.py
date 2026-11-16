"""C1 axiom schemas EXACTLY as Soundness.dfy's Conclusion(Ax1..Ax8).

A8 uses Iff(Until(p,q), Imp(Not(q), And(p,Next(Until(p,q)))))
(the equivalent q OR (...) form is not a literal axiom instance in this AST).
"""
from Component_1.formula import Formula, Not, And, Imp, Iff, Next, Always, Eventually, Until

AXIOM_ARITY = {"A1": 1, "A2": 2, "A3": 1, "A4": 2, "A5": 1, "A6": 1, "A7": 2, "A8": 2}


def axiom_instance(name: str, parameters: tuple[Formula, ...]) -> Formula:
    """Construct the only conclusion permitted for a supplied schema/instantiation."""
    if name not in AXIOM_ARITY:
        raise ValueError(f"unknown axiom: {name}")
    if len(parameters) != AXIOM_ARITY[name]:
        raise ValueError(f"{name} expects {AXIOM_ARITY[name]} parameter(s)")
    p = parameters[0]
    q = parameters[1] if len(parameters) == 2 else None
    if name == "A1":
        return Iff(Eventually(p), Not(Always(Not(p))))
    if name == "A2":
        return Imp(Always(Imp(p, q)), Imp(Always(p), Always(q)))
    if name == "A3":
        return Iff(Next(Not(p)), Not(Next(p)))
    if name == "A4":
        return Imp(Next(Imp(p, q)), Imp(Next(p), Next(q)))
    if name == "A5":
        return Imp(Always(p), And(p, And(Next(p), Next(Always(p)))))
    if name == "A6":
        return Imp(Always(Imp(p, Next(p))), Imp(p, Always(p)))
    if name == "A7":
        return Imp(Always(p), Until(p, q))
    if name == "A8":
        return Iff(Until(p, q), Imp(Not(q), And(p, Next(Until(p, q)))))
    raise AssertionError("unreachable")


def is_axiom_instance(name: str, formula: Formula, parameters: tuple[Formula, ...]) -> bool:
    try:
        return formula == axiom_instance(name, parameters)
    except (ValueError, TypeError):
        return False

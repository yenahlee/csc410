"""Immutable LTL abstract syntax, matching the nine constructors in LTL.dfy.

Serialization format: {"op":"Atom","id":0}, {"op":"Not","p":...},
{"op":"And"|"Imp"|"Iff"|"Until","p":...,"q":...}, and
{"op":"Next"|"Always"|"Eventually","p":...}.
"""
from dataclasses import dataclass
from typing import Union

@dataclass(frozen=True)
class Atom:
    id: int
    def __post_init__(self):
        if type(self.id) is not int or self.id < 0:
            raise ValueError("Atom.id must be a nonnegative integer, as in Dafny nat")

@dataclass(frozen=True)
class Not:
    p: "Formula"

@dataclass(frozen=True)
class And:
    p: "Formula"
    q: "Formula"

@dataclass(frozen=True)
class Imp:
    p: "Formula"
    q: "Formula"

@dataclass(frozen=True)
class Iff:
    p: "Formula"
    q: "Formula"

@dataclass(frozen=True)
class Next:
    p: "Formula"

@dataclass(frozen=True)
class Always:
    p: "Formula"

@dataclass(frozen=True)
class Eventually:
    p: "Formula"

@dataclass(frozen=True)
class Until:
    p: "Formula"
    q: "Formula"

Formula = Union[Atom, Not, And, Imp, Iff, Next, Always, Eventually, Until]
UNARY = {"Not": Not, "Next": Next, "Always": Always, "Eventually": Eventually}
BINARY = {"And": And, "Imp": Imp, "Iff": Iff, "Until": Until}


def from_dict(data: dict) -> Formula:
    """Parse strictly: reject extra/missing keys and unexpected formula constructors."""
    if not isinstance(data, dict) or not isinstance(data.get("op"), str):
        raise ValueError("formula must be an object with an 'op' string")
    op = data["op"]
    if op == "Atom":
        if set(data) != {"op", "id"}:
            raise ValueError("Atom expects exactly op and id")
        return Atom(data["id"])
    if op in UNARY:
        if set(data) != {"op", "p"}:
            raise ValueError(f"{op} expects exactly op and p")
        return UNARY[op](from_dict(data["p"]))
    if op in BINARY:
        if set(data) != {"op", "p", "q"}:
            raise ValueError(f"{op} expects exactly op, p and q")
        return BINARY[op](from_dict(data["p"]), from_dict(data["q"]))
    raise ValueError(f"unknown formula operator: {op!r}")


def to_dict(f: Formula) -> dict:
    if isinstance(f, Atom):
        return {"op": "Atom", "id": f.id}
    if isinstance(f, tuple(UNARY.values())):
        return {"op": type(f).__name__, "p": to_dict(f.p)}
    if isinstance(f, tuple(BINARY.values())):
        return {"op": type(f).__name__, "p": to_dict(f.p), "q": to_dict(f.q)}
    raise TypeError(f"not a Formula: {f!r}")

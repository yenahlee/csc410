"""C1 executable checker for numbered derivations, with C2 as the R1 oracle.

Exact propositional checking is the default (no DPLL search-node budget).
A resource-budgeted mode is available by explicitly specifying node_limit,
for C3 exploration. Unexpected runtime failures are UNKNOWN, never REJECT.


Proof format: {"goal": FORMULA, "lines": [
 {"formula": FORMULA, "rule": "A1", "params": [FORMULA]},
 {"formula": FORMULA, "rule": "R1"},
 {"formula": FORMULA, "rule": "R3", "refs": [0]},
 {"formula": FORMULA, "rule": "R2", "refs": [antecedent_index, implication_index]}
]}. Refs are 0-based indices and must refer to strictly earlier lines.
"""
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence
import argparse
import json
from Component_1.formula import Formula, Imp, Always, from_dict
from Component_1.axioms import AXIOM_ARITY, is_axiom_instance
from Component_2.propositional import is_tautology, SolverResourceLimit, DPLL_NODE_LIMIT


@dataclass(frozen=True)
class ProofLine:
    formula: Formula
    rule: str
    params: tuple[Formula, ...] = ()
    refs: tuple[int, ...] = ()


@dataclass(frozen=True)
class CheckResult:
    accepted: bool
    reason: str
    line_index: int | None = None
    status: str = "REJECT"  # ACCEPT / REJECT; UNKNOWN only for resource failure


def check_line(line: ProofLine, previous: Sequence[Formula], *,
               node_limit: int | None = None) -> str | None:
    """Return None if line is justified, else a human-readable error."""
    if not isinstance(line.rule, str):
        return "rule must be a string"
    if line.rule in AXIOM_ARITY:
        if line.refs:
            return "axiom step must not have references"
        if not is_axiom_instance(line.rule, line.formula, line.params):
            return f"formula does not match supplied {line.rule} instantiation"
        return None
    if line.rule == "R1":
        if line.params or line.refs:
            return "R1 requires no parameters or references"
        return None if is_tautology(line.formula, node_limit=node_limit) else "R1 formula is not a propositional tautology"
    if line.rule in ("R2", "R3"):
        if line.params:
            return f"{line.rule} must not have axiom parameters"
        required = 2 if line.rule == "R2" else 1
        if len(line.refs) != required:
            return f"{line.rule} requires {required} earlier-line reference(s)"
        if any(type(i) is not int or i < 0 or i >= len(previous) for i in line.refs):
            return "reference must be a nonnegative index of an earlier line"
        if line.rule == "R3":
            return None if line.formula == Always(previous[line.refs[0]]) else "R3 conclusion is not Always(premise)"
        antecedent = previous[line.refs[0]]
        implication = previous[line.refs[1]]
        if not isinstance(implication, Imp) or implication.p != antecedent:
            return "R2 second referenced line must be implication with first line as antecedent"
        return None if line.formula == implication.q else "R2 conclusion must be consequent of implication"
    return f"unknown rule: {line.rule!r}"


def check_derivation(goal: Formula, lines: Sequence[ProofLine], *,
                     node_limit: int | None = None) -> CheckResult:
    try:
        return _check_derivation_impl(goal, lines, node_limit=node_limit)
    except (RecursionError, SolverResourceLimit) as exc:
        return CheckResult(False, f"resource limit: {exc}", status="REJECT")


def _check_derivation_impl(goal: Formula, lines: Sequence[ProofLine], *,
                           node_limit: int | None = None) -> CheckResult:
    if not lines:
        return CheckResult(False, "derivation cannot be empty")
    previous = []
    for i, line in enumerate(lines):
        try:
            message = check_line(line, previous, node_limit=node_limit)
        except (RecursionError, SolverResourceLimit) as exc:
            return CheckResult(False, f"resource limit: {exc}", i, "REJECT")
        if message is not None:
            return CheckResult(False, message, i)
        previous.append(line.formula)
    if previous[-1] != goal:
        return CheckResult(False, "last line is not the requested goal", len(lines) - 1)
    return CheckResult(True, "all steps justified and final line matches goal", status="ACCEPT")


def proof_from_dict(data: dict) -> tuple[Formula, list[ProofLine]]:
    """Reject malformed proof records rather than interpreting them leniently."""
    if not isinstance(data, dict) or set(data) != {"goal", "lines"}:
        raise ValueError("proof must contain exactly goal and lines")
    if not isinstance(data["lines"], list):
        raise ValueError("lines must be a list")
    goal = from_dict(data["goal"])
    lines = []
    for i, obj in enumerate(data["lines"]):
        if not isinstance(obj, dict) or not {"formula", "rule"} <= set(obj) or set(obj) - {"formula", "rule", "params", "refs"}:
            raise ValueError(f"line {i}: unexpected/missing fields")
        if not isinstance(obj["rule"], str):
            raise ValueError(f"line {i}: rule must be a string")
        if not isinstance(obj.get("params", []), list) or not isinstance(obj.get("refs", []), list):
            raise ValueError(f"line {i}: params and refs must be lists")
        refs = obj.get("refs", [])
        if any(type(j) is not int for j in refs):
            raise ValueError(f"line {i}: refs must be integers")
        lines.append(ProofLine(from_dict(obj["formula"]), obj["rule"],
                               tuple(from_dict(x) for x in obj.get("params", [])), tuple(refs)))
    return goal, lines


def check_json(data: dict, *, node_limit: int | None = None) -> CheckResult:
    try:
        goal, lines = proof_from_dict(data)
        return check_derivation(goal, lines, node_limit=node_limit)
    except (RecursionError, SolverResourceLimit) as exc:
        return CheckResult(False, f"resource limit: {exc}", status="REJECT")
    except (TypeError, ValueError, KeyError) as exc:
        return CheckResult(False, f"malformed proof: {exc}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Check a CSC410 axiomatic LTL derivation")
    parser.add_argument("proof", type=Path, help="Path to a JSON proof")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--no-limit", action="store_true", help="Explicitly use exact checking (already the default)")
    group.add_argument("--dpll-node-limit", type=int, default=None,
                       help="Opt in to resource-limited DPLL checking (suggested for C3; e.g. 5000)")
    args = parser.parse_args()
    node_limit = args.dpll_node_limit  # None (exact) unless budget explicitly requested
    if node_limit is not None and node_limit < 0:
        parser.error("--dpll-node-limit must be nonnegative")
    try:
        proof = json.loads(args.proof.read_text(encoding="utf-8"))
        if isinstance(proof, dict) and "expected_accept" in proof:
            proof = {k: v for k, v in proof.items() if k != "expected_accept"}
        result = check_json(proof, node_limit=node_limit)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"REJECT: {exc}")
        return 1
    where = "" if result.line_index is None else f" (line {result.line_index + 1})"
    print(f"{result.status}{where}: {result.reason}")
    return {"ACCEPT": 0, "REJECT": 1}[result.status]


if __name__ == "__main__":
    raise SystemExit(main())

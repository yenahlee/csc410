
"""Component 4: Evaluation runner for the LTL theorem prover."""

import csv
from pathlib import Path
from time import perf_counter
from statistics import mean, median

from Component_1.checker import check_derivation
from Component_3.search import search, show
from Component_4.benchmarks import BENCHMARKS, formula_size


OUTPUT_PATH = Path(__file__).parent / "results.csv"


def evaluate_benchmark(benchmark):

    goal = benchmark.formula

    result = {
        "name": benchmark.name,
        "formula": show(goal),
        "category": benchmark.category,
        "difficulty": benchmark.difficulty,
        "valid": benchmark.valid,
        "in_fragment": benchmark.in_fragment,
        "formula_size": formula_size(goal),
        "search_result": "NOT FOUND",
        "checker_result": "N/A",
        "search_time_ms": 0.0,
        "verification_time_ms": 0.0,
        "proof_length": 0,
        "error": "",
        "justification": benchmark.justification,
    }

    # measure proof search independently
    start = perf_counter()

    try:
        lines = search(goal)

    except Exception as exc:
        result["search_time_ms"] = (
            perf_counter() - start
        ) * 1000
        result["search_result"] = "ERROR"
        result["error"] = f"{type(exc).__name__}: {exc}"
        return result

    result["search_time_ms"] = (
        perf_counter() - start
    ) * 1000

    # search failure does not imply invalidity
    if lines is None:
        return result

    result["search_result"] = "FOUND"
    result["proof_length"] = len(lines)

    # independently verify the candidate proof
    start = perf_counter()

    try:
        checked = check_derivation(goal, lines)
        result["checker_result"] = checked.status

        if not checked.accepted:
            result["error"] = checked.reason

    except Exception as exc:
        result["checker_result"] = "ERROR"
        result["error"] = f"{type(exc).__name__}: {exc}"

    result["verification_time_ms"] = (
        perf_counter() - start
    ) * 1000

    return result


def percentage(numerator, denominator):
    if denominator == 0:
        return "N/A"

    return f"{100 * numerator / denominator:.2f}%"


def print_summary(results, title):
    """Print aggregate performance for a benchmark subset."""

    valid = [r for r in results if r["valid"]]
    invalid = [r for r in results if not r["valid"]]

    found = [
        r for r in results
        if r["search_result"] == "FOUND"
    ]

    accepted = [
        r for r in results
        if r["checker_result"] == "ACCEPT"
    ]

    valid_proved = [
        r for r in valid
        if r["checker_result"] == "ACCEPT"
    ]

    invalid_accepted = [
        r for r in invalid
        if r["checker_result"] == "ACCEPT"
    ]

    missed = [
        r for r in valid
        if r["checker_result"] != "ACCEPT"
    ]

    errors = [
        r for r in results
        if r["search_result"] == "ERROR"
        or r["checker_result"] == "ERROR"
    ]

    print(f"\n{'=' * 60}")
    print(title)
    print("=" * 60)

    print(f"Total formulas: {len(results)}")
    print(f"Valid formulas: {len(valid)}")
    print(f"Invalid formulas: {len(invalid)}")
    print(f"Candidate proofs found: {len(found)}")
    print(f"Accepted proofs: {len(accepted)}")
    print(f"Valid formulas proved: {len(valid_proved)}")
    print(f"Valid formulas missed: {len(missed)}")
    print(f"Invalid formulas accepted: {len(invalid_accepted)}")
    print(f"Execution errors: {len(errors)}")

    print(
        "Valid formula coverage: "
        f"{percentage(len(valid_proved), len(valid))}"
    )

    print(
        "False acceptance rate: "
        f"{percentage(len(invalid_accepted), len(invalid))}"
    )

    print(
        "Generated proof acceptance rate: "
        f"{percentage(len(accepted), len(found))}"
    )

    if results:
        times = [r["search_time_ms"] for r in results]

        print(f"Mean search time: {mean(times):.3f} ms")
        print(f"Median search time: {median(times):.3f} ms")
        print(f"Maximum search time: {max(times):.3f} ms")

    if accepted:
        lengths = [r["proof_length"] for r in accepted]
        verification_times = [
            r["verification_time_ms"] for r in accepted
        ]

        print(f"Mean proof length: {mean(lengths):.2f}")
        print(f"Median proof length: {median(lengths):.2f}")
        print(f"Maximum proof length: {max(lengths)}")

        print(
            "Mean verification time: "
            f"{mean(verification_times):.3f} ms"
        )


def print_category_results(results):
    """Report coverage separately for each benchmark category."""

    categories = list(dict.fromkeys(
        r["category"] for r in results
    ))

    print("\n" + "=" * 60)
    print("RESULTS BY CATEGORY")
    print("=" * 60)

    for category in categories:
        group = [
            r for r in results
            if r["category"] == category
        ]

        valid = [r for r in group if r["valid"]]

        proved = [
            r for r in valid
            if r["checker_result"] == "ACCEPT"
        ]

        false_accepts = [
            r for r in group
            if not r["valid"]
            and r["checker_result"] == "ACCEPT"
        ]

        times = [r["search_time_ms"] for r in group]

        print(f"\n{category}")
        print(f"  Total: {len(group)}")
        print(f"  Valid proved: {len(proved)}/{len(valid)}")
        print(f"  Coverage: {percentage(len(proved), len(valid))}")
        print(f"  False acceptances: {len(false_accepts)}")
        print(f"  Mean search time: {mean(times):.3f} ms")


def print_failures(results):
    # identify the smallest valid formula without an accepted proof

    missed = sorted(
        [
            r for r in results
            if r["valid"]
            and r["checker_result"] != "ACCEPT"
        ],
        key=lambda r: (r["formula_size"], r["name"])
    )

    print("\n" + "=" * 60)
    print("VALID FORMULAS MISSED")
    print("=" * 60)

    if not missed:
        print("All valid benchmarks were proved.")
        return

    for r in missed:
        print(
            f"{r['name']}: {r['formula']} "
            f"(size={r['formula_size']}, "
            f"search={r['search_result']}, "
            f"checker={r['checker_result']})"
        )

    smallest = missed[0]

    print("\nSmallest valid failure (all benchmarks):")
    print(f"  ID: {smallest['name']}")
    print(f"  Formula: {smallest['formula']}")
    print(f"  AST size: {smallest['formula_size']}")
    print(f"  Category: {smallest['category']}")
    print(f"  Validity: {smallest['justification']}")

    core_missed = [
        r for r in missed if r["in_fragment"]
    ]

    if core_missed:
        smallest_core = core_missed[0]

        print("\nSmallest valid failure within target fragment:")
        print(f"  ID: {smallest_core['name']}")
        print(f"  Formula: {smallest_core['formula']}")
        print(f"  AST size: {smallest_core['formula_size']}")
        print(f"  Validity: {smallest_core['justification']}")


def save_results(results):
    # export individual benchmark results to csv file

    with OUTPUT_PATH.open(
        "w", newline="", encoding="utf-8"
    ) as file:
        writer = csv.DictWriter(
            file,
            fieldnames=list(results[0].keys())
        )

        writer.writeheader()
        writer.writerows(results)

    print(f"\nResults saved to: {OUTPUT_PATH}")


def main():
    results = []

    print(f"Running {len(BENCHMARKS)} benchmarks...\n")

    for i, benchmark in enumerate(BENCHMARKS, start=1):
        result = evaluate_benchmark(benchmark)
        results.append(result)

        print(
            f"[{i:02d}/{len(BENCHMARKS)}] "
            f"{result['name']} | "
            f"valid={result['valid']} | "
            f"{result['search_result']} | "
            f"{result['checker_result']} | "
            f"{result['search_time_ms']:.3f} ms",
            flush=True
        )

    save_results(results)

    print_summary(results, "OVERALL RESULTS")

    print_summary(
        [r for r in results if r["in_fragment"]],
        "TARGET FRAGMENT RESULTS"
    )

    print_summary(
        [r for r in results if not r["in_fragment"]],
        "OUTSIDE FRAGMENT RESULTS"
    )

    print_category_results(results)
    print_failures(results)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Empirical census of small rigid magmas.

For each sampled magma (A, ·) on n elements, computes:
  - Automorphism group size (rigid iff |Aut| = 1)
  - Structural properties of rigid magmas: absorbers, identities,
    idempotents, row/column uniqueness, non-trivial sub-magmas, etc.

Usage:
  uv run python rigid_census.py --max-n 5 --samples 1000
  uv run python rigid_census.py --max-n 8 --samples 100000
"""

import argparse
import itertools
import time
from collections import defaultdict

import numpy as np


def random_magma(n: int, rng: np.random.Generator) -> np.ndarray:
    """Return a random Cayley table (n x n) with entries in {0, ..., n-1}."""
    return rng.integers(0, n, size=(n, n))


def all_magmas(n: int):
    """Yield every Cayley table on n elements (n^(n^2) tables)."""
    cells = n * n
    for combo in itertools.product(range(n), repeat=cells):
        yield np.array(combo, dtype=np.int64).reshape(n, n)


def automorphism_count(table: np.ndarray, n: int) -> int:
    """Count automorphisms by brute-force over all n! permutations."""
    count = 0
    for perm in itertools.permutations(range(n)):
        sigma = np.array(perm, dtype=np.int64)
        # Check σ(a·b) == σ(a)·σ(b) for all a, b
        # Left side: sigma[table[a, b]] for all a, b
        lhs = sigma[table]
        # Right side: table[sigma[a], sigma[b]] for all a, b
        rhs = table[np.ix_(sigma, sigma)]
        if np.array_equal(lhs, rhs):
            count += 1
    return count


def analyze_structure(table: np.ndarray, n: int) -> dict:
    """Compute structural properties of a magma."""
    props = {}

    # Left absorber: e·x = e for all x
    props["left_absorber"] = any(
        np.all(table[e, :] == e) for e in range(n)
    )

    # Right absorber: x·e = e for all x
    props["right_absorber"] = any(
        np.all(table[:, e] == e) for e in range(n)
    )

    # Left identity: e·x = x for all x
    elems = np.arange(n)
    props["left_identity"] = any(
        np.array_equal(table[e, :], elems) for e in range(n)
    )

    # Right identity: x·e = x for all x
    props["right_identity"] = any(
        np.array_equal(table[:, e], elems) for e in range(n)
    )

    # Idempotent: e·e = e for some e
    props["idempotent"] = any(table[e, e] == e for e in range(n))

    # All rows distinct
    props["all_rows_distinct"] = len(set(map(tuple, table))) == n

    # All columns distinct
    props["all_cols_distinct"] = len(set(map(tuple, table.T))) == n

    # Non-trivial sub-magma: subset S with 1 < |S| < n, closed under ·
    props["nontrivial_sub"] = False
    for size in range(2, n):
        for subset in itertools.combinations(range(n), size):
            s = set(subset)
            closed = True
            for a in subset:
                for b in subset:
                    if table[a, b] not in s:
                        closed = False
                        break
                if not closed:
                    break
            if closed:
                props["nontrivial_sub"] = True
                break
        if props["nontrivial_sub"]:
            break

    # Boolean sub-algebra: two distinct left-absorbers
    left_abs = [e for e in range(n) if np.all(table[e, :] == e)]
    props["boolean_sub"] = len(left_abs) >= 2

    # Structureless rigid: all rows distinct, but NO absorber, NO identity, NO non-trivial sub
    props["structureless"] = (
        props["all_rows_distinct"]
        and not props["left_absorber"]
        and not props["right_absorber"]
        and not props["left_identity"]
        and not props["right_identity"]
        and not props["nontrivial_sub"]
    )

    return props


def run_census(n: int, samples: int, exhaustive: bool):
    """Run census for magmas of order n."""
    stats = defaultdict(int)
    stats["total"] = 0

    if exhaustive:
        source = all_magmas(n)
        label = f"n={n}, exhaustive ({n}^{n*n} = {n**(n*n):,} magmas)"
    else:
        rng = np.random.default_rng(seed=42 + n)
        label = f"n={n}, {samples:,} samples"

    t0 = time.time()
    count = 0
    target = n ** (n * n) if exhaustive else samples

    while count < target:
        if exhaustive:
            try:
                table = next(source)
            except StopIteration:
                break
        else:
            table = random_magma(n, rng)

        count += 1
        stats["total"] += 1

        aut = automorphism_count(table, n)
        if aut == 1:
            stats["rigid"] += 1
            props = analyze_structure(table, n)
            for key, val in props.items():
                if val:
                    stats[key] += 1

        # Progress for long runs
        if count % 10000 == 0:
            elapsed = time.time() - t0
            rate = count / elapsed
            eta = (target - count) / rate
            print(
                f"  [{count:,}/{target:,}] "
                f"{elapsed:.1f}s elapsed, ~{eta:.0f}s remaining",
                flush=True,
            )

    elapsed = time.time() - t0
    return label, stats, elapsed


def print_results(label: str, stats: dict, elapsed: float):
    """Pretty-print census results."""
    total = stats["total"]
    rigid = stats["rigid"]
    print(f"\n{label}  ({elapsed:.1f}s)")
    print(f"  Total:  {total:,}")
    print(f"  Rigid:  {rigid:,} ({100*rigid/total:.1f}%)")

    if rigid == 0:
        print("  (no rigid magmas found)")
        return

    properties = [
        ("left_absorber", "Has left absorber"),
        ("right_absorber", "Has right absorber"),
        ("left_identity", "Has left identity"),
        ("right_identity", "Has right identity"),
        ("idempotent", "Has idempotent"),
        ("all_rows_distinct", "All rows distinct"),
        ("all_cols_distinct", "All cols distinct"),
        ("nontrivial_sub", "Has non-trivial sub"),
        ("boolean_sub", "Boolean sub-algebra"),
        ("structureless", "Structureless rigid"),
    ]

    print("  Of rigid:")
    for key, desc in properties:
        c = stats.get(key, 0)
        marker = "  <-- key" if key == "structureless" else ""
        print(f"    {desc:<25s} {c:>8,} ({100*c/rigid:5.1f}%){marker}")


def main():
    parser = argparse.ArgumentParser(description="Census of small rigid magmas")
    parser.add_argument(
        "--max-n", type=int, default=6, help="Largest n to test (default: 6)"
    )
    parser.add_argument(
        "--samples",
        type=int,
        default=100_000,
        help="Samples per n for non-exhaustive (default: 100000)",
    )
    args = parser.parse_args()

    print("=" * 60)
    print("  Rigid Magma Census")
    print("=" * 60)

    for n in range(3, args.max_n + 1):
        # n=3 is small enough for exhaustive enumeration (19,683 tables)
        exhaustive = n <= 3
        label, stats, elapsed = run_census(
            n, args.samples, exhaustive=exhaustive
        )
        print_results(label, stats, elapsed)

    print("\n" + "=" * 60)
    print("  Done.")
    print("=" * 60)


if __name__ == "__main__":
    main()

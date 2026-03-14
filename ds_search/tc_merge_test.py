#!/usr/bin/env python3
"""
Test whether any pair of TC elements {⊤, Q, E, ρ, f, g, η} can be merged
(forced to have identical rows AND columns in the Cayley table) while still
satisfying all Ψ₁₆ᶠ axioms.

21 pairs total. For each pair (a, b), we add:
  ∀j: dot[a][j] == dot[b][j]   (same row)
  ∀i: dot[i][a] == dot[i][b]   (same column)
and check SAT/UNSAT.
"""

import time
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from itertools import combinations
from ds_search.n16_freedom import build_solver, N, NAMES

# The 7 TC elements and their indices
TC_ELEMENTS = {
    "⊤": 0,
    "Q": 6,
    "E": 7,
    "ρ": 8,
    "f": 2,
    "g": 4,
    "η": 9,
}

TC_NAMES = list(TC_ELEMENTS.keys())
TC_INDICES = list(TC_ELEMENTS.values())


def test_merge(s, dot, a_idx, b_idx, a_name, b_name):
    """Test if merging elements a and b is SAT."""
    s.push()

    # Force identical rows: dot[a][j] == dot[b][j] for all j
    for j in range(N):
        s.add(dot[a_idx][j] == dot[b_idx][j])

    # Force identical columns: dot[i][a] == dot[i][b] for all i
    for i in range(N):
        s.add(dot[i][a_idx] == dot[i][b_idx])

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0

    s.pop()
    return result, elapsed


def main():
    print("=" * 70)
    print("TC ELEMENT MERGE TEST — Ψ₁₆ᶠ (N=16)")
    print("Can any pair of {⊤, Q, E, ρ, f, g, η} be identified?")
    print("=" * 70)

    s, dot = build_solver()

    # First verify base is SAT
    print("\nVerifying base solver is SAT...", flush=True)
    t0 = time.time()
    base_result = s.check()
    base_time = time.time() - t0
    print(f"  Base: {base_result} ({base_time:.1f}s)")

    if str(base_result) != "sat":
        print("  ERROR: Base solver is not SAT. Cannot proceed.")
        return

    pairs = list(combinations(range(len(TC_NAMES)), 2))
    print(f"\nTesting {len(pairs)} pairs...\n")
    print(f"{'Pair':>12s}  {'Result':>8s}  {'Time':>8s}")
    print("-" * 34)

    results = {}
    sat_count = 0
    unsat_count = 0

    for i, j in pairs:
        a_name, b_name = TC_NAMES[i], TC_NAMES[j]
        a_idx, b_idx = TC_INDICES[i], TC_INDICES[j]
        label = f"{a_name}={b_name}"

        result, elapsed = test_merge(s, dot, a_idx, b_idx, a_name, b_name)
        result_str = str(result).upper()
        results[label] = result_str

        if result_str == "SAT":
            sat_count += 1
        elif result_str == "UNSAT":
            unsat_count += 1

        print(f"{label:>12s}  {result_str:>8s}  {elapsed:>7.1f}s", flush=True)

    print("-" * 34)
    print(f"\n{'=' * 70}")
    print("SUMMARY")
    print(f"{'=' * 70}")
    print(f"  Total pairs:  {len(pairs)}")
    print(f"  UNSAT:        {unsat_count}  (merge blocked by axioms)")
    print(f"  SAT:          {sat_count}  (merge possible)")
    other = len(pairs) - sat_count - unsat_count
    if other:
        print(f"  UNKNOWN:      {other}  (timeout/unknown)")

    if sat_count > 0:
        print(f"\n  Mergeable pairs:")
        for label, r in results.items():
            if r == "SAT":
                print(f"    {label}")

    if unsat_count == len(pairs):
        print(f"\n  All 21 pairs are UNSAT — no TC element can be identified")
        print(f"  with any other. The 7-element TC set is irreducible.")


if __name__ == "__main__":
    main()

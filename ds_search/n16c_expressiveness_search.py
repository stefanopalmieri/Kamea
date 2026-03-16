#!/usr/bin/env python3
"""
Search for the maximally expressive Ψ₁₆ᶜ table.

The Ψ₁₆ᶜ axiom constraints (INC/DEC cycles, INV involution, cancellation
rules, etc.) admit many satisfying tables. The previous search took the
first model Z3 returned. This script searches for the model that maximizes
compositional expressiveness — the number of distinct values produced by
pairwise compositions among all non-absorber elements.

Usage:
  uv run python -m ds_search.n16c_expressiveness_search
  uv run python -m ds_search.n16c_expressiveness_search --models 100
"""

import sys
import os
import time
from collections import Counter

import numpy as np
from z3 import Or, sat

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ds_search.n16_c_interop import build_solver, N, NAMES, verify_table, print_table
from ds_search.axiom_explorer import extract_table


# Non-absorber elements (the ones that contribute to expressiveness)
ACTIVE = list(range(2, N))  # elements 2..15

# Named role elements (TC7 + extensions)
TC7 = [0, 6, 7, 2, 4, 8, 9]  # ⊤, Q, E, f, g, ρ, η
EXTENSIONS = [12, 13, 14, 15]  # SEQ, INC, INV, DEC
ALL_NAMED = TC7 + [3, 5, 10] + EXTENSIONS  # + τ, 5, Y


def expressiveness_score(table):
    """
    Score a table by compositional expressiveness.

    Returns a tuple (1-step distinct values among active elements,
    2-step distinct values, 1-step among all named roles,
    2-step among all named roles).
    """
    # 1-step among all active (non-absorber) elements
    vals_1_active = set()
    for a in ACTIVE:
        for b in ACTIVE:
            vals_1_active.add(table[a][b])

    # 2-step among active elements
    vals_2_active = set()
    for a in ACTIVE:
        for b in ACTIVE:
            ab = table[a][b]
            for c in ACTIVE:
                vals_2_active.add(table[ab][c] if ab < N else 0)
    # Actually, simpler: dot(a, dot(b, c))
    vals_2_active = set()
    for a in ACTIVE:
        for b in ACTIVE:
            for c in ACTIVE:
                bc = table[b][c]
                vals_2_active.add(table[a][bc])

    # 1-step among all named role elements
    vals_1_named = set()
    for a in ALL_NAMED:
        for b in ALL_NAMED:
            vals_1_named.add(table[a][b])

    # 2-step among named
    vals_2_named = set()
    for a in ALL_NAMED:
        for b in ALL_NAMED:
            for c in ALL_NAMED:
                bc = table[b][c]
                vals_2_named.add(table[a][bc])

    return (len(vals_1_active), len(vals_2_active),
            len(vals_1_named), len(vals_2_named))


def cancellation_count(table):
    """Count how many cancellation rules hold perfectly on core [2,6)."""
    Q, E = 6, 7
    INC, DEC, INV = 13, 15, 14
    core = range(2, 6)
    count = 0

    # E·(Q·x) = x
    if all(table[E][table[Q][x]] == x for x in core):
        count += 1
    # Q·(E·x) = x
    if all(table[Q][table[E][x]] == x for x in core):
        count += 1
    # INC·(DEC·x) = x
    if all(table[INC][table[DEC][x]] == x for x in core):
        count += 1
    # DEC·(INC·x) = x
    if all(table[DEC][table[INC][x]] == x for x in core):
        count += 1
    # INV·(INV·x) = x (on ALL elements, not just core)
    if all(table[INV][table[INV][x]] == x for x in range(N)):
        count += 1

    return count


def wl_refine(table, n, max_rounds=100):
    """WL-1 color refinement. Returns (num_colors, rounds)."""
    arr = np.array(table, dtype=np.int64)
    init_sigs = {}
    colors = np.zeros(n, dtype=np.int64)
    for x in range(n):
        row_spec = tuple(sorted(Counter(int(v) for v in arr[x, :]).values()))
        col_spec = tuple(sorted(Counter(int(v) for v in arr[:, x]).values()))
        is_idemp = int(arr[x, x]) == x
        sig = (row_spec, col_spec, is_idemp)
        if sig not in init_sigs:
            init_sigs[sig] = len(init_sigs)
        colors[x] = init_sigs[sig]

    for round_num in range(max_rounds):
        sig_to_id = {}
        new_colors = np.zeros(n, dtype=np.int64)
        for x in range(n):
            neighbors = []
            for y in range(n):
                neighbors.append((int(colors[y]),
                                  int(colors[arr[x, y]]),
                                  int(colors[arr[y, x]])))
            neighbors.sort()
            sig = (int(colors[x]), tuple(neighbors))
            if sig not in sig_to_id:
                sig_to_id[sig] = len(sig_to_id)
            new_colors[x] = sig_to_id[sig]
        num_old = len(set(colors))
        num_new = len(set(new_colors))
        colors = new_colors
        if num_new == num_old:
            return num_new, round_num + 1
        if num_new == n:
            return n, round_num + 1
    return len(set(colors)), max_rounds


def main():
    max_models = 50
    for i, arg in enumerate(sys.argv):
        if arg == "--models" and i + 1 < len(sys.argv):
            max_models = int(sys.argv[i + 1])

    print("=" * 70)
    print(f"Ψ₁₆ᶜ EXPRESSIVENESS SEARCH — finding maximally expressive table")
    print(f"Searching up to {max_models} models")
    print("=" * 70)

    s, dot = build_solver()

    best_score = None
    best_table = None
    best_idx = -1
    all_scores = []

    for model_num in range(max_models):
        t0 = time.time()
        result = s.check()
        elapsed = time.time() - t0

        if result != sat:
            print(f"\n  Model {model_num + 1}: {result} ({elapsed:.1f}s) — exhausted")
            break

        table = extract_table(s.model(), dot, N)
        score = expressiveness_score(table)
        cancels = cancellation_count(table)
        wl_colors, wl_rounds = wl_refine(table, N)
        rigid = wl_colors == N

        all_scores.append(score)

        # Primary metric: 1-step active values. Tiebreak: 2-step active.
        score_key = (score[0], score[1], score[2], score[3])

        if best_score is None or score_key > best_score:
            best_score = score_key
            best_table = [row[:] for row in table]
            best_idx = model_num

        status = "★ NEW BEST" if model_num == best_idx else ""
        print(f"  Model {model_num + 1:3d}: "
              f"1s-act={score[0]:2d} 2s-act={score[1]:2d} "
              f"1s-named={score[2]:2d} 2s-named={score[3]:2d} "
              f"cancel={cancels} rigid={'Y' if rigid else 'N'} "
              f"({elapsed:.1f}s) {status}", flush=True)

        # Block this table
        block = Or([dot[i][j] != table[i][j]
                    for i in range(N) for j in range(N)])
        s.add(block)

    n_found = len(all_scores)
    print(f"\n{'='*70}")
    print(f"SEARCH COMPLETE — {n_found} models examined")
    print(f"{'='*70}")

    if not best_table:
        print("  No models found!")
        return

    # Score distribution
    act1_scores = [s[0] for s in all_scores]
    act2_scores = [s[1] for s in all_scores]
    print(f"\n  1-step active: min={min(act1_scores)}, max={max(act1_scores)}, "
          f"mean={sum(act1_scores)/len(act1_scores):.1f}")
    print(f"  2-step active: min={min(act2_scores)}, max={max(act2_scores)}, "
          f"mean={sum(act2_scores)/len(act2_scores):.1f}")

    print(f"\n  Best model: #{best_idx + 1}")
    print(f"  Score: 1s-act={best_score[0]}, 2s-act={best_score[1]}, "
          f"1s-named={best_score[2]}, 2s-named={best_score[3]}")

    # Print best table
    print_table(best_table)

    # Print as Python
    print("\n  Python TABLE:")
    print("TABLE = [")
    for i in range(N):
        row = ",".join(f"{best_table[i][j]:2d}" for j in range(N))
        print(f"    [{row}],")
    print("]")

    # Print as C
    print("\n  C psi_cayley:")
    print("static const uint8_t psi_cayley[16][16] = {")
    for i in range(N):
        row = ",".join(f"{best_table[i][j]:2d}" for j in range(N))
        print(f"    {{{row}}},")
    print("};")

    # Verify
    ok = verify_table(best_table)

    # WL-1 check
    wl_colors, wl_rounds = wl_refine(best_table, N)
    print(f"\n  WL-1: {wl_colors}/{N} colors in {wl_rounds} rounds — "
          f"{'RIGID' if wl_colors == N else 'NOT RIGID'}")

    # Cancellation count
    cancels = cancellation_count(best_table)
    print(f"  Cancellation rules: {cancels}/5")

    # Compare with a random (first) model
    if n_found > 1:
        first_score = all_scores[0]
        print(f"\n  Comparison:")
        print(f"    First model Z3 returned: 1s-act={first_score[0]}, 2s-act={first_score[1]}")
        print(f"    Best model found:        1s-act={best_score[0]}, 2s-act={best_score[1]}")
        improvement_1 = best_score[0] - first_score[0]
        improvement_2 = best_score[1] - first_score[1]
        print(f"    Improvement: +{improvement_1} 1-step values, +{improvement_2} 2-step values")


if __name__ == "__main__":
    main()

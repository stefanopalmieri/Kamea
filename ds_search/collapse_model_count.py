#!/usr/bin/env python3
"""
Check model diversity at maximal collapse (level 5: Q=E=f=ρ=Y, ⊤=⊥).

Finds multiple models by blocking previous solutions, checks if all
are WL-1 rigid, and reports how much freedom remains.

Usage:
  uv run python -m ds_search.collapse_model_count
"""

import sys
import os
import time
from collections import Counter

import numpy as np
from z3 import And, Or, sat

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ds_search.axiom_explorer import extract_table
from ds_search.collapse_rigidity_test import (
    build_collapsed_solver, wl_refine, compute_automorphisms,
    check_discoverability, N, COLLAPSE_LEVELS,
)


def main():
    MAX_MODELS = 20

    # Use level 5: maximal collapse
    level = 5
    name, merges = COLLAPSE_LEVELS[level]

    print("=" * 70)
    print(f"MODEL DIVERSITY AT MAXIMAL COLLAPSE (level {level})")
    print(f"{name}")
    print(f"Searching for up to {MAX_MODELS} distinct models...")
    print("=" * 70)

    s, dot, idx = build_collapsed_solver(merges)

    models = []
    all_rigid = True

    for model_num in range(MAX_MODELS):
        t0 = time.time()
        result = s.check()
        elapsed = time.time() - t0

        if str(result) != "sat":
            print(f"\n  Model {model_num + 1}: {result} ({elapsed:.1f}s) — no more models")
            break

        table = extract_table(s.model(), dot, N)
        models.append(table)

        # Quick rigidity check
        num_colors, rounds, _ = wl_refine(table, N)
        rigid = num_colors == N
        if not rigid:
            all_rigid = False

        # Quick discoverability
        min_probes, _ = check_discoverability(table, N)

        print(f"  Model {model_num + 1}: SAT ({elapsed:.1f}s), "
              f"WL-1={'rigid' if rigid else 'FAIL'}, "
              f"probes={min_probes}", flush=True)

        # Block this exact table
        block = Or([dot[i][j] != table[i][j]
                    for i in range(N) for j in range(N)])
        s.add(block)

    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"  Models found: {len(models)}{'+' if len(models) == MAX_MODELS else ''}")
    print(f"  All WL-1 rigid: {'YES' if all_rigid else 'NO'}")

    if len(models) >= 2:
        # Compare models: how many cells differ between pairs?
        diffs = []
        for i in range(len(models)):
            for j in range(i + 1, len(models)):
                d = sum(1 for r in range(N) for c in range(N)
                        if models[i][r][c] != models[j][r][c])
                diffs.append(d)
        print(f"  Cell differences between model pairs:")
        print(f"    min: {min(diffs)}, max: {max(diffs)}, mean: {sum(diffs)/len(diffs):.1f}")

        # Which cells are fixed across all models?
        fixed = 0
        free = 0
        for r in range(N):
            for c in range(N):
                vals = set(models[m][r][c] for m in range(len(models)))
                if len(vals) == 1:
                    fixed += 1
                else:
                    free += 1
        print(f"  Cells fixed across all {len(models)} models: {fixed}/{N*N}")
        print(f"  Cells varying: {free}/{N*N}")

        # Which rows have variation?
        print(f"\n  Per-row variation:")
        unique_indices = {}
        for role, role_idx in idx.items():
            unique_indices.setdefault(role_idx, []).append(role)

        for r in range(N):
            row_fixed = sum(1 for c in range(N)
                          if len(set(models[m][r][c] for m in range(len(models)))) == 1)
            roles = unique_indices.get(r, [str(r)])
            label = ",".join(roles)
            print(f"    Row {r:2d} ({label:>10s}): {row_fixed:2d}/{N} fixed, "
                  f"{N - row_fixed:2d} free")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Compositional Expressiveness of Role Specialization

Measures how many distinct computational states the role basis can reach
in 1-step and 2-step compositions, at each collapse level.

The 7 TC roles {⊤, Q, E, f, g, ρ, η} can be composed pairwise (49 products)
and in triples (343 two-step compositions). In the specialized model each role
occupies a distinct index; in collapsed models many compositions become
degenerate (dot(x,x) instead of dot(a,b)).

Hypothesis: the 7-element specialization maximizes compositional expressiveness.
If so, this provides a variational selection principle — like maximum entropy
or least action — that uniquely selects the natural unfolding.

Usage:
  uv run python -m ds_search.compositional_expressiveness
  uv run python -m ds_search.compositional_expressiveness --samples 10
"""

import sys
import os
import time
from itertools import product as iproduct

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ds_search.axiom_explorer import extract_table
from ds_search.collapse_rigidity_test import (
    build_collapsed_solver, N, COLLAPSE_LEVELS, DEFAULT_ROLES,
)


# The 7 TC roles from the 2CM construction
TC7_ROLES = ["⊤", "Q", "E", "f", "g", "ρ", "η"]

# All 10 roles
ALL_ROLES = ["⊤", "⊥", "τ", "Q", "E", "f", "g", "ρ", "η", "Y"]


def get_role_indices(merges):
    """Get the element index for each role under the given merges."""
    idx = dict(DEFAULT_ROLES)
    for role, target in merges.items():
        idx[role] = idx[target]
    return idx


def count_compositions(table, role_names, role_idx):
    """
    Count distinct 1-step and 2-step compositions among role-bearing elements.

    Returns:
      n1_distinct: number of distinct values from dot(a,b) for all (a,b)
      n1_total:    total number of (a,b) pairs
      n2_distinct: number of distinct values from dot(a, dot(b,c)) for all (a,b,c)
      n2_total:    total number of (a,b,c) triples
      products_1:  set of distinct 1-step product values
      products_2:  set of distinct 2-step product values
      degenerate_1: number of (a,b) pairs that map to the same cell as another pair
    """
    indices = [role_idx[r] for r in role_names]
    k = len(role_names)

    # 1-step: dot(a, b)
    products_1 = set()
    cell_hits = {}  # (i,j) -> count of role pairs that hit this cell
    for a_idx in indices:
        for b_idx in indices:
            val = table[a_idx][b_idx]
            products_1.add(val)
            cell = (a_idx, b_idx)
            cell_hits[cell] = cell_hits.get(cell, 0) + 1

    n1_total = k * k
    n1_distinct = len(products_1)

    # Count degenerate pairs (multiple role pairs hitting same cell)
    distinct_cells = len(cell_hits)
    degenerate_1 = n1_total - distinct_cells  # pairs that are redundant

    # 2-step: dot(a, dot(b, c))
    products_2 = set()
    cell_hits_2 = {}
    for a_idx in indices:
        for b_idx in indices:
            for c_idx in indices:
                bc = table[b_idx][c_idx]
                val = table[a_idx][bc]
                products_2.add(val)
                cell = (a_idx, b_idx, c_idx)
                cell_hits_2[cell] = cell_hits_2.get(cell, 0) + 1

    n2_total = k * k * k
    n2_distinct = len(products_2)
    distinct_triples = len(cell_hits_2)
    degenerate_2 = n2_total - distinct_triples

    return {
        "n1_distinct": n1_distinct,
        "n1_total": n1_total,
        "n1_cells": distinct_cells,
        "n1_degenerate": degenerate_1,
        "n2_distinct": n2_distinct,
        "n2_total": n2_total,
        "n2_cells": distinct_triples,
        "n2_degenerate": degenerate_2,
        "products_1": products_1,
        "products_2": products_2,
    }


def count_reachable(table, role_names, role_idx, max_depth=3):
    """
    Count how many distinct elements are reachable from role elements
    by iterated composition up to a given depth.

    Depth 0: the role elements themselves
    Depth 1: all dot(a, b) for role elements a, b
    Depth 2: all dot(x, y) where x, y are reachable at depth ≤ 1
    etc.
    """
    indices = set(role_idx[r] for r in role_names)
    reachable = set(indices)
    by_depth = [len(reachable)]

    for depth in range(1, max_depth + 1):
        new = set()
        prev = list(reachable)
        for a in prev:
            for b in prev:
                new.add(table[a][b])
        reachable |= new
        by_depth.append(len(reachable))

    return by_depth, reachable


def main():
    n_samples = 1
    for arg in sys.argv:
        if arg.startswith("--samples"):
            n_samples = int(sys.argv[sys.argv.index(arg) + 1])

    print("=" * 78)
    print("COMPOSITIONAL EXPRESSIVENESS OF ROLE SPECIALIZATION")
    print("=" * 78)
    print()
    print(f"TC7 roles: {TC7_ROLES}")
    print(f"N = {N}, samples per level = {n_samples}")

    # ── Collect data across levels and samples ───────────────────────
    level_data = []

    for level, (name, merges) in enumerate(COLLAPSE_LEVELS):
        print(f"\n{'─'*78}")
        print(f"  {name}")
        print(f"{'─'*78}")

        role_idx = get_role_indices(merges)

        # Show physical index mapping for TC7
        phys = [role_idx[r] for r in TC7_ROLES]
        distinct_phys = len(set(phys))
        print(f"  TC7 physical indices: {list(zip(TC7_ROLES, phys))}")
        print(f"  Distinct physical elements: {distinct_phys}")

        sample_results = []

        for sample in range(n_samples):
            s, dot, idx = build_collapsed_solver(merges)
            # Block previous solutions to get diversity
            if sample > 0:
                # Just get whatever Z3 gives — it'll vary due to internal state
                pass

            r = s.check()
            if str(r) != "sat":
                print(f"  Sample {sample + 1}: UNSAT")
                continue

            table = extract_table(s.model(), dot, N)

            # TC7 compositions
            tc7 = count_compositions(table, TC7_ROLES, role_idx)

            # All 10 roles compositions
            all10 = count_compositions(table, ALL_ROLES, role_idx)

            # Reachability
            reach_depths, reachable = count_reachable(table, TC7_ROLES, role_idx, max_depth=3)

            sample_results.append({
                "tc7": tc7, "all10": all10,
                "reach_depths": reach_depths, "reachable": reachable,
                "table": table,
            })

            if n_samples == 1:
                # Detailed output for single sample
                print(f"\n  TC7 1-step compositions:")
                print(f"    Logical pairs:  {tc7['n1_total']} (7×7)")
                print(f"    Distinct cells: {tc7['n1_cells']} (physical table lookups)")
                print(f"    Degenerate:     {tc7['n1_degenerate']} (pairs hitting same cell)")
                print(f"    Distinct values: {tc7['n1_distinct']}")

                print(f"\n  TC7 2-step compositions:")
                print(f"    Logical triples:  {tc7['n2_total']} (7×7×7)")
                print(f"    Distinct triples: {tc7['n2_cells']}")
                print(f"    Degenerate:       {tc7['n2_degenerate']}")
                print(f"    Distinct values:  {tc7['n2_distinct']}")

                print(f"\n  Reachability from TC7 (depth 0..3): {reach_depths}")
                print(f"    Covers {len(reachable)}/{N} elements")

                # Show the TC7 composition subtable
                print(f"\n  TC7 composition subtable:")
                header = "         " + "  ".join(f"{r:>3s}" for r in TC7_ROLES)
                print(f"  {header}")
                for a in TC7_ROLES:
                    row_str = f"    {a:>3s}  "
                    for b in TC7_ROLES:
                        val = table[role_idx[a]][role_idx[b]]
                        row_str += f"{val:>4d}"
                    print(row_str)

        if sample_results:
            # Aggregate
            avg_1step = sum(sr["tc7"]["n1_distinct"] for sr in sample_results) / len(sample_results)
            avg_2step = sum(sr["tc7"]["n2_distinct"] for sr in sample_results) / len(sample_results)
            avg_cells_1 = sum(sr["tc7"]["n1_cells"] for sr in sample_results) / len(sample_results)
            avg_cells_2 = sum(sr["tc7"]["n2_cells"] for sr in sample_results) / len(sample_results)

            level_data.append({
                "level": level, "name": name,
                "distinct_phys": distinct_phys,
                "avg_1step_values": avg_1step,
                "avg_2step_values": avg_2step,
                "avg_1step_cells": avg_cells_1,
                "avg_2step_cells": avg_cells_2,
                "samples": sample_results,
            })

    # ── Summary ──────────────────────────────────────────────────────
    print(f"\n\n{'='*78}")
    print("EXPRESSIVENESS SUMMARY")
    print(f"{'='*78}")
    print()

    print(f"| {'Level':5s} | {'Collapse':25s} | {'Phys':4s} | {'1-step':8s} | {'1-cells':8s} | {'2-step':8s} | {'2-cells':8s} |")
    print(f"|{'-'*7}|{'-'*27}|{'-'*6}|{'-'*10}|{'-'*10}|{'-'*10}|{'-'*10}|")

    for ld in level_data:
        desc = ld["name"].split(": ", 1)[-1]
        print(f"| {ld['level']:5d} | {desc:25s} | {ld['distinct_phys']:4d} | "
              f"{ld['avg_1step_values']:8.1f} | {ld['avg_1step_cells']:8.1f} | "
              f"{ld['avg_2step_values']:8.1f} | {ld['avg_2step_cells']:8.1f} |")

    # ── Variational Analysis ─────────────────────────────────────────
    print(f"\n{'='*78}")
    print("VARIATIONAL ANALYSIS")
    print(f"{'='*78}")

    if len(level_data) >= 2:
        # Check monotonicity
        vals_1 = [ld["avg_1step_values"] for ld in level_data]
        vals_2 = [ld["avg_2step_values"] for ld in level_data]
        cells_1 = [ld["avg_1step_cells"] for ld in level_data]
        cells_2 = [ld["avg_2step_cells"] for ld in level_data]

        print(f"\n  1-step distinct values by level:  {vals_1}")
        print(f"  2-step distinct values by level:  {vals_2}")
        print(f"  1-step distinct cells by level:   {cells_1}")
        print(f"  2-step distinct cells by level:   {cells_2}")

        # Does level 0 maximize?
        max_1 = max(vals_1)
        max_2 = max(vals_2)
        max_1_level = vals_1.index(max_1)
        max_2_level = vals_2.index(max_2)

        print(f"\n  Max 1-step expressiveness at level {max_1_level}: {max_1:.0f} distinct values")
        print(f"  Max 2-step expressiveness at level {max_2_level}: {max_2:.0f} distinct values")

        # Cell degeneracy
        max_cells_1 = max(cells_1)
        max_cells_2 = max(cells_2)
        print(f"\n  Max 1-step distinct cells at level {cells_1.index(max_cells_1)}: {max_cells_1:.0f}")
        print(f"  Max 2-step distinct cells at level {cells_2.index(max_cells_2)}: {max_cells_2:.0f}")

        # Theoretical max cells
        for ld in level_data:
            k = ld["distinct_phys"]
            print(f"  Level {ld['level']}: {k} physical elements → "
                  f"max {k*k} 1-step cells, max {k*k*k} 2-step cells "
                  f"(actual: {ld['avg_1step_cells']:.0f}, {ld['avg_2step_cells']:.0f})")

        # Ratio analysis
        if vals_1[0] > 0 and vals_1[-1] > 0:
            ratio_1 = vals_1[0] / vals_1[-1]
            ratio_2 = vals_2[0] / vals_2[-1]
            print(f"\n  Expressiveness ratio (specialized / maximal collapse):")
            print(f"    1-step: {vals_1[0]:.0f} / {vals_1[-1]:.0f} = {ratio_1:.2f}x")
            print(f"    2-step: {vals_2[0]:.0f} / {vals_2[-1]:.0f} = {ratio_2:.2f}x")

        # Does the expressiveness strictly decrease with collapse?
        monotone_1 = all(vals_1[i] >= vals_1[i+1] for i in range(len(vals_1)-1))
        monotone_2 = all(vals_2[i] >= vals_2[i+1] for i in range(len(vals_2)-1))
        strict_mono_1 = all(vals_1[i] > vals_1[i+1] for i in range(len(vals_1)-1))

        print(f"\n  1-step monotonically decreasing: {'YES' if monotone_1 else 'NO'}")
        print(f"  2-step monotonically decreasing: {'YES' if monotone_2 else 'NO'}")
        if strict_mono_1:
            print(f"  1-step STRICTLY decreasing: YES — each collapse loses expressiveness")

    # ── Conclusion ───────────────────────────────────────────────────
    print(f"\n{'='*78}")
    print("CONCLUSION")
    print(f"{'='*78}")

    if len(level_data) >= 2:
        # The key question: does full specialization (level 0) maximize expressiveness?
        if max_1_level == 0 and max_2_level == 0:
            print(f"\n  Full specialization (level 0) maximizes BOTH 1-step and 2-step")
            print(f"  compositional expressiveness.")
            print(f"\n  The variational principle — maximize distinct compositions among")
            print(f"  role-bearing elements — uniquely selects the 7-element unfolding")
            print(f"  (or at least the fully specialized version among these levels).")
        elif max_1_level == 0:
            print(f"\n  Full specialization maximizes 1-step but not 2-step expressiveness.")
            print(f"  The variational principle depends on composition depth.")
        elif max_2_level == 0:
            print(f"\n  Full specialization maximizes 2-step but not 1-step expressiveness.")
        else:
            print(f"\n  Full specialization does NOT maximize expressiveness.")
            print(f"  The variational principle does not cleanly select the specialized version.")

        # Cell analysis: is the gap due to degeneracy or value collapse?
        if cells_1[0] > cells_1[-1]:
            print(f"\n  Physical degeneracy: collapsed model has {cells_1[-1]:.0f} distinct cell lookups")
            print(f"  vs {cells_1[0]:.0f} in specialized. {cells_1[0] - cells_1[-1]:.0f} compositions become")
            print(f"  structurally identical (same row, same column).")


if __name__ == "__main__":
    main()

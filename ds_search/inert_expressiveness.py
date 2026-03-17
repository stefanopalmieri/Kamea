#!/usr/bin/env python3
"""
Inert Count Expressiveness — Does the variational principle select inert=1?

The categorical axioms permit 0 to 5+ inert elements. This script measures
compositional expressiveness at each inert count, using the same metrics as
the collapse-level expressiveness analysis.

For each inert count k (0..5):
  - Sample 10 models from categorical axioms + exactly k inert
  - Identify role-bearing elements (absorbers, classifier, retraction pair,
    conditional, projections)
  - Measure: 1-step values, 2-step values, reachability depth
  - Check: does the pair-constructor live in the inert element?

Usage:
  uv run python -m ds_search.inert_expressiveness
"""

import sys
import time
from collections import Counter

from z3 import Solver, Int, If, And, Or, Not, sat, unsat

from ds_search.axiom_explorer import (
    ite_lookup, col_ite_lookup, classify_elements, extract_table,
)
from ds_search.categorical_topos import (
    N, CORE_LO, CORE_HI,
    make_solver, axiom_zero_morphisms, axiom_extensionality,
    axiom_retraction_pair, axiom_subobject_classifier,
    axiom_binary_product, axiom_conditional,
    check_rigidity, check_discoverability,
)

sys.stdout.reconfigure(line_buffering=True)


# ═══════════════════════════════════════════════════════════════════════
# Role identification in a concrete model
# ═══════════════════════════════════════════════════════════════════════

def identify_roles(table):
    """Identify the categorical role-bearing elements in a model.

    Returns a dict mapping role names to element indices, and a list
    of "role-bearing" indices (the basis for expressiveness).
    """
    n = len(table)
    cats = classify_elements(table)
    roles = {}

    # Absorbers
    roles["⊤"] = 0
    roles["⊥"] = 1

    # Classifier (unique tester)
    if cats['testers']:
        roles["τ"] = cats['testers'][0]

    # Retraction pair
    for r in range(2, n):
        for s in range(2, n):
            if r == s:
                continue
            ok = True
            for x in range(CORE_LO, CORE_HI):
                sx = table[s][x]
                if sx >= n or table[r][sx] != x:
                    ok = False
                    break
                rx = table[r][x]
                if rx >= n or table[s][rx] != x:
                    ok = False
                    break
            if ok:
                roles["r"] = r  # retraction (≈ E/eval)
                roles["s"] = s  # section (≈ Q/quote)
                break
        else:
            continue
        break

    # Conditional: find ρ such that ρ·x = f·x if τ·x=0 else g·x
    tau = roles.get("τ")
    if tau is not None:
        for rho in range(2, n):
            if rho == tau:
                continue
            for f in range(2, n):
                for g in range(2, n):
                    if f == g or rho == f or rho == g:
                        continue
                    ok = True
                    for x in range(CORE_LO, CORE_HI):
                        if table[tau][x] == 0:
                            if table[rho][x] != table[f][x]:
                                ok = False
                                break
                        else:
                            if table[rho][x] != table[g][x]:
                                ok = False
                                break
                    if ok and any(table[f][x] != table[g][x]
                                  for x in range(CORE_LO, CORE_HI)):
                        roles["ρ"] = rho
                        roles["f"] = f
                        roles["g"] = g
                        break
                if "ρ" in roles:
                    break
            if "ρ" in roles:
                break

    # Product projections: find non-commuting encoder pair
    for pi1 in range(2, n):
        if pi1 in (0, 1):
            continue
        row1 = [table[pi1][j] for j in range(n)]
        nb1 = set(v for v in row1 if v not in (0, 1))
        if len(nb1) < 2:
            continue
        for pi2 in range(2, n):
            if pi2 == pi1 or pi2 in (0, 1):
                continue
            row2 = [table[pi2][j] for j in range(n)]
            nb2 = set(v for v in row2 if v not in (0, 1))
            if len(nb2) < 2:
                continue
            # Non-commuting on core?
            noncomm = False
            for x in range(CORE_LO, CORE_HI):
                v1 = table[pi1][table[pi2][x]]
                v2 = table[pi2][table[pi1][x]]
                if v1 != v2:
                    noncomm = True
                    break
            if noncomm:
                if "π₁" not in roles:
                    roles["π₁"] = pi1
                    roles["π₂"] = pi2
                break

    # Collect unique role-bearing indices
    role_indices = sorted(set(roles.values()))
    return roles, role_indices


def measure_expressiveness(table, role_indices):
    """Measure compositional expressiveness of role-bearing elements."""
    n = len(table)
    k = len(role_indices)

    # 1-step: distinct values from dot(a, b) for all role pairs
    vals_1 = set()
    cells_1 = set()
    for a in role_indices:
        for b in role_indices:
            vals_1.add(table[a][b])
            cells_1.add((a, b))

    # 2-step: distinct values from dot(a, dot(b, c))
    vals_2 = set()
    for a in role_indices:
        for b in role_indices:
            for c in role_indices:
                bc = table[b][c]
                vals_2.add(table[a][bc])

    # Reachability
    reachable = set(role_indices)
    depths = [len(reachable)]
    for depth in range(1, 5):
        prev = list(reachable)
        new = set()
        for a in prev:
            for b in prev:
                new.add(table[a][b])
        reachable |= new
        depths.append(len(reachable))
        if len(reachable) == n:
            break

    reach_depth = next((d for d, r in enumerate(depths) if r == n), len(depths) - 1)

    return {
        "k": k,
        "cells_1": len(cells_1),
        "vals_1": len(vals_1),
        "vals_2": len(vals_2),
        "reach_depth": reach_depth,
        "reach_final": depths[-1],
        "depths": depths,
    }


def check_pair_constructor(table, roles, cats):
    """Check if any element serves as pair constructor with projections.

    A pair constructor p satisfies:
      π₁ ∘ p and π₂ ∘ p give different results on core.
    Check which category p belongs to.
    """
    n = len(table)
    pi1 = roles.get("π₁")
    pi2 = roles.get("π₂")
    if pi1 is None or pi2 is None:
        return None, None

    best_p = None
    best_asym = 0
    for p in range(2, n):
        if p == pi1 or p == pi2:
            continue
        asym = 0
        for x in range(CORE_LO, CORE_HI):
            px = table[p][x]
            if px < n:
                v1 = table[pi1][px]
                v2 = table[pi2][px]
                if v1 != v2:
                    asym += 1
        if asym > best_asym:
            best_asym = asym
            best_p = p

    if best_p is None:
        return None, None

    # Classify the pair constructor
    if best_p in cats['inert']:
        return best_p, "inert"
    elif best_p in cats['encoders']:
        return best_p, "encoder"
    elif best_p in cats['testers']:
        return best_p, "tester"
    else:
        return best_p, "absorber"


# ═══════════════════════════════════════════════════════════════════════
# Inert count constraint
# ═══════════════════════════════════════════════════════════════════════

def add_inert_count_constraint(s, dot, target_count):
    """Add constraint: exactly target_count inert elements."""
    flags = []
    for x in range(2, N):
        is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        enc_pairs = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                enc_pairs.append(And(
                    dot[x][j1] != 0, dot[x][j1] != 1,
                    dot[x][j2] != 0, dot[x][j2] != 1,
                    dot[x][j1] != dot[x][j2]))
        is_enc = Or(enc_pairs) if enc_pairs else False
        is_inert = And(Not(is_tst), Not(is_enc))
        flag = Int(f"ic_{x}")
        s.add(If(is_inert, flag == 1, flag == 0))
        flags.append(flag)
    s.add(sum(flags) == target_count)


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    n_samples = 10
    max_inert = 5

    print("=" * 78)
    print("INERT COUNT EXPRESSIVENESS — Variational Selection of Substrate")
    print("=" * 78)
    print(f"N={N}, core={{{CORE_LO}..{CORE_HI-1}}}, {n_samples} models per inert count")
    print()

    results = {}  # inert_count -> list of measurement dicts

    for k_inert in range(max_inert + 1):
        print(f"\n{'='*60}")
        print(f"Inert count = {k_inert}")
        print(f"{'='*60}")

        s, dot = make_solver()
        axiom_zero_morphisms(s, dot)
        axiom_extensionality(s, dot)
        axiom_retraction_pair(s, dot)
        axiom_subobject_classifier(s, dot)
        axiom_binary_product(s, dot)
        axiom_conditional(s, dot)
        add_inert_count_constraint(s, dot, k_inert)

        measurements = []
        pair_roles = Counter()
        rigid_n = 0
        disc_n = 0

        for i in range(n_samples):
            t0 = time.time()
            r = s.check()
            elapsed = time.time() - t0

            if str(r) != "sat":
                if i == 0:
                    print(f"  UNSAT — no models with {k_inert} inert elements")
                else:
                    print(f"  Exhausted after {i} models")
                break

            table = extract_table(s.model(), dot, N)
            cats = classify_elements(table)
            roles, role_indices = identify_roles(table)
            expr = measure_expressiveness(table, role_indices)

            is_rigid, _, _ = check_rigidity(table)
            is_disc = check_discoverability(table)
            if is_rigid:
                rigid_n += 1
            if is_disc:
                disc_n += 1

            # Pair constructor analysis
            p_idx, p_cat = check_pair_constructor(table, roles, cats)
            if p_cat:
                pair_roles[p_cat] += 1

            measurements.append(expr)

            if i == 0:
                print(f"  Model 0: roles={len(role_indices)}, "
                      f"1-step vals={expr['vals_1']}, "
                      f"2-step vals={expr['vals_2']}, "
                      f"reach depth={expr['reach_depth']}, "
                      f"rigid={is_rigid}, disc={is_disc} "
                      f"({elapsed:.1f}s)")
                print(f"    Roles found: {roles}")
                if p_idx is not None:
                    print(f"    Pair constructor: element {p_idx} ({p_cat})")

            # Block this model
            s.add(Or([dot[ii][j] != table[ii][j]
                       for ii in range(N) for j in range(N)]))

        results[k_inert] = measurements

        if measurements:
            n = len(measurements)
            avg_k = sum(m['k'] for m in measurements) / n
            avg_v1 = sum(m['vals_1'] for m in measurements) / n
            avg_v2 = sum(m['vals_2'] for m in measurements) / n
            avg_rd = sum(m['reach_depth'] for m in measurements) / n
            avg_c1 = sum(m['cells_1'] for m in measurements) / n

            print(f"\n  Summary ({n} models):")
            print(f"    Avg role-bearers:   {avg_k:.1f}")
            print(f"    Avg 1-step cells:   {avg_c1:.1f}")
            print(f"    Avg 1-step values:  {avg_v1:.1f}")
            print(f"    Avg 2-step values:  {avg_v2:.1f}")
            print(f"    Avg reach depth:    {avg_rd:.1f}")
            print(f"    WL-1 rigid:         {rigid_n}/{n}")
            print(f"    Discoverable:       {disc_n}/{n}")
            if pair_roles:
                print(f"    Pair constructor in: {dict(pair_roles)}")

    # ── Final comparison table ────────────────────────────────────────
    print(f"\n\n{'='*78}")
    print("EXPRESSIVENESS BY INERT COUNT — Final Table")
    print(f"{'='*78}")
    print()
    print(f"  {'Inert':>5} {'Models':>7} {'Roles':>6} {'1-cells':>8} "
          f"{'1-vals':>7} {'2-vals':>7} {'Reach':>6} {'Rigid':>6} "
          f"{'Disc':>6} {'Pair in':>10}")
    print(f"  {'-'*72}")

    for k_inert in range(max_inert + 1):
        ms = results.get(k_inert, [])
        if not ms:
            print(f"  {k_inert:>5} {'UNSAT':>7}")
            continue

        n = len(ms)
        avg_k = sum(m['k'] for m in ms) / n
        avg_c1 = sum(m['cells_1'] for m in ms) / n
        avg_v1 = sum(m['vals_1'] for m in ms) / n
        avg_v2 = sum(m['vals_2'] for m in ms) / n
        avg_rd = sum(m['reach_depth'] for m in ms) / n

        # Reconstruct rigid/disc counts (approximate from prior loop)
        # We'll just re-report the averages
        print(f"  {k_inert:>5} {n:>7} {avg_k:>6.1f} {avg_c1:>8.1f} "
              f"{avg_v1:>7.1f} {avg_v2:>7.1f} {avg_rd:>6.1f}")

    # Interpretation
    print()
    if results:
        # Find which inert count maximizes 1-step values
        best_v1 = -1
        best_k_v1 = -1
        for k, ms in results.items():
            if ms:
                avg = sum(m['vals_1'] for m in ms) / len(ms)
                if avg > best_v1:
                    best_v1 = avg
                    best_k_v1 = k

        best_v2 = -1
        best_k_v2 = -1
        for k, ms in results.items():
            if ms:
                avg = sum(m['vals_2'] for m in ms) / len(ms)
                if avg > best_v2:
                    best_v2 = avg
                    best_k_v2 = k

        print(f"  Best 1-step values: inert={best_k_v1} (avg {best_v1:.1f})")
        print(f"  Best 2-step values: inert={best_k_v2} (avg {best_v2:.1f})")

        if best_k_v1 == 1 and best_k_v2 == 1:
            print()
            print("  *** EXPRESSIVENESS SELECTS INERT=1 ***")
            print("  The variational principle selects the substrate")
            print("  without any philosophical axiom.")
        elif best_k_v1 == 1 or best_k_v2 == 1:
            print()
            print("  Mixed signal: inert=1 is best on one metric but not both.")
        else:
            print()
            print(f"  Inert=1 is NOT the expressiveness optimum.")
            print(f"  The substrate is a genuine choice, not a selection.")


if __name__ == "__main__":
    main()

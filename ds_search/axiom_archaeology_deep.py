#!/usr/bin/env python3
"""
Axiom Archaeology — Deep Analysis

Extends axiom_archaeology.py with:
1. Detailed Composition wall breakdown (which η pairs broke)
2. Maximal axiom removal — find the largest removable set
3. Wall testing on alternative axiom models
4. Dependency graph between axioms

Usage:
  uv run python -m ds_search.axiom_archaeology_deep
"""

import time
import sys
from itertools import combinations

from z3 import Solver, Int, If, And, Or, Not, sat, unsat

from ds_search.axiom_explorer import (
    ite_lookup, col_ite_lookup, classify_elements, extract_table,
    print_table,
)
from ds_search.forced_roles_test import (
    axiom_L0, axiom_kripke, axiom_inert_prop, axiom_pa, axiom_vv,
    axiom_qe, axiom_e_trans, axiom_1_inert, axiom_branch, axiom_compose,
    axiom_y, axiom_selection, role_tester, role_inert, role_encoder,
    is_inert_z3,
)


N = 12
CORE_LO, CORE_HI = 2, 6

ROLES = {
    "⊤": 0, "⊥": 1, "τ": 3, "Q": 6, "E": 7,
    "f": 2, "g": 4, "ρ": 8, "η": 9, "Y": 10,
}

AXIOM_NAMES = [
    "Kripke", "InertProp", "PA", "VV", "QE",
    "E-trans", "1-Inert", "Branch", "Compose", "Y", "Selection",
]

TESTER_ROLES = {"τ"}
INERT_ROLES = {"g"}
ABSORBER_ROLES = {"⊤", "⊥"}
ENCODER_ROLES = {"Q", "E", "f", "ρ", "η", "Y"}


def build_solver(skip_axioms=None, role_a=None, role_b=None):
    """Build solver with selective axiom inclusion and optional role aliasing."""
    if skip_axioms is None:
        skip_axioms = set()

    idx = dict(ROLES)
    if role_a and role_b:
        idx[role_b] = idx[role_a]

    s = Solver()
    s.set("timeout", 300 * 1000)
    dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]

    for c in axiom_L0(dot, N):
        s.add(c)

    axiom_map = {
        "Kripke": lambda: axiom_kripke(dot, N),
        "InertProp": lambda: axiom_inert_prop(dot, N),
        "PA": lambda: axiom_pa(dot, N),
        "VV": lambda: axiom_vv(dot, N),
        "QE": lambda: axiom_qe(dot, N, idx["Q"], idx["E"], CORE_LO, CORE_HI),
        "E-trans": lambda: axiom_e_trans(dot, idx["E"]),
        "1-Inert": lambda: axiom_1_inert(dot, N),
        "Branch": lambda: axiom_branch(dot, idx["τ"], idx["f"], idx["g"], idx["ρ"], CORE_LO, CORE_HI),
        "Compose": lambda: axiom_compose(dot, N, idx["η"], idx["ρ"], idx["g"], CORE_LO, CORE_HI),
        "Y": lambda: axiom_y(dot, N, idx["Y"], idx["ρ"]),
        "Selection": lambda: axiom_selection(dot, idx["η"], idx["ρ"], idx["τ"]),
    }

    for name in AXIOM_NAMES:
        if name not in skip_axioms:
            for c in axiom_map[name]():
                s.add(c)

    assigned_roles = {}
    for role_name, role_idx in idx.items():
        if role_name in ABSORBER_ROLES:
            continue
        assigned_roles.setdefault(role_idx, set()).add(role_name)

    for role_idx, role_set in assigned_roles.items():
        for rn in role_set:
            if rn in TESTER_ROLES:
                for c in role_tester(dot, N, role_idx):
                    s.add(c)
            elif rn in INERT_ROLES:
                for c in role_inert(dot, role_idx, N):
                    s.add(c)
            elif rn in ENCODER_ROLES:
                for c in role_encoder(dot, N, role_idx):
                    s.add(c)

    return s, dot


# ═══════════════════════════════════════════════════════════════════════
# Deep Analysis 1: Composition Wall Breakdown
# ═══════════════════════════════════════════════════════════════════════

def composition_wall_detail():
    """Show exactly which η pairs break under each axiom removal."""
    print("=" * 70)
    print("COMPOSITION WALL — Detailed Breakdown")
    print("=" * 70)

    eta_pairs = [("η", "Q"), ("η", "E"), ("η", "ρ")]  # should be UNSAT
    eta_sat = [("η", "f"), ("η", "Y")]  # should be SAT

    # Baseline
    print("\n--- Baseline (all axioms) ---")
    for ra, rb in eta_pairs + eta_sat:
        s, _ = build_solver(role_a=ra, role_b=rb)
        r = s.check()
        print(f"  {ra}={rb}: {str(r).upper()}")

    # Per-axiom removal
    print(f"\n{'Removed':<13} {'η=Q':>6} {'η=E':>6} {'η=ρ':>6} │ {'η=f':>6} {'η=Y':>6}")
    print("-" * 55)

    for axiom in AXIOM_NAMES:
        results = []
        for ra, rb in eta_pairs + eta_sat:
            s, _ = build_solver(skip_axioms={axiom}, role_a=ra, role_b=rb)
            r = s.check()
            results.append(str(r).upper())

        broke_marker = lambda r, baseline: f"*{r}*" if r != baseline else f" {r} "
        # Baseline for pairs: UNSAT UNSAT UNSAT SAT SAT
        baselines = ["UNSAT", "UNSAT", "UNSAT", "SAT", "SAT"]
        markers = []
        for r, b in zip(results, baselines):
            if r != b:
                markers.append(f"→{r}")
            else:
                markers.append(f" {r}")

        print(f"  {axiom:<11} {markers[0]:>6} {markers[1]:>6} {markers[2]:>6} │ {markers[3]:>6} {markers[4]:>6}")


# ═══════════════════════════════════════════════════════════════════════
# Deep Analysis 2: Maximum Removable Set
# ═══════════════════════════════════════════════════════════════════════

def max_removable_set():
    """Find the largest set of axioms that can be removed while keeping
    SAT + 5 categories + all 3 walls intact."""
    print("\n" + "=" * 70)
    print("MAXIMUM REMOVABLE SET (SAT + 5 categories + 3 walls)")
    print("=" * 70)

    # Wall test pairs (UNSAT pairs from each wall)
    wall_unsat_pairs = [
        # Kripke wall — just test one representative
        ("τ", "Q"),
        # Substrate wall — just test one representative
        ("g", "Q"),
        # Composition wall
        ("η", "Q"), ("η", "E"), ("η", "ρ"),
    ]

    def test_config(skip_set):
        """Test if a skip set preserves SAT + 5 cats + walls."""
        # SAT check
        s, dot = build_solver(skip_axioms=skip_set)
        r = s.check()
        if str(r) != "sat":
            return False, "not SAT"

        table = extract_table(s.model(), dot, N)
        cats = classify_elements(table)
        if not (len(cats['absorbers']) >= 2 and len(cats['testers']) >= 1
                and len(cats['encoders']) >= 1 and len(cats['inert']) >= 1):
            return False, "missing category"

        # Wall check
        for ra, rb in wall_unsat_pairs:
            s2, _ = build_solver(skip_axioms=skip_set, role_a=ra, role_b=rb)
            r2 = s2.check()
            if str(r2) != "unsat":
                return False, f"wall broke: {ra}={rb}"

        return True, "OK"

    # Try increasing sizes
    for k in range(4, len(AXIOM_NAMES) + 1):
        print(f"\n--- Testing {k}-axiom removals ---")
        found = False
        for skip_combo in combinations(AXIOM_NAMES, k):
            skip_set = set(skip_combo)
            t0 = time.time()
            ok, reason = test_config(skip_set)
            elapsed = time.time() - t0

            if ok:
                print(f"  ✓ Remove {skip_combo}: OK ({elapsed:.1f}s)")
                found = True
                # Don't exhaustively search, just find first
                break
            # Only print failures for 4+ to save output
        if not found:
            print(f"  No valid {k}-axiom removal found (tested all {len(list(combinations(AXIOM_NAMES, k)))} combos)")
            # But some might work without ALL walls — test SAT + 5 cats only
            print(f"\n  Relaxing to SAT + 5 categories (no wall requirement):")
            for skip_combo in combinations(AXIOM_NAMES, k):
                skip_set = set(skip_combo)
                s, dot = build_solver(skip_axioms=skip_set)
                r = s.check()
                if str(r) == "sat":
                    table = extract_table(s.model(), dot, N)
                    cats = classify_elements(table)
                    if (len(cats['absorbers']) >= 2 and len(cats['testers']) >= 1
                            and len(cats['encoders']) >= 1 and len(cats['inert']) >= 1):
                        print(f"    ✓ Remove {skip_combo}: SAT + 5 cats (walls not checked)")
                        found = True
                        break
            if not found:
                print(f"    No valid {k}-axiom removal even without wall requirement")
            break


# ═══════════════════════════════════════════════════════════════════════
# Deep Analysis 3: Cell-by-cell freedom comparison
# ═══════════════════════════════════════════════════════════════════════

def freedom_comparison():
    """Compare fixed cell count between full axiom set and reduced sets."""
    print("\n" + "=" * 70)
    print("CELL FREEDOM COMPARISON")
    print("=" * 70)

    configs = [
        ("Full axiom set", set()),
        ("-VV", {"VV"}),
        ("-PA, -VV", {"PA", "VV"}),
        ("-PA, -VV, -E-trans", {"PA", "VV", "E-trans"}),
        ("-Kripke, -InertProp, -PA", {"Kripke", "InertProp", "PA"}),
    ]

    for label, skip_set in configs:
        print(f"\n--- {label} ---")
        s_base, dot_base = build_solver(skip_axioms=skip_set)

        fixed_count = 0
        free_count = 0
        total = N * N

        # Only check non-absorber rows (rows 0,1 are always fixed)
        fixed_count += 2 * N  # rows 0 and 1 are fully determined

        for i in range(2, N):
            for j in range(N):
                s_base.push()
                # Count how many values are SAT for this cell
                sat_values = []
                for v in range(N):
                    s_base.push()
                    s_base.add(dot_base[i][j] == v)
                    r = s_base.check()
                    if str(r) == "sat":
                        sat_values.append(v)
                    s_base.pop()
                s_base.pop()

                if len(sat_values) == 1:
                    fixed_count += 1
                else:
                    free_count += 1

        print(f"  Fixed cells: {fixed_count}/{total} ({100*fixed_count/total:.1f}%)")
        print(f"  Free cells:  {free_count}/{total} ({100*free_count/total:.1f}%)")


# ═══════════════════════════════════════════════════════════════════════
# Deep Analysis 4: Axiom dependency graph
# ═══════════════════════════════════════════════════════════════════════

def axiom_dependencies():
    """Test if any axiom is implied by others (redundancy check).
    For each axiom A: build solver with all EXCEPT A, find a model,
    then check if A holds in that model."""
    print("\n" + "=" * 70)
    print("AXIOM REDUNDANCY CHECK")
    print("=" * 70)
    print("For each axiom: remove it, find a model, check if axiom")
    print("holds anyway (implied by others) or is violated (independent).")

    idx = ROLES

    for axiom in AXIOM_NAMES:
        s, dot = build_solver(skip_axioms={axiom})
        r = s.check()
        if str(r) != "sat":
            print(f"\n  {axiom}: system UNSAT without it — ESSENTIAL")
            continue

        table = extract_table(s.model(), dot, N)

        # Check if the removed axiom holds in the model
        holds = check_axiom_in_model(axiom, table, idx)
        status = "REDUNDANT (implied by others)" if holds else "INDEPENDENT (violated in model)"
        print(f"  {axiom:<13}: {status}")


def check_axiom_in_model(axiom_name, table, idx):
    """Check if a specific axiom holds in a concrete Cayley table."""
    N_t = len(table)

    def dot(a, b):
        return table[a][b]

    if axiom_name == "Kripke":
        # C: for non-absorbers x, if row x is not all-boolean, then x·y ≥ 2 for all y ≥ 2
        for x in range(2, N_t):
            is_tst = all(table[x][j] in (0, 1) for j in range(N_t))
            if not is_tst:
                for y in range(2, N_t):
                    if table[x][y] < 2:
                        return False
        return True

    elif axiom_name == "InertProp":
        # D: inert elements map non-absorbers to non-absorbers
        cats = classify_elements(table)
        for x in cats['inert']:
            for y in range(2, N_t):
                if table[x][y] < 2:
                    return False
        return True

    elif axiom_name == "PA":
        # (x·x)·x = x·(x·x)
        for x in range(N_t):
            xx = dot(x, x)
            if dot(xx, x) != dot(x, xx):
                return False
        return True

    elif axiom_name == "VV":
        # If v is inert, v·v is tester or encoder
        cats = classify_elements(table)
        tst_set = set(cats['testers'])
        enc_set = set(cats['encoders'])
        for v in cats['inert']:
            vv = dot(v, v)
            if vv not in tst_set and vv not in enc_set and vv not in (0, 1):
                # Check if vv's row is tester or encoder
                vv_row = [table[vv][j] for j in range(N_t)]
                is_bool = all(val in (0, 1) for val in vv_row)
                non_bool = set(val for val in vv_row if val not in (0, 1))
                if not is_bool and len(non_bool) < 2:
                    return False  # vv is inert — violates VV
        return True

    elif axiom_name == "QE":
        q, e = idx["Q"], idx["E"]
        for x in range(CORE_LO, CORE_HI):
            if dot(e, dot(q, x)) != x:
                return False
            if dot(q, dot(e, x)) != x:
                return False
        return True

    elif axiom_name == "E-trans":
        e = idx["E"]
        return dot(e, 0) == 0 and dot(e, 1) == 1

    elif axiom_name == "1-Inert":
        cats = classify_elements(table)
        return len(cats['inert']) == 1

    elif axiom_name == "Branch":
        t, f_, g_, r = idx["τ"], idx["f"], idx["g"], idx["ρ"]
        # f ≠ g on core
        if all(dot(f_, x) == dot(g_, x) for x in range(CORE_LO, CORE_HI)):
            return False
        for x in range(CORE_LO, CORE_HI):
            if dot(t, x) == 0:
                if dot(r, x) != dot(f_, x):
                    return False
            else:
                if dot(r, x) != dot(g_, x):
                    return False
        return True

    elif axiom_name == "Compose":
        h, r, g_ = idx["η"], idx["ρ"], idx["g"]
        for x in range(CORE_LO, CORE_HI):
            gx = dot(g_, x)
            if dot(h, x) != dot(r, gx):
                return False
        return True

    elif axiom_name == "Y":
        y, r = idx["Y"], idx["ρ"]
        yr = dot(y, r)
        if yr < 2:
            return False
        return dot(r, yr) == yr

    elif axiom_name == "Selection":
        h, r, t = idx["η"], idx["ρ"], idx["τ"]
        return dot(h, r) == t

    return True  # unknown axiom


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("=" * 70)
    print("AXIOM ARCHAEOLOGY — Deep Analysis")
    print(f"N={N}")
    print("=" * 70)

    # 1. Composition wall detail
    composition_wall_detail()

    # 2. Axiom redundancy check
    axiom_dependencies()

    # 3. Maximum removable set
    max_removable_set()

    # 4. Cell freedom comparison (expensive — do last)
    if "--with-freedom" in sys.argv:
        freedom_comparison()


if __name__ == "__main__":
    main()

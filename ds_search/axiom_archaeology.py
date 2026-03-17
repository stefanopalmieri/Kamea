#!/usr/bin/env python3
"""
Axiom Archaeology — Direction 1 from AXIOM_PROMPT.md

For each behavioral axiom: remove it, run SAT at N=12, and characterize
what changes. Not just "is it still SAT?" but:
  - Do the five forced categories survive?
  - Do the three hard walls (Kleene, Substrate, Composition) survive?
  - How many cells become free vs. the baseline?
  - Which role merges become newly possible?

Goal: find the MINIMAL axiom set that still forces the five categories
and three walls.

Usage:
  uv run python -m ds_search.axiom_archaeology
"""

import time
import sys
from itertools import combinations

from z3 import Solver, Int, If, And, Or, Not, sat, unsat

from ds_search.axiom_explorer import (
    ite_lookup, col_ite_lookup, classify_elements, extract_table,
    print_table, print_model_summary,
)
from ds_search.forced_roles_test import (
    axiom_L0, axiom_kleene, axiom_inert_prop, axiom_pa, axiom_vv,
    axiom_qe, axiom_e_trans, axiom_1_inert, axiom_branch, axiom_compose,
    axiom_y, axiom_selection, role_tester, role_inert, role_encoder,
    is_inert_z3,
)


# ═══════════════════════════════════════════════════════════════════════
# Parameters
# ═══════════════════════════════════════════════════════════════════════

N = 12
CORE_LO, CORE_HI = 2, 6

# Standard role assignments at N=12
ROLES = {
    "⊤": 0, "⊥": 1, "τ": 3, "Q": 6, "E": 7,
    "f": 2, "g": 4, "ρ": 8, "η": 9, "Y": 10,
}

# The three walls to test
WALL_PAIRS = {
    "Kleene (τ isolated)": [
        ("τ", "⊤"), ("τ", "⊥"), ("τ", "Q"), ("τ", "E"),
        ("τ", "f"), ("τ", "g"), ("τ", "ρ"), ("τ", "η"), ("τ", "Y"),
    ],
    "Substrate (g isolated)": [
        ("g", "⊤"), ("g", "⊥"), ("g", "Q"), ("g", "E"),
        ("g", "f"), ("g", "τ"), ("g", "ρ"), ("g", "η"), ("g", "Y"),
    ],
    "Composition (η partial)": [
        ("η", "Q"), ("η", "E"), ("η", "ρ"),  # should be UNSAT
        ("η", "f"), ("η", "Y"),               # should be SAT
    ],
}

# Axiom names (excluding L0 which is always present)
AXIOM_NAMES = [
    "Kleene", "InertProp", "PA", "VV", "QE",
    "E-trans", "1-Inert", "Branch", "Compose", "Y", "Selection",
]

TESTER_ROLES = {"τ"}
INERT_ROLES = {"g"}
ABSORBER_ROLES = {"⊤", "⊥"}
ENCODER_ROLES = {"Q", "E", "f", "ρ", "η", "Y"}


# ═══════════════════════════════════════════════════════════════════════
# Build solver with selective axiom inclusion
# ═══════════════════════════════════════════════════════════════════════

def build_solver(skip_axioms=None, role_a=None, role_b=None):
    """
    Build a solver with all axioms EXCEPT those in skip_axioms.
    If role_a and role_b are specified, alias role_b to role_a's index.
    Returns (solver, dot).
    """
    if skip_axioms is None:
        skip_axioms = set()

    idx = dict(ROLES)
    if role_a and role_b:
        idx[role_b] = idx[role_a]

    s = Solver()
    s.set("timeout", 300 * 1000)

    dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]

    # L0 always present
    for c in axiom_L0(dot, N):
        s.add(c)

    # Behavioral axioms — skip as requested
    axiom_map = {
        "Kleene": lambda: axiom_kleene(dot, N),
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

    # Role constraints
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
# Phase 1: Single axiom removal — SAT + classification
# ═══════════════════════════════════════════════════════════════════════

def phase1_single_removal():
    """Remove each axiom one at a time, check SAT, classify elements."""
    print("=" * 70)
    print("PHASE 1: Single Axiom Removal (N=12)")
    print("=" * 70)

    # Baseline: all axioms
    print("\n--- Baseline (all axioms) ---")
    t0 = time.time()
    s, dot = build_solver()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  Status: {str(r).upper()} ({elapsed:.1f}s)")

    if str(r) == "sat":
        table = extract_table(s.model(), dot, N)
        cats = classify_elements(table)
        print(f"  Categories: abs={len(cats['absorbers'])} tst={len(cats['testers'])} "
              f"enc={len(cats['encoders'])} inert={len(cats['inert'])}")
        baseline_cats = (len(cats['absorbers']), len(cats['testers']),
                         len(cats['encoders']), len(cats['inert']))
    else:
        print("  ERROR: baseline is not SAT!")
        return

    # Remove each axiom
    print(f"\n{'Removed':<15} {'Status':>8} {'Time':>7} {'Abs':>4} {'Tst':>4} {'Enc':>4} {'Inr':>4} {'Change':>10}")
    print("-" * 65)

    results = {}
    for axiom in AXIOM_NAMES:
        t0 = time.time()
        s, dot = build_solver(skip_axioms={axiom})
        r = s.check()
        elapsed = time.time() - t0

        status = str(r).upper()
        if status == "SAT":
            table = extract_table(s.model(), dot, N)
            cats = classify_elements(table)
            new_cats = (len(cats['absorbers']), len(cats['testers']),
                        len(cats['encoders']), len(cats['inert']))
            change = "SAME" if new_cats == baseline_cats else "CHANGED"
            print(f"  {axiom:<13} {status:>8} {elapsed:>6.1f}s {new_cats[0]:>4} {new_cats[1]:>4} "
                  f"{new_cats[2]:>4} {new_cats[3]:>4} {change:>10}")
            results[axiom] = {"status": "SAT", "cats": cats, "table": table}
        else:
            print(f"  {axiom:<13} {status:>8} {elapsed:>6.1f}s    -    -    -    -          -")
            results[axiom] = {"status": status}

    return results


# ═══════════════════════════════════════════════════════════════════════
# Phase 2: Wall survival under axiom removal
# ═══════════════════════════════════════════════════════════════════════

def phase2_wall_survival():
    """For each axiom removal, test if the three walls still hold."""
    print("\n" + "=" * 70)
    print("PHASE 2: Wall Survival Under Axiom Removal")
    print("=" * 70)

    # First, establish baseline walls
    print("\n--- Baseline walls (all axioms) ---")
    baseline_walls = {}
    for wall_name, pairs in WALL_PAIRS.items():
        wall_results = {}
        for ra, rb in pairs:
            s, dot = build_solver(role_a=ra, role_b=rb)
            r = s.check()
            wall_results[(ra, rb)] = str(r).upper()
        unsat_count = sum(1 for v in wall_results.values() if v == "UNSAT")
        sat_count = sum(1 for v in wall_results.values() if v == "SAT")
        print(f"  {wall_name}: {unsat_count} UNSAT, {sat_count} SAT")
        baseline_walls[wall_name] = wall_results

    # For each axiom removal, test critical wall pairs
    # Focus on the UNSAT pairs — do they become SAT?
    print(f"\n{'Removed':<13} {'Kleene':>10} {'Substrate':>10} {'Compose':>10}")
    print("-" * 50)

    for axiom in AXIOM_NAMES:
        wall_status = {}
        for wall_name, pairs in WALL_PAIRS.items():
            # Only test pairs that were UNSAT in baseline
            broken = 0
            tested = 0
            for ra, rb in pairs:
                if baseline_walls[wall_name].get((ra, rb)) == "UNSAT":
                    tested += 1
                    s, dot = build_solver(skip_axioms={axiom}, role_a=ra, role_b=rb)
                    r = s.check()
                    if str(r) == "sat":
                        broken += 1
            if tested == 0:
                wall_status[wall_name] = "N/A"
            elif broken == 0:
                wall_status[wall_name] = "HOLDS"
            else:
                wall_status[wall_name] = f"{broken}/{tested} BROKE"

        k = wall_status.get("Kleene (τ isolated)", "?")
        sub = wall_status.get("Substrate (g isolated)", "?")
        comp = wall_status.get("Composition (η partial)", "?")
        print(f"  {axiom:<11} {k:>10} {sub:>10} {comp:>10}")


# ═══════════════════════════════════════════════════════════════════════
# Phase 3: Multi-axiom removal — find minimal set
# ═══════════════════════════════════════════════════════════════════════

def phase3_minimal_set():
    """Try removing multiple axioms to find the minimal set."""
    print("\n" + "=" * 70)
    print("PHASE 3: Multi-Axiom Removal — Finding Minimal Set")
    print("=" * 70)

    # Try removing pairs of axioms
    print("\n--- Removing pairs ---")
    removable_pairs = []
    for a1, a2 in combinations(AXIOM_NAMES, 2):
        t0 = time.time()
        s, dot = build_solver(skip_axioms={a1, a2})
        r = s.check()
        elapsed = time.time() - t0
        status = str(r).upper()
        if status == "SAT":
            table = extract_table(s.model(), dot, N)
            cats = classify_elements(table)
            has_5 = (len(cats['absorbers']) >= 2 and len(cats['testers']) >= 1
                     and len(cats['encoders']) >= 1 and len(cats['inert']) >= 1)
            if has_5:
                removable_pairs.append((a1, a2))
                print(f"  -{a1}, -{a2}: SAT, 5 categories present ({elapsed:.1f}s)")
            else:
                print(f"  -{a1}, -{a2}: SAT, categories CHANGED "
                      f"(abs={len(cats['absorbers'])} tst={len(cats['testers'])} "
                      f"enc={len(cats['encoders'])} inr={len(cats['inert'])}) ({elapsed:.1f}s)")
        else:
            print(f"  -{a1}, -{a2}: {status} ({elapsed:.1f}s)")

    # Try removing triples from the removable pairs
    if removable_pairs:
        print("\n--- Removing triples (from successful pairs) ---")
        # Collect axioms that appear in removable pairs
        candidates = set()
        for a1, a2 in removable_pairs:
            candidates.add(a1)
            candidates.add(a2)

        for a1, a2, a3 in combinations(sorted(candidates), 3):
            t0 = time.time()
            s, dot = build_solver(skip_axioms={a1, a2, a3})
            r = s.check()
            elapsed = time.time() - t0
            status = str(r).upper()
            if status == "SAT":
                table = extract_table(s.model(), dot, N)
                cats = classify_elements(table)
                has_5 = (len(cats['absorbers']) >= 2 and len(cats['testers']) >= 1
                         and len(cats['encoders']) >= 1 and len(cats['inert']) >= 1)
                cats_str = (f"abs={len(cats['absorbers'])} tst={len(cats['testers'])} "
                            f"enc={len(cats['encoders'])} inr={len(cats['inert'])}")
                tag = "5 cats" if has_5 else "CHANGED"
                print(f"  -{a1}, -{a2}, -{a3}: SAT, {tag} ({cats_str}) ({elapsed:.1f}s)")
            else:
                print(f"  -{a1}, -{a2}, -{a3}: {status} ({elapsed:.1f}s)")


# ═══════════════════════════════════════════════════════════════════════
# Phase 4: Direction 3 — Missing axioms (new candidates)
# ═══════════════════════════════════════════════════════════════════════

def phase4_new_axioms():
    """Test candidate new axioms from AXIOM_PROMPT.md Direction 3."""
    print("\n" + "=" * 70)
    print("PHASE 4: Candidate New Axioms (Direction 3)")
    print("=" * 70)

    idx = ROLES

    # Build baseline solver
    def baseline_solver():
        return build_solver()

    # --- Candidate 1: Restricted associativity on QE pair ---
    print("\n--- Candidate: QE associativity: Q·(E·x) = (Q·E)·x on core ---")
    s, dot = baseline_solver()
    q, e = idx["Q"], idx["E"]
    for x in range(CORE_LO, CORE_HI):
        # Q·(E·x) = (Q·E)·x
        # ex = dot[e][x] is Z3 expr, q_ex needs ite_lookup for row
        ex = dot[e][x]
        q_ex = col_ite_lookup(dot, q, ex, N)  # q is concrete, ex is Z3 — OK
        qe = dot[q][e]  # Z3 expr
        qe_x = ite_lookup(dot, qe, x, N)  # qe is Z3 row, x is concrete — use ite_lookup
        s.add(q_ex == qe_x)
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  Status: {str(r).upper()} ({elapsed:.1f}s)")
    if str(r) == "sat":
        table = extract_table(s.model(), dot, N)
        cats = classify_elements(table)
        print(f"  Categories: abs={len(cats['absorbers'])} tst={len(cats['testers'])} "
              f"enc={len(cats['encoders'])} inert={len(cats['inert'])}")

    # --- Candidate 2: Full associativity restricted to encoders ---
    print("\n--- Candidate: Encoder associativity: a·(b·c) = (a·b)·c for all encoders ---")
    s, dot = baseline_solver()
    enc_indices = [idx[r] for r in ENCODER_ROLES]
    for a in enc_indices:
        for b in enc_indices:
            for c in enc_indices:
                bc = dot[b][c]
                a_bc = col_ite_lookup(dot, a, bc, N)  # a concrete, bc Z3
                ab = dot[a][b]
                ab_c = ite_lookup(dot, ab, c, N)  # ab Z3 row, c concrete
                s.add(a_bc == ab_c)
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  Status: {str(r).upper()} ({elapsed:.1f}s)")

    # --- Candidate 3: Absorption law a·(b·a) = a for some pair ---
    print("\n--- Candidate: ∃ a,b ≥ 2 with a·(b·a) = a (absorption) ---")
    s, dot = baseline_solver()
    abs_clauses = []
    for a in range(2, N):
        for b in range(2, N):
            ba = dot[b][a]
            a_ba = col_ite_lookup(dot, a, ba, N)
            abs_clauses.append(a_ba == a)
    s.add(Or(abs_clauses))
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  Status: {str(r).upper()} ({elapsed:.1f}s)")
    if str(r) == "sat":
        m = s.model()
        table = extract_table(m, dot, N)
        # Find which pair satisfies absorption
        for a in range(2, N):
            for b in range(2, N):
                ba = table[b][a]
                if ba < N and table[a][ba] == a:
                    cats = classify_elements(table)
                    a_role = "tst" if a in cats['testers'] else "enc" if a in cats['encoders'] else "inr" if a in cats['inert'] else "abs"
                    b_role = "tst" if b in cats['testers'] else "enc" if b in cats['encoders'] else "inr" if b in cats['inert'] else "abs"
                    print(f"  Witness: a={a}({a_role}), b={b}({b_role}), "
                          f"b·a={ba}, a·(b·a)={table[a][ba]} = a ✓")
                    break
            else:
                continue
            break

    # --- Candidate 4: Idempotent elements act as local identities ---
    print("\n--- Candidate: ∃ idempotent x (x·x=x, x≥2) ---")
    s, dot = baseline_solver()
    idemp_clauses = []
    for x in range(2, N):
        idemp_clauses.append(dot[x][x] == x)
    s.add(Or(idemp_clauses))
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  Status: {str(r).upper()} ({elapsed:.1f}s)")
    if str(r) == "sat":
        m = s.model()
        table = extract_table(m, dot, N)
        cats = classify_elements(table)
        for x in range(2, N):
            if table[x][x] == x:
                role = "tst" if x in cats['testers'] else "enc" if x in cats['encoders'] else "inr" if x in cats['inert'] else "abs"
                print(f"  Witness: x={x}({role}), x·x={x} ✓")

    # --- Candidate 5: Left-distributivity a·(b·c) = (a·b)·(a·c) for specific elements ---
    print("\n--- Candidate: ∃ a≥2 left-distributive: a·(b·c)=(a·b)·(a·c) ∀b,c ---")
    s, dot = baseline_solver()
    dist_clauses = []
    for a in range(2, N):
        # a is left-distributive over all b, c
        all_dist = []
        for b in range(N):
            for c in range(N):
                bc = dot[b][c]
                a_bc = col_ite_lookup(dot, a, bc, N)  # a concrete, bc Z3
                ab = dot[a][b]  # Z3
                ac = dot[a][c]  # Z3
                # dot[ab][ac] — both Z3. Double indirect: first row lookup, then col
                # Build: for each possible row r, if ab==r then col_ite_lookup(dot, r, ac, N)
                ab_ac = col_ite_lookup(dot, 0, ac, N)
                for r in range(1, N):
                    ab_ac = If(ab == r, col_ite_lookup(dot, r, ac, N), ab_ac)
                all_dist.append(a_bc == ab_ac)
        dist_clauses.append(And(all_dist))
    s.add(Or(dist_clauses))
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  Status: {str(r).upper()} ({elapsed:.1f}s)")
    if str(r) == "sat":
        m = s.model()
        table = extract_table(m, dot, N)
        cats = classify_elements(table)
        for a in range(2, N):
            is_dist = True
            for b in range(N):
                for c in range(N):
                    bc = table[b][c]
                    if table[a][bc] != table[table[a][b]][table[a][c]]:
                        is_dist = False
                        break
                if not is_dist:
                    break
            if is_dist:
                role = "tst" if a in cats['testers'] else "enc" if a in cats['encoders'] else "inr" if a in cats['inert'] else "abs"
                print(f"  Witness: a={a}({role}) is left-distributive ✓")

    # --- Candidate 6: Column distinctness (right-ext) ---
    print("\n--- Candidate: Column distinctness (right-extensionality) ---")
    s, dot = baseline_solver()
    for y1 in range(N):
        for y2 in range(y1 + 1, N):
            s.add(Or([dot[x][y1] != dot[x][y2] for x in range(N)]))
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  Status: {str(r).upper()} ({elapsed:.1f}s)")
    if str(r) == "sat":
        table = extract_table(s.model(), dot, N)
        cats = classify_elements(table)
        print(f"  Categories: abs={len(cats['absorbers'])} tst={len(cats['testers'])} "
              f"enc={len(cats['encoders'])} inert={len(cats['inert'])}")


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("=" * 70)
    print("AXIOM ARCHAEOLOGY — Direction 1 + Direction 3 from AXIOM_PROMPT.md")
    print(f"N={N}, {len(AXIOM_NAMES)} behavioral axioms to test")
    print("=" * 70)
    print()

    # Phase 1: Single removal
    phase1_results = phase1_single_removal()

    # Phase 2: Wall survival
    phase2_wall_survival()

    # Phase 3: Minimal set
    phase3_minimal_set()

    # Phase 4: New axiom candidates
    phase4_new_axioms()


if __name__ == "__main__":
    main()

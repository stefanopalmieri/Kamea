#!/usr/bin/env python3
"""
Task 1: Composition Closure Axiom — does requiring role-bearing elements
to form a sub-magma force any of the 10 expressiveness-only distinctness pairs?

Task 2: Symmetric Impossibility — is commutativity compatible with the Ψ axioms
or with the DichotomicRetractMagma axioms?

Usage:
  uv run python -m ds_search.closure_and_symmetry_test
"""

import time
import sys
import os
from itertools import combinations

from z3 import Solver, Int, If, And, Or, Not, sat, unsat

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ds_search.axiom_explorer import ite_lookup, col_ite_lookup

# ═══════════════════════════════════════════════════════════════════════
# Parameters
# ═══════════════════════════════════════════════════════════════════════

N = 12
CORE_LO, CORE_HI = 2, 6  # core range for QE, Branch, Compose

# Role indices at N=12
ROLES = {
    "⊤": 0, "⊥": 1, "τ": 3, "Q": 6, "E": 7,
    "f": 2, "g": 4, "ρ": 8, "η": 9, "Y": 10,
}

# The 10 expressiveness-only pairs (SAT under categorical+TC axioms)
EXPRESSIVENESS_PAIRS = [
    ("⊤", "⊥"), ("Q", "ρ"), ("Q", "Y"), ("E", "ρ"), ("E", "Y"),
    ("E", "f"), ("f", "ρ"), ("f", "Y"), ("ρ", "Y"), ("η", "Y"),
]

# Role type classification
TESTER_ROLES = {"τ"}
INERT_ROLES = {"g"}
ABSORBER_ROLES = {"⊤", "⊥"}
ENCODER_ROLES = {"Q", "E", "f", "ρ", "η", "Y"}

ROLE_SET = set(ROLES.keys())  # all 10 role-bearing elements


# ═══════════════════════════════════════════════════════════════════════
# Z3 helpers
# ═══════════════════════════════════════════════════════════════════════

def is_inert_z3(dot, x, N):
    is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
    enc_pairs = []
    for j1 in range(N):
        for j2 in range(j1 + 1, N):
            enc_pairs.append(And(
                dot[x][j1] != 0, dot[x][j1] != 1,
                dot[x][j2] != 0, dot[x][j2] != 1,
                dot[x][j1] != dot[x][j2]))
    is_enc = Or(enc_pairs) if enc_pairs else False
    return And(Not(is_tst), Not(is_enc))


# ═══════════════════════════════════════════════════════════════════════
# Axiom groups (from forced_roles_test.py)
# ═══════════════════════════════════════════════════════════════════════

def axiom_L0(dot, N):
    constraints = []
    for i in range(N):
        for j in range(N):
            constraints.append(dot[i][j] >= 0)
            constraints.append(dot[i][j] < N)
    for j in range(N):
        constraints.append(dot[0][j] == 0)
        constraints.append(dot[1][j] == 1)
    for x in range(2, N):
        constraints.append(Or([dot[x][j] != x for j in range(N)]))
    for x in range(N):
        for y in range(x + 1, N):
            constraints.append(Or([dot[x][j] != dot[y][j] for j in range(N)]))
    return constraints


def axiom_kripke(dot, N):
    constraints = []
    for x in range(2, N):
        is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        for y in range(2, N):
            constraints.append(Or(is_tst, dot[x][y] >= 2))
    return constraints


def axiom_inert_prop(dot, N):
    constraints = []
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
        for y in range(2, N):
            constraints.append(Or(Not(is_inert), dot[x][y] >= 2))
    return constraints


def axiom_pa(dot, N):
    constraints = []
    for x in range(N):
        xx = dot[x][x]
        constraints.append(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))
    return constraints


def axiom_vv(dot, N):
    constraints = []
    for v in range(2, N):
        is_tst_v = And([Or(dot[v][j] == 0, dot[v][j] == 1) for j in range(N)])
        enc_pairs_v = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                enc_pairs_v.append(And(
                    dot[v][j1] != 0, dot[v][j1] != 1,
                    dot[v][j2] != 0, dot[v][j2] != 1,
                    dot[v][j1] != dot[v][j2]))
        is_enc_v = Or(enc_pairs_v) if enc_pairs_v else False
        is_inert_v = And(Not(is_tst_v), Not(is_enc_v))
        vv = dot[v][v]
        vv_is_tst = And([Or(ite_lookup(dot, vv, j, N) == 0,
                            ite_lookup(dot, vv, j, N) == 1) for j in range(N)])
        vv_enc_pairs = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                vv_enc_pairs.append(And(
                    ite_lookup(dot, vv, j1, N) != 0,
                    ite_lookup(dot, vv, j1, N) != 1,
                    ite_lookup(dot, vv, j2, N) != 0,
                    ite_lookup(dot, vv, j2, N) != 1,
                    ite_lookup(dot, vv, j1, N) != ite_lookup(dot, vv, j2, N)))
        vv_is_enc = Or(vv_enc_pairs) if vv_enc_pairs else False
        vv_is_core = Or(vv_is_tst, vv_is_enc)
        constraints.append(Or(Not(is_inert_v), vv_is_core))
    return constraints


def axiom_qe(dot, N, q, e, core_lo, core_hi):
    constraints = []
    for x in range(core_lo, core_hi):
        qx = dot[q][x]
        constraints.append(col_ite_lookup(dot, e, qx, N) == x)
        ex = dot[e][x]
        constraints.append(col_ite_lookup(dot, q, ex, N) == x)
    return constraints


def axiom_e_trans(dot, e):
    return [dot[e][0] == 0, dot[e][1] == 1]


def axiom_1_inert(dot, N):
    constraints = []
    flags = []
    for x in range(2, N):
        flag = Int(f"zi_{x}")
        constraints.append(If(is_inert_z3(dot, x, N), flag == 1, flag == 0))
        flags.append(flag)
    constraints.append(sum(flags) == 1)
    return constraints


def axiom_branch(dot, t, f_, g_, r, core_lo, core_hi):
    constraints = []
    for x in range(core_lo, core_hi):
        tx = dot[t][x]
        fx = dot[f_][x]
        gx = dot[g_][x]
        constraints.append(If(tx == 0, dot[r][x] == fx, dot[r][x] == gx))
    constraints.append(Or([dot[f_][j] != dot[g_][j] for j in range(core_lo, core_hi)]))
    return constraints


def axiom_compose(dot, N, h, r, g_, core_lo, core_hi):
    constraints = []
    for x in range(core_lo, core_hi):
        gx = dot[g_][x]
        r_gx = col_ite_lookup(dot, r, gx, N)
        constraints.append(dot[h][x] == r_gx)
    return constraints


def axiom_y(dot, N, y, r):
    yr = dot[y][r]
    r_yr = col_ite_lookup(dot, r, yr, N)
    return [yr == r_yr, yr >= 2]


def axiom_selection(dot, h, r, t):
    return [dot[h][r] == t]


def role_tester(dot, N, idx):
    return [Or(dot[idx][j] == 0, dot[idx][j] == 1) for j in range(N)]


def role_inert(dot, idx, N):
    return [is_inert_z3(dot, idx, N)]


def role_encoder(dot, N, idx):
    enc_pairs = []
    for j1 in range(N):
        for j2 in range(j1 + 1, N):
            enc_pairs.append(And(
                dot[idx][j1] != 0, dot[idx][j1] != 1,
                dot[idx][j2] != 0, dot[idx][j2] != 1,
                dot[idx][j1] != dot[idx][j2]))
    return [Or(enc_pairs)]


# ═══════════════════════════════════════════════════════════════════════
# Composition closure axiom variants
# ═══════════════════════════════════════════════════════════════════════

def axiom_closure(dot, N, role_indices):
    """
    For all a, b in role_indices: dot(a, b) ∈ role_indices.

    role_indices: list of concrete indices that must be closed.
    """
    constraints = []
    idx_set = list(set(role_indices))
    for a in idx_set:
        for b in idx_set:
            # dot[a][b] must be one of the role indices
            constraints.append(Or([dot[a][b] == r for r in idx_set]))
    return constraints


# ═══════════════════════════════════════════════════════════════════════
# Build full solver
# ═══════════════════════════════════════════════════════════════════════

def build_solver(role_overrides=None, extra_constraints=None,
                 skip_axiom_groups=None, timeout_s=300, n=N):
    """
    Build a solver with all Ψ axioms.

    role_overrides: dict mapping role_name -> index (for aliasing pairs)
    extra_constraints: list of additional Z3 constraints
    skip_axiom_groups: set of axiom group names to skip
    """
    if role_overrides is None:
        role_overrides = {}
    if extra_constraints is None:
        extra_constraints = []
    if skip_axiom_groups is None:
        skip_axiom_groups = set()

    idx = dict(ROLES)
    idx.update(role_overrides)

    s = Solver()
    s.set("timeout", timeout_s * 1000)

    dot = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]

    def add_group(name, constraints):
        if name not in skip_axiom_groups:
            for c in constraints:
                s.add(c)

    # Core axioms
    add_group("L0", axiom_L0(dot, n))
    add_group("Kripke", axiom_kripke(dot, n))
    add_group("InertProp", axiom_inert_prop(dot, n))
    add_group("PA", axiom_pa(dot, n))
    add_group("VV", axiom_vv(dot, n))
    add_group("QE", axiom_qe(dot, n, idx["Q"], idx["E"], CORE_LO, CORE_HI))
    add_group("E-trans", axiom_e_trans(dot, idx["E"]))
    add_group("1-Inert", axiom_1_inert(dot, n))
    add_group("Branch", axiom_branch(
        dot, idx["τ"], idx["f"], idx["g"], idx["ρ"], CORE_LO, CORE_HI))
    add_group("Compose", axiom_compose(
        dot, n, idx["η"], idx["ρ"], idx["g"], CORE_LO, CORE_HI))
    add_group("Y", axiom_y(dot, n, idx["Y"], idx["ρ"]))
    add_group("Selection", axiom_selection(dot, idx["η"], idx["ρ"], idx["τ"]))

    # Role constraints
    assigned_roles = {}
    for role_name, role_idx in idx.items():
        if role_name in ABSORBER_ROLES:
            continue
        assigned_roles.setdefault(role_idx, set()).add(role_name)

    tester_indices = set()
    inert_indices = set()
    encoder_indices = set()

    for role_idx, role_set in assigned_roles.items():
        for rn in role_set:
            if rn in TESTER_ROLES:
                tester_indices.add(role_idx)
            elif rn in INERT_ROLES:
                inert_indices.add(role_idx)
            elif rn in ENCODER_ROLES:
                encoder_indices.add(role_idx)

    role_constraints = []
    for t in tester_indices:
        role_constraints.extend(role_tester(dot, n, t))
    for i_idx in inert_indices:
        role_constraints.extend(role_inert(dot, i_idx, n))
    for e in encoder_indices:
        role_constraints.extend(role_encoder(dot, n, e))

    add_group("Roles", role_constraints)

    # Extra constraints (closure, commutativity, etc.)
    for c in extra_constraints:
        s.add(c)

    return s, dot, idx


def get_role_indices(idx=None):
    """Get the list of concrete indices for all 10 role-bearing elements."""
    if idx is None:
        idx = ROLES
    return [idx[r] for r in ROLE_SET]


def classify_model(dot, m, n):
    """Classify elements into absorber/tester/encoder/inert."""
    cats = {}
    for i in range(n):
        row = [m.evaluate(dot[i][j]).as_long() for j in range(n)]
        if all(v == i for v in row):
            cats[i] = "absorber"
        elif all(v in (0, 1) for v in row):
            cats[i] = "tester"
        else:
            non_bool = [v for v in row if v not in (0, 1)]
            if len(set(non_bool)) >= 2:
                cats[i] = "encoder"
            else:
                cats[i] = "inert"
    return cats


def print_table(dot, m, n, label=""):
    """Print extracted Cayley table."""
    if label:
        print(f"\n  {label}")
    for i in range(n):
        row = [m.evaluate(dot[i][j]).as_long() for j in range(n)]
        print(f"    [{', '.join(f'{v:2d}' for v in row)}]")


# ═══════════════════════════════════════════════════════════════════════
# Task 1: Composition Closure
# ═══════════════════════════════════════════════════════════════════════

def task1_closure():
    print("=" * 70)
    print("TASK 1: COMPOSITION CLOSURE AXIOM")
    print("=" * 70)

    role_indices = list(set(ROLES.values()))  # unique indices
    print(f"\nRole-bearing element indices: {sorted(role_indices)}")
    print(f"Non-role (infrastructure) indices: "
          f"{sorted(set(range(N)) - set(role_indices))}")

    # ── Step 1: Check SAT with full closure ──────────────────────────
    print(f"\n{'─'*70}")
    print("Step 1: Full closure (all 10 roles form sub-magma)")
    print(f"{'─'*70}")

    closure_constraints = axiom_closure(
        [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)],
        N, role_indices)

    # Need to rebuild with fresh variables
    t0 = time.time()
    s, dot, idx = build_solver(timeout_s=600)
    closure = axiom_closure(dot, N, list(set(idx[r] for r in ROLE_SET)))
    for c in closure:
        s.add(c)
    r = s.check()
    elapsed = time.time() - t0

    print(f"  Full closure at N={N}: {str(r).upper()} ({elapsed:.1f}s)")

    if str(r) == "sat":
        m = s.model()
        cats = classify_model(dot, m, N)
        cat_counts = {}
        for c in cats.values():
            cat_counts[c] = cat_counts.get(c, 0) + 1
        dist = f"{cat_counts.get('absorber', 0)}-{cat_counts.get('tester', 0)}-" \
               f"{cat_counts.get('encoder', 0)}-{cat_counts.get('inert', 0)}"
        print(f"  Category distribution: {dist}")
        print_table(dot, m, N, "Extracted Cayley table:")

        # Verify closure holds
        role_idx_set = set(idx[r] for r in ROLE_SET)
        violations = 0
        for a in role_idx_set:
            for b in role_idx_set:
                v = m.evaluate(dot[a][b]).as_long()
                if v not in role_idx_set:
                    violations += 1
        print(f"  Closure violations: {violations}")
    elif str(r) == "unsat":
        print("  Full closure UNSAT at N=12. Trying N=16...")
        t0 = time.time()
        s16, dot16, idx16 = build_solver(timeout_s=600, n=16)
        # Adjust role indices for N=16 (same indices work)
        closure16 = axiom_closure(dot16, 16, list(set(idx16[r] for r in ROLE_SET)))
        for c in closure16:
            s16.add(c)
        r16 = s16.check()
        elapsed = time.time() - t0
        print(f"  Full closure at N=16: {str(r16).upper()} ({elapsed:.1f}s)")

    # ── Step 2: Test each of the 10 pairs ────────────────────────────
    full_closure_sat = (str(r) == "sat")

    if full_closure_sat:
        print(f"\n{'─'*70}")
        print("Step 2: Test each expressiveness-only pair under closure")
        print(f"{'─'*70}")

        pair_results_full = {}
        for role_a, role_b in EXPRESSIVENESS_PAIRS:
            # Merge pair: set role_b = role_a's index
            overrides = {role_b: ROLES[role_a]}
            t0 = time.time()
            s, dot, idx = build_solver(role_overrides=overrides, timeout_s=300)
            # Add closure for the (now aliased) role set
            ridx = list(set(idx[r] for r in ROLE_SET))
            closure = axiom_closure(dot, N, ridx)
            for c in closure:
                s.add(c)
            result = s.check()
            elapsed = time.time() - t0

            status = str(result).upper()
            pair_results_full[(role_a, role_b)] = status
            forced = "FORCED DISTINCT" if status == "UNSAT" else "still mergeable"
            print(f"  {role_a}={role_b}: {status} ({forced}) [{elapsed:.1f}s]")

        # ── Step 3: Report table ─────────────────────────────────────
        print(f"\n{'─'*70}")
        print("Step 3: Full Closure Results")
        print(f"{'─'*70}")
        print(f"\n  | {'Pair':>6s} | {'Without closure':>16s} | {'With closure':>14s} | {'Status':>20s} |")
        print(f"  |{'-'*8}|{'-'*18}|{'-'*16}|{'-'*22}|")
        killed = 0
        for role_a, role_b in EXPRESSIVENESS_PAIRS:
            pair_label = f"{role_a}={role_b}"
            with_closure = pair_results_full[(role_a, role_b)]
            if with_closure == "UNSAT":
                status = "closure-forced"
                killed += 1
            else:
                status = "still expressiveness"
            print(f"  | {pair_label:>6s} | {'SAT (mergeable)':>16s} | {with_closure:>14s} | {status:>20s} |")
        print(f"\n  Full closure kills {killed}/10 pairs")

    # ── Step 4: Weaker variants ──────────────────────────────────────
    print(f"\n{'─'*70}")
    print("Step 4: Weaker closure variants")
    print(f"{'─'*70}")

    variants = {
        "computational_core": {"Q", "E", "f", "g", "ρ", "η"},
        "one_sided_core": None,  # special handling
        "non_zeros": {"τ", "Q", "E", "f", "g", "ρ", "η", "Y"},
    }

    variant_results = {}

    for variant_name, variant_roles in variants.items():
        if variant_name == "one_sided_core":
            # One-sided: for all a in comp_core, for all b in {0..N-1}:
            # dot(a,b) in role_set
            print(f"\n  Variant: one-sided core closure")
            print(f"    For a in {{Q,E,f,g,ρ,η}}, ∀b: dot(a,b) ∈ roles")
            t0 = time.time()
            s, dot, idx = build_solver(timeout_s=600)
            comp_core = {"Q", "E", "f", "g", "ρ", "η"}
            role_idx_list = list(set(idx[r] for r in ROLE_SET))
            for r in comp_core:
                a = idx[r]
                for b in range(N):
                    s.add(Or([dot[a][b] == ri for ri in role_idx_list]))
            result = s.check()
            elapsed = time.time() - t0
            print(f"    SAT: {str(result).upper()} ({elapsed:.1f}s)")
            variant_results[variant_name] = str(result).upper()

            if str(result) == "sat":
                # Test pairs
                print(f"    Testing expressiveness pairs...")
                pair_results = {}
                for role_a, role_b in EXPRESSIVENESS_PAIRS:
                    overrides = {role_b: ROLES[role_a]}
                    s2, dot2, idx2 = build_solver(
                        role_overrides=overrides, timeout_s=300)
                    ridx2 = list(set(idx2[r] for r in ROLE_SET))
                    for r in comp_core:
                        a = idx2[r]
                        for b in range(N):
                            s2.add(Or([dot2[a][b] == ri for ri in ridx2]))
                    res = s2.check()
                    pair_results[(role_a, role_b)] = str(res).upper()
                    forced = "FORCED" if str(res) == "UNSAT" else "still SAT"
                    print(f"      {role_a}={role_b}: {str(res).upper()} ({forced})")
                killed = sum(1 for v in pair_results.values() if v == "UNSAT")
                print(f"    One-sided core kills {killed}/10")
                variant_results[variant_name + "_pairs"] = pair_results
            continue

        # Standard closure variants
        variant_idx = list(set(ROLES[r] for r in variant_roles))
        print(f"\n  Variant: {variant_name}")
        print(f"    Roles: {variant_roles}")
        print(f"    Indices: {sorted(variant_idx)} ({len(variant_idx)}² = "
              f"{len(variant_idx)**2} compositions)")

        t0 = time.time()
        s, dot, idx = build_solver(timeout_s=600)
        closure = axiom_closure(dot, N, variant_idx)
        for c in closure:
            s.add(c)
        result = s.check()
        elapsed = time.time() - t0
        print(f"    SAT: {str(result).upper()} ({elapsed:.1f}s)")
        variant_results[variant_name] = str(result).upper()

        if str(result) == "sat":
            # Test pairs
            print(f"    Testing expressiveness pairs...")
            pair_results = {}
            for role_a, role_b in EXPRESSIVENESS_PAIRS:
                overrides = {role_b: ROLES[role_a]}
                s2, dot2, idx2 = build_solver(
                    role_overrides=overrides, timeout_s=300)
                vidx = list(set(idx2[r] for r in variant_roles
                                if r in idx2))
                closure2 = axiom_closure(dot2, N, vidx)
                for c in closure2:
                    s2.add(c)
                res = s2.check()
                pair_results[(role_a, role_b)] = str(res).upper()
                forced = "FORCED" if str(res) == "UNSAT" else "still SAT"
                print(f"      {role_a}={role_b}: {str(res).upper()} ({forced})")
            killed = sum(1 for v in pair_results.values() if v == "UNSAT")
            print(f"    {variant_name} kills {killed}/10")
            variant_results[variant_name + "_pairs"] = pair_results

    return variant_results


# ═══════════════════════════════════════════════════════════════════════
# Task 2: Symmetric Impossibility
# ═══════════════════════════════════════════════════════════════════════

def task2_symmetry():
    print("\n" + "=" * 70)
    print("TASK 2: SYMMETRIC IMPOSSIBILITY")
    print("=" * 70)

    # ── Step 1: Full Ψ axioms + commutativity at N=12 ────────────────
    print(f"\n{'─'*70}")
    print("Step 1: Full Ψ axioms + commutativity at N=12")
    print(f"{'─'*70}")

    t0 = time.time()
    s, dot, idx = build_solver(timeout_s=600)
    # Add commutativity
    for a in range(N):
        for b in range(a + 1, N):
            s.add(dot[a][b] == dot[b][a])
    result = s.check()
    elapsed = time.time() - t0
    print(f"  Ψ axioms + commutativity at N={N}: {str(result).upper()} ({elapsed:.1f}s)")

    if str(result) == "sat":
        m = s.model()
        print_table(dot, m, N, "Commutative model:")
    elif str(result) == "unsat":
        print("  Commutativity INCOMPATIBLE with Ψ axioms!")
        print("\n  Identifying conflicting axioms (remove one at a time)...")

        axiom_groups = [
            "Kripke", "InertProp", "PA", "VV", "QE",
            "E-trans", "1-Inert", "Branch", "Compose", "Y",
            "Selection", "Roles",
        ]

        for skip_name in axiom_groups:
            t0 = time.time()
            s2, dot2, idx2 = build_solver(
                skip_axiom_groups={skip_name}, timeout_s=300)
            for a in range(N):
                for b in range(a + 1, N):
                    s2.add(dot2[a][b] == dot2[b][a])
            res = s2.check()
            elapsed = time.time() - t0
            status = "SAT (this axiom is necessary)" if str(res) == "sat" \
                else "still UNSAT"
            print(f"    Remove {skip_name:>12s}: {str(res).upper():>6s} "
                  f"  {status}  ({elapsed:.1f}s)")

    # ── Step 2: DichotomicRetractMagma axioms + commutativity ───────────────────
    print(f"\n{'─'*70}")
    print("Step 2: DichotomicRetractMagma axioms + commutativity")
    print(f"{'─'*70}")

    for test_n in [5, 6, 7, 8]:
        t0 = time.time()
        s, dot = build_kripke_solver(test_n, commutative=True, timeout_s=300)
        result = s.check()
        elapsed = time.time() - t0
        print(f"  DichotomicRetractMagma + commutativity at N={test_n}: "
              f"{str(result).upper()} ({elapsed:.1f}s)")
        if str(result) == "sat":
            m = s.model()
            print_table(dot, m, test_n, f"Commutative DichotomicRetractMagma N={test_n}:")

    # ── Step 3: DichotomicRetractMagma without commutativity (sanity check) ─────
    print(f"\n  Sanity check: DichotomicRetractMagma without commutativity")
    for test_n in [4, 5]:
        t0 = time.time()
        s, dot = build_kripke_solver(test_n, commutative=False, timeout_s=60)
        result = s.check()
        elapsed = time.time() - t0
        print(f"    DichotomicRetractMagma at N={test_n}: {str(result).upper()} ({elapsed:.1f}s)")


def build_kripke_solver(n, commutative=False, timeout_s=120):
    """
    Encode the DichotomicRetractMagma axioms from CatKripkeWallMinimal.lean.

    Structure:
    - zero₁, zero₂: left-absorbers (indices 0, 1)
    - sec, ret: retraction pair
    - cls: classifier
    - Kripke dichotomy
    - has_non_classifier
    """
    s = Solver()
    s.set("timeout", timeout_s * 1000)

    dot = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]

    # Range
    for i in range(n):
        for j in range(n):
            s.add(dot[i][j] >= 0)
            s.add(dot[i][j] < n)

    # zero₁ = 0, zero₂ = 1 (left-absorbers)
    z1, z2 = 0, 1
    for j in range(n):
        s.add(dot[z1][j] == z1)
        s.add(dot[z2][j] == z2)

    # zeros_distinct (already distinct by index)
    # no_other_zeros
    for x in range(2, n):
        s.add(Or([dot[x][j] != x for j in range(n)]))

    # Extensionality
    for x in range(n):
        for y in range(x + 1, n):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(n)]))

    # sec and ret are variables (pick from non-zero elements)
    # We'll try sec=2, ret=3 for n>=4, or search
    # Actually, let's make sec and ret Z3 variables to allow flexibility
    sec = Int("sec")
    ret = Int("ret")
    cls = Int("cls")

    s.add(sec >= 2, sec < n)
    s.add(ret >= 2, ret < n)
    s.add(cls >= 2, cls < n)

    # sec ≠ ret (for n >= 5 tests); for n=4 allow sec=ret
    if n >= 5:
        s.add(sec != ret)

    # Retraction pair: ret ∘ sec = id on core, sec ∘ ret = id on core
    for x in range(2, n):
        # dot[ret][dot[sec][x]] = x (on core: x ≠ z1, x ≠ z2, already guaranteed by range)
        sec_x = col_ite_lookup(dot, x, sec, n)  # need dot[sec][x]
        # Actually: sec_x = ite_lookup where row is sec
        # dot[sec][x] where sec is a Z3 variable
        # We need: for each core x, dot[ret][dot[sec][x]] = x
        # This requires nested ITE lookups

        # dot[sec][x]: sec is Z3 var, x is concrete
        sec_x = dot[2][x]  # placeholder
        for r in range(3, n):
            sec_x = If(sec == r, dot[r][x], sec_x)
        sec_x = If(sec == 2, dot[2][x], sec_x)

        # dot[ret][sec_x]: ret is Z3 var, sec_x is Z3 expr
        # Double ITE: first resolve ret to a row, then resolve sec_x to a column
        ret_sec_x = dot[2][0]  # placeholder
        for row in range(2, n):
            row_val = dot[row][0]
            for col in range(n):
                row_val = If(sec_x == col, dot[row][col], row_val)
            ret_sec_x = If(ret == row, row_val, ret_sec_x)
        # Fix: need proper initialization
        # Let me redo this more carefully

        # dot[sec][x] where sec is Z3 int
        sec_x_expr = dot[0][x]  # will be overwritten
        for r in range(n):
            sec_x_expr = If(sec == r, dot[r][x], sec_x_expr)

        # dot[ret][sec_x_expr] where ret is Z3 int, sec_x_expr is Z3 int
        ret_sec_x_expr = dot[0][0]
        for r in range(n):
            col_expr = dot[r][0]
            for c in range(1, n):
                col_expr = If(sec_x_expr == c, dot[r][c], col_expr)
            ret_sec_x_expr = If(ret == r, col_expr, ret_sec_x_expr)

        s.add(ret_sec_x_expr == x)

        # sec ∘ ret = id on core: dot[sec][dot[ret][x]] = x
        ret_x_expr = dot[0][x]
        for r in range(n):
            ret_x_expr = If(ret == r, dot[r][x], ret_x_expr)

        sec_ret_x_expr = dot[0][0]
        for r in range(n):
            col_expr = dot[r][0]
            for c in range(1, n):
                col_expr = If(ret_x_expr == c, dot[r][c], col_expr)
            sec_ret_x_expr = If(sec == r, col_expr, sec_ret_x_expr)

        s.add(sec_ret_x_expr == x)

    # ret_zero₁: dot[ret][0] = 0
    for r in range(n):
        # If ret == r, then dot[r][0] == 0
        pass
    # Simpler: encode as conjunction over possible ret values
    ret_z1_expr = dot[0][0]
    for r in range(n):
        ret_z1_expr = If(ret == r, dot[r][0], ret_z1_expr)
    s.add(ret_z1_expr == 0)

    # cls_boolean: for all x, dot[cls][x] ∈ {0, 1}
    for x in range(n):
        cls_x = dot[0][x]
        for r in range(n):
            cls_x = If(cls == r, dot[r][x], cls_x)
        s.add(Or(cls_x == 0, cls_x == 1))

    # cls_ne_zero₁, cls_ne_zero₂ (cls ≥ 2 already handles this)

    # Kripke dichotomy: for all y with y ≠ 0, y ≠ 1:
    #   either all core outputs are in {0,1}, or all core outputs are NOT in {0,1}
    for y in range(2, n):
        # All-boolean on core
        all_bool = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in range(2, n)])
        # All-non-boolean on core
        all_non_bool = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in range(2, n)])
        s.add(Or(all_bool, all_non_bool))

    # has_non_classifier: ∃ y ≠ 0,1 with ∃ x ≠ 0,1 with dot[y][x] ∉ {0,1}
    nc_clauses = []
    for y in range(2, n):
        for x in range(2, n):
            nc_clauses.append(And(dot[y][x] != 0, dot[y][x] != 1))
    s.add(Or(nc_clauses))

    # Commutativity
    if commutative:
        for a in range(n):
            for b in range(a + 1, n):
                s.add(dot[a][b] == dot[b][a])

    return s, dot


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    t_start = time.time()

    task1_closure()
    task2_symmetry()

    print(f"\n{'='*70}")
    print(f"Total time: {time.time() - t_start:.1f}s")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()

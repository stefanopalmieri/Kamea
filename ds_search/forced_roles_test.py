#!/usr/bin/env python3
"""
Forced Roles Theorem — Honest Characterization

Tests which pairs of TC roles are forced distinct by the behavioral axioms
vs. which can share a single element index.

METHODOLOGY: For each pair (R1, R2), assign both roles to the SAME index.
Apply all base axioms (L0-L8, C, D, PA, VV, QE, E-trans, 1-Inert, Branch,
Compose, Y, Selection). If UNSAT, the axioms force those roles apart.
If SAT, they can share an element.

This is NOT the same as forcing two different indices to have identical
rows — that's trivially UNSAT due to Ext (extensionality). The correct
test checks whether the combined behavioral constraints on a single index
are jointly satisfiable.

N=12: minimum size where all axioms are satisfiable. Using the minimum
makes results maximally general (if forced distinct at N=12, forced
distinct at all N≥12 by monotonicity).

Usage:
  uv run python -m ds_search.forced_roles_test
  uv run python -m ds_search.forced_roles_test --quick    # skip necessity analysis
"""

import time
import sys
import os
from itertools import combinations

from z3 import Solver, Int, If, And, Or, Not, sat, unsat

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ds_search.axiom_explorer import (
    encode_level, ite_lookup, col_ite_lookup,
)


# ═══════════════════════════════════════════════════════════════════════
# Parameters
# ═══════════════════════════════════════════════════════════════════════

N = 12
CORE_LO, CORE_HI = 2, 6  # core range for QE, Branch, Compose

# All 10 TC roles and their default indices (at N=12)
ROLES = {
    "⊤":  0,
    "⊥":  1,
    "τ":  3,
    "Q":  6,
    "E":  7,
    "f":  2,
    "g":  4,
    "ρ":  8,
    "η":  9,
    "Y": 10,
}

ROLE_NAMES = list(ROLES.keys())


# ═══════════════════════════════════════════════════════════════════════
# Z3 helpers (local copies — same as n16_freedom.py)
# ═══════════════════════════════════════════════════════════════════════

def is_inert_z3(dot, x, N):
    """Z3 expression: element x is inert (not tester, not encoder)."""
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
# Axiom groups — each returns constraints as a list, NOT added to solver
# This allows us to selectively include/exclude for necessity analysis
# ═══════════════════════════════════════════════════════════════════════

def axiom_L0(dot, N):
    """Level 0: absorbers + Ext + range + no extra absorbers."""
    constraints = []
    # Range
    for i in range(N):
        for j in range(N):
            constraints.append(dot[i][j] >= 0)
            constraints.append(dot[i][j] < N)
    # Absorbers
    for j in range(N):
        constraints.append(dot[0][j] == 0)
        constraints.append(dot[1][j] == 1)
    # No other absorbers
    for x in range(2, N):
        constraints.append(Or([dot[x][j] != x for j in range(N)]))
    # Ext: all rows distinct
    for x in range(N):
        for y in range(x + 1, N):
            constraints.append(Or([dot[x][j] != dot[y][j] for j in range(N)]))
    return constraints


def axiom_kripke(dot, N):
    """C (Kripke): only testers produce boolean output on non-absorbers."""
    constraints = []
    for x in range(2, N):
        is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        for y in range(2, N):
            constraints.append(Or(is_tst, dot[x][y] >= 2))
    return constraints


def axiom_inert_prop(dot, N):
    """D (Inert propagation): inert elements preserve non-absorber status."""
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
    """PA: power-associativity (x·x)·x = x·(x·x)."""
    constraints = []
    for x in range(N):
        xx = dot[x][x]
        constraints.append(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))
    return constraints


def axiom_vv(dot, N):
    """VV: inert self-application yields tester or encoder."""
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
    """QE: E·(Q·x) = x and Q·(E·x) = x on core."""
    constraints = []
    for x in range(core_lo, core_hi):
        qx = dot[q][x]
        constraints.append(col_ite_lookup(dot, e, qx, N) == x)
        ex = dot[e][x]
        constraints.append(col_ite_lookup(dot, q, ex, N) == x)
    return constraints


def axiom_e_trans(dot, e):
    """E-transparency: E·⊤ = ⊤, E·⊥ = ⊥."""
    return [dot[e][0] == 0, dot[e][1] == 1]


def axiom_1_inert(dot, N):
    """1-Inert: exactly 1 inert element."""
    constraints = []
    flags = []
    for x in range(2, N):
        flag = Int(f"zi_{x}")
        constraints.append(If(is_inert_z3(dot, x, N), flag == 1, flag == 0))
        flags.append(flag)
    constraints.append(sum(flags) == 1)
    return constraints


def axiom_branch(dot, t, f_, g_, r, core_lo, core_hi):
    """Branch: ρ·x = f·x if τ·x=⊤ else g·x, plus f≠g discrimination."""
    constraints = []
    for x in range(core_lo, core_hi):
        tx = dot[t][x]
        fx = dot[f_][x]
        gx = dot[g_][x]
        constraints.append(If(tx == 0, dot[r][x] == fx, dot[r][x] == gx))
    # f ≠ g on core (discrimination clause)
    constraints.append(Or([dot[f_][j] != dot[g_][j] for j in range(core_lo, core_hi)]))
    return constraints


def axiom_compose(dot, N, h, r, g_, core_lo, core_hi):
    """Compose: η·x = ρ·(g·x) on core."""
    constraints = []
    for x in range(core_lo, core_hi):
        gx = dot[g_][x]
        r_gx = col_ite_lookup(dot, r, gx, N)
        constraints.append(dot[h][x] == r_gx)
    return constraints


def axiom_y(dot, N, y, r):
    """Y-combinator: Y·ρ = ρ·(Y·ρ), Y·ρ ≥ 2."""
    yr = dot[y][r]
    r_yr = col_ite_lookup(dot, r, yr, N)
    return [yr == r_yr, yr >= 2]


def axiom_selection(dot, h, r, t):
    """Selection: η·ρ = τ."""
    return [dot[h][r] == t]


# Role constraints — force specific rows to be tester/inert/encoder
def role_tester(dot, N, idx):
    """Row idx is all-boolean."""
    return [Or(dot[idx][j] == 0, dot[idx][j] == 1) for j in range(N)]


def role_inert(dot, idx, N):
    """Row idx is inert."""
    return [is_inert_z3(dot, idx, N)]


def role_encoder(dot, N, idx):
    """Row idx is an encoder (≥2 distinct non-boolean outputs)."""
    enc_pairs = []
    for j1 in range(N):
        for j2 in range(j1 + 1, N):
            enc_pairs.append(And(
                dot[idx][j1] != 0, dot[idx][j1] != 1,
                dot[idx][j2] != 0, dot[idx][j2] != 1,
                dot[idx][j1] != dot[idx][j2]))
    return [Or(enc_pairs)]


# ═══════════════════════════════════════════════════════════════════════
# Build solver with role aliasing
# ═══════════════════════════════════════════════════════════════════════

# Which role is which type?
TESTER_ROLES = {"τ"}
INERT_ROLES = {"g"}
ABSORBER_ROLES = {"⊤", "⊥"}
ENCODER_ROLES = {"Q", "E", "f", "ρ", "η", "Y"}


def build_aliased_solver(role_a, role_b, skip_axiom_groups=None):
    """
    Build a solver where role_a and role_b share the same element index.

    Returns (solver, dot, axiom_group_names) where axiom_group_names
    maps group name -> list of constraints added.
    """
    if skip_axiom_groups is None:
        skip_axiom_groups = set()

    # Build index assignment: role_b gets the same index as role_a
    idx = dict(ROLES)  # copy defaults
    idx[role_b] = idx[role_a]  # alias!

    s = Solver()
    s.set("timeout", 300 * 1000)  # 5 min timeout

    # Create dot table
    dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]

    # Collect axiom groups for necessity analysis
    axiom_groups = {}

    def add_group(name, constraints):
        axiom_groups[name] = constraints
        if name not in skip_axiom_groups:
            for c in constraints:
                s.add(c)

    # L0 is always present (structural foundation)
    add_group("L0", axiom_L0(dot, N))

    # Behavioral axioms
    add_group("Kripke", axiom_kripke(dot, N))
    add_group("InertProp", axiom_inert_prop(dot, N))
    add_group("PA", axiom_pa(dot, N))
    add_group("VV", axiom_vv(dot, N))
    add_group("QE", axiom_qe(dot, N, idx["Q"], idx["E"], CORE_LO, CORE_HI))
    add_group("E-trans", axiom_e_trans(dot, idx["E"]))
    add_group("1-Inert", axiom_1_inert(dot, N))
    add_group("Branch", axiom_branch(
        dot, idx["τ"], idx["f"], idx["g"], idx["ρ"], CORE_LO, CORE_HI))
    add_group("Compose", axiom_compose(
        dot, N, idx["η"], idx["ρ"], idx["g"], CORE_LO, CORE_HI))
    add_group("Y", axiom_y(dot, N, idx["Y"], idx["ρ"]))
    add_group("Selection", axiom_selection(dot, idx["η"], idx["ρ"], idx["τ"]))

    # Role constraints for ALL 10 roles, using their (possibly aliased) indices
    # An aliased index gets BOTH role constraints — that's the whole point
    assigned_roles = {}  # idx -> set of roles
    for role_name, role_idx in idx.items():
        if role_name in ABSORBER_ROLES:
            continue  # absorber constraints are in L0
        assigned_roles.setdefault(role_idx, set()).add(role_name)

    # Determine tester/inert/encoder indices from all roles assigned to each index
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
        role_constraints.extend(role_tester(dot, N, t))
    for i_idx in inert_indices:
        role_constraints.extend(role_inert(dot, i_idx, N))
    for e in encoder_indices:
        role_constraints.extend(role_encoder(dot, N, e))

    add_group("Roles", role_constraints)

    return s, dot, axiom_groups


# ═══════════════════════════════════════════════════════════════════════
# Necessity analysis: which axiom group is responsible for UNSAT?
# ═══════════════════════════════════════════════════════════════════════

def find_necessary_axiom(role_a, role_b, axiom_group_names):
    """
    For an UNSAT pair, find which axiom group is necessary for the UNSAT.
    Removes one group at a time; the first removal that makes it SAT
    is (at least partly) responsible.
    """
    responsible = []
    for skip_name in axiom_group_names:
        if skip_name == "L0":
            continue  # never skip structural foundation
        s, _, _ = build_aliased_solver(role_a, role_b, skip_axiom_groups={skip_name})
        r = s.check()
        if str(r) == "sat":
            responsible.append(skip_name)
    return responsible


# ═══════════════════════════════════════════════════════════════════════
# Extract witness model for SAT pairs
# ═══════════════════════════════════════════════════════════════════════

def extract_witness(solver, dot, role_a, role_b):
    """Extract a compact witness from a SAT model."""
    m = solver.model()
    idx = dict(ROLES)
    idx[role_b] = idx[role_a]

    shared_idx = idx[role_a]
    row = [m.evaluate(dot[shared_idx][j]).as_long() for j in range(N)]

    # Show the shared row and a few key properties
    witness = {
        "shared_index": shared_idx,
        "shared_row": row,
    }
    return witness


# ═══════════════════════════════════════════════════════════════════════
# Graph analysis
# ═══════════════════════════════════════════════════════════════════════

def max_independent_set_bruteforce(can_merge_pairs, nodes):
    """
    Find maximum independent set of the forced-distinct graph
    (= maximum clique of the can-merge graph).
    With 10 nodes this is trivial to brute force.
    """
    # Build can-merge adjacency
    can_merge = set()
    for a, b in can_merge_pairs:
        can_merge.add((a, b))
        can_merge.add((b, a))

    # The "can-merge graph" has edges where merging is possible.
    # Maximum clique in can-merge graph = max set of roles that can all share one element.
    # But that's not quite right — we want min elements needed.
    # What we want: chromatic number of the forced-distinct graph.
    # Forced-distinct graph: edge iff UNSAT (cannot merge).
    # Chromatic number = min colors = min distinct elements needed.

    # Build forced-distinct adjacency
    forced_distinct = set()
    all_pairs = set(combinations(nodes, 2))
    for a, b in all_pairs:
        if (a, b) not in can_merge and (b, a) not in can_merge:
            forced_distinct.add((a, b))

    # For chromatic number with 10 nodes, try all k-colorings for k=1..10
    from itertools import product as iproduct
    for k in range(1, len(nodes) + 1):
        # Try all k-colorings
        for coloring in iproduct(range(k), repeat=len(nodes)):
            valid = True
            for (a, b) in forced_distinct:
                ia = nodes.index(a)
                ib = nodes.index(b)
                if coloring[ia] == coloring[ib]:
                    valid = False
                    break
            if valid:
                # Build the partition
                partition = {}
                for i, node in enumerate(nodes):
                    partition.setdefault(coloring[i], []).append(node)
                return k, partition
    return len(nodes), {i: [n] for i, n in enumerate(nodes)}


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    quick = "--quick" in sys.argv

    print("=" * 70)
    print("FORCED ROLES THEOREM — Honest Characterization")
    print(f"N={N}, all 10 TC roles, C(10,2) = 45 pairwise tests")
    print("=" * 70)
    print()
    print("Methodology: for each pair (R1, R2), assign both roles to the")
    print("SAME element index and check if all axioms are jointly SAT.")
    print("This tests role-forcing, NOT extensionality.")
    print()

    pairs = list(combinations(ROLE_NAMES, 2))
    assert len(pairs) == 45, f"Expected 45 pairs, got {len(pairs)}"

    results = {}  # label -> "SAT" or "UNSAT"
    sat_pairs = []
    unsat_pairs = []
    timings = {}

    print(f"{'Pair':>12s}  {'Result':>8s}  {'Time':>8s}")
    print("-" * 34)

    for role_a, role_b in pairs:
        label = f"{role_a}={role_b}"

        t0 = time.time()
        s, dot, axiom_groups = build_aliased_solver(role_a, role_b)
        r = s.check()
        elapsed = time.time() - t0

        result_str = str(r).upper()
        results[label] = result_str
        timings[label] = elapsed

        if result_str == "SAT":
            sat_pairs.append((role_a, role_b, label))
        elif result_str == "UNSAT":
            unsat_pairs.append((role_a, role_b, label))

        print(f"{label:>12s}  {result_str:>8s}  {elapsed:>7.1f}s", flush=True)

    # ── Summary ──────────────────────────────────────────────────────
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"  Total pairs:  {len(pairs)}")
    print(f"  UNSAT:        {len(unsat_pairs)}  (forced distinct by axioms)")
    print(f"  SAT:          {len(sat_pairs)}  (can share one element)")
    unknown = len(pairs) - len(sat_pairs) - len(unsat_pairs)
    if unknown:
        print(f"  UNKNOWN:      {unknown}  (timeout)")

    # ── SAT pairs: extract witnesses ─────────────────────────────────
    if sat_pairs:
        print(f"\n{'='*70}")
        print("MERGEABLE PAIRS (SAT)")
        print(f"{'='*70}")
        for role_a, role_b, label in sat_pairs:
            s, dot, _ = build_aliased_solver(role_a, role_b)
            r = s.check()
            if str(r) == "sat":
                w = extract_witness(s, dot, role_a, role_b)
                print(f"\n  {label}: shared index {w['shared_index']}")
                print(f"    row = {w['shared_row']}")

    # ── UNSAT pairs: necessity analysis ──────────────────────────────
    if unsat_pairs and not quick:
        print(f"\n{'='*70}")
        print("NECESSITY ANALYSIS (which axiom forces each distinction?)")
        print(f"{'='*70}")

        axiom_group_names = [
            "Kripke", "InertProp", "PA", "VV", "QE",
            "E-trans", "1-Inert", "Branch", "Compose", "Y",
            "Selection", "Roles",
        ]

        for role_a, role_b, label in unsat_pairs:
            t0 = time.time()
            responsible = find_necessary_axiom(role_a, role_b, axiom_group_names)
            elapsed = time.time() - t0
            if responsible:
                print(f"  {label:>12s}: necessary group(s) = {responsible}  ({elapsed:.1f}s)")
            else:
                print(f"  {label:>12s}: no single group sufficient (interaction)  ({elapsed:.1f}s)")

    # ── Graph analysis ───────────────────────────────────────────────
    print(f"\n{'='*70}")
    print("FORCED-DISTINCT GRAPH ANALYSIS")
    print(f"{'='*70}")

    can_merge = [(a, b) for a, b, _ in sat_pairs]
    cannot_merge = [(a, b) for a, b, _ in unsat_pairs]

    print(f"\n  Forced-distinct edges (UNSAT): {len(cannot_merge)}")
    print(f"  Can-merge edges (SAT):         {len(can_merge)}")

    # Chromatic number = minimum distinct elements needed
    min_elements, partition = max_independent_set_bruteforce(
        can_merge, ROLE_NAMES)

    print(f"\n  Minimum distinct elements needed: {min_elements}")
    print(f"  One possible partition:")
    for color, roles in sorted(partition.items()):
        print(f"    Element {color}: {roles}")

    # ── Adjacency matrix ─────────────────────────────────────────────
    print(f"\n  Forced-distinct matrix (X = forced distinct, · = can merge):")
    header = "         " + "  ".join(f"{r:>2s}" for r in ROLE_NAMES)
    print(header)
    for i, ri in enumerate(ROLE_NAMES):
        row_str = f"  {ri:>5s}  "
        for j, rj in enumerate(ROLE_NAMES):
            if i == j:
                row_str += " - "
            elif i < j:
                label = f"{ri}={rj}"
                row_str += " X " if results.get(label) == "UNSAT" else " · "
            else:
                label = f"{rj}={ri}"
                row_str += " X " if results.get(label) == "UNSAT" else " · "
        print(row_str)


if __name__ == "__main__":
    main()

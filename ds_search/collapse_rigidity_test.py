#!/usr/bin/env python3
"""
Test whether role collapse kills rigidity.

For each collapse level (0-5), build an N=12 model with progressively
merged TC roles, then check:
  - SAT? (does a model exist?)
  - WL-1 rigid? (does WL-1 color refinement fully discriminate?)
  - Automorphism group (exact, brute-force on (N-2)! or similar)
  - Discoverability (can behavioral probes distinguish all elements?)

Collapse levels:
  0: No collapse (baseline — all 10 roles on separate indices)
  1: Q=E only (9 distinct role elements)
  2: Q=E, ρ=Y (8 distinct role elements)
  3: Q=E=f, ρ=Y (7 distinct role elements)
  4: Q=E=f=ρ=Y (6 distinct role elements — η separate)
  5: Q=E=f=ρ=Y, ⊤=⊥ (5 distinct role elements — maximal)

Usage:
  uv run python -m ds_search.collapse_rigidity_test
"""

import sys
import os
import time
from itertools import permutations, combinations
from collections import Counter

import numpy as np
from z3 import Solver, Int, If, And, Or, Not, sat

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ds_search.axiom_explorer import (
    encode_level, extract_table, ite_lookup, col_ite_lookup,
)
from ds_search.forced_roles_test import (
    is_inert_z3,
    axiom_kripke, axiom_inert_prop, axiom_pa, axiom_vv,
    axiom_qe, axiom_e_trans, axiom_1_inert,
    axiom_branch, axiom_compose, axiom_y, axiom_selection,
    role_tester, role_inert, role_encoder,
    TESTER_ROLES, INERT_ROLES, ABSORBER_ROLES, ENCODER_ROLES,
)


# ═══════════════════════════════════════════════════════════════════════
# Parameters
# ═══════════════════════════════════════════════════════════════════════

N = 12
CORE_LO, CORE_HI = 2, 6

# Default role indices (no collapse)
DEFAULT_ROLES = {
    "⊤": 0, "⊥": 1, "τ": 3, "Q": 6, "E": 7,
    "f": 2, "g": 4, "ρ": 8, "η": 9, "Y": 10,
}

# Collapse levels: list of (level_name, merges) where merges
# maps role -> role_it_shares_index_with
COLLAPSE_LEVELS = [
    ("Level 0: no collapse", {}),
    ("Level 1: Q=E", {"E": "Q"}),
    ("Level 2: Q=E, ρ=Y", {"E": "Q", "Y": "ρ"}),
    ("Level 3: Q=E=f, ρ=Y", {"E": "Q", "f": "Q", "Y": "ρ"}),
    ("Level 4: Q=E=f=ρ=Y", {"E": "Q", "f": "Q", "ρ": "Q", "Y": "Q"}),
    ("Level 5: Q=E=f=ρ=Y, ⊤=⊥", {"E": "Q", "f": "Q", "ρ": "Q", "Y": "Q", "⊥": "⊤"}),
]


# ═══════════════════════════════════════════════════════════════════════
# Build solver for a given collapse level
# ═══════════════════════════════════════════════════════════════════════

def build_collapsed_solver(merges):
    """
    Build a solver with the given role merges.
    merges: dict mapping role_name -> role_it_shares_index_with
    """
    # Compute index assignment
    idx = dict(DEFAULT_ROLES)
    for role, target in merges.items():
        idx[role] = idx[target]

    s = Solver()
    s.set("timeout", 300 * 1000)

    dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]

    # Range + L0 basics
    for i in range(N):
        for j in range(N):
            s.add(dot[i][j] >= 0)
            s.add(dot[i][j] < N)

    # Absorbers — use the actual indices
    top_idx = idx["⊤"]
    bot_idx = idx["⊥"]

    for j in range(N):
        s.add(dot[top_idx][j] == top_idx)

    if bot_idx != top_idx:
        for j in range(N):
            s.add(dot[bot_idx][j] == bot_idx)

    # No other absorbers
    for x in range(N):
        if x == top_idx or x == bot_idx:
            continue
        s.add(Or([dot[x][j] != x for j in range(N)]))

    # Ext: all rows distinct
    for x in range(N):
        for y in range(x + 1, N):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(N)]))

    # Behavioral axioms — use aliased indices
    for c in axiom_kripke(dot, N):
        s.add(c)
    for c in axiom_inert_prop(dot, N):
        s.add(c)
    for c in axiom_pa(dot, N):
        s.add(c)
    for c in axiom_vv(dot, N):
        s.add(c)
    for c in axiom_qe(dot, N, idx["Q"], idx["E"], CORE_LO, CORE_HI):
        s.add(c)
    for c in axiom_e_trans(dot, idx["E"]):
        s.add(c)
    for c in axiom_1_inert(dot, N):
        s.add(c)
    for c in axiom_branch(dot, idx["τ"], idx["f"], idx["g"], idx["ρ"],
                          CORE_LO, CORE_HI):
        s.add(c)
    for c in axiom_compose(dot, N, idx["η"], idx["ρ"], idx["g"],
                           CORE_LO, CORE_HI):
        s.add(c)
    for c in axiom_y(dot, N, idx["Y"], idx["ρ"]):
        s.add(c)
    for c in axiom_selection(dot, idx["η"], idx["ρ"], idx["τ"]):
        s.add(c)

    # Role constraints — apply to the (possibly aliased) indices
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

    for t in tester_indices:
        for c in role_tester(dot, N, t):
            s.add(c)
    for i_idx in inert_indices:
        for c in role_inert(dot, i_idx, N):
            s.add(c)
    for e in encoder_indices:
        for c in role_encoder(dot, N, e):
            s.add(c)

    return s, dot, idx


# ═══════════════════════════════════════════════════════════════════════
# WL-1 Color Refinement
# ═══════════════════════════════════════════════════════════════════════

def wl_refine(table, n, max_rounds=100):
    """WL-1 color refinement. Returns (num_colors, rounds, colors)."""
    arr = np.array(table, dtype=np.int64)

    # Initial coloring: row spectrum + col spectrum + idempotent flag
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
                neighbors.append(
                    (int(colors[y]),
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
            return num_new, round_num + 1, colors
        if num_new == n:
            return n, round_num + 1, colors

    return len(set(colors)), max_rounds, colors


# ═══════════════════════════════════════════════════════════════════════
# Automorphism Group (brute force with absorber pruning)
# ═══════════════════════════════════════════════════════════════════════

def compute_automorphisms(table, n):
    """
    Compute Aut(table) by brute force. Prunes by fixing elements whose
    rows are unique constant rows (absorbers).

    Returns list of automorphisms as tuples.
    """
    arr = np.array(table, dtype=np.int64)

    # Find absorber indices (constant rows: row[j] = i for all j)
    absorbers = []
    for i in range(n):
        if all(arr[i, j] == i for j in range(n)):
            absorbers.append(i)

    # Absorbers must map to absorbers. With 2 absorbers and their rows
    # being different constants, each must map to itself.
    # With 1 absorber (⊤=⊥ collapse), it maps to itself.
    fixed = set(absorbers)
    free = [i for i in range(n) if i not in fixed]

    auts = []
    for perm_free in permutations(free):
        p = list(range(n))
        for i, v in zip(free, perm_free):
            p[i] = v

        # Check homomorphism: p[table[x][y]] == table[p[x]][p[y]]
        is_aut = True
        for x in range(n):
            if not is_aut:
                break
            for y in range(n):
                if p[arr[x, y]] != arr[p[x], p[y]]:
                    is_aut = False
                    break
        if is_aut:
            auts.append(tuple(p))

    return auts


def format_perm(p):
    """Format permutation as cycle notation."""
    n = len(p)
    visited = [False] * n
    cycles = []
    for i in range(n):
        if visited[i] or p[i] == i:
            visited[i] = True
            continue
        cycle = [i]
        visited[i] = True
        j = p[i]
        while j != i:
            cycle.append(j)
            visited[j] = True
            j = p[j]
        if len(cycle) > 1:
            cycles.append(tuple(cycle))
    if not cycles:
        return "id"
    return " ".join(f"({' '.join(str(x) for x in c)})" for c in cycles)


# ═══════════════════════════════════════════════════════════════════════
# Discoverability Check
# ═══════════════════════════════════════════════════════════════════════

def check_discoverability(table, n):
    """
    Check if all elements can be distinguished by behavioral probes.

    A "probe" is a tuple (x·a, a·x) for some fixed probe element a.
    Check how many probe elements are needed to distinguish all n elements.

    Also checks the stronger condition: is the 2-probe signature
    (x·a, a·x, x·b, b·x) injective for some pair (a, b)?

    Returns (min_probes_needed, injective_pair_or_None).
    """
    # For each single probe a, compute signatures
    for a in range(n):
        sigs = {}
        all_distinct = True
        for x in range(n):
            sig = (table[x][a], table[a][x])
            if sig in sigs:
                all_distinct = False
                break
            sigs[sig] = x
        if all_distinct:
            return 1, (a,)

    # Try 2-probe pairs
    for a in range(n):
        for b in range(a + 1, n):
            sigs = {}
            all_distinct = True
            for x in range(n):
                sig = (table[x][a], table[a][x], table[x][b], table[b][x])
                if sig in sigs:
                    all_distinct = False
                    break
                sigs[sig] = x
            if all_distinct:
                return 2, (a, b)

    # Try 3-probe triples
    for a in range(n):
        for b in range(a + 1, n):
            for c in range(b + 1, n):
                sigs = {}
                all_distinct = True
                for x in range(n):
                    sig = (table[x][a], table[a][x],
                           table[x][b], table[b][x],
                           table[x][c], table[c][x])
                    if sig in sigs:
                        all_distinct = False
                        break
                    sigs[sig] = x
                if all_distinct:
                    return 3, (a, b, c)

    # Try 4
    for combo in combinations(range(n), 4):
        sigs = {}
        all_distinct = True
        for x in range(n):
            sig = tuple(v for a in combo for v in (table[x][a], table[a][x]))
            if sig in sigs:
                all_distinct = False
                break
            sigs[sig] = x
        if all_distinct:
            return 4, combo

    return n, None  # worst case: need all elements as probes


def find_indistinguishable_pairs(table, n):
    """Find pairs of elements that no single probe can distinguish."""
    # Full signature using ALL probes
    full_sigs = {}
    for x in range(n):
        sig = tuple(table[x][a] for a in range(n)) + tuple(table[a][x] for a in range(n))
        full_sigs.setdefault(sig, []).append(x)

    indistinguishable = []
    for sig, elems in full_sigs.items():
        if len(elems) > 1:
            indistinguishable.append(elems)
    return indistinguishable


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("=" * 78)
    print("ROLE COLLAPSE vs RIGIDITY — N=12")
    print("Does collapsing TC roles kill self-knowledge?")
    print("=" * 78)

    results = []

    for level, (name, merges) in enumerate(COLLAPSE_LEVELS):
        print(f"\n{'─'*78}")
        print(f"  {name}")
        print(f"{'─'*78}")

        # Build solver
        t0 = time.time()
        s, dot, idx = build_collapsed_solver(merges)
        build_time = time.time() - t0

        # Show index assignment
        unique_indices = {}
        for role, role_idx in sorted(idx.items(), key=lambda x: x[1]):
            unique_indices.setdefault(role_idx, []).append(role)
        print(f"  Index assignment:")
        for role_idx in sorted(unique_indices):
            roles = unique_indices[role_idx]
            print(f"    {role_idx}: {', '.join(roles)}")

        # Check SAT
        print(f"  Checking SAT...", flush=True)
        t0 = time.time()
        result = s.check()
        sat_time = time.time() - t0
        is_sat = str(result) == "sat"
        print(f"  Result: {result} ({sat_time:.1f}s)")

        if not is_sat:
            results.append({
                "level": level, "name": name, "sat": False,
                "wl1_rigid": None, "aut_size": None, "aut_generators": [],
                "discoverable": None, "probes": None,
            })
            continue

        # Extract table
        table = extract_table(s.model(), dot, N)

        # Print table
        print(f"\n  Cayley table:")
        print(f"        ", end="")
        for j in range(N):
            print(f"{j:3d}", end="")
        print()
        for i in range(N):
            roles_at_i = unique_indices.get(i, [])
            label = ",".join(roles_at_i) if roles_at_i else str(i)
            print(f"  {i:2d} ({label:>6s})", end=" ")
            for j in range(N):
                print(f"{table[i][j]:3d}", end="")
            print()

        # WL-1 refinement
        print(f"\n  WL-1 color refinement:", flush=True)
        num_colors, rounds, colors = wl_refine(table, N)
        wl1_rigid = num_colors == N
        print(f"    Colors: {num_colors}/{N}, rounds: {rounds}")
        print(f"    Rigid: {'YES' if wl1_rigid else 'NO'}")
        if not wl1_rigid:
            # Show which elements share colors
            color_groups = {}
            for x in range(N):
                color_groups.setdefault(int(colors[x]), []).append(x)
            for color, elems in sorted(color_groups.items()):
                if len(elems) > 1:
                    roles_info = []
                    for e in elems:
                        r = unique_indices.get(e, [str(e)])
                        roles_info.append(f"{e}({','.join(r)})")
                    print(f"    WL-indistinguishable: {roles_info}")

        # Automorphism group
        print(f"\n  Automorphism group:", flush=True)
        t0 = time.time()
        auts = compute_automorphisms(table, N)
        aut_time = time.time() - t0
        print(f"    |Aut| = {len(auts)} ({aut_time:.1f}s)")

        non_trivial = [a for a in auts if any(a[i] != i for i in range(N))]
        if non_trivial:
            print(f"    Non-trivial automorphisms:")
            for a in non_trivial[:10]:  # show up to 10
                print(f"      {format_perm(a)}")
                # Show which role elements are moved
                moved_roles = []
                for i in range(N):
                    if a[i] != i:
                        r = unique_indices.get(i, [str(i)])
                        moved_roles.append(f"{i}({','.join(r)})->{a[i]}")
                print(f"        moves: {', '.join(moved_roles)}")
            if len(non_trivial) > 10:
                print(f"      ... and {len(non_trivial) - 10} more")

        # Discoverability
        print(f"\n  Discoverability:", flush=True)
        min_probes, probe_set = check_discoverability(table, N)
        print(f"    Min probes needed: {min_probes}")
        if probe_set:
            print(f"    Distinguishing probe set: {probe_set}")

        # Check for indistinguishable pairs even with all probes
        inds = find_indistinguishable_pairs(table, N)
        if inds:
            print(f"    WARNING: indistinguishable element groups: {inds}")
            discoverable = False
        else:
            discoverable = True
            print(f"    All {N} elements distinguishable: YES")

        results.append({
            "level": level, "name": name, "sat": True,
            "wl1_rigid": wl1_rigid, "aut_size": len(auts),
            "aut_generators": non_trivial[:5],
            "discoverable": discoverable, "probes": min_probes,
        })

    # ── Summary Table ────────────────────────────────────────────────
    print(f"\n\n{'='*78}")
    print("SUMMARY TABLE")
    print(f"{'='*78}")
    print()
    print(f"| {'Level':5s} | {'Roles Merged':25s} | {'SAT?':4s} | {'WL-1':5s} | {'|Aut|':6s} | {'Probes':6s} |")
    print(f"|{'-'*7}|{'-'*27}|{'-'*6}|{'-'*7}|{'-'*8}|{'-'*8}|")

    for r in results:
        level = r["level"]
        merges_desc = COLLAPSE_LEVELS[level][0].split(": ", 1)[-1]
        sat_str = "YES" if r["sat"] else "NO"
        wl1_str = "YES" if r["wl1_rigid"] else ("NO" if r["wl1_rigid"] is not None else "—")
        aut_str = str(r["aut_size"]) if r["aut_size"] is not None else "—"
        probe_str = str(r["probes"]) if r["probes"] is not None else "—"
        print(f"| {level:5d} | {merges_desc:25s} | {sat_str:4s} | {wl1_str:5s} | {aut_str:>6s} | {probe_str:>6s} |")

    # ── Analysis ─────────────────────────────────────────────────────
    print(f"\n{'='*78}")
    print("ANALYSIS")
    print(f"{'='*78}")

    # Find transition point
    rigid_levels = [r["level"] for r in results if r["wl1_rigid"]]
    non_rigid_levels = [r["level"] for r in results if r["wl1_rigid"] is False]

    if rigid_levels and non_rigid_levels:
        threshold = min(non_rigid_levels)
        last_rigid = max(l for l in rigid_levels if l < threshold)
        print(f"\n  Rigidity threshold: breaks at level {threshold}")
        print(f"  Last rigid level: {last_rigid}")
        print(f"  → Role specialization beyond level {last_rigid} is necessary for self-knowledge")
    elif rigid_levels and not non_rigid_levels:
        print(f"\n  Rigidity survives all collapse levels!")
        print(f"  → Self-knowledge does NOT require role specialization")
        print(f"  → The algebra is robust: even minimal instantiation knows itself")
    elif non_rigid_levels and not rigid_levels:
        print(f"\n  No collapse level preserves rigidity")
        print(f"  (This would be surprising — check baseline)")
    else:
        print(f"\n  Could not determine rigidity pattern (some levels UNSAT?)")

    # For non-rigid levels, show what elements become interchangeable
    for r in results:
        if r["aut_size"] and r["aut_size"] > 1:
            print(f"\n  Level {r['level']} automorphism analysis:")
            for a in r["aut_generators"]:
                # Classify moved elements
                role_moved = []
                filler_moved = []
                for i in range(N):
                    if a[i] != i:
                        roles = COLLAPSE_LEVELS[r["level"]][1]
                        idx = dict(DEFAULT_ROLES)
                        for role, target in roles.items():
                            idx[role] = idx[target]
                        role_at_i = [rn for rn, ri in idx.items() if ri == i]
                        if role_at_i:
                            role_moved.append(i)
                        else:
                            filler_moved.append(i)
                if role_moved:
                    print(f"    Automorphism moves ROLE elements: {role_moved}")
                if filler_moved:
                    print(f"    Automorphism moves FILLER elements: {filler_moved}")


if __name__ == "__main__":
    main()

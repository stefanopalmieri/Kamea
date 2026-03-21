#!/usr/bin/env python3
"""
Cell-by-cell freedom analysis for Ψ₁₆ᶠ (N=16).

For each of the 256 cells in the 16×16 Cayley table, test each of the 16
possible values individually using Z3 push/pop. A cell is "fixed" if exactly
1 value is SAT. Reports determination percentage and classifies free cells
by role (tester vs structural).

Previous results:
  N=8:  18/64 fixed  (28.1%)
  N=12: 27/144 fixed (18.8%)
  N=16: ???

Usage:
  uv run python -m ds_search.n16_freedom           # full analysis
  uv run python -m ds_search.n16_freedom --quick    # fixed/free scan only (no value enum)
"""

import time
import sys
from z3 import Solver, Int, If, And, Or, Not, sat

from ds_search.axiom_explorer import (
    encode_level, extract_table, classify_elements,
    ite_lookup, col_ite_lookup, row_is_boolean,
)


# ═══════════════════════════════════════════════════════════════════════
# Ψ₁₆ᶠ element assignments
# ═══════════════════════════════════════════════════════════════════════

N = 16

# Core range for QE: elements 2..5 (f, τ, g, SEQ)
CORE_LO, CORE_HI = 2, 6
Q_IDX, E_IDX = 6, 7

# Named elements
T_IDX = 3    # τ (tester / branch selector)
F_IDX = 2    # f (branch-if)
G_IDX = 4    # g (inert / branch-else)
R_IDX = 8    # ρ (branch element)
H_IDX = 9    # η (compose element)
Y_IDX = 10   # Y-combinator
INC_IDX = 13
S0_IDX = 12  # s0 (counter zero state)

# Testers in Ψ₁₆ᶠ: τ(3), SEQ(5), s0(12)
TESTER_INDICES = {3, 5, 12}
# Inert: g(4)
INERT_INDICES = {4}
# Encoders: everything else that's not absorber/tester/inert
ENCODER_INDICES = {2, 6, 7, 8, 9, 10, 11, 13, 14, 15}

NAMES = {
    0: "⊤", 1: "⊥", 2: "f", 3: "τ", 4: "g", 5: "SEQ",
    6: "Q", 7: "E", 8: "ρ", 9: "η", 10: "Y", 11: "PAIR",
    12: "s0", 13: "INC", 14: "s1", 15: "DEC",
}

# 8-state counter cycle: s0→s1→s2→s3→s4→s5→s6→s7→s0
COUNTER_CYCLE = [12, 14, 6, 11, 10, 15, 8, 7]


# ═══════════════════════════════════════════════════════════════════════
# Axiom encoding helpers (same as stacking_analysis.py)
# ═══════════════════════════════════════════════════════════════════════

def add_kripke_c(s, dot, N):
    """Kripke: only testers produce boolean output on non-absorbers."""
    for x in range(2, N):
        is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        for y in range(2, N):
            s.add(Or(is_tst, dot[x][y] >= 2))


def add_inert_propagation(s, dot, N):
    """D: inert elements preserve non-absorber status."""
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
            s.add(Or(Not(is_inert), dot[x][y] >= 2))


def add_pa(s, dot, N):
    """Power-associativity: (x·x)·x = x·(x·x)."""
    for x in range(N):
        xx = dot[x][x]
        s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))


def add_vv(s, dot, N):
    """VV: inert self-application yields tester or encoder."""
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
        s.add(Or(Not(is_inert_v), vv_is_core))


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


def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo, core_hi):
    """QE: E·(Q·x) = x and Q·(E·x) = x on core."""
    for x in range(core_lo, core_hi):
        qx = dot[q_idx][x]
        s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
        ex = dot[e_idx][x]
        s.add(col_ite_lookup(dot, q_idx, ex, N) == x)


# ═══════════════════════════════════════════════════════════════════════
# Build the full N=16 solver
# ═══════════════════════════════════════════════════════════════════════

def build_solver():
    """Full Ψ₁₆ᶠ axiom set at N=16."""
    print("  Building solver...", flush=True)
    t0 = time.time()

    s, dot = encode_level(8, N, timeout_seconds=600)

    # Base axioms
    add_kripke_c(s, dot, N)
    add_inert_propagation(s, dot, N)
    add_pa(s, dot, N)
    add_vv(s, dot, N)

    # QE pair on core [2, 6)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, CORE_LO, CORE_HI)

    # E-transparency
    s.add(dot[E_IDX][0] == 0)
    s.add(dot[E_IDX][1] == 1)

    # 1-inert: exactly 1 inert element
    for x in range(2, N):
        iflag = Int(f"zi_{x}")
        s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
    s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)

    # Branch: ρ·x = f·x if τ·x = ⊤, else ρ·x = g·x (on core)
    for x in range(CORE_LO, CORE_HI):
        tx = dot[T_IDX][x]
        fx = dot[F_IDX][x]
        gx = dot[G_IDX][x]
        s.add(If(tx == 0, dot[R_IDX][x] == fx, dot[R_IDX][x] == gx))
    s.add(Or([dot[F_IDX][j] != dot[G_IDX][j] for j in range(CORE_LO, CORE_HI)]))

    # Compose: η·x = ρ·(g·x) on core
    for x in range(CORE_LO, CORE_HI):
        gx = dot[G_IDX][x]
        r_gx = col_ite_lookup(dot, R_IDX, gx, N)
        s.add(dot[H_IDX][x] == r_gx)

    # Y-combinator: Y·ρ = ρ·(Y·ρ), Y·ρ ≥ 2
    yr = dot[Y_IDX][R_IDX]
    r_yr = col_ite_lookup(dot, R_IDX, yr, N)
    s.add(yr == r_yr)
    s.add(yr >= 2)

    # Selection: η·ρ = τ
    s.add(dot[H_IDX][R_IDX] == T_IDX)

    # Role constraints (from Ψ₁₆ᶠ element assignments)
    # Testers: rows 3, 5, 12 are all-boolean
    for t in TESTER_INDICES:
        for j in range(N):
            s.add(Or(dot[t][j] == 0, dot[t][j] == 1))

    # Inert: element 4 is inert
    s.add(is_inert_z3(dot, G_IDX, N))

    # Encoders: elements in ENCODER_INDICES are encoders
    for e in ENCODER_INDICES:
        enc_pairs = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                enc_pairs.append(And(
                    dot[e][j1] != 0, dot[e][j1] != 1,
                    dot[e][j2] != 0, dot[e][j2] != 1,
                    dot[e][j1] != dot[e][j2]))
        s.add(Or(enc_pairs))

    # 8-state counter: INC cycles s0 through 8 states
    cur = S0_IDX
    for si in COUNTER_CYCLE[1:]:
        # INC · cur = next state
        s.add(dot[INC_IDX][cur] == si)
        cur = si
    s.add(dot[INC_IDX][cur] == S0_IDX)  # wrap around

    # DEC reverses: DEC · s_i = s_{i-1 mod 8}
    DEC_IDX = 15
    for i in range(8):
        si = COUNTER_CYCLE[i]
        si_prev = COUNTER_CYCLE[(i - 1) % 8]
        s.add(dot[DEC_IDX][si] == si_prev)

    # Zero test: τ·s0 = ⊤, τ·sₖ = ⊥ for k≠0
    s.add(dot[T_IDX][S0_IDX] == 0)
    for si in COUNTER_CYCLE[1:]:
        s.add(dot[T_IDX][si] != 0)

    # IO roundtrip: GET·(PUT·x) = x on core
    PUT_IDX, GET_IDX = 15, 14
    for x in range(CORE_LO, CORE_HI):
        put_x = dot[PUT_IDX][x]
        s.add(col_ite_lookup(dot, GET_IDX, put_x, N) == x)

    # PAIR/FST/SND: curried 2×2 product on {s0, s1}
    PAIR_IDX, FST_IDX, SND_IDX = 11, 14, 6
    S1_IDX = 14
    for si in [S0_IDX, S1_IDX]:
        for sj in [S0_IDX, S1_IDX]:
            # (PAIR · si) · sj = p_ij
            pair_si = dot[PAIR_IDX][si]
            p_ij = col_ite_lookup(dot, pair_si, sj, N) if isinstance(pair_si, int) else col_ite_lookup(dot, PAIR_IDX, si, N)
            # Actually need: dot[dot[PAIR][si]][sj]
            # pair_si is a Z3 expr, so use ite_lookup
            p_ij = ite_lookup(dot, dot[PAIR_IDX][si], sj, N)
            # FST · p_ij = si
            s.add(col_ite_lookup(dot, FST_IDX, p_ij, N) == si)
            # SND · p_ij = sj
            s.add(col_ite_lookup(dot, SND_IDX, p_ij, N) == sj)

    # SWAP involution on core: SWAP·(SWAP·x) = x
    SWAP_IDX = 14
    for x in range(CORE_LO, CORE_HI):
        swap_x = dot[SWAP_IDX][x]
        s.add(col_ite_lookup(dot, SWAP_IDX, swap_x, N) == x)

    # INC2 sub-counter on {s0, s1, s2, s3}: E cycles s0→s1→s2→s3→s0
    INC2_IDX = 7  # E
    sub_states = COUNTER_CYCLE[:4]  # s0, s1, s2, s3
    for i in range(4):
        s.add(dot[INC2_IDX][sub_states[i]] == sub_states[(i + 1) % 4])

    elapsed = time.time() - t0
    print(f"  Solver built ({elapsed:.1f}s)", flush=True)
    return s, dot


# ═══════════════════════════════════════════════════════════════════════
# Cell-by-cell freedom analysis
# ═══════════════════════════════════════════════════════════════════════

def run_analysis(quick=False):
    print("=" * 70)
    print("CELL-BY-CELL FREEDOM ANALYSIS — Ψ₁₆ᶠ (N=16)")
    print("=" * 70)

    s, dot = build_solver()

    # Step 1: Get reference model
    print("\nStep 1: Finding reference model...", flush=True)
    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    if result != sat:
        print(f"  UNSAT or timeout ({result}, {elapsed:.1f}s)")
        return
    ref = extract_table(s.model(), dot, N)
    print(f"  SAT ({elapsed:.1f}s)")

    # Step 2: Fast fixed/free scan
    print(f"\n{'='*70}")
    print(f"Step 2: Cell-by-cell SAT scan ({N*N} cells)")
    print(f"{'='*70}\n")

    free_cells = []
    fixed_cells = []
    t_total = time.time()

    for i in range(N):
        row_t0 = time.time()
        row_free_count = 0
        for j in range(N):
            ref_val = ref[i][j]
            s.push()
            s.add(dot[i][j] != ref_val)
            r = s.check()
            if r == sat:
                free_cells.append((i, j))
                row_free_count += 1
            else:
                fixed_cells.append((i, j))
            s.pop()
        row_elapsed = time.time() - row_t0
        name = NAMES.get(i, str(i))
        print(f"  Row {i:2d} ({name:>4s}): {N - row_free_count:2d} fixed, "
              f"{row_free_count:2d} free  ({row_elapsed:.1f}s)", flush=True)

    total_elapsed = time.time() - t_total
    n_fixed = len(fixed_cells)
    n_free = len(free_cells)
    pct = 100 * n_fixed / (N * N)
    print(f"\n  Total: {n_fixed} fixed, {n_free} free out of {N*N}")
    print(f"  Determination: {pct:.1f}%")
    print(f"  Scan time: {total_elapsed:.1f}s")

    # Classify free cells
    tester_free = [(i, j) for i, j in free_cells if i in TESTER_INDICES]
    structural_free = [(i, j) for i, j in free_cells if i not in TESTER_INDICES]
    absorber_fixed = [(i, j) for i, j in fixed_cells if i in (0, 1)]

    print(f"\n  Breakdown:")
    print(f"    Absorber rows (0, 1):  {len(absorber_fixed)} fixed")
    print(f"    Tester free cells:     {len(tester_free)}")
    print(f"    Structural free cells: {len(structural_free)}")

    if quick:
        print("\n  (--quick mode: skipping value enumeration)")
        return

    # Step 3: Value enumeration for free cells
    print(f"\n{'='*70}")
    print(f"Step 3: Value enumeration for {n_free} free cells")
    print(f"{'='*70}\n")

    tester_results = []
    structural_results = []
    t_enum = time.time()

    for idx, (i, j) in enumerate(free_cells):
        sat_vals = []
        for v in range(N):
            s.push()
            s.add(dot[i][j] == v)
            if s.check() == sat:
                sat_vals.append(v)
            s.pop()

        is_tester = i in TESTER_INDICES
        category = "TESTER" if is_tester else "STRUCT"
        name = NAMES.get(i, str(i))
        print(f"  ({i:2d},{j:2d}) [{name:>4s}] {category}: "
              f"{len(sat_vals)} values {sat_vals}", flush=True)

        if is_tester:
            tester_results.append((i, j, sat_vals))
        else:
            structural_results.append((i, j, sat_vals))

    enum_elapsed = time.time() - t_enum
    print(f"\n  Enumeration time: {enum_elapsed:.1f}s")

    # Step 4: Summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"\n  N=16: {n_fixed}/{N*N} fixed ({pct:.1f}% determination)")
    print(f"  Tester free:     {len(tester_results)} cells")
    print(f"  Structural free: {len(structural_results)} cells")

    if tester_results:
        # Check if all tester free cells are binary {0,1}
        all_binary = all(set(v) <= {0, 1} for _, _, v in tester_results)
        print(f"  Tester cells all binary: {all_binary}")
        if all_binary:
            print(f"  → Actuality irreducibility confirmed at N=16")

    if structural_results:
        print(f"\n  Structural free cells:")
        for i, j, vals in structural_results:
            name = NAMES.get(i, str(i))
            print(f"    ({i:2d},{j:2d}) [{name:>4s}]: {len(vals)} values")

    # Comparison
    print(f"\n  Scale comparison:")
    print(f"    N=8:  18/64 fixed   (28.1%)")
    print(f"    N=12: 27/144 fixed  (18.8%)")
    print(f"    N=16: {n_fixed}/{N*N} fixed  ({pct:.1f}%)")


if __name__ == "__main__":
    quick = "--quick" in sys.argv
    run_analysis(quick=quick)

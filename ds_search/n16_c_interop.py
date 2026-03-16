#!/usr/bin/env python3
"""
SAT search for Ψ₁₆ᶜ — C-interop-optimized N=16 extension.

Extension elements (12-15):
  12: SEQ  — tester (boolean predicate)
  13: INC  — encoder (4-cycle on core: 2→3→4→5→2)
  14: INV  — encoder (involution on core: INV(x) = 7-x)
  15: DEC  — encoder (reverse 4-cycle on core: 2→5→4→3→2)

Cycle states are core elements {2,3,4,5}, which are contiguous indices.
This enables arithmetic C expressions instead of switch/lookup:
  INC(x) = ((x - 1) & 3) + 2    (modular increment on core)
  DEC(x) = ((x - 3) & 3) + 2    (modular decrement on core)
  INV(x) = 7 - x                 (reflection on core)

Design note: the original plan placed INC/INV as cycle states themselves
(5→11→14→13→5), but this caused a PA conflict: INC·INC = INC·13 = 5 (a
tester), then PA requires TABLE[5][13] = INC·5 = 11, but tester rows are
boolean. Using core as cycle states avoids this since INC/DEC/INV (13,14,15)
are not in their own cycles.

New supercompiler cancellation rules (5 total, up from 2):
  E·(Q·x) → x     (existing QE)
  Q·(E·x) → x     (existing EQ)
  INC·(DEC·x) → x  (on core, from cycle definitions)
  DEC·(INC·x) → x  (on core, from cycle definitions)
  INV·(INV·x) → x  (full involution, explicit constraint)

Usage:
  uv run python -m ds_search.n16_c_interop
  uv run python -m ds_search.n16_c_interop --freedom   # cell-by-cell analysis
"""

import time
import sys
from z3 import Solver, Int, If, And, Or, Not, sat

from ds_search.axiom_explorer import (
    encode_level, extract_table, classify_elements,
    ite_lookup, col_ite_lookup, row_is_boolean,
)


# ═══════════════════════════════════════════════════════════════════════
# Ψ₁₆ᶜ element assignments
# ═══════════════════════════════════════════════════════════════════════

N = 16

CORE_LO, CORE_HI = 2, 6
Q_IDX, E_IDX = 6, 7

T_IDX = 3    # τ (tester / branch selector)
F_IDX = 2    # f (branch-if)
G_IDX = 4    # g (inert / branch-else)
R_IDX = 8    # ρ (branch element)
H_IDX = 9    # η (compose element)
Y_IDX = 10   # Y-combinator

# Extension elements
SEQ_IDX = 12   # tester (boolean predicate)
INC_IDX = 13   # encoder (4-cycle on core)
INV_IDX = 14   # encoder (involution: 7-x on core)
DEC_IDX = 15   # encoder (reverse 4-cycle on core)

# Cycle states are core elements: f(2), τ(3), g(4), 5
CYCLE_STATES = [2, 3, 4, 5]

TESTER_INDICES = {3, 5, 12}
INERT_INDICES = {4}
ENCODER_INDICES = {2, 6, 7, 8, 9, 10, 11, 13, 14, 15}

NAMES = {
    0: "⊤", 1: "⊥", 2: "f", 3: "τ", 4: "g", 5: "5",
    6: "Q", 7: "E", 8: "ρ", 9: "η", 10: "Y", 11: "11",
    12: "SEQ", 13: "INC", 14: "INV", 15: "DEC",
}


# ═══════════════════════════════════════════════════════════════════════
# Axiom encoding helpers (same as n16_freedom.py)
# ═══════════════════════════════════════════════════════════════════════

def add_kleene_c(s, dot, N):
    """Kleene: only testers produce boolean output on non-absorbers."""
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
# Build the Ψ₁₆ᶜ solver
# ═══════════════════════════════════════════════════════════════════════

def build_solver():
    """Full Ψ₁₆ᶜ axiom set at N=16."""
    print("  Building solver...", flush=True)
    t0 = time.time()

    s, dot = encode_level(8, N, timeout_seconds=600)

    # ── Base axioms (same as Ψ₁₆ᶠ) ──────────────────────────────────
    add_kleene_c(s, dot, N)
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

    # ── Role constraints ─────────────────────────────────────────────
    # Testers: rows 3, 5, 12 are all-boolean
    for t in TESTER_INDICES:
        for j in range(N):
            s.add(Or(dot[t][j] == 0, dot[t][j] == 1))

    # Inert: element 4
    s.add(is_inert_z3(dot, G_IDX, N))

    # Encoders
    for e in ENCODER_INDICES:
        enc_pairs = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                enc_pairs.append(And(
                    dot[e][j1] != 0, dot[e][j1] != 1,
                    dot[e][j2] != 0, dot[e][j2] != 1,
                    dot[e][j1] != dot[e][j2]))
        s.add(Or(enc_pairs))

    # ── Extension constraints (Ψ₁₆ᶜ-specific) ──────────────────────

    # INC 4-cycle on core: 2→3→4→5→2
    # C arithmetic: ((x - 1) & 3) + 2
    s.add(dot[INC_IDX][2] == 3)
    s.add(dot[INC_IDX][3] == 4)
    s.add(dot[INC_IDX][4] == 5)
    s.add(dot[INC_IDX][5] == 2)

    # DEC reverse 4-cycle on core: 2→5→4→3→2
    # C arithmetic: ((x - 3) & 3) + 2
    s.add(dot[DEC_IDX][2] == 5)
    s.add(dot[DEC_IDX][3] == 2)
    s.add(dot[DEC_IDX][4] == 3)
    s.add(dot[DEC_IDX][5] == 4)

    # INV on core: INV(x) = 7-x
    # INV·2=5, INV·3=4, INV·4=3, INV·5=2
    for x in range(CORE_LO, CORE_HI):
        s.add(dot[INV_IDX][x] == 7 - x)

    # INV involution on all: INV·(INV·x) = x for all x
    for x in range(N):
        inv_x = dot[INV_IDX][x]
        inv_inv_x = col_ite_lookup(dot, INV_IDX, inv_x, N)
        s.add(inv_inv_x == x)

    # No non-absorber idempotents: x·x ≠ x for x ≥ 2
    # Preserves recovery algorithm compatibility (Phase 1: only absorbers are idempotent)
    for x in range(2, N):
        s.add(dot[x][x] != x)

    elapsed = time.time() - t0
    print(f"  Solver built ({elapsed:.1f}s)", flush=True)
    return s, dot


# ═══════════════════════════════════════════════════════════════════════
# Verification
# ═══════════════════════════════════════════════════════════════════════

def verify_table(table):
    """Verify algebraic properties of the extracted table."""
    print("\n" + "=" * 70)
    print("VERIFICATION")
    print("=" * 70)

    ok = True

    # INV on core: INV(x) = 7-x
    print("\n  INV on core (7-x):")
    for x in range(CORE_LO, CORE_HI):
        expected = 7 - x
        actual = table[INV_IDX][x]
        status = "OK" if actual == expected else "FAIL"
        if actual != expected:
            ok = False
        print(f"    INV·{x} = {actual} (expected {expected}) {status}")

    # INV involution
    print("\n  INV involution (INV·INV·x = x):")
    inv_ok = True
    for x in range(N):
        inv_x = table[INV_IDX][x]
        inv_inv_x = table[INV_IDX][inv_x]
        if inv_inv_x != x:
            print(f"    FAIL: INV·INV·{x} = {inv_inv_x} ≠ {x}")
            inv_ok = False
            ok = False
    if inv_ok:
        print("    All 16 elements: OK")

    # INC 4-cycle on core
    print("\n  INC 4-cycle on core (2→3→4→5→2):")
    inc_ok = True
    for x in range(CORE_LO, CORE_HI):
        expected = ((x - 1) % 4) + 2
        actual = table[INC_IDX][x]
        if actual != expected:
            print(f"    FAIL: INC·{x} = {actual} ≠ {expected}")
            inc_ok = False
            ok = False
    if inc_ok:
        print("    OK (arithmetic: ((x-1)&3)+2)")

    # DEC reverse cycle on core
    print("\n  DEC reverse on core (2→5→4→3→2):")
    dec_ok = True
    for x in range(CORE_LO, CORE_HI):
        expected = ((x - 3) % 4) + 2
        actual = table[DEC_IDX][x]
        if actual != expected:
            print(f"    FAIL: DEC·{x} = {actual} ≠ {expected}")
            dec_ok = False
            ok = False
    if dec_ok:
        print("    OK (arithmetic: ((x-3)&3)+2)")

    # INC·DEC and DEC·INC cancellation on core
    print("\n  INC·DEC / DEC·INC cancellation on core:")
    cancel_ok = True
    for x in range(CORE_LO, CORE_HI):
        dec_x = table[DEC_IDX][x]
        inc_dec_x = table[INC_IDX][dec_x]
        if inc_dec_x != x:
            print(f"    FAIL: INC·(DEC·{x}) = {inc_dec_x} ≠ {x}")
            cancel_ok = False
            ok = False
        inc_x = table[INC_IDX][x]
        dec_inc_x = table[DEC_IDX][inc_x]
        if dec_inc_x != x:
            print(f"    FAIL: DEC·(INC·{x}) = {dec_inc_x} ≠ {x}")
            cancel_ok = False
            ok = False
    if cancel_ok:
        print("    All cancellations OK")

    # QE cancellation on core
    print("\n  QE cancellation on core [2,6):")
    qe_ok = True
    for x in range(CORE_LO, CORE_HI):
        qx = table[Q_IDX][x]
        eqx = table[E_IDX][qx]
        if eqx != x:
            print(f"    FAIL: E·(Q·{x}) = E·{qx} = {eqx} ≠ {x}")
            qe_ok = False
            ok = False
        ex = table[E_IDX][x]
        qex = table[Q_IDX][ex]
        if qex != x:
            print(f"    FAIL: Q·(E·{x}) = Q·{ex} = {qex} ≠ {x}")
            qe_ok = False
            ok = False
    if qe_ok:
        print("    All QE/EQ cancellations OK")

    # Producibility
    print("\n  Producibility (every element in image):")
    produced = set()
    for i in range(N):
        for j in range(N):
            produced.add(table[i][j])
    missing = set(range(N)) - produced
    if missing:
        print(f"    NOT fully producible: missing {missing}")
    else:
        print("    All 16 elements producible: OK")

    # Row roles
    print("\n  Row roles:")
    for i in range(N):
        row = table[i]
        is_abs = all(v == i for v in row)
        is_tst = all(v in (0, 1) for v in row) and not is_abs
        non_bool = [v for v in row if v not in (0, 1)]
        is_enc = len(set(non_bool)) >= 2
        role = "absorber" if is_abs else "tester" if is_tst else "encoder" if is_enc else "inert"
        name = NAMES.get(i, str(i))
        expected = ("absorber" if i < 2 else
                    "tester" if i in TESTER_INDICES else
                    "inert" if i in INERT_INDICES else "encoder")
        status = "OK" if role == expected else f"FAIL (expected {expected})"
        print(f"    {i:2d} ({name:>4s}): {role:8s} {status}")
        if role != expected:
            ok = False

    # Power-associativity spot check
    print("\n  Power-associativity spot check:")
    pa_ok = True
    for x in range(N):
        xx = table[x][x]
        lhs = table[xx][x]
        rhs = table[x][xx]
        if lhs != rhs:
            print(f"    FAIL: ({x}·{x})·{x} = {lhs} ≠ {x}·({x}·{x}) = {rhs}")
            pa_ok = False
            ok = False
    if pa_ok:
        print("    All 16 elements: OK")

    print(f"\n  Overall: {'ALL CHECKS PASSED' if ok else 'SOME CHECKS FAILED'}")
    return ok


def print_table(table):
    """Print the Cayley table."""
    print("\n  Cayley table (Ψ₁₆ᶜ):")
    print("      ", end="")
    for j in range(N):
        print(f"{j:3d}", end="")
    print()
    for i in range(N):
        name = NAMES.get(i, str(i))
        print(f"  {i:2d} ({name:>4s})", end=" ")
        for j in range(N):
            print(f"{table[i][j]:3d}", end="")
        print()


def print_python_table(table):
    """Print table as Python list-of-lists for psi_star_c.py."""
    print("\n  Python TABLE:")
    print("TABLE = [")
    for i in range(N):
        row = ",".join(f"{table[i][j]:2d}" for j in range(N))
        print(f"    [{row}],")
    print("]")


def print_c_table(table):
    """Print table as C array for psi_runtime_c.h."""
    print("\n  C psi_cayley:")
    print("static const uint8_t psi_cayley[16][16] = {")
    for i in range(N):
        row = ",".join(f"{table[i][j]:2d}" for j in range(N))
        print(f"    {{{row}}},")
    print("};")


# ═══════════════════════════════════════════════════════════════════════
# Logic gate check (monitor question)
# ═══════════════════════════════════════════════════════════════════════

def check_logic_gates(table):
    """Check if the table admits 1-bit logic gates (AND, OR, XOR)."""
    print("\n" + "=" * 70)
    print("LOGIC GATE CHECK")
    print("=" * 70)

    print("\n  Rows restricted to absorber columns {0, 1}:")
    for i in range(N):
        v0 = table[i][0]
        v1 = table[i][1]
        name = NAMES.get(i, str(i))
        label = ""
        if v0 == 0 and v1 == 0:
            label = " (constant ⊤)"
        elif v0 == 1 and v1 == 1:
            label = " (constant ⊥)"
        elif v0 == 0 and v1 == 1:
            label = " (identity)"
        elif v0 == 1 and v1 == 0:
            label = " (NOT)"
        print(f"    {i:2d} ({name:>4s}): [{v0}, {v1}]{label}")

    # For 2-input gates, check a·(b·x) patterns on {0,1}
    print("\n  2-input gate search: a·(b·x) for x ∈ {0,1}")
    gates_found = {}
    for a in range(N):
        for b in range(N):
            r0 = table[a][table[b][0]]  # a·(b·⊤)
            r1 = table[a][table[b][1]]  # a·(b·⊥)
            if r0 in (0, 1) and r1 in (0, 1):
                pattern = (r0, r1)
                key = f"({r0},{r1})"
                if key not in gates_found:
                    gates_found[key] = []
                gates_found[key].append((a, b))

    gate_labels = {
        "(0,0)": "const-⊤", "(0,1)": "identity", "(1,0)": "NOT", "(1,1)": "const-⊥"
    }
    for pattern, examples in sorted(gates_found.items()):
        label = gate_labels.get(pattern, "")
        print(f"    {pattern} {label:10s}: {len(examples)} implementations "
              f"(first: a={examples[0][0]}, b={examples[0][1]})")


# ═══════════════════════════════════════════════════════════════════════
# Cell-by-cell freedom analysis
# ═══════════════════════════════════════════════════════════════════════

def run_freedom_analysis(s, dot, ref):
    """Cell-by-cell freedom analysis."""
    print(f"\n{'='*70}")
    print(f"CELL-BY-CELL FREEDOM ANALYSIS — Ψ₁₆ᶜ (N=16)")
    print(f"{'='*70}")

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

    tester_free = [(i, j) for i, j in free_cells if i in TESTER_INDICES]
    structural_free = [(i, j) for i, j in free_cells if i not in TESTER_INDICES]

    print(f"\n  Breakdown:")
    print(f"    Tester free cells:     {len(tester_free)}")
    print(f"    Structural free cells: {len(structural_free)}")

    return n_fixed, n_free


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def run():
    do_freedom = "--freedom" in sys.argv

    print("=" * 70)
    print("Ψ₁₆ᶜ SAT SEARCH — C-Interop-Optimized Extension")
    print("=" * 70)
    print()
    print("  Elements 0-11: same as Ψ₁₆ᶠ")
    print("  12: SEQ (tester)")
    print("  13: INC (encoder, 4-cycle on core: 2→3→4→5→2)")
    print("  14: INV (encoder, involution: INV(x) = 7-x on core)")
    print("  15: DEC (encoder, reverse 4-cycle: 2→5→4→3→2)")
    print()
    print("  C arithmetic (single-expression, no switch):")
    print("    INC(x) = ((x - 1) & 3) + 2")
    print("    DEC(x) = ((x - 3) & 3) + 2")
    print("    INV(x) = 7 - x")
    print()

    s, dot = build_solver()

    # Find a model
    print("\n  Checking SAT...", flush=True)
    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0

    if result != sat:
        print(f"  RESULT: {result} ({elapsed:.1f}s)")
        return

    print(f"  SAT ({elapsed:.1f}s)")

    # Extract table
    table = extract_table(s.model(), dot, N)
    print_table(table)
    print_python_table(table)
    print_c_table(table)

    # Verify
    verify_table(table)

    # Logic gates
    check_logic_gates(table)

    # Freedom analysis
    if do_freedom:
        run_freedom_analysis(s, dot, table)
    else:
        print("\n  (Use --freedom for cell-by-cell analysis)")


if __name__ == "__main__":
    run()

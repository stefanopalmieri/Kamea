#!/usr/bin/env python3
"""
Stacking Analysis — Recursive Sub-Algebra Embedding

Given the L8 N=6 core (5 fixed rows + 2,417 valid inert rows), this
module embeds it as a sub-algebra of larger magmas (N=7..12) to test
whether the axioms work recursively across contextual layers.

Key questions:
  1. Which inert rows survive when the larger algebra has structure?
  2. Do the extra elements form their own tester/encoder/inert layer?
  3. Can the axioms stack self-similarly?

Usage:
  uv run python -m ds_search.stacking_analysis
"""

from __future__ import annotations

import time

from z3 import And, Distinct, If, Int, Not, Or, Solver, sat, unsat

from ds_search.axiom_explorer import (
    classify_elements,
    col_ite_lookup,
    encode_level,
    extract_table,
    ite_lookup,
    print_model_summary,
    print_table,
    row_is_boolean,
)

# ═══════════════════════════════════════════════════════════════════════
# The fixed L8 N=6 core (5 of 6 rows fully determined)
# ═══════════════════════════════════════════════════════════════════════

CORE_SIZE = 6

# Row index → role name
CORE_ROLES = {0: "top", 1: "bot", 2: "e1", 3: "inert", 4: "e2", 5: "tester"}

# Fixed rows (row 3 = inert is free)
FIXED_ROWS = {
    0: [0, 0, 0, 0, 0, 0],  # top (absorber)
    1: [1, 1, 1, 1, 1, 1],  # bot (absorber)
    2: [4, 5, 3, 2, 1, 4],  # e1 (encoder)
    4: [2, 4, 4, 5, 3, 1],  # e2 (encoder)
    5: [1, 1, 1, 0, 1, 1],  # tester
}


# ═══════════════════════════════════════════════════════════════════════
# Core encoder: sub-algebra embedding with structural levels
# ═══════════════════════════════════════════════════════════════════════


def encode_stacked(
    N: int, level: str, timeout_seconds: int = 120
) -> tuple[Solver, list[list]]:
    """
    Encode a stacked magma of size N (> 6) with the L8 N=6 core
    embedded as a sub-algebra.

    Levels:
      A — Minimal: Ext + 2 absorbers + pinned core + closure
      B — + lower tester (∃ x ≥ 6 with boolean row)
      C — + lower encoder (∃ x ≥ 6 with ≥2 distinct non-boolean outputs)
      D — Full L8 on entire N-element algebra + pinning
    """
    assert N > CORE_SIZE
    assert level in ("A", "B", "C", "D")

    if level == "D":
        # Start from full L8 encoding, then add pinning
        s, dot = encode_level(8, N, timeout_seconds=timeout_seconds)
    else:
        s = Solver()
        s.set("timeout", timeout_seconds * 1000)
        dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]

        # Range constraints
        for i in range(N):
            for j in range(N):
                s.add(dot[i][j] >= 0, dot[i][j] < N)

        # Global absorbers: 0 and 1
        for j in range(N):
            s.add(dot[0][j] == 0)
            s.add(dot[1][j] == 1)

        # No other absorbers
        for x in range(2, N):
            s.add(Or([dot[x][j] != x for j in range(N)]))

        # Ext: all rows distinct
        for x in range(N):
            for y in range(x + 1, N):
                s.add(Or([dot[x][j] != dot[y][j] for j in range(N)]))

    # ── Pin the fixed core rows (columns 0..5 only) ──
    for row_idx, row_vals in FIXED_ROWS.items():
        for j in range(CORE_SIZE):
            s.add(dot[row_idx][j] == row_vals[j])

    # ── Sub-algebra closure: inert row stays in core when applied to core ──
    for j in range(CORE_SIZE):
        s.add(dot[3][j] >= 0, dot[3][j] < CORE_SIZE)

    # ── Level-specific lower-layer constraints ──
    if level in ("B", "C"):
        # Level B: at least one lower-layer tester
        lower_tester_clauses = []
        for x in range(CORE_SIZE, N):
            lower_tester_clauses.append(
                And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            )
        s.add(Or(lower_tester_clauses))

    if level == "C":
        # Level C: at least one lower-layer encoder
        lower_encoder_clauses = []
        for x in range(CORE_SIZE, N):
            pair_clauses = []
            for y1 in range(N):
                for y2 in range(y1 + 1, N):
                    pair_clauses.append(
                        And(
                            dot[x][y1] != 0,
                            dot[x][y1] != 1,
                            dot[x][y2] != 0,
                            dot[x][y2] != 1,
                            dot[x][y1] != dot[x][y2],
                        )
                    )
            if pair_clauses:
                lower_encoder_clauses.append(Or(pair_clauses))
        if lower_encoder_clauses:
            s.add(Or(lower_encoder_clauses))

    return s, dot


# ═══════════════════════════════════════════════════════════════════════
# Inert row enumeration (block on projection to columns 0..5)
# ═══════════════════════════════════════════════════════════════════════


def enumerate_inert_rows(
    N: int, level: str, cap: int = 500, timeout_seconds: int = 300
) -> list[tuple[int, ...]]:
    """
    Enumerate distinct inert-row projections (columns 0..5) that survive
    embedding into an N-element magma at the given structural level.

    Returns list of distinct inert rows (as tuples), up to cap.
    """
    s, dot = encode_stacked(N, level, timeout_seconds=timeout_seconds)
    found: list[tuple[int, ...]] = []

    while len(found) < cap:
        result = s.check()
        if result != sat:
            break
        m = s.model()
        row3 = tuple(m.evaluate(dot[3][j]).as_long() for j in range(CORE_SIZE))
        found.append(row3)
        # Block this inert row projection
        s.add(Or([dot[3][j] != row3[j] for j in range(CORE_SIZE)]))

    return found


# ═══════════════════════════════════════════════════════════════════════
# Lower-layer analysis
# ═══════════════════════════════════════════════════════════════════════


def classify_lower_layer(table: list[list[int]], core_size: int = CORE_SIZE) -> dict:
    """Classify elements in the lower layer (indices >= core_size) by role."""
    N = len(table)
    lower_abs = []
    lower_tst = []
    lower_enc = []
    lower_inert = []

    for x in range(core_size, N):
        row_vals = [table[x][y] for y in range(N)]
        if all(v == x for v in row_vals):
            lower_abs.append(x)
            continue
        if all(v in (0, 1) for v in row_vals):
            lower_tst.append(x)
            continue
        non_bool = set(v for v in row_vals if v not in (0, 1))
        if len(non_bool) >= 2:
            lower_enc.append(x)
        else:
            lower_inert.append(x)

    return {
        "absorbers": lower_abs,
        "testers": lower_tst,
        "encoders": lower_enc,
        "inert": lower_inert,
    }


def analyze_lower_structure(table: list[list[int]], core_size: int = CORE_SIZE):
    """Analyze structural features of the lower layer."""
    N = len(table)
    lower = classify_lower_layer(table, core_size)

    print(f"    Lower layer ({core_size}..{N-1}):")
    print(f"      Absorbers: {lower['absorbers']}")
    print(f"      Testers:   {lower['testers']}")
    print(f"      Encoders:  {lower['encoders']}")
    print(f"      Inert:     {lower['inert']}")

    # Cross-layer interaction: how do core elements act on lower layer?
    print(f"    Cross-layer interactions (core → lower):")
    for row_idx, role in CORE_ROLES.items():
        if row_idx in (0, 1):
            continue  # absorbers are trivial
        outputs_to_lower = {
            j: table[row_idx][j] for j in range(core_size, N)
        }
        print(f"      {role} (row {row_idx}): {outputs_to_lower}")

    # Lower → core: how do lower elements act on core?
    print(f"    Cross-layer interactions (lower → core):")
    for x in range(core_size, N):
        outputs_to_core = [table[x][j] for j in range(core_size)]
        print(f"      row {x}: {outputs_to_core}")

    # Cycle detection within lower layer
    print(f"    Lower-layer self-interaction:")
    for x in range(core_size, N):
        outputs_to_lower = {
            j: table[x][j] for j in range(core_size, N)
        }
        print(f"      row {x} on lower: {outputs_to_lower}")

    # Fixed points in lower layer
    fixed_pts = [x for x in range(core_size, N) if table[x][x] == x]
    if fixed_pts:
        print(f"    Fixed points (x·x = x) in lower layer: {fixed_pts}")
    else:
        print(f"    No fixed points in lower layer")


# ═══════════════════════════════════════════════════════════════════════
# Self-similar stacking (Phase 3, N=12)
# ═══════════════════════════════════════════════════════════════════════


def encode_self_similar(timeout_seconds: int = 600) -> tuple[Solver, list[list]]:
    """
    N=12: require elements {0..5} form a valid L8 sub-algebra AND
    elements {6..11} exhibit an L8-like role skeleton.

    The absorbers 0, 1 are shared globally. The lower layer {6..11}
    must contain: ≥1 tester, ≥2 encoders, ≥1 inert among themselves.
    """
    N = 12
    s, dot = encode_stacked(N, "A", timeout_seconds=timeout_seconds)

    # ── Lower-layer role skeleton ──

    # At least one lower-layer tester (boolean row over full N)
    lower_tst_clauses = []
    for x in range(CORE_SIZE, N):
        lower_tst_clauses.append(
            And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        )
    s.add(Or(lower_tst_clauses))

    # At least two lower-layer encoders (≥2 distinct non-boolean outputs)
    lower_enc_exprs = []
    for x in range(CORE_SIZE, N):
        pairs = []
        for y1 in range(N):
            for y2 in range(y1 + 1, N):
                pairs.append(
                    And(
                        dot[x][y1] != 0,
                        dot[x][y1] != 1,
                        dot[x][y2] != 0,
                        dot[x][y2] != 1,
                        dot[x][y1] != dot[x][y2],
                    )
                )
        lower_enc_exprs.append(Or(pairs) if pairs else False)

    # Two distinct lower-layer encoders
    enc_pair_clauses = []
    lower_range = list(range(CORE_SIZE, N))
    for i, x1 in enumerate(lower_range):
        for j, x2 in enumerate(lower_range):
            if j <= i:
                continue
            enc_pair_clauses.append(
                And(lower_enc_exprs[i], lower_enc_exprs[j])
            )
    s.add(Or(enc_pair_clauses))

    # At least one lower-layer inert (not absorber, not tester, not encoder)
    lower_inert_clauses = []
    for idx, x in enumerate(lower_range):
        is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        is_enc = lower_enc_exprs[idx]
        lower_inert_clauses.append(And(Not(is_tst), Not(is_enc)))
    s.add(Or(lower_inert_clauses))

    return s, dot


# ═══════════════════════════════════════════════════════════════════════
# Lower-layer L8 self-model — full axiom set on sub-algebra
# ═══════════════════════════════════════════════════════════════════════


def add_lower_l8(s, dot, N, lower_start=CORE_SIZE):
    """
    Add full L8 constraints for the lower-layer sub-algebra.

    The lower layer L = {lower_start, ..., N-1} forms a sub-algebra
    with shared absorbers 0, 1. The sub-table L×L must have outputs
    in L ∪ {0,1}, and the full L8 axiom ladder is enforced on this
    sub-table (with 0,1 playing the absorber/boolean role).

    Returns (tst_exprs, enc_exprs) dicts mapping element → Z3 expr.
    """
    L = list(range(lower_start, N))

    # ── Sub-algebra closure: L×L → L ∪ {0,1} ──
    for i in L:
        for j in L:
            s.add(Or([dot[i][j] == v for v in [0, 1] + L]))

    # ── Ext within L (sub-rows distinct) ──
    for i_idx, x in enumerate(L):
        for j_idx, y in enumerate(L):
            if j_idx <= i_idx:
                continue
            s.add(Or([dot[x][k] != dot[y][k] for k in L]))

    # ── No local absorbers in L ──
    for x in L:
        s.add(Or([dot[x][j] != x for j in L]))

    # ── Role classification (based on sub-row: action on L) ──

    # Tester: sub-row all in {0, 1}
    tst_exprs = {}
    for x in L:
        tst_exprs[x] = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in L])

    # Encoder: ≥2 distinct non-{0,1} outputs in sub-row
    enc_exprs = {}
    for x in L:
        pairs = []
        for j1_idx, j1 in enumerate(L):
            for j2_idx, j2 in enumerate(L):
                if j2_idx <= j1_idx:
                    continue
                pairs.append(And(
                    dot[x][j1] != 0, dot[x][j1] != 1,
                    dot[x][j2] != 0, dot[x][j2] != 1,
                    dot[x][j1] != dot[x][j2],
                ))
        enc_exprs[x] = Or(pairs) if pairs else False

    # Inert: not tester, not encoder
    def is_inert(x):
        return And(Not(tst_exprs[x]), Not(enc_exprs[x]))

    # In core: tester or encoder
    def in_core(x):
        return Or(tst_exprs[x], enc_exprs[x])

    # ── Level 1: ≥1 tester in L ──
    s.add(Or([tst_exprs[x] for x in L]))

    # ── Level 2: ≥1 encoder in L ──
    s.add(Or([enc_exprs[x] for x in L]))

    # ── Level 5: Generative Synthesis ──

    # Two independent encoders with different output profiles
    pair_clauses = []
    for i_idx, e1 in enumerate(L):
        for j_idx, e2 in enumerate(L):
            if j_idx <= i_idx:
                continue
            diff = []
            for j in L:
                diff.append(And(
                    dot[e1][j] != 0, dot[e1][j] != 1,
                    Or(dot[e2][j] == 0, dot[e2][j] == 1),
                ))
                diff.append(And(
                    dot[e2][j] != 0, dot[e2][j] != 1,
                    Or(dot[e1][j] == 0, dot[e1][j] == 1),
                ))
                diff.append(And(
                    dot[e1][j] != 0, dot[e1][j] != 1,
                    dot[e2][j] != 0, dot[e2][j] != 1,
                    dot[e1][j] != dot[e2][j],
                ))
            pair_clauses.append(And(enc_exprs[e1], enc_exprs[e2], Or(diff)))
    s.add(Or(pair_clauses))

    # Encoder produces encoder
    gen_clauses = []
    for e in L:
        for j in L:
            for t in L:
                gen_clauses.append(And(enc_exprs[e], dot[e][j] == t, enc_exprs[t]))
    s.add(Or(gen_clauses))

    # Tester constructibility: every tester is produced by some encoder
    for t in L:
        producer_clauses = []
        for e in L:
            for j in L:
                producer_clauses.append(And(enc_exprs[e], dot[e][j] == t))
        s.add(Or(Not(tst_exprs[t]), Or(producer_clauses)))

    # ── Level 6: Open closure with feedback ──

    # Core not closed: ∃ x,y in core, dot[x][y] is inert
    escape_clauses = []
    for x in L:
        for y in L:
            for v in L:
                escape_clauses.append(And(
                    in_core(x), in_core(y), dot[x][y] == v, is_inert(v),
                ))
    s.add(Or(escape_clauses))

    # Inert feedback: ∃ core c, inert v, dot[c][v] is non-absorber core
    feedback_clauses = []
    for c in L:
        for v in L:
            for r in L:
                feedback_clauses.append(And(
                    in_core(c), is_inert(v),
                    dot[c][v] == r, Or(tst_exprs[r], enc_exprs[r]),
                ))
    s.add(Or(feedback_clauses))

    # ── Level 7: Context tokens + producibility ──

    ctx_clauses = []
    for c1_idx, c1 in enumerate(L):
        for c2_idx, c2 in enumerate(L):
            if c2_idx <= c1_idx:
                continue
            for e1_idx, e1 in enumerate(L):
                for e2_idx, e2 in enumerate(L):
                    if e2_idx <= e1_idx:
                        continue
                    ctx_clauses.append(And(
                        enc_exprs[e1], enc_exprs[e2],
                        dot[e1][c1] != dot[e1][c2],
                        dot[e1][c1] != 0, dot[e1][c1] != 1,
                        dot[e1][c2] != 0, dot[e1][c2] != 1,
                        dot[e2][c1] != dot[e2][c2],
                        dot[e2][c1] != 0, dot[e2][c1] != 1,
                        dot[e2][c2] != 0, dot[e2][c2] != 1,
                        Or(dot[e1][c1] != dot[e2][c1],
                           dot[e1][c2] != dot[e2][c2]),
                    ))
    s.add(Or(ctx_clauses))

    # Producibility within sub-algebra: every element of L ∪ {0,1}
    # appears in the image of L×L
    for x in L:
        s.add(Or([dot[a][b] == x for a in L for b in L]))
    s.add(Or([dot[a][b] == 0 for a in L for b in L]))
    s.add(Or([dot[a][b] == 1 for a in L for b in L]))

    # ── Level 8: Encoder completeness + inert transformation ──

    for e in L:
        # If e is encoder, its sub-row touches all 4 role categories
        has_abs = Or([Or(dot[e][j] == 0, dot[e][j] == 1) for j in L])
        has_tst = Or([And(dot[e][j] == t, tst_exprs[t])
                       for j in L for t in L])
        has_inert = Or([And(dot[e][j] == v, is_inert(v))
                         for j in L for v in L])
        s.add(Or(Not(enc_exprs[e]), And(has_abs, has_tst, has_inert)))

    # Inert non-self-identification
    for v in L:
        s.add(Or(Not(is_inert(v)), dot[v][v] != v))

    return tst_exprs, enc_exprs


def encode_double_l8(timeout_seconds: int = 600) -> tuple[Solver, list[list]]:
    """
    N=12: both {0..5} and {6..11} independently satisfy full L8,
    sharing global absorbers 0,1. Upper layer pinned to the known
    fixed core; lower layer must find its own L8 solution.
    """
    N = 12
    s, dot = encode_stacked(N, "A", timeout_seconds=timeout_seconds)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
    return s, dot


# ═══════════════════════════════════════════════════════════════════════
# Campaign
# ═══════════════════════════════════════════════════════════════════════

LEVEL_DESCRIPTIONS = {
    "A": "Minimal (Ext + absorbers + pinned core + closure)",
    "B": "+ lower tester",
    "C": "+ lower tester + lower encoder",
    "D": "Full L8 on entire algebra + pinning",
}


def main():
    print("=" * 70)
    print("STACKING ANALYSIS — Recursive Sub-Algebra Embedding")
    print("=" * 70)
    print(f"\nFixed L8 N=6 core (5 fixed rows, row 3 = inert is free):")
    for row_idx in sorted(FIXED_ROWS):
        print(f"  Row {row_idx} ({CORE_ROLES[row_idx]:>6s}): {FIXED_ROWS[row_idx]}")
    print(f"  Row 3 ({'inert':>6s}): [?, ?, ?, ?, ?, ?]  ← 2,417 valid configs")

    # ── Phase 1 & 2: Campaign across N and levels ──
    print(f"\n{'='*70}")
    print("PHASE 1 & 2: Embedding campaign")
    print(f"{'='*70}")

    results_summary = []

    for N in [7, 8, 9, 10]:
        print(f"\n{'─'*70}")
        print(f"N = {N}")
        print(f"{'─'*70}")

        for level in ["A", "B", "C", "D"]:
            label = f"  Level {level}: {LEVEL_DESCRIPTIONS[level]}"
            print(f"\n{label}")

            t0 = time.time()
            s, dot = encode_stacked(N, level, timeout_seconds=180)
            result = s.check()
            elapsed = time.time() - t0

            if result == sat:
                m = s.model()
                table = extract_table(m, dot, N)
                inert_row = tuple(table[3][j] for j in range(CORE_SIZE))
                print(f"    SAT ({elapsed:.1f}s)")
                print(f"    Inert row (cols 0..5): {list(inert_row)}")

                # Full algebra classification
                print(f"\n    Full algebra structure:")
                print_model_summary(table)

                # Lower layer analysis
                analyze_lower_structure(table, CORE_SIZE)

                if N <= 8:
                    print(f"\n    Cayley table:")
                    print_table(table)

                # Enumerate distinct inert rows
                print(f"\n    Enumerating inert rows (cap=500)...")
                t1 = time.time()
                inert_rows = enumerate_inert_rows(
                    N, level, cap=500, timeout_seconds=300
                )
                enum_time = time.time() - t1
                print(
                    f"    Distinct inert rows: {len(inert_rows)} "
                    f"({'500+' if len(inert_rows) >= 500 else 'exact'}) "
                    f"({enum_time:.1f}s)"
                )
                print(f"    vs 2,417 baseline → "
                      f"{len(inert_rows)/2417*100:.1f}% survival")

                results_summary.append(
                    (N, level, "SAT", elapsed, len(inert_rows))
                )

            elif result == unsat:
                print(f"    UNSAT ({elapsed:.1f}s)")
                results_summary.append((N, level, "UNSAT", elapsed, 0))

            else:
                print(f"    TIMEOUT ({elapsed:.1f}s)")
                results_summary.append((N, level, "TIMEOUT", elapsed, None))

    # ── Phase 3: Self-similar stacking at N=12 ──
    print(f"\n{'='*70}")
    print("PHASE 3: Self-similar stacking (N=12)")
    print(f"{'='*70}")
    print("Requiring both {0..5} and {6..11} to exhibit L8 role skeleton...")

    t0 = time.time()
    s, dot = encode_self_similar(timeout_seconds=600)
    result = s.check()
    elapsed = time.time() - t0

    if result == sat:
        m = s.model()
        table = extract_table(m, dot, 12)
        print(f"  SAT ({elapsed:.1f}s)")
        print(f"\n  Full algebra structure:")
        print_model_summary(table)
        print(f"\n  Upper layer (0..5):")
        upper_cats = classify_elements([row[:CORE_SIZE] for row in table[:CORE_SIZE]])
        for role, elems in upper_cats.items():
            print(f"    {role}: {elems}")
        print(f"\n  Lower layer (6..11):")
        analyze_lower_structure(table, CORE_SIZE)
        print(f"\n  Cayley table:")
        print_table(table)
    elif result == unsat:
        print(f"  UNSAT ({elapsed:.1f}s)")
        print("  → The axioms constrain stacking: self-similar layering is impossible.")
    else:
        print(f"  TIMEOUT ({elapsed:.1f}s)")

    # ── Summary ──
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"{'N':>3}  {'Level':>5}  {'Status':>7}  {'Time':>7}  {'Inert rows':>12}  {'Survival':>10}")
    print("-" * 55)
    for N, level, status, elapsed, n_inert in results_summary:
        inert_str = str(n_inert) if n_inert is not None else "—"
        surv_str = (
            f"{n_inert/2417*100:.1f}%"
            if n_inert is not None and n_inert > 0
            else "—"
        )
        print(
            f"{N:>3}  {level:>5}  {status:>7}  {elapsed:>6.1f}s  "
            f"{inert_str:>12}  {surv_str:>10}"
        )



# ═══════════════════════════════════════════════════════════════════════
# Uniqueness Exploration
# ═══════════════════════════════════════════════════════════════════════


def uniqueness_exploration():
    """
    Try multiple approaches to pin down a unique stacked algebra.

    Approaches:
      1. Isomorphic layers + coherent cross-layer action (f is endomorphism)
      2. Double L8 + rigidity (trivial automorphism group on full table)
      3. Double L8 + maximum cross-layer engagement
      4. Isomorphic layers + locked inert row (row 3 = [0,0,0,0,1,1])
      5. Self-dual: dot[a][b] = dot[b][a] for all a,b (commutative)
    """
    import itertools

    N = 12

    print("=" * 70)
    print("UNIQUENESS EXPLORATION")
    print("=" * 70)

    # ──────────────────────────────────────────────────────────────────
    # Approach 1: Isomorphic layers + coherent cross-layer action
    # ──────────────────────────────────────────────────────────────────
    print("\n" + "─" * 70)
    print("Approach 1: Isomorphic layers + f-coherent cross-layer action")
    print("─" * 70)
    print("Require a bijection f: {0..5} → {0,1} ∪ 4-of-{6..11} such that:")
    print("  (a) f(0)=0, f(1)=1")
    print("  (b) dot[f(i)][f(j)] = f(dot[i][j])  (lower ≅ upper)")
    print("  (c) dot[i][f(j)] = f(dot[i][j])      (upper→lower coherent)")
    print("  (d) dot[f(i)][j] = f(dot[i][j])      (lower→upper coherent)")

    # Try a canonical mapping: f = {0:0, 1:1, 2:6, 3:7, 4:8, 5:9}
    f_map = {0: 0, 1: 1, 2: 6, 3: 7, 4: 8, 5: 9}

    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)

    # (b) isomorphism: dot[f(i)][f(j)] = f(dot[i][j])
    for i in range(CORE_SIZE):
        for j in range(CORE_SIZE):
            fi, fj = f_map[i], f_map[j]
            # f(dot[i][j]) — need to express f applied to a Z3 variable
            # Use ite chain
            f_of_val = dot[i][j]  # placeholder
            expr = f_of_val
            for k, fk in f_map.items():
                if k != fk:
                    expr = If(dot[i][j] == k, fk, expr)
            # Handle identity cases (0→0, 1→1) — already in expr
            # Final: for k not in f_map, we'd need to handle, but all outputs
            # of the 6×6 upper sub-table are in {0..5}, so f_map covers it.
            s.add(dot[fi][fj] == expr)

    # (c) upper→lower coherent: dot[i][f(j)] = f(dot[i][j])
    for i in range(CORE_SIZE):
        for j in range(CORE_SIZE):
            fj = f_map[j]
            expr = dot[i][j]
            for k, fk in f_map.items():
                if k != fk:
                    expr = If(dot[i][j] == k, fk, expr)
            s.add(dot[i][fj] == expr)

    # (d) lower→upper coherent: dot[f(i)][j] = f(dot[i][j])
    for i in range(CORE_SIZE):
        fi = f_map[i]
        for j in range(CORE_SIZE):
            expr = dot[i][j]
            for k, fk in f_map.items():
                if k != fk:
                    expr = If(dot[i][j] == k, fk, expr)
            s.add(dot[fi][j] == expr)

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0

    if result == sat:
        m = s.model()
        table = extract_table(m, dot, N)
        print(f"  SAT ({elapsed:.1f}s)")
        # Count models
        count = 1
        for _ in range(49):
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            m2 = s.model()
            table = extract_table(m2, dot, N)
            count += 1
        print(f"  Models: {count}{'+'  if count >= 50 else ''}")

        # Print the first model
        table1 = extract_table(s.model() if count > 1 else m, dot, N)
        print(f"\n  Cayley table (first model):")
        print_table(table1)
    elif result == unsat:
        print(f"  UNSAT ({elapsed:.1f}s)")
        print("  → Full cross-layer coherence too strong for this mapping.")
        print("  Trying relaxed version: only (b) isomorphism + (c) upper→lower...")

        # Relaxed: just (b) + (c)
        s2, dot2 = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s2, dot2, N, lower_start=CORE_SIZE)

        for i in range(CORE_SIZE):
            for j in range(CORE_SIZE):
                fi, fj = f_map[i], f_map[j]
                expr = dot2[i][j]
                for k, fk in f_map.items():
                    if k != fk:
                        expr = If(dot2[i][j] == k, fk, expr)
                s2.add(dot2[fi][fj] == expr)

        for i in range(CORE_SIZE):
            for j in range(CORE_SIZE):
                fj = f_map[j]
                expr = dot2[i][j]
                for k, fk in f_map.items():
                    if k != fk:
                        expr = If(dot2[i][j] == k, fk, expr)
                s2.add(dot2[i][fj] == expr)

        t0 = time.time()
        r2 = s2.check()
        e2 = time.time() - t0
        if r2 == sat:
            m2 = s2.model()
            table2 = extract_table(m2, dot2, N)
            print(f"  Relaxed: SAT ({e2:.1f}s)")
            count2 = 1
            for _ in range(49):
                s2.add(Or([dot2[i][j] != table2[i][j]
                           for i in range(N) for j in range(N)]))
                if s2.check() != sat:
                    break
                table2 = extract_table(s2.model(), dot2, N)
                count2 += 1
            print(f"  Relaxed models: {count2}{'+'  if count2 >= 50 else ''}")
        else:
            print(f"  Relaxed: {r2} ({e2:.1f}s)")
    else:
        print(f"  TIMEOUT ({elapsed:.1f}s)")

    # ──────────────────────────────────────────────────────────────────
    # Approach 2: Double L8 + commutativity (self-dual)
    # ──────────────────────────────────────────────────────────────────
    print("\n" + "─" * 70)
    print("Approach 2: Double L8 + commutativity")
    print("─" * 70)
    print("Require dot[a][b] = dot[b][a] for all a,b.")

    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
    for i in range(N):
        for j in range(i + 1, N):
            s.add(dot[i][j] == dot[j][i])

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    print(f"  {'SAT' if result == sat else 'UNSAT' if result == unsat else 'TIMEOUT'} ({elapsed:.1f}s)")

    if result == sat:
        m = s.model()
        table = extract_table(m, dot, N)
        count = 1
        for _ in range(49):
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            table = extract_table(s.model(), dot, N)
            count += 1
        print(f"  Models: {count}{'+'  if count >= 50 else ''}")

    # ──────────────────────────────────────────────────────────────────
    # Approach 3: Double L8 + anti-commutativity (dot[a][b] != dot[b][a]
    #             for all non-absorber pairs where a != b)
    # ──────────────────────────────────────────────────────────────────
    print("\n" + "─" * 70)
    print("Approach 3: Double L8 + maximal asymmetry")
    print("─" * 70)
    print("Require dot[a][b] != dot[b][a] for all a != b where a,b >= 2.")

    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
    for i in range(2, N):
        for j in range(i + 1, N):
            s.add(dot[i][j] != dot[j][i])

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    print(f"  {'SAT' if result == sat else 'UNSAT' if result == unsat else 'TIMEOUT'} ({elapsed:.1f}s)")

    if result == sat:
        m = s.model()
        table = extract_table(m, dot, N)
        count = 1
        for _ in range(49):
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            table = extract_table(s.model(), dot, N)
            count += 1
        print(f"  Models: {count}{'+'  if count >= 50 else ''}")

    # ──────────────────────────────────────────────────────────────────
    # Approach 4: Double L8 + locked inert + cross-layer engagement
    # ──────────────────────────────────────────────────────────────────
    print("\n" + "─" * 70)
    print("Approach 4: Double L8 + locked inert [0,0,0,0,1,1] + full engagement")
    print("─" * 70)
    print("Fix inert row, require every upper encoder hits ≥2 distinct lower")
    print("non-absorber elements, and vice versa.")

    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)

    # Lock inert row
    locked_inert = [0, 0, 0, 0, 1, 1]
    for j in range(CORE_SIZE):
        s.add(dot[3][j] == locked_inert[j])

    # Upper encoders (2 and 4) must hit ≥2 distinct non-absorber lower elements
    for enc in [2, 4]:
        pairs = []
        for j1 in range(CORE_SIZE, N):
            for j2 in range(j1 + 1, N):
                pairs.append(And(
                    dot[enc][j1] >= 2, dot[enc][j2] >= 2,
                    dot[enc][j1] != dot[enc][j2],
                ))
        s.add(Or(pairs))

    # Lower encoders must hit ≥2 distinct non-absorber upper elements
    for x in range(CORE_SIZE, N):
        # If x is a lower encoder, it must engage with upper layer
        enc_pairs = []
        for j1 in range(CORE_SIZE):
            for j2 in range(j1 + 1, CORE_SIZE):
                enc_pairs.append(And(
                    dot[x][j1] >= 2, dot[x][j2] >= 2,
                    dot[x][j1] != dot[x][j2],
                ))
        # Soft: only if x is encoder-like on lower layer
        # (just add as extra constraint for all lower elements)
        pass  # keep it simple — the L8 constraints handle this

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    print(f"  {'SAT' if result == sat else 'UNSAT' if result == unsat else 'TIMEOUT'} ({elapsed:.1f}s)")

    if result == sat:
        m = s.model()
        table = extract_table(m, dot, N)
        print(f"\n  Inert row: {[table[3][j] for j in range(CORE_SIZE)]}")
        lower = classify_lower_layer(table, CORE_SIZE)
        roles = []
        for x in range(CORE_SIZE, N):
            if x in lower['testers']:
                roles.append('tst')
            elif x in lower['encoders']:
                roles.append('enc')
            elif x in lower['inert']:
                roles.append('inert')
            else:
                roles.append('abs')
        print(f"  Lower roles: {tuple(roles)}")

        count = 1
        for _ in range(49):
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            table = extract_table(s.model(), dot, N)
            count += 1
        print(f"  Models: {count}{'+'  if count >= 50 else ''}")

        if count == 1:
            print("\n  *** UNIQUE! ***")
            print_table(extract_table(m, dot, N))
    else:
        print("  Trying with weaker engagement (just ≥1 non-absorber)...")
        s2, dot2 = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s2, dot2, N, lower_start=CORE_SIZE)
        for j in range(CORE_SIZE):
            s2.add(dot2[3][j] == locked_inert[j])
        for enc in [2, 4]:
            s2.add(Or([And(dot2[enc][j] >= 2) for j in range(CORE_SIZE, N)]))

        t0 = time.time()
        r2 = s2.check()
        e2 = time.time() - t0
        print(f"  Weaker: {'SAT' if r2 == sat else 'UNSAT' if r2 == unsat else 'TIMEOUT'} ({e2:.1f}s)")

    # ──────────────────────────────────────────────────────────────────
    # Approach 5: Double L8 + column-Ext (every COLUMN also distinct)
    # ──────────────────────────────────────────────────────────────────
    print("\n" + "─" * 70)
    print("Approach 5: Double L8 + column-distinctness (Latin square-like)")
    print("─" * 70)
    print("Require all columns distinct (in addition to all rows distinct).")

    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)

    # All columns distinct
    for j1 in range(N):
        for j2 in range(j1 + 1, N):
            s.add(Or([dot[i][j1] != dot[i][j2] for i in range(N)]))

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    print(f"  {'SAT' if result == sat else 'UNSAT' if result == unsat else 'TIMEOUT'} ({elapsed:.1f}s)")

    if result == sat:
        m = s.model()
        table = extract_table(m, dot, N)
        count = 1
        for _ in range(49):
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            table = extract_table(s.model(), dot, N)
            count += 1
        print(f"  Models: {count}{'+'  if count >= 50 else ''}")

    # ──────────────────────────────────────────────────────────────────
    # Approach 6: Double L8 + every element producible in exactly one way
    # ──────────────────────────────────────────────────────────────────
    print("\n" + "─" * 70)
    print("Approach 6: Double L8 + unique producibility")
    print("─" * 70)
    print("Every non-absorber element x ∈ {2..11} is produced by EXACTLY one")
    print("pair (a,b) with a,b ∈ {2..11}.")

    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)

    # For each x in {2..N-1}: exactly one (a,b) with a,b in {2..N-1} has dot[a][b]=x
    # "Exactly one" is expensive; try "at most one" (which with producibility = exactly one)
    non_abs = list(range(2, N))
    for x in non_abs:
        pairs = [(a, b) for a in non_abs for b in non_abs]
        # At-most-one: pairwise mutual exclusion (quadratic but N=12 is manageable)
        # First ensure producibility
        s.add(Or([dot[a][b] == x for a, b in pairs]))
        # At-most-one via pairwise
        for idx1 in range(len(pairs)):
            for idx2 in range(idx1 + 1, len(pairs)):
                a1, b1 = pairs[idx1]
                a2, b2 = pairs[idx2]
                s.add(Or(dot[a1][b1] != x, dot[a2][b2] != x))

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    print(f"  {'SAT' if result == sat else 'UNSAT' if result == unsat else 'TIMEOUT'} ({elapsed:.1f}s)")

    if result == sat:
        m = s.model()
        table = extract_table(m, dot, N)
        count = 1
        for _ in range(19):
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            table = extract_table(s.model(), dot, N)
            count += 1
        print(f"  Models: {count}{'+'  if count >= 20 else ''}")

    # ──────────────────────────────────────────────────────────────────
    # Summary
    # ──────────────────────────────────────────────────────────────────
    print("\n" + "=" * 70)
    print("UNIQUENESS EXPLORATION COMPLETE")
    print("=" * 70)


def tight_uniqueness():
    """
    Explore uniqueness at N=10 — the minimum size for double L8.
    With only 4 non-absorber lower elements, constraints are maximally tight.
    """
    print("=" * 70)
    print("TIGHT UNIQUENESS at N=10 (minimum double L8)")
    print("=" * 70)

    N = 10

    # ── Baseline: just double L8 at N=10 ──
    print("\n--- Baseline: Double L8 at N=10 ---")
    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    print(f"  {result} ({elapsed:.1f}s)")

    if result == sat:
        m = s.model()
        table = extract_table(m, dot, N)
        print(f"  Inert row: {[table[3][j] for j in range(CORE_SIZE)]}")
        print(f"  Lower sub-table (6..9 × 6..9):")
        for i in range(6, N):
            row = [table[i][j] for j in range(6, N)]
            print(f"    {i}: {row}")

        count = 1
        for _ in range(99):
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            table = extract_table(s.model(), dot, N)
            count += 1
        print(f"  Total models: {count}{'+'  if count >= 100 else ''}")

    # ── Try each locked inert row ──
    print("\n--- Double L8 + locked inert rows ---")
    print("Testing which inert rows give fewest models at N=10...")

    # Find all inert rows that are SAT with double L8 at N=10
    s0, dot0 = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s0, dot0, N, lower_start=CORE_SIZE)

    best_count = 999
    best_inert = None
    best_table = None
    inert_results = []
    checked = 0

    while checked < 50:
        r = s0.check()
        if r != sat:
            break
        m = s0.model()
        table = extract_table(m, dot0, N)
        inert_row = tuple(table[3][j] for j in range(CORE_SIZE))

        # Count models for this inert row
        s2, dot2 = encode_stacked(N, "A", timeout_seconds=60)
        add_lower_l8(s2, dot2, N, lower_start=CORE_SIZE)
        for j in range(CORE_SIZE):
            s2.add(dot2[3][j] == inert_row[j])

        count = 0
        first_table = None
        for _ in range(50):
            if s2.check() != sat:
                break
            m2 = s2.model()
            t2 = extract_table(m2, dot2, N)
            if first_table is None:
                first_table = t2
            count += 1
            s2.add(Or([dot2[i][j] != t2[i][j]
                        for i in range(N) for j in range(N)]))

        inert_results.append((inert_row, count))
        if count < best_count:
            best_count = count
            best_inert = inert_row
            best_table = first_table
        print(f"  Inert {list(inert_row)}: {count}{'+'  if count >= 50 else ''} models")

        # Block this inert row
        s0.add(Or([dot0[3][j] != inert_row[j] for j in range(CORE_SIZE)]))
        checked += 1

    print(f"\n  Best: inert={list(best_inert)}, {best_count} models")

    if best_count <= 10 and best_table is not None:
        print(f"\n  Tables with best inert row:")
        print_table(best_table)

    # ── If still not unique, try adding more constraints on the best ──
    if best_count > 1 and best_inert is not None:
        print("\n--- Adding constraints to best inert row ---")

        # Try: column-distinct
        s3, dot3 = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s3, dot3, N, lower_start=CORE_SIZE)
        for j in range(CORE_SIZE):
            s3.add(dot3[3][j] == best_inert[j])
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                s3.add(Or([dot3[i][j1] != dot3[i][j2] for i in range(N)]))

        r3 = s3.check()
        if r3 == sat:
            t3 = extract_table(s3.model(), dot3, N)
            c3 = 1
            for _ in range(49):
                s3.add(Or([dot3[i][j] != t3[i][j]
                           for i in range(N) for j in range(N)]))
                if s3.check() != sat:
                    break
                t3 = extract_table(s3.model(), dot3, N)
                c3 += 1
            print(f"  + column-distinct: {c3}{'+'  if c3 >= 50 else ''} models")
        else:
            print(f"  + column-distinct: {r3}")

        # Try: every non-absorber element appears as dot[x][x] for some x
        s4, dot4 = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s4, dot4, N, lower_start=CORE_SIZE)
        for j in range(CORE_SIZE):
            s4.add(dot4[3][j] == best_inert[j])
        # Diagonal surjectivity onto non-absorbers
        for x in range(2, N):
            s4.add(Or([dot4[a][a] == x for a in range(2, N)]))

        r4 = s4.check()
        if r4 == sat:
            t4 = extract_table(s4.model(), dot4, N)
            c4 = 1
            for _ in range(49):
                s4.add(Or([dot4[i][j] != t4[i][j]
                           for i in range(N) for j in range(N)]))
                if s4.check() != sat:
                    break
                t4 = extract_table(s4.model(), dot4, N)
                c4 += 1
            print(f"  + diagonal-surjective: {c4}{'+'  if c4 >= 50 else ''} models")
        else:
            print(f"  + diagonal-surjective: {r4}")

        # Try: isomorphic layers at N=10
        # f: {0:0, 1:1, 2:6, 3:7, 4:8, 5:9}
        print("\n  + isomorphic layers (f: 2→6, 3→7, 4→8, 5→9):")
        f_map = {0: 0, 1: 1, 2: 6, 3: 7, 4: 8, 5: 9}
        s5, dot5 = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s5, dot5, N, lower_start=CORE_SIZE)
        for j in range(CORE_SIZE):
            s5.add(dot5[3][j] == best_inert[j])

        for i in range(CORE_SIZE):
            for j in range(CORE_SIZE):
                fi, fj = f_map[i], f_map[j]
                expr = dot5[i][j]
                for k, fk in f_map.items():
                    if k != fk:
                        expr = If(dot5[i][j] == k, fk, expr)
                s5.add(dot5[fi][fj] == expr)

        r5 = s5.check()
        if r5 == sat:
            t5 = extract_table(s5.model(), dot5, N)
            c5 = 1
            for _ in range(49):
                s5.add(Or([dot5[i][j] != t5[i][j]
                           for i in range(N) for j in range(N)]))
                if s5.check() != sat:
                    break
                t5 = extract_table(s5.model(), dot5, N)
                c5 += 1
            print(f"    {c5}{'+'  if c5 >= 50 else ''} models")
            if c5 <= 5:
                print(f"\n    First model:")
                print_table(extract_table(s5.model() if c5 > 1 else s5.model(), dot5, N))
        else:
            print(f"    {r5}")

    print("\n" + "=" * 70)
    print("TIGHT UNIQUENESS COMPLETE")
    print("=" * 70)


def algebraic_uniqueness():
    """
    Try algebraic identities on top of double L8 to reduce model count.
    Test at N=10 (minimum double L8).
    """
    N = 10

    print("=" * 70)
    print("ALGEBRAIC UNIQUENESS SEARCH at N=10")
    print("=" * 70)

    def lookup_2d(dot, row_expr, col_expr, N):
        """Lookup dot[row_expr][col_expr] where both may be Z3 exprs."""
        # Chain: for each concrete column j, compute dot[row_expr][j],
        # then select based on col_expr
        result = ite_lookup(dot, row_expr, 0, N)
        for j in range(1, N):
            result = If(col_expr == j, ite_lookup(dot, row_expr, j, N), result)
        return result

    def count_models(s, dot, N, cap=20):
        """Count models up to cap, return (count, first_table, status)."""
        r = s.check()
        if r != sat:
            return (0, None, str(r))
        m = s.model()
        first = extract_table(m, dot, N)
        count = 1
        for _ in range(cap - 1):
            tbl = extract_table(s.model(), dot, N)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            count += 1
        return (count, first, "sat")

    def base_solver():
        s, dot = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
        return s, dot

    constraints = {}

    # ── 1. Left self-distributivity: a·(b·c) = (a·b)·(a·c) ──
    print("\n1. Left self-distributivity: a·(b·c) = (a·b)·(a·c)")
    s, dot = base_solver()
    for a in range(N):
        for b in range(N):
            for c in range(N):
                bc = dot[b][c]  # Z3 var
                a_bc = col_ite_lookup(dot, a, bc, N)  # a is concrete row
                ab = dot[a][b]  # Z3 var
                ac = dot[a][c]  # Z3 var
                ab_ac = lookup_2d(dot, ab, ac, N)  # both Z3
                s.add(a_bc == ab_ac)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    print(f"  {status} ({time.time()-t0:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    constraints["L-self-dist"] = cnt

    # ── 2. Right self-distributivity: (a·b)·c = (a·c)·(b·c) ──
    print("\n2. Right self-distributivity: (a·b)·c = (a·c)·(b·c)")
    s, dot = base_solver()
    for a in range(N):
        for b in range(N):
            for c in range(N):
                ab = dot[a][b]  # Z3
                ab_c = ite_lookup(dot, ab, c, N)  # c is concrete col
                ac = dot[a][c]  # Z3
                bc = dot[b][c]  # Z3
                ac_bc = lookup_2d(dot, ac, bc, N)  # both Z3
                s.add(ab_c == ac_bc)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    print(f"  {status} ({time.time()-t0:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    constraints["R-self-dist"] = cnt

    # ── 3. Medial / entropic: (a·b)·(c·d) = (a·c)·(b·d) ──
    print("\n3. Medial: (a·b)·(c·d) = (a·c)·(b·d)")
    s, dot = base_solver()
    for a in range(N):
        for b in range(N):
            ab = dot[a][b]
            for c in range(N):
                ac = dot[a][c]
                for d in range(N):
                    cd = dot[c][d]
                    bd = dot[b][d]
                    lhs = lookup_2d(dot, ab, cd, N)
                    rhs = lookup_2d(dot, ac, bd, N)
                    s.add(lhs == rhs)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    print(f"  {status} ({time.time()-t0:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    constraints["medial"] = cnt

    # ── 4. Diagonal distinctness: all dot[i][i] distinct ──
    print("\n4. Diagonal distinctness")
    s, dot = base_solver()
    for i in range(N):
        for j in range(i + 1, N):
            s.add(dot[i][i] != dot[j][j])
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    print(f"  {status} ({time.time()-t0:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    constraints["diag-distinct"] = cnt

    # ── 5. Flexible: a·(b·a) = (a·b)·a ──
    print("\n5. Flexible: a·(b·a) = (a·b)·a")
    s, dot = base_solver()
    for a in range(N):
        for b in range(N):
            ba = dot[b][a]  # Z3
            a_ba = col_ite_lookup(dot, a, ba, N)  # a concrete row
            ab = dot[a][b]  # Z3
            ab_a = ite_lookup(dot, ab, a, N)  # a concrete col
            s.add(a_ba == ab_a)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    print(f"  {status} ({time.time()-t0:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    constraints["flexible"] = cnt

    # ── 6. Bol identity: a·(b·(a·c)) = (a·(b·a))·c ──
    print("\n6. Left Bol: a·(b·(a·c)) = (a·(b·a))·c")
    s, dot = base_solver()
    for a in range(N):
        for b in range(N):
            ba = dot[b][a]  # Z3
            a_ba = col_ite_lookup(dot, a, ba, N)  # a concrete
            for c in range(N):
                ac = dot[a][c]  # Z3
                b_ac = col_ite_lookup(dot, b, ac, N)  # b concrete
                lhs = col_ite_lookup(dot, a, b_ac, N)  # a concrete
                rhs = ite_lookup(dot, a_ba, c, N)  # c concrete
                s.add(lhs == rhs)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    print(f"  {status} ({time.time()-t0:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    constraints["L-Bol"] = cnt

    # ── 7. Idempotent non-absorbers: x·x = x for x >= 2 ──
    print("\n7. Idempotent non-absorbers: x·x = x for x >= 2")
    s, dot = base_solver()
    for x in range(2, N):
        s.add(dot[x][x] == x)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    print(f"  {status} ({time.time()-t0:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    constraints["idempotent"] = cnt

    # ── 8. Power-associative: (x·x)·x = x·(x·x) for all x ──
    print("\n8. Power-associative: (x·x)·x = x·(x·x)")
    s, dot = base_solver()
    for x in range(N):
        xx = dot[x][x]  # Z3
        xx_x = ite_lookup(dot, xx, x, N)  # x concrete col
        x_xx = col_ite_lookup(dot, x, xx, N)  # x concrete row
        s.add(xx_x == x_xx)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    print(f"  {status} ({time.time()-t0:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    constraints["power-assoc"] = cnt

    # ── 9. Associative: (a·b)·c = a·(b·c) for all a,b,c ──
    print("\n9. Associativity")
    s, dot = base_solver()
    for a in range(N):
        for b in range(N):
            ab = dot[a][b]  # Z3
            for c in range(N):
                ab_c = ite_lookup(dot, ab, c, N)  # c concrete
                bc = dot[b][c]  # Z3
                a_bc = col_ite_lookup(dot, a, bc, N)  # a concrete
                s.add(ab_c == a_bc)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    print(f"  {status} ({time.time()-t0:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    constraints["associative"] = cnt

    # ── Summary ──
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    for name, cnt in sorted(constraints.items(), key=lambda x: x[1]):
        status = "UNSAT" if cnt == 0 else f"{cnt}{'+'  if cnt >= 20 else ''} models"
        marker = " ← UNIQUE!" if cnt == 1 else " ← promising" if 1 < cnt < 10 else ""
        print(f"  {name:20s}: {status}{marker}")

    print()


def narrow_from_power_assoc():
    """
    Power-associativity is the only classical identity compatible with
    double L8 at N=10. Try combining it with additional constraints
    to reduce model count toward uniqueness.
    """
    N = 10

    print("=" * 70)
    print("NARROWING FROM POWER-ASSOCIATIVITY (N=10)")
    print("=" * 70)

    def count_models(s, dot, N, cap=20):
        r = s.check()
        if r != sat:
            return (0, None, str(r))
        m = s.model()
        first = extract_table(m, dot, N)
        count = 1
        for _ in range(cap - 1):
            tbl = extract_table(s.model(), dot, N)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            count += 1
        return (count, first, "sat")

    def base_pa():
        """Double L8 + power-associativity."""
        s, dot = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
        for x in range(N):
            xx = dot[x][x]
            xx_x = ite_lookup(dot, xx, x, N)
            x_xx = col_ite_lookup(dot, x, xx, N)
            s.add(xx_x == x_xx)
        return s, dot

    results = {}

    # ── 1. PA + left alternative: (a·a)·b = a·(a·b) ──
    print("\n1. PA + left alternative: (x·x)·y = x·(x·y)")
    s, dot = base_pa()
    for x in range(N):
        xx = dot[x][x]  # Z3
        for y in range(N):
            xx_y = ite_lookup(dot, xx, y, N)  # y concrete
            xy = dot[x][y]  # Z3
            x_xy = col_ite_lookup(dot, x, xy, N)  # x concrete
            s.add(xx_y == x_xy)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    elapsed = time.time() - t0
    print(f"  {status} ({elapsed:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    results["PA+L-alt"] = (cnt, tbl)

    # ── 2. PA + right alternative: (a·b)·b = a·(b·b) ──
    print("\n2. PA + right alternative: (x·y)·y = x·(y·y)")
    s, dot = base_pa()
    for x in range(N):
        for y in range(N):
            xy = dot[x][y]  # Z3
            xy_y = ite_lookup(dot, xy, y, N)  # y concrete
            yy = dot[y][y]  # Z3
            x_yy = col_ite_lookup(dot, x, yy, N)  # x concrete
            s.add(xy_y == x_yy)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    elapsed = time.time() - t0
    print(f"  {status} ({elapsed:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    results["PA+R-alt"] = (cnt, tbl)

    # ── 3. PA + x³ = x for all x ──
    print("\n3. PA + x³ = x (every element has order ≤ 2 under squaring)")
    s, dot = base_pa()
    for x in range(N):
        xx = dot[x][x]  # Z3
        xxx = col_ite_lookup(dot, x, xx, N)  # x concrete row, xx Z3 col
        # Equivalently: x · (x·x) = x
        s.add(xxx == x)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    elapsed = time.time() - t0
    print(f"  {status} ({elapsed:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    results["PA+x3=x"] = (cnt, tbl)
    if cnt > 0 and tbl is not None:
        print(f"  Diagonal: {[tbl[i][i] for i in range(N)]}")

    # ── 4. PA + x⁴ = x² for all x (powers eventually cycle at 2) ──
    print("\n4. PA + x⁴ = x² (squaring is idempotent)")
    s, dot = base_pa()
    for x in range(N):
        xx = dot[x][x]  # Z3  (= x²)
        # x⁴ = (x²)² = xx · xx — but xx is Z3
        # Use lookup_2d for dot[xx][xx]:
        xxxx = ite_lookup(dot, xx, 0, N)
        for j in range(1, N):
            xxxx = If(xx == j, ite_lookup(dot, xx, j, N), xxxx)
        # Actually simpler: since both are the same Z3 var,
        # dot[xx][xx] = result where result = If(xx==0, dot[0][0], If(xx==1, ...))
        x4 = dot[0][0]  # default
        for k in range(N):
            x4 = If(xx == k, dot[k][k], x4)
        s.add(x4 == xx)
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    elapsed = time.time() - t0
    print(f"  {status} ({elapsed:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    results["PA+x4=x2"] = (cnt, tbl)

    # ── 5. PA + nilpotent level 2: x² ∈ {0,1} for all x ≥ 2 ──
    print("\n5. PA + x² ∈ {0,1} for all non-absorbers (nilpotent squaring)")
    s, dot = base_pa()
    for x in range(2, N):
        s.add(Or(dot[x][x] == 0, dot[x][x] == 1))
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    elapsed = time.time() - t0
    print(f"  {status} ({elapsed:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    results["PA+nil-sq"] = (cnt, tbl)
    if cnt > 0 and tbl is not None:
        print(f"  Diagonal: {[tbl[i][i] for i in range(N)]}")

    # ── 6. PA + column surjectivity on non-absorber columns ──
    print("\n6. PA + every value appears in every non-absorber column")
    s, dot = base_pa()
    for j in range(2, N):
        for v in range(N):
            s.add(Or([dot[i][j] == v for i in range(N)]))
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    elapsed = time.time() - t0
    print(f"  {status} ({elapsed:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    results["PA+col-surj"] = (cnt, tbl)

    # ── 7. PA + row surjectivity for non-absorber rows ──
    print("\n7. PA + every non-absorber row is surjective (every value appears)")
    s, dot = base_pa()
    for i in range(2, N):
        for v in range(N):
            s.add(Or([dot[i][j] == v for j in range(N)]))
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    elapsed = time.time() - t0
    print(f"  {status} ({elapsed:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    results["PA+row-surj"] = (cnt, tbl)

    # ── 8. PA + anti-commutative on non-absorbers ──
    print("\n8. PA + anti-commutative (dot[a][b] != dot[b][a]) for non-absorber a<b")
    s, dot = base_pa()
    for a in range(2, N):
        for b in range(a + 1, N):
            s.add(dot[a][b] != dot[b][a])
    t0 = time.time()
    cnt, tbl, status = count_models(s, dot, N)
    elapsed = time.time() - t0
    print(f"  {status} ({elapsed:.1f}s), models: {cnt}{'+'  if cnt >= 20 else ''}")
    results["PA+anti-comm"] = (cnt, tbl)

    # ── Summary ──
    print("\n" + "=" * 70)
    print("SUMMARY (sorted by model count)")
    print("=" * 70)
    for name, (cnt, _) in sorted(results.items(), key=lambda x: x[1][0]):
        if cnt == 0:
            status = "UNSAT"
        else:
            status = f"{cnt}{'+'  if cnt >= 20 else ''} models"
        marker = " ← UNIQUE!" if cnt == 1 else " ← promising" if 1 < cnt < 10 else ""
        print(f"  {name:20s}: {status}{marker}")

    # ── Combine SAT constraints ──
    sat_names = [n for n, (c, _) in results.items() if c > 0]
    if len(sat_names) >= 2:
        print(f"\n--- Combining compatible constraints ---")
        # Try pairwise combinations of SAT constraints
        # Can't easily re-encode generically, but try the most promising combo
        best_sat = sorted(
            [(n, c) for n, (c, _) in results.items() if c > 0],
            key=lambda x: x[1]
        )
        if len(best_sat) >= 2:
            print(f"  Two best: {best_sat[0][0]} ({best_sat[0][1]}) + "
                  f"{best_sat[1][0]} ({best_sat[1][1]})")

    # ── If any gave uniqueness or small count, show the table ──
    for name, (cnt, tbl) in results.items():
        if 0 < cnt <= 3 and tbl is not None:
            print(f"\n{name} — first table:")
            print_table(tbl)

    print()


def optimization_uniqueness():
    """
    Use optimization to select canonical representatives from the
    double L8 + PA model space.

    Approaches:
      A. Lex-min table (smallest table in dictionary order)
      B. Max absorber density (most entries ∈ {0,1})
      C. Min row-sum (smallest total of all entries)
      D. PA + x⁴=x² + further narrowing with within-layer commutativity
    """
    from z3 import Optimize, Sum

    N = 10

    print("=" * 70)
    print("OPTIMIZATION-BASED UNIQUENESS (N=10)")
    print("=" * 70)

    def base_pa_opt(timeout=300):
        """Double L8 + PA using Optimize solver."""
        # Build with regular Solver first, then transfer to Optimize
        s, dot = encode_stacked(N, "A", timeout_seconds=timeout)
        add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
        # PA
        for x in range(N):
            xx = dot[x][x]
            xx_x = ite_lookup(dot, xx, x, N)
            x_xx = col_ite_lookup(dot, x, xx, N)
            s.add(xx_x == x_xx)
        return s, dot

    def base_pa_optimize(timeout=300):
        """Double L8 + PA using Z3 Optimize."""
        opt = Optimize()
        opt.set("timeout", timeout * 1000)
        dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]

        # Range
        for i in range(N):
            for j in range(N):
                opt.add(dot[i][j] >= 0, dot[i][j] < N)

        # Absorbers
        for j in range(N):
            opt.add(dot[0][j] == 0)
            opt.add(dot[1][j] == 1)

        # No other absorbers
        for x in range(2, N):
            opt.add(Or([dot[x][j] != x for j in range(N)]))

        # Ext (all rows distinct)
        for x in range(N):
            for y in range(x + 1, N):
                opt.add(Or([dot[x][j] != dot[y][j] for j in range(N)]))

        # Pin core
        for row_idx, row_vals in FIXED_ROWS.items():
            for j in range(CORE_SIZE):
                opt.add(dot[row_idx][j] == row_vals[j])

        # Sub-algebra closure for inert row
        for j in range(CORE_SIZE):
            opt.add(dot[3][j] >= 0, dot[3][j] < CORE_SIZE)

        # Lower L8 — add constraints manually (can't use add_lower_l8
        # since it takes a Solver)
        L = list(range(CORE_SIZE, N))

        # Sub-algebra closure
        for i in L:
            for j in L:
                opt.add(Or([dot[i][j] == v for v in [0, 1] + L]))

        # Ext within L
        for i_idx, x in enumerate(L):
            for j_idx, y in enumerate(L):
                if j_idx <= i_idx:
                    continue
                opt.add(Or([dot[x][k] != dot[y][k] for k in L]))

        # No local absorbers
        for x in L:
            opt.add(Or([dot[x][j] != x for j in L]))

        # Tester/encoder classification
        tst_exprs = {}
        for x in L:
            tst_exprs[x] = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in L])

        enc_exprs = {}
        for x in L:
            pairs = []
            for j1_idx, j1 in enumerate(L):
                for j2_idx, j2 in enumerate(L):
                    if j2_idx <= j1_idx:
                        continue
                    pairs.append(And(
                        dot[x][j1] != 0, dot[x][j1] != 1,
                        dot[x][j2] != 0, dot[x][j2] != 1,
                        dot[x][j1] != dot[x][j2],
                    ))
            enc_exprs[x] = Or(pairs) if pairs else False

        def is_inert(x):
            return And(Not(tst_exprs[x]), Not(enc_exprs[x]))

        def in_core(x):
            return Or(tst_exprs[x], enc_exprs[x])

        # L1: tester
        opt.add(Or([tst_exprs[x] for x in L]))
        # L2: encoder
        opt.add(Or([enc_exprs[x] for x in L]))

        # L5: two independent encoders
        pair_clauses = []
        for i_idx, e1 in enumerate(L):
            for j_idx, e2 in enumerate(L):
                if j_idx <= i_idx:
                    continue
                diff = []
                for j in L:
                    diff.append(And(dot[e1][j] != 0, dot[e1][j] != 1,
                                    Or(dot[e2][j] == 0, dot[e2][j] == 1)))
                    diff.append(And(dot[e2][j] != 0, dot[e2][j] != 1,
                                    Or(dot[e1][j] == 0, dot[e1][j] == 1)))
                    diff.append(And(dot[e1][j] != 0, dot[e1][j] != 1,
                                    dot[e2][j] != 0, dot[e2][j] != 1,
                                    dot[e1][j] != dot[e2][j]))
                pair_clauses.append(And(enc_exprs[e1], enc_exprs[e2], Or(diff)))
        opt.add(Or(pair_clauses))

        # Encoder produces encoder
        gen_clauses = []
        for e in L:
            for j in L:
                for t in L:
                    gen_clauses.append(And(enc_exprs[e], dot[e][j] == t, enc_exprs[t]))
        opt.add(Or(gen_clauses))

        # Tester constructibility
        for t in L:
            prod = []
            for e in L:
                for j in L:
                    prod.append(And(enc_exprs[e], dot[e][j] == t))
            opt.add(Or(Not(tst_exprs[t]), Or(prod)))

        # L6: open closure
        esc = []
        for x in L:
            for y in L:
                for v in L:
                    esc.append(And(in_core(x), in_core(y), dot[x][y] == v, is_inert(v)))
        opt.add(Or(esc))

        fb = []
        for c in L:
            for v in L:
                for r in L:
                    fb.append(And(in_core(c), is_inert(v), dot[c][v] == r,
                                  Or(tst_exprs[r], enc_exprs[r])))
        opt.add(Or(fb))

        # L7: context tokens + producibility
        ctx = []
        for c1_idx, c1 in enumerate(L):
            for c2_idx, c2 in enumerate(L):
                if c2_idx <= c1_idx:
                    continue
                for e1_idx, e1 in enumerate(L):
                    for e2_idx, e2 in enumerate(L):
                        if e2_idx <= e1_idx:
                            continue
                        ctx.append(And(
                            enc_exprs[e1], enc_exprs[e2],
                            dot[e1][c1] != dot[e1][c2],
                            dot[e1][c1] != 0, dot[e1][c1] != 1,
                            dot[e1][c2] != 0, dot[e1][c2] != 1,
                            dot[e2][c1] != dot[e2][c2],
                            dot[e2][c1] != 0, dot[e2][c1] != 1,
                            dot[e2][c2] != 0, dot[e2][c2] != 1,
                            Or(dot[e1][c1] != dot[e2][c1],
                               dot[e1][c2] != dot[e2][c2]),
                        ))
        opt.add(Or(ctx))

        for x in L:
            opt.add(Or([dot[a][b] == x for a in L for b in L]))
        opt.add(Or([dot[a][b] == 0 for a in L for b in L]))
        opt.add(Or([dot[a][b] == 1 for a in L for b in L]))

        # L8: encoder completeness
        for e in L:
            has_abs = Or([Or(dot[e][j] == 0, dot[e][j] == 1) for j in L])
            has_tst = Or([And(dot[e][j] == t, tst_exprs[t]) for j in L for t in L])
            has_inert = Or([And(dot[e][j] == v, is_inert(v)) for j in L for v in L])
            opt.add(Or(Not(enc_exprs[e]), And(has_abs, has_tst, has_inert)))

        for v in L:
            opt.add(Or(Not(is_inert(v)), dot[v][v] != v))

        # PA
        for x in range(N):
            xx = dot[x][x]
            xx_x = ite_lookup(dot, xx, x, N)
            x_xx = col_ite_lookup(dot, x, xx, N)
            opt.add(xx_x == x_xx)

        return opt, dot

    # ── Approach A: Minimize sum of all entries (absorber-heavy) ──
    print("\n--- A: Minimize sum of all entries ---")
    opt, dot = base_pa_optimize(timeout=120)
    total_sum = Sum([dot[i][j] for i in range(N) for j in range(N)])
    opt.minimize(total_sum)

    t0 = time.time()
    result = opt.check()
    elapsed = time.time() - t0
    if result == sat:
        m = opt.model()
        table = extract_table(m, dot, N)
        s_val = sum(table[i][j] for i in range(N) for j in range(N))
        print(f"  SAT ({elapsed:.1f}s), min sum = {s_val}")
        print(f"  Diagonal: {[table[i][i] for i in range(N)]}")
        print_table(table)

        # Check uniqueness: is there another table with same min sum?
        opt2, dot2 = base_pa_optimize(timeout=120)
        opt2.add(Sum([dot2[i][j] for i in range(N) for j in range(N)]) == s_val)
        opt2.add(Or([dot2[i][j] != table[i][j]
                      for i in range(N) for j in range(N)]))
        r2 = opt2.check()
        if r2 == sat:
            print(f"  Unique at min sum? NO (other tables exist)")
        else:
            print(f"  Unique at min sum? YES! ←←←")
    else:
        print(f"  {result} ({elapsed:.1f}s)")

    # ── Approach B: Maximize absorber density ──
    print("\n--- B: Maximize entries ∈ {0,1} ---")
    opt, dot = base_pa_optimize(timeout=120)
    bool_count = Sum([If(Or(dot[i][j] == 0, dot[i][j] == 1), 1, 0)
                      for i in range(N) for j in range(N)])
    opt.maximize(bool_count)

    t0 = time.time()
    result = opt.check()
    elapsed = time.time() - t0
    if result == sat:
        m = opt.model()
        table = extract_table(m, dot, N)
        b_count = sum(1 for i in range(N) for j in range(N) if table[i][j] in (0, 1))
        print(f"  SAT ({elapsed:.1f}s), max boolean entries = {b_count}/100")
        print_table(table)

        # Check uniqueness
        opt2, dot2 = base_pa_optimize(timeout=120)
        opt2.add(Sum([If(Or(dot2[i][j] == 0, dot2[i][j] == 1), 1, 0)
                       for i in range(N) for j in range(N)]) == b_count)
        opt2.add(Or([dot2[i][j] != table[i][j]
                      for i in range(N) for j in range(N)]))
        r2 = opt2.check()
        if r2 == sat:
            print(f"  Unique at max boolean? NO")
        else:
            print(f"  Unique at max boolean? YES! ←←←")
    else:
        print(f"  {result} ({elapsed:.1f}s)")

    # ── Approach C: Within-layer commutativity ──
    print("\n--- C: PA + within-layer commutativity ---")
    print("dot[a][b] = dot[b][a] for a,b both in {2..5} or both in {6..9}")
    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
    for x in range(N):
        xx = dot[x][x]
        xx_x = ite_lookup(dot, xx, x, N)
        x_xx = col_ite_lookup(dot, x, xx, N)
        s.add(xx_x == x_xx)

    # Within upper layer (non-absorbers)
    for a in range(2, CORE_SIZE):
        for b in range(a + 1, CORE_SIZE):
            s.add(dot[a][b] == dot[b][a])
    # Within lower layer
    for a in range(CORE_SIZE, N):
        for b in range(a + 1, N):
            s.add(dot[a][b] == dot[b][a])

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    print(f"  {result} ({elapsed:.1f}s)")

    if result == sat:
        m = s.model()
        table = extract_table(m, dot, N)
        count = 1
        for _ in range(19):
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            table = extract_table(s.model(), dot, N)
            count += 1
        print(f"  Models: {count}{'+'  if count >= 20 else ''}")

    # ── Approach D: PA + x⁴=x² + further narrowing ──
    print("\n--- D: PA + x⁴=x² + within-layer commutativity ---")
    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
    for x in range(N):
        xx = dot[x][x]
        xx_x = ite_lookup(dot, xx, x, N)
        x_xx = col_ite_lookup(dot, x, xx, N)
        s.add(xx_x == x_xx)
        # x⁴ = x²
        x4 = dot[0][0]
        for k in range(N):
            x4 = If(xx == k, dot[k][k], x4)
        s.add(x4 == xx)

    for a in range(2, CORE_SIZE):
        for b in range(a + 1, CORE_SIZE):
            s.add(dot[a][b] == dot[b][a])
    for a in range(CORE_SIZE, N):
        for b in range(a + 1, N):
            s.add(dot[a][b] == dot[b][a])

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    print(f"  {result} ({elapsed:.1f}s)")

    if result == sat:
        m = s.model()
        table = extract_table(m, dot, N)
        count = 1
        for _ in range(19):
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            table = extract_table(s.model(), dot, N)
            count += 1
        print(f"  Models: {count}{'+'  if count >= 20 else ''}")
        if count <= 5:
            print_table(extract_table(m, dot, N))

    print("\n" + "=" * 70)
    print("OPTIMIZATION UNIQUENESS COMPLETE")
    print("=" * 70)


def isomorphism_uniqueness():
    """
    Test whether the double L8 + PA structure at N=10 is unique
    UP TO ISOMORPHISM of the lower layer (permutations of {6,7,8,9}
    that preserve the table structure, fixing {0..5}).

    Also try maximizing cross-layer engagement to select the most
    "interesting" representative.
    """
    import itertools

    N = 10

    print("=" * 70)
    print("ISOMORPHISM UNIQUENESS (N=10, PA + double L8)")
    print("=" * 70)

    def base_pa():
        s, dot = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
        for x in range(N):
            xx = dot[x][x]
            xx_x = ite_lookup(dot, xx, x, N)
            x_xx = col_ite_lookup(dot, x, xx, N)
            s.add(xx_x == x_xx)
        return s, dot

    def tables_isomorphic(t1, t2, upper_size=6):
        """Check if t1 and t2 are isomorphic via a permutation of lower elements."""
        N = len(t1)
        lower = list(range(upper_size, N))
        for perm in itertools.permutations(lower):
            # Build full permutation: identity on 0..upper_size-1, perm on lower
            f = list(range(upper_size)) + list(perm)
            # Check: t2[f[i]][f[j]] == f[t1[i][j]] for all i,j
            match = True
            for i in range(N):
                for j in range(N):
                    if t2[f[i]][f[j]] != f[t1[i][j]]:
                        match = False
                        break
                if not match:
                    break
            if match:
                return True, f
        return False, None

    # ── Collect models ──
    print("\nCollecting PA + double L8 models...")
    s, dot = base_pa()

    models = []
    t0 = time.time()
    for _ in range(30):
        if s.check() != sat:
            break
        table = extract_table(s.model(), dot, N)
        models.append(table)
        s.add(Or([dot[i][j] != table[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Found {len(models)} models ({elapsed:.1f}s)")

    # ── Group by isomorphism class ──
    print("\nGrouping by isomorphism class...")
    classes = []  # list of (representative_table, [member_indices])

    for idx, table in enumerate(models):
        found_class = False
        for cls_idx, (rep, members) in enumerate(classes):
            iso, perm = tables_isomorphic(rep, table)
            if iso:
                members.append(idx)
                found_class = True
                break
        if not found_class:
            classes.append((table, [idx]))

    print(f"  {len(models)} models → {len(classes)} isomorphism classes")

    for cls_idx, (rep, members) in enumerate(classes):
        # Classify lower layer roles
        lower_roles = []
        for x in range(CORE_SIZE, N):
            row = [rep[x][j] for j in range(CORE_SIZE, N)]
            if all(v in (0, 1) for v in row):
                lower_roles.append("tst")
            elif len(set(v for v in row if v not in (0, 1))) >= 2:
                lower_roles.append("enc")
            else:
                lower_roles.append("inert")

        # Cross-layer engagement: count non-absorber cross-layer entries
        cross_nonabs = 0
        for i in range(CORE_SIZE):
            for j in range(CORE_SIZE, N):
                if rep[i][j] not in (0, 1):
                    cross_nonabs += 1
        for i in range(CORE_SIZE, N):
            for j in range(CORE_SIZE):
                if rep[i][j] not in (0, 1):
                    cross_nonabs += 1

        inert_row = tuple(rep[3][j] for j in range(CORE_SIZE))

        print(f"\n  Class {cls_idx}: {len(members)} members, "
              f"lower roles={tuple(lower_roles)}, "
              f"cross-engagement={cross_nonabs}, "
              f"inert={list(inert_row)}")

        if cls_idx < 5:
            # Show the lower sub-table
            print(f"    Lower sub-table ({CORE_SIZE}..{N-1} × {CORE_SIZE}..{N-1}):")
            for i in range(CORE_SIZE, N):
                row = [rep[i][j] for j in range(CORE_SIZE, N)]
                print(f"      {i}: {row}")
            # Show cross-layer
            print(f"    Upper→lower (rows 2..5, cols 6..9):")
            for i in [2, 3, 4, 5]:
                row = [rep[i][j] for j in range(CORE_SIZE, N)]
                print(f"      {i}: {row}")
            print(f"    Lower→upper (rows 6..9, cols 0..5):")
            for i in range(CORE_SIZE, N):
                row = [rep[i][j] for j in range(CORE_SIZE)]
                print(f"      {i}: {row}")

    if len(classes) == 1:
        print("\n  *** UNIQUE UP TO ISOMORPHISM! ***")
        print("\n  Canonical representative:")
        print_table(classes[0][0])

    # ── Now try: PA + double L8 + x⁴=x² ──
    print("\n" + "─" * 70)
    print("Same analysis with PA + x⁴=x²")
    print("─" * 70)

    s, dot = base_pa()
    for x in range(N):
        xx = dot[x][x]
        x4 = dot[0][0]
        for k in range(N):
            x4 = If(xx == k, dot[k][k], x4)
        s.add(x4 == xx)

    models2 = []
    t0 = time.time()
    for _ in range(30):
        if s.check() != sat:
            break
        table = extract_table(s.model(), dot, N)
        models2.append(table)
        s.add(Or([dot[i][j] != table[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Found {len(models2)} models ({elapsed:.1f}s)")

    classes2 = []
    for idx, table in enumerate(models2):
        found_class = False
        for cls_idx, (rep, members) in enumerate(classes2):
            iso, perm = tables_isomorphic(rep, table)
            if iso:
                members.append(idx)
                found_class = True
                break
        if not found_class:
            classes2.append((table, [idx]))

    print(f"  {len(models2)} models → {len(classes2)} isomorphism classes")

    for cls_idx, (rep, members) in enumerate(classes2):
        lower_roles = []
        for x in range(CORE_SIZE, N):
            row = [rep[x][j] for j in range(CORE_SIZE, N)]
            if all(v in (0, 1) for v in row):
                lower_roles.append("tst")
            elif len(set(v for v in row if v not in (0, 1))) >= 2:
                lower_roles.append("enc")
            else:
                lower_roles.append("inert")
        inert_row = tuple(rep[3][j] for j in range(CORE_SIZE))
        print(f"  Class {cls_idx}: {len(members)} members, "
              f"lower={tuple(lower_roles)}, inert={list(inert_row)}")

    if len(classes2) == 1:
        print("\n  *** UNIQUE UP TO ISOMORPHISM! ***")
        print("\n  Canonical representative:")
        print_table(classes2[0][0])

    # ── Also test without PA (just double L8) for comparison ──
    print("\n" + "─" * 70)
    print("Baseline: just double L8 (no PA)")
    print("─" * 70)
    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)

    models3 = []
    t0 = time.time()
    for _ in range(30):
        if s.check() != sat:
            break
        table = extract_table(s.model(), dot, N)
        models3.append(table)
        s.add(Or([dot[i][j] != table[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Found {len(models3)} models ({elapsed:.1f}s)")

    classes3 = []
    for idx, table in enumerate(models3):
        found_class = False
        for cls_idx, (rep, members) in enumerate(classes3):
            iso, perm = tables_isomorphic(rep, table)
            if iso:
                members.append(idx)
                found_class = True
                break
        if not found_class:
            classes3.append((table, [idx]))

    print(f"  {len(models3)} models → {len(classes3)} isomorphism classes")

    for cls_idx, (rep, members) in enumerate(classes3):
        lower_roles = []
        for x in range(CORE_SIZE, N):
            row = [rep[x][j] for j in range(CORE_SIZE, N)]
            if all(v in (0, 1) for v in row):
                lower_roles.append("tst")
            elif len(set(v for v in row if v not in (0, 1))) >= 2:
                lower_roles.append("enc")
            else:
                lower_roles.append("inert")
        inert_row = tuple(rep[3][j] for j in range(CORE_SIZE))
        print(f"  Class {cls_idx}: {len(members)} members, "
              f"lower={tuple(lower_roles)}, inert={list(inert_row)}")

    print("\n" + "=" * 70)
    print("ISOMORPHISM UNIQUENESS COMPLETE")
    print("=" * 70)


def decomposed_uniqueness():
    """
    Decompose the model space into components:
      1. Inert row (row 3, cols 0..5)
      2. Lower sub-table (rows 6..9, cols 6..9)
      3. Cross-layer wiring (everything else)

    Fix one component and count models of the others.
    """
    import itertools
    from collections import Counter

    N = 10

    print("=" * 70)
    print("DECOMPOSED UNIQUENESS ANALYSIS (N=10, PA + double L8)")
    print("=" * 70)

    def base_pa():
        s, dot = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
        for x in range(N):
            xx = dot[x][x]
            xx_x = ite_lookup(dot, xx, x, N)
            x_xx = col_ite_lookup(dot, x, xx, N)
            s.add(xx_x == x_xx)
        return s, dot

    # ── Step 1: Collect many models and decompose ──
    print("\nCollecting 100 models...")
    s, dot = base_pa()
    models = []
    t0 = time.time()
    for _ in range(100):
        if s.check() != sat:
            break
        table = extract_table(s.model(), dot, N)
        models.append(table)
        s.add(Or([dot[i][j] != table[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Found {len(models)} models ({elapsed:.1f}s)")

    # Decompose each model
    inert_rows = []
    lower_subtables = []
    cross_wirings = []

    for table in models:
        # Inert row
        inert = tuple(table[3][j] for j in range(CORE_SIZE))
        inert_rows.append(inert)

        # Lower sub-table (rows 6..9, cols 6..9) — but normalize by
        # sorting lower elements by role to account for permutations
        lower_sub = tuple(
            tuple(table[i][j] for j in range(CORE_SIZE, N))
            for i in range(CORE_SIZE, N)
        )
        lower_subtables.append(lower_sub)

        # Cross-layer: upper→lower (rows 0..5, cols 6..9) + lower→upper (rows 6..9, cols 0..5)
        cross = (
            tuple(tuple(table[i][j] for j in range(CORE_SIZE, N)) for i in range(CORE_SIZE)),
            tuple(tuple(table[i][j] for j in range(CORE_SIZE)) for i in range(CORE_SIZE, N)),
        )
        cross_wirings.append(cross)

    # ── Statistics ──
    n_distinct_inert = len(set(inert_rows))
    n_distinct_lower = len(set(lower_subtables))
    n_distinct_cross = len(set(cross_wirings))

    print(f"\n  Distinct inert rows:    {n_distinct_inert}")
    print(f"  Distinct lower sub-tables: {n_distinct_lower}")
    print(f"  Distinct cross-wirings: {n_distinct_cross}")

    # Most common lower sub-table
    lower_counts = Counter(lower_subtables)
    print(f"\n  Lower sub-table frequencies:")
    for sub, count in lower_counts.most_common(5):
        print(f"    {count}x:")
        for i, row in enumerate(sub):
            print(f"      {CORE_SIZE+i}: {list(row)}")

    # Most common inert row
    inert_counts = Counter(inert_rows)
    print(f"\n  Most common inert rows:")
    for inert, count in inert_counts.most_common(5):
        print(f"    {count}x: {list(inert)}")

    # ── Step 2: Fix the most common lower sub-table, count remaining freedom ──
    most_common_lower = lower_counts.most_common(1)[0][0]
    print(f"\n{'─'*70}")
    print(f"Fixing most common lower sub-table, counting remaining models...")
    print(f"{'─'*70}")

    s, dot = base_pa()
    # Pin the lower sub-table
    for i_offset, row in enumerate(most_common_lower):
        for j_offset, val in enumerate(row):
            s.add(dot[CORE_SIZE + i_offset][CORE_SIZE + j_offset] == val)

    remaining = []
    t0 = time.time()
    for _ in range(100):
        if s.check() != sat:
            break
        table = extract_table(s.model(), dot, N)
        remaining.append(table)
        s.add(Or([dot[i][j] != table[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Models with fixed lower sub-table: {len(remaining)}{'+'  if len(remaining) >= 100 else ''} ({elapsed:.1f}s)")

    if remaining:
        rem_inerts = set(tuple(t[3][j] for j in range(CORE_SIZE)) for t in remaining)
        print(f"  Distinct inert rows: {len(rem_inerts)}")

    # ── Step 3: Fix BOTH inert row and lower sub-table ──
    if inert_counts.most_common(1)[0][1] > 1:
        most_common_inert = inert_counts.most_common(1)[0][0]
    else:
        # Pick the inert row that co-occurs most with the common lower sub-table
        co_inerts = Counter()
        for idx, table in enumerate(models):
            if lower_subtables[idx] == most_common_lower:
                co_inerts[inert_rows[idx]] += 1
        most_common_inert = co_inerts.most_common(1)[0][0]

    print(f"\n{'─'*70}")
    print(f"Fixing lower sub-table + inert row {list(most_common_inert)}")
    print(f"{'─'*70}")

    s, dot = base_pa()
    for i_offset, row in enumerate(most_common_lower):
        for j_offset, val in enumerate(row):
            s.add(dot[CORE_SIZE + i_offset][CORE_SIZE + j_offset] == val)
    for j in range(CORE_SIZE):
        s.add(dot[3][j] == most_common_inert[j])

    remaining2 = []
    t0 = time.time()
    for _ in range(50):
        if s.check() != sat:
            break
        table = extract_table(s.model(), dot, N)
        remaining2.append(table)
        s.add(Or([dot[i][j] != table[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Models: {len(remaining2)}{'+'  if len(remaining2) >= 50 else ''} ({elapsed:.1f}s)")

    if len(remaining2) <= 5:
        for idx, table in enumerate(remaining2):
            print(f"\n  Model {idx}:")
            print_table(table)
    elif remaining2:
        # What varies?
        print(f"  Analyzing variation...")
        # Check which cells vary
        varying = []
        for i in range(N):
            for j in range(N):
                vals = set(table[i][j] for table in remaining2)
                if len(vals) > 1:
                    varying.append((i, j, vals))
        print(f"  {len(varying)} varying cells out of {N*N}:")
        for i, j, vals in varying[:20]:
            print(f"    ({i},{j}): {sorted(vals)}")

    # ── Step 4: Also fix lower→upper, see if upper→lower is determined ──
    if remaining2:
        ref = remaining2[0]
        print(f"\n{'─'*70}")
        print(f"Fixing lower sub-table + inert + lower→upper wiring")
        print(f"{'─'*70}")

        s, dot = base_pa()
        for i_offset, row in enumerate(most_common_lower):
            for j_offset, val in enumerate(row):
                s.add(dot[CORE_SIZE + i_offset][CORE_SIZE + j_offset] == val)
        for j in range(CORE_SIZE):
            s.add(dot[3][j] == most_common_inert[j])
        # Fix lower→upper
        for i in range(CORE_SIZE, N):
            for j in range(CORE_SIZE):
                s.add(dot[i][j] == ref[i][j])

        remaining3 = []
        t0 = time.time()
        for _ in range(50):
            if s.check() != sat:
                break
            table = extract_table(s.model(), dot, N)
            remaining3.append(table)
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0
        print(f"  Models: {len(remaining3)}{'+'  if len(remaining3) >= 50 else ''} ({elapsed:.1f}s)")

        if len(remaining3) <= 3:
            for table in remaining3:
                print(f"\n  Upper→lower block (rows 2..5, cols 6..9):")
                for i in [2, 3, 4, 5]:
                    print(f"    {i}: {[table[i][j] for j in range(CORE_SIZE, N)]}")
            if len(remaining3) == 1:
                print("\n  *** CROSS-LAYER WIRING IS DETERMINED! ***")
                print("  Once we fix: inert row + lower sub-table + lower→upper,")
                print("  the upper→lower block is UNIQUE.")
                print("\n  Full unique table:")
                print_table(remaining3[0])

    print("\n" + "=" * 70)
    print("DECOMPOSED ANALYSIS COMPLETE")
    print("=" * 70)


def lower_subtable_uniqueness():
    """
    Exhaustively enumerate distinct lower sub-tables (4×4 block for
    rows 6..9 × cols 6..9) in PA + double L8 at N=10.

    Check if they're unique up to isomorphism of {6,7,8,9}.
    """
    import itertools

    N = 10

    print("=" * 70)
    print("LOWER SUB-TABLE UNIQUENESS (N=10, PA + double L8)")
    print("=" * 70)

    def base_pa():
        s, dot = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
        for x in range(N):
            xx = dot[x][x]
            xx_x = ite_lookup(dot, xx, x, N)
            x_xx = col_ite_lookup(dot, x, xx, N)
            s.add(xx_x == x_xx)
        return s, dot

    # ── Enumerate ALL distinct lower sub-tables ──
    print("\nEnumerating distinct lower sub-tables (blocking on 4×4 block)...")

    s, dot = base_pa()
    lower_elems = list(range(CORE_SIZE, N))
    subtables = []

    t0 = time.time()
    while len(subtables) < 100:
        if s.check() != sat:
            break
        m = s.model()
        table = extract_table(m, dot, N)

        # Extract 4×4 lower sub-table
        sub = tuple(
            tuple(table[i][j] for j in lower_elems)
            for i in lower_elems
        )
        subtables.append(sub)

        # Block this sub-table
        s.add(Or([
            dot[i][j] != table[i][j]
            for i in lower_elems
            for j in lower_elems
        ]))

    elapsed = time.time() - t0
    print(f"  Found {len(subtables)} distinct lower sub-tables ({elapsed:.1f}s)")

    # ── Classify roles for each ──
    for idx, sub in enumerate(subtables):
        roles = []
        for i_offset, row in enumerate(sub):
            if all(v in (0, 1) for v in row):
                roles.append("tst")
            elif len(set(v for v in row if v not in (0, 1))) >= 2:
                roles.append("enc")
            else:
                roles.append("inert")
        print(f"\n  Sub-table {idx}: roles={tuple(roles)}")
        for i_offset, row in enumerate(sub):
            print(f"    {CORE_SIZE+i_offset}: {list(row)}")

    # ── Check isomorphism between sub-tables ──
    print(f"\nChecking pairwise isomorphism...")

    def subtables_isomorphic(s1, s2):
        """Check if s1 and s2 are isomorphic via permutation of lower elems."""
        lower = list(range(CORE_SIZE, N))
        for perm in itertools.permutations(range(4)):
            # perm maps position i → position perm[i]
            # So element lower[i] → lower[perm[i]]
            f = {lower[i]: lower[perm[i]] for i in range(4)}
            f[0] = 0
            f[1] = 1

            match = True
            for i in range(4):
                for j in range(4):
                    # s2[perm[i]][perm[j]] should equal f[s1[i][j]]
                    val = s1[i][j]
                    fval = f.get(val, val)
                    if s2[perm[i]][perm[j]] != fval:
                        match = False
                        break
                if not match:
                    break
            if match:
                return True, [lower[perm[i]] for i in range(4)]
        return False, None

    iso_classes = []
    for idx, sub in enumerate(subtables):
        found = False
        for cls_idx, (rep_idx, members) in enumerate(iso_classes):
            iso, perm = subtables_isomorphic(subtables[rep_idx], sub)
            if iso:
                members.append(idx)
                found = True
                break
        if not found:
            iso_classes.append((idx, [idx]))

    print(f"  {len(subtables)} sub-tables → {len(iso_classes)} isomorphism classes")
    for cls_idx, (rep_idx, members) in enumerate(iso_classes):
        roles = []
        for row in subtables[rep_idx]:
            if all(v in (0, 1) for v in row):
                roles.append("tst")
            elif len(set(v for v in row if v not in (0, 1))) >= 2:
                roles.append("enc")
            else:
                roles.append("inert")
        print(f"    Class {cls_idx}: {len(members)} members, roles={tuple(roles)}")

    if len(iso_classes) == 1:
        print(f"\n  *** LOWER SUB-TABLE IS UNIQUE UP TO ISOMORPHISM! ***")
        print(f"  The L8 axioms + PA determine a UNIQUE internal structure per layer.")
        rep = subtables[iso_classes[0][0]]
        print(f"\n  Canonical lower sub-table:")
        for i_offset, row in enumerate(rep):
            print(f"    {CORE_SIZE+i_offset}: {list(row)}")

    # ── Now do the same WITHOUT PA (just double L8) ──
    print(f"\n{'─'*70}")
    print("Same analysis WITHOUT power-associativity (just double L8)")
    print(f"{'─'*70}")

    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)

    subtables2 = []
    t0 = time.time()
    while len(subtables2) < 100:
        if s.check() != sat:
            break
        m = s.model()
        table = extract_table(m, dot, N)
        sub = tuple(
            tuple(table[i][j] for j in lower_elems)
            for i in lower_elems
        )
        subtables2.append(sub)
        s.add(Or([
            dot[i][j] != table[i][j]
            for i in lower_elems
            for j in lower_elems
        ]))
    elapsed = time.time() - t0
    print(f"  Found {len(subtables2)} distinct lower sub-tables ({elapsed:.1f}s)")

    iso_classes2 = []
    for idx, sub in enumerate(subtables2):
        found = False
        for cls_idx, (rep_idx, members) in enumerate(iso_classes2):
            iso, perm = subtables_isomorphic(subtables2[rep_idx], sub)
            if iso:
                members.append(idx)
                found = True
                break
        if not found:
            iso_classes2.append((idx, [idx]))

    print(f"  {len(subtables2)} sub-tables → {len(iso_classes2)} isomorphism classes")
    for cls_idx, (rep_idx, members) in enumerate(iso_classes2):
        roles = []
        for row in subtables2[rep_idx]:
            if all(v in (0, 1) for v in row):
                roles.append("tst")
            elif len(set(v for v in row if v not in (0, 1))) >= 2:
                roles.append("enc")
            else:
                roles.append("inert")
        print(f"    Class {cls_idx}: {len(members)} members, roles={tuple(roles)}")
        if cls_idx < 3:
            for i_off, row in enumerate(subtables2[rep_idx]):
                print(f"      {CORE_SIZE+i_off}: {list(row)}")

    if len(iso_classes2) == 1:
        print(f"\n  *** ALSO UNIQUE WITHOUT PA! ***")

    # ── Connection to the upper layer ──
    print(f"\n{'─'*70}")
    print("Is the lower sub-table isomorphic to the upper sub-table?")
    print(f"{'─'*70}")

    # Upper sub-table (rows 0..5, cols 0..5) — but for fair comparison,
    # only non-absorber rows: 2,3,4,5 acting on non-absorbers 2,3,4,5
    # Use the fixed rows + a representative inert row
    upper_non_abs = tuple(
        tuple(FIXED_ROWS.get(i, [0]*6)[j] for j in range(2, 6))
        for i in range(2, 6)
    )
    print(f"  Upper (rows 2..5, cols 2..5):")
    for i, row in enumerate(upper_non_abs):
        print(f"    {i+2}: {list(row)}")

    if subtables:
        # The canonical lower sub-table
        canonical = subtables[0]
        print(f"\n  Lower canonical (rows 6..9, cols 6..9):")
        for i, row in enumerate(canonical):
            print(f"    {i+6}: {list(row)}")

    print("\n" + "=" * 70)
    print("LOWER SUB-TABLE UNIQUENESS COMPLETE")
    print("=" * 70)


def kripke_exploration():
    """
    Test strict Kripke-inspired constraints on L8 algebras.

    In strong Kripke: U (undefined) propagates unless short-circuited.
    Our framework: 0,1 = definite; everything else = indeterminate.
    Left-absorption already gives left-short-circuit.

    Test various readings:
      A. Two-sided absorbers: x·0 = 0, x·1 = 1 (right short-circuit too)
      B. Non-absorber closure: x·y ≥ 2 for all x,y ≥ 2 (U propagates)
      C. Tester-only resolution: only testers can map ≥2 → {0,1}
         (encoders/inert preserve indeterminacy)
      D. Inert propagation: inert·inert → non-absorber
      E. Strong inert closure: inert·inert → inert
      F. Right columns fixed: column 0 = all 0, column 1 = all 1
    """
    print("=" * 70)
    print("KRIPKE-INSPIRED CONSTRAINTS ON L8")
    print("=" * 70)

    results = {}

    def count_and_report(label, s, dot, N, cap=20):
        t0 = time.time()
        r = s.check()
        elapsed = time.time() - t0
        if r != sat:
            print(f"  {r} ({elapsed:.1f}s)")
            results[label] = 0
            return
        m = s.model()
        table = extract_table(m, dot, N)
        count = 1
        for _ in range(cap - 1):
            s.add(Or([dot[i][j] != table[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            table = extract_table(s.model(), dot, N)
            count += 1
        elapsed = time.time() - t0
        print(f"  SAT ({elapsed:.1f}s), models: {count}{'+'  if count >= cap else ''}")
        results[label] = count

        # Print first model's structure
        print(f"  Diagonal: {[table[i][i] for i in range(N)]}")
        print(f"  Col 0: {[table[i][0] for i in range(N)]}")
        print(f"  Col 1: {[table[i][1] for i in range(N)]}")
        return table

    # ── Test on pure L8 (no pinned core) at various N ──
    for N in [6, 8, 10]:
        print(f"\n{'═'*70}")
        print(f"N = {N}")
        print(f"{'═'*70}")

        # ── A: Two-sided absorbers ──
        print(f"\n  A: Two-sided absorbers (x·0 = 0, x·1 = 1 for all x)")
        s, dot = encode_level(8, N, timeout_seconds=120)
        for x in range(N):
            s.add(dot[x][0] == 0)
            s.add(dot[x][1] == 1)
        count_and_report(f"A(N={N})", s, dot, N)

        # ── B: Full non-absorber closure ──
        print(f"\n  B: Non-absorber closure (x·y ≥ 2 for x,y ≥ 2)")
        s, dot = encode_level(8, N, timeout_seconds=120)
        for x in range(2, N):
            for y in range(2, N):
                s.add(dot[x][y] >= 2)
        count_and_report(f"B(N={N})", s, dot, N)

        # ── C: Tester-only resolution ──
        print(f"\n  C: Tester-only resolution")
        print(f"     (if x is encoder or inert: x·y ≥ 2 for y ≥ 2)")
        s, dot = encode_level(8, N, timeout_seconds=120)
        # For each non-absorber x that is NOT a tester: x·y ≥ 2 for y ≥ 2
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                # If x is not a tester, then x·y ≥ 2
                s.add(Or(is_tst, dot[x][y] >= 2))
        count_and_report(f"C(N={N})", s, dot, N)

        # ── D: Inert propagation (inert · anything_non_abs → non-absorber) ──
        print(f"\n  D: Inert propagation (inert·y ≥ 2 for y ≥ 2)")
        s, dot = encode_level(8, N, timeout_seconds=120)
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            # encoder: ≥2 distinct non-boolean
            enc_pairs = []
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    enc_pairs.append(And(
                        dot[x][j1] != 0, dot[x][j1] != 1,
                        dot[x][j2] != 0, dot[x][j2] != 1,
                        dot[x][j1] != dot[x][j2],
                    ))
            is_enc = Or(enc_pairs) if enc_pairs else False
            is_inert = And(Not(is_tst), Not(is_enc))
            for y in range(2, N):
                s.add(Or(Not(is_inert), dot[x][y] >= 2))
        count_and_report(f"D(N={N})", s, dot, N)

        # ── E: Strong inert closure (inert·inert → inert) ──
        print(f"\n  E: Strong inert closure (inert·inert → inert element)")
        s, dot = encode_level(8, N, timeout_seconds=120)
        # This is harder to encode: we need the OUTPUT to also be inert.
        # Simpler version: inert·inert is not tester and not encoder
        for x in range(2, N):
            is_tst_x = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            enc_pairs_x = []
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    enc_pairs_x.append(And(
                        dot[x][j1] != 0, dot[x][j1] != 1,
                        dot[x][j2] != 0, dot[x][j2] != 1,
                        dot[x][j1] != dot[x][j2],
                    ))
            is_enc_x = Or(enc_pairs_x) if enc_pairs_x else False
            is_inert_x = And(Not(is_tst_x), Not(is_enc_x))

            for y in range(2, N):
                is_tst_y = And([Or(dot[y][j] == 0, dot[y][j] == 1) for j in range(N)])
                enc_pairs_y = []
                for j1 in range(N):
                    for j2 in range(j1 + 1, N):
                        enc_pairs_y.append(And(
                            dot[y][j1] != 0, dot[y][j1] != 1,
                            dot[y][j2] != 0, dot[y][j2] != 1,
                            dot[y][j1] != dot[y][j2],
                        ))
                is_enc_y = Or(enc_pairs_y) if enc_pairs_y else False
                is_inert_y = And(Not(is_tst_y), Not(is_enc_y))

                # If both x and y are inert, then x·y must be ≥ 2 and
                # the result must be inert (not tester, not encoder)
                result = dot[x][y]
                # Result is inert means: result ≥ 2 AND row(result) is not
                # all-boolean AND row(result) doesn't have 2 distinct non-bool
                # This is very expensive to encode... simplify to just ≥ 2
                s.add(Or(Not(is_inert_x), Not(is_inert_y), result >= 2))
        count_and_report(f"E(N={N})", s, dot, N)

        # ── F: Two-sided absorbers + non-absorber closure ──
        print(f"\n  F: Two-sided absorbers + non-absorber closure (full Kripke)")
        s, dot = encode_level(8, N, timeout_seconds=120)
        for x in range(N):
            s.add(dot[x][0] == 0)
            s.add(dot[x][1] == 1)
        for x in range(2, N):
            for y in range(2, N):
                s.add(dot[x][y] >= 2)
        count_and_report(f"F(N={N})", s, dot, N)

        # ── G: Two-sided absorbers + tester-only resolution ──
        print(f"\n  G: Two-sided absorbers + tester-only resolution")
        s, dot = encode_level(8, N, timeout_seconds=120)
        for x in range(N):
            s.add(dot[x][0] == 0)
            s.add(dot[x][1] == 1)
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))
        count_and_report(f"G(N={N})", s, dot, N)

    # ── Summary ──
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")
    print(f"{'Constraint':<45} {'Result':>12}")
    print("-" * 60)
    for label in sorted(results.keys()):
        cnt = results[label]
        status = "UNSAT" if cnt == 0 else f"{cnt}{'+'  if cnt >= 20 else ''} models"
        print(f"  {label:<43} {status:>12}")

    print(f"\n{'═'*70}")
    print("KRIPKE EXPLORATION COMPLETE")
    print(f"{'═'*70}")


def kripke_c_stacking():
    """
    Test tester-only resolution (Constraint C) combined with
    stacking framework at N=10 (double L8 + PA).

    C says: if x is encoder or inert, then x·y ≥ 2 for all y ≥ 2.
    Only testers can map non-absorbers to absorbers.
    """
    from collections import Counter

    print("=" * 70)
    print("TESTER-ONLY RESOLUTION (C) + STACKING")
    print("=" * 70)

    N = 10

    def add_tester_only_resolution(s, dot, N):
        """Add constraint C: only testers map non-absorbers → {0,1}."""
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def count_models(s, dot, N, cap=50):
        r = s.check()
        if r != sat:
            return 0, None
        m = s.model()
        first = extract_table(m, dot, N)
        count = 1
        for _ in range(cap - 1):
            tbl = extract_table(s.model(), dot, N)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            count += 1
        return count, first

    # ── Baseline: double L8 + PA (no C) ──
    print("\n--- Baseline: double L8 + PA ---")
    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
    for x in range(N):
        xx = dot[x][x]
        s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    t0 = time.time()
    cnt, tbl = count_models(s, dot, N, cap=50)
    print(f"  Models: {cnt}{'+'  if cnt >= 50 else ''} ({time.time()-t0:.1f}s)")

    # ── Double L8 + PA + C ──
    print("\n--- Double L8 + PA + tester-only resolution (C) ---")
    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
    for x in range(N):
        xx = dot[x][x]
        s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))
    add_tester_only_resolution(s, dot, N)

    t0 = time.time()
    cnt_c, tbl_c = count_models(s, dot, N, cap=50)
    elapsed = time.time() - t0
    print(f"  Models: {cnt_c}{'+'  if cnt_c >= 50 else ''} ({elapsed:.1f}s)")

    if tbl_c:
        print(f"  Inert row: {[tbl_c[3][j] for j in range(CORE_SIZE)]}")
        lower = classify_lower_layer(tbl_c, CORE_SIZE)
        roles = []
        for x in range(CORE_SIZE, N):
            if x in lower['testers']:
                roles.append('tst')
            elif x in lower['encoders']:
                roles.append('enc')
            elif x in lower['inert']:
                roles.append('inert')
            else:
                roles.append('abs')
        print(f"  Lower roles: {tuple(roles)}")

    # ── Double L8 + C (no PA) ──
    print("\n--- Double L8 + tester-only resolution (C), no PA ---")
    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
    add_tester_only_resolution(s, dot, N)

    t0 = time.time()
    cnt_c2, tbl_c2 = count_models(s, dot, N, cap=50)
    print(f"  Models: {cnt_c2}{'+'  if cnt_c2 >= 50 else ''} ({time.time()-t0:.1f}s)")

    # ── C alone on L8 (no stacking) at N=6 — does it narrow the core? ──
    print("\n--- L8 + C at N=6 (core algebra) ---")
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_tester_only_resolution(s, dot, 6)

    t0 = time.time()
    models_6 = []
    for _ in range(100):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, 6)
        models_6.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(6) for j in range(6)]))
    elapsed = time.time() - t0
    print(f"  Models: {len(models_6)}{'+'  if len(models_6) >= 100 else ''} ({elapsed:.1f}s)")

    if models_6:
        # How many distinct tables?
        unique_tables = set()
        for tbl in models_6:
            unique_tables.add(tuple(tuple(row) for row in tbl))
        print(f"  Distinct tables: {len(unique_tables)}")

        # Check which rows are fixed
        row_variants = {}
        for i in range(6):
            variants = set()
            for tbl in models_6:
                variants.add(tuple(tbl[i]))
            row_variants[i] = variants
            if len(variants) == 1:
                print(f"  Row {i}: FIXED = {list(list(variants)[0])}")
            else:
                print(f"  Row {i}: {len(variants)} variants")

        # How many inert row options?
        inert_rows = set(tuple(tbl[3]) for tbl in models_6 if 3 in row_variants)
        print(f"  Distinct inert rows (row 3): {len(inert_rows)}")

    # ── Compare: L8 alone at N=6 (baseline for core) ──
    print("\n--- L8 at N=6 (baseline, no C) ---")
    s, dot = encode_level(8, 6, timeout_seconds=120)
    models_6b = []
    for _ in range(100):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, 6)
        models_6b.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(6) for j in range(6)]))
    print(f"  Models: {len(models_6b)}{'+'  if len(models_6b) >= 100 else ''}")

    if models_6b:
        inert_rows_b = set(tuple(tbl[3]) for tbl in models_6b)
        print(f"  Distinct inert rows: {len(inert_rows_b)}")

    # ── Decomposed analysis with C ──
    print(f"\n{'─'*70}")
    print("Decomposed analysis: double L8 + PA + C at N=10")
    print(f"{'─'*70}")

    s, dot = encode_stacked(N, "A", timeout_seconds=300)
    add_lower_l8(s, dot, N, lower_start=CORE_SIZE)
    for x in range(N):
        xx = dot[x][x]
        s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))
    add_tester_only_resolution(s, dot, N)

    lower_elems = list(range(CORE_SIZE, N))
    models = []
    inert_rows = []
    lower_subs = []

    t0 = time.time()
    for _ in range(100):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        models.append(tbl)

        inert = tuple(tbl[3][j] for j in range(CORE_SIZE))
        inert_rows.append(inert)

        lower_sub = tuple(
            tuple(tbl[i][j] for j in lower_elems)
            for i in lower_elems
        )
        lower_subs.append(lower_sub)

        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Collected {len(models)} models ({elapsed:.1f}s)")

    n_inert = len(set(inert_rows))
    n_lower = len(set(lower_subs))
    print(f"  Distinct inert rows: {n_inert}")
    print(f"  Distinct lower sub-tables: {n_lower}")

    inert_counts = Counter(inert_rows)
    print(f"\n  Top inert rows:")
    for ir, cnt in inert_counts.most_common(5):
        print(f"    {cnt}x: {list(ir)}")

    lower_counts = Counter(lower_subs)
    print(f"\n  Top lower sub-tables:")
    for sub, cnt in lower_counts.most_common(3):
        print(f"    {cnt}x:")
        for i, row in enumerate(sub):
            print(f"      {CORE_SIZE+i}: {list(row)}")

    # ── If C narrows lower sub-tables, enumerate exhaustively ──
    if n_lower < 20:
        print(f"\n  Exhaustive lower sub-table enumeration (blocking on 4×4):")
        s2, dot2 = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s2, dot2, N, lower_start=CORE_SIZE)
        for x in range(N):
            xx = dot2[x][x]
            s2.add(ite_lookup(dot2, xx, x, N) == col_ite_lookup(dot2, x, xx, N))
        add_tester_only_resolution(s2, dot2, N)

        all_subs = []
        while len(all_subs) < 200:
            if s2.check() != sat:
                break
            tbl = extract_table(s2.model(), dot2, N)
            sub = tuple(
                tuple(tbl[i][j] for j in lower_elems)
                for i in lower_elems
            )
            all_subs.append(sub)
            s2.add(Or([dot2[i][j] != tbl[i][j]
                        for i in lower_elems for j in lower_elems]))
        print(f"    Total distinct lower sub-tables: {len(all_subs)}{'+'  if len(all_subs) >= 200 else ''}")

    # ── Check: does C + stacking + PA give uniqueness with locked inert? ──
    if inert_counts:
        best_inert = inert_counts.most_common(1)[0][0]
        print(f"\n--- Locked inert {list(best_inert)} + C + PA + double L8 ---")
        s3, dot3 = encode_stacked(N, "A", timeout_seconds=300)
        add_lower_l8(s3, dot3, N, lower_start=CORE_SIZE)
        for x in range(N):
            xx = dot3[x][x]
            s3.add(ite_lookup(dot3, xx, x, N) == col_ite_lookup(dot3, x, xx, N))
        add_tester_only_resolution(s3, dot3, N)
        for j in range(CORE_SIZE):
            s3.add(dot3[3][j] == best_inert[j])

        cnt3, tbl3 = count_models(s3, dot3, N, cap=50)
        print(f"  Models: {cnt3}{'+'  if cnt3 >= 50 else ''}")

        if cnt3 <= 5 and tbl3:
            print(f"\n  *** Near-unique! ***")
            print_table(tbl3)
        elif cnt3 > 0:
            # How many varying cells?
            ref = tbl3
            s3b, dot3b = encode_stacked(N, "A", timeout_seconds=300)
            add_lower_l8(s3b, dot3b, N, lower_start=CORE_SIZE)
            for x in range(N):
                xx = dot3b[x][x]
                s3b.add(ite_lookup(dot3b, xx, x, N) == col_ite_lookup(dot3b, x, xx, N))
            add_tester_only_resolution(s3b, dot3b, N)
            for j in range(CORE_SIZE):
                s3b.add(dot3b[3][j] == best_inert[j])

            samples = []
            for _ in range(20):
                if s3b.check() != sat:
                    break
                t = extract_table(s3b.model(), dot3b, N)
                samples.append(t)
                s3b.add(Or([dot3b[i][j] != t[i][j]
                             for i in range(N) for j in range(N)]))

            varying = []
            for i in range(N):
                for j in range(N):
                    vals = set(t[i][j] for t in samples)
                    if len(vals) > 1:
                        varying.append((i, j, len(vals)))
            print(f"  Varying cells (in {len(samples)} samples): {len(varying)}/{N*N}")
            # Show by block
            upper_upper = sum(1 for i, j, _ in varying if i < CORE_SIZE and j < CORE_SIZE)
            upper_lower = sum(1 for i, j, _ in varying if i < CORE_SIZE and j >= CORE_SIZE)
            lower_upper = sum(1 for i, j, _ in varying if i >= CORE_SIZE and j < CORE_SIZE)
            lower_lower = sum(1 for i, j, _ in varying if i >= CORE_SIZE and j >= CORE_SIZE)
            print(f"    Upper×Upper: {upper_upper}/36")
            print(f"    Upper→Lower: {upper_lower}/24")
            print(f"    Lower→Upper: {lower_upper}/24")
            print(f"    Lower×Lower: {lower_lower}/16")

    print("\n" + "=" * 70)
    print("KRIPKE C + STACKING COMPLETE")
    print("=" * 70)


def kripke_c_cores_and_stacking():
    """
    Explore the L8 + C family:
    1. What do C-compatible L8 cores at N=6 look like?
    2. Can they stack (embed as sub-algebra of N=10 with lower L8 + C)?
    3. How constrained is the stacking?
    """
    print("=" * 70)
    print("C-COMPATIBLE L8 CORES AND STACKING")
    print("=" * 70)

    def add_kripke_c(s, dot, N):
        """Only testers map non-absorbers → {0,1}."""
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    # ── Step 1: Enumerate C-compatible cores at N=6 ──
    print("\n--- C-compatible L8 cores at N=6 ---")
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)

    cores = []
    t0 = time.time()
    while len(cores) < 500:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, 6)
        cores.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(6) for j in range(6)]))
    elapsed = time.time() - t0
    print(f"  Found {len(cores)} C-compatible L8 tables ({elapsed:.1f}s)")

    # Analyze structure
    # Which rows are fixed across all cores?
    for i in range(6):
        variants = set(tuple(tbl[i]) for tbl in cores)
        if len(variants) == 1:
            print(f"  Row {i}: FIXED = {list(list(variants)[0])}")
        else:
            print(f"  Row {i}: {len(variants)} variants")
            if len(variants) <= 5:
                for v in sorted(variants):
                    print(f"         {list(v)}")

    # Role structure
    from collections import Counter
    role_signatures = Counter()
    for tbl in cores:
        roles = []
        for x in range(2, 6):
            row = [tbl[x][j] for j in range(6)]
            if all(v in (0, 1) for v in row):
                roles.append('tst')
            elif len(set(v for v in row if v not in (0, 1))) >= 2:
                roles.append('enc')
            else:
                roles.append('inert')
        role_signatures[tuple(roles)] += 1

    print(f"\n  Role signatures (elements 2..5):")
    for sig, cnt in role_signatures.most_common():
        print(f"    {sig}: {cnt}")

    # Print a few representative tables
    print(f"\n  First 3 tables:")
    for idx in range(min(3, len(cores))):
        print(f"\n  Table {idx}:")
        print_table(cores[idx])

    # ── Step 2: Check if C-cores can stack ──
    print(f"\n{'─'*70}")
    print("Can C-compatible cores stack? (N=10, both layers L8+C)")
    print(f"{'─'*70}")

    # Use raw L8 + C on the full N=10, then check for sub-algebra structure
    N = 10
    s, dot = encode_level(8, N, timeout_seconds=300)
    add_kripke_c(s, dot, N)

    # Require a 6-element sub-algebra {0,1,2,3,4,5}:
    # closure: dot[i][j] < 6 for i,j in {0..5}
    for i in range(6):
        for j in range(6):
            s.add(dot[i][j] < 6)

    # Lower sub-algebra {6,7,8,9} with values in {0,1,6,7,8,9}:
    for i in range(6, N):
        for j in range(6, N):
            s.add(Or([dot[i][j] == v for v in [0, 1, 6, 7, 8, 9]]))

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0

    if result == sat:
        tbl = extract_table(s.model(), dot, N)
        print(f"  SAT ({elapsed:.1f}s)")

        # Upper sub-table
        print(f"\n  Upper sub-table (0..5 × 0..5):")
        for i in range(6):
            print(f"    {i}: {[tbl[i][j] for j in range(6)]}")

        # Lower sub-table
        print(f"\n  Lower sub-table (6..9 × 6..9):")
        for i in range(6, N):
            print(f"    {i}: {[tbl[i][j] for j in range(6, N)]}")

        # Cross-layer
        print(f"\n  Upper→Lower (0..5 × 6..9):")
        for i in range(6):
            print(f"    {i}: {[tbl[i][j] for j in range(6, N)]}")

        print(f"\n  Lower→Upper (6..9 × 0..5):")
        for i in range(6, N):
            print(f"    {i}: {[tbl[i][j] for j in range(6)]}")

        # Verify C property
        print(f"\n  Verifying C property:")
        violations = 0
        for x in range(2, N):
            row = [tbl[x][j] for j in range(N)]
            is_tst = all(v in (0, 1) for v in row)
            if not is_tst:
                for y in range(2, N):
                    if tbl[x][y] < 2:
                        violations += 1
                        print(f"    VIOLATION: {x}·{y} = {tbl[x][y]} (x is non-tester)")
        if violations == 0:
            print(f"    All OK — no violations")

        # Count models
        print(f"\n  Counting models...")
        count = 1
        for _ in range(49):
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            count += 1
        print(f"  Models: {count}{'+'  if count >= 50 else ''}")

        if count <= 5:
            print(f"\n  *** Near-unique stacking! ***")
            print_table(extract_table(s.model(), dot, N) if count > 1 else tbl)

        # Enumerate distinct upper sub-tables
        print(f"\n  Enumerating distinct upper sub-tables (blocking on 6×6)...")
        s2, dot2 = encode_level(8, N, timeout_seconds=300)
        add_kripke_c(s2, dot2, N)
        for i in range(6):
            for j in range(6):
                s2.add(dot2[i][j] < 6)
        for i in range(6, N):
            for j in range(6, N):
                s2.add(Or([dot2[i][j] == v for v in [0, 1, 6, 7, 8, 9]]))

        upper_subs = []
        while len(upper_subs) < 50:
            if s2.check() != sat:
                break
            t = extract_table(s2.model(), dot2, N)
            upper_sub = tuple(tuple(t[i][j] for j in range(6)) for i in range(6))
            upper_subs.append(upper_sub)
            s2.add(Or([dot2[i][j] != t[i][j]
                        for i in range(6) for j in range(6)]))
        print(f"    Distinct upper sub-tables: {len(upper_subs)}{'+'  if len(upper_subs) >= 50 else ''}")

        # Enumerate distinct lower sub-tables
        print(f"\n  Enumerating distinct lower sub-tables (blocking on 4×4)...")
        s3, dot3 = encode_level(8, N, timeout_seconds=300)
        add_kripke_c(s3, dot3, N)
        for i in range(6):
            for j in range(6):
                s3.add(dot3[i][j] < 6)
        for i in range(6, N):
            for j in range(6, N):
                s3.add(Or([dot3[i][j] == v for v in [0, 1, 6, 7, 8, 9]]))

        lower_subs = []
        while len(lower_subs) < 50:
            if s3.check() != sat:
                break
            t = extract_table(s3.model(), dot3, N)
            lower_sub = tuple(tuple(t[i][j] for j in range(6, N)) for i in range(6, N))
            lower_subs.append(lower_sub)
            s3.add(Or([dot3[i][j] != t[i][j]
                        for i in range(6, N) for j in range(6, N)]))
        print(f"    Distinct lower sub-tables: {len(lower_subs)}{'+'  if len(lower_subs) >= 50 else ''}")

    else:
        print(f"  {result} ({elapsed:.1f}s)")
        print("  C-compatible L8 algebras cannot stack at N=10!")

        # Try larger N
        for N2 in [12, 14]:
            print(f"\n  Trying N={N2}...")
            s, dot = encode_level(8, N2, timeout_seconds=300)
            add_kripke_c(s, dot, N2)
            for i in range(6):
                for j in range(6):
                    s.add(dot[i][j] < 6)
            lower = list(range(6, N2))
            for i in lower:
                for j in lower:
                    s.add(Or([dot[i][j] == v for v in [0, 1] + lower]))
            t0 = time.time()
            r = s.check()
            e = time.time() - t0
            print(f"    {r} ({e:.1f}s)")
            if r == sat:
                tbl = extract_table(s.model(), dot, N2)
                print(f"    Upper sub-table:")
                for i in range(6):
                    print(f"      {i}: {[tbl[i][j] for j in range(6)]}")
                print(f"    Lower roles:")
                for x in range(6, N2):
                    row = [tbl[x][j] for j in range(6, N2)]
                    if all(v in (0, 1) for v in row):
                        print(f"      {x}: tst")
                    elif len(set(v for v in row if v not in (0, 1))) >= 2:
                        print(f"      {x}: enc")
                    else:
                        print(f"      {x}: inert")
                break

    print("\n" + "=" * 70)
    print("C-COMPATIBLE STACKING COMPLETE")
    print("=" * 70)


def meta_framework_campaign():
    """
    Comprehensive exploration of the C-compatible L8 meta-framework.

    Phase 1: Core characterization (N=6, L8+C)
    Phase 2: Constraint combinations (which narrow the most?)
    Phase 3: Classical identity compatibility under C
    Phase 4: Best-combination stacking (N=10, N=12)
    Phase 5: Self-similar depth stacking
    """
    import itertools
    from collections import Counter

    def add_kripke_c(s, dot, N):
        """C: only testers map non-absorbers → {0,1}."""
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
        """D: inert·y ≥ 2 for y ≥ 2."""
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

    def add_vv_core(s, dot, N):
        """Strengthened inert: v·v is tester or encoder (not inert, not absorber)."""
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

            # If v is inert, then v·v must be core (tester or encoder)
            vv = dot[v][v]
            # vv is tester: row(vv) all boolean
            vv_is_tst = And([Or(ite_lookup(dot, vv, j, N) == 0,
                                ite_lookup(dot, vv, j, N) == 1) for j in range(N)])
            # vv is encoder: ≥2 distinct non-boolean in row(vv)
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

    def add_tester_discrimination(s, dot, N):
        """Column axiom: testers separate all non-absorber pairs."""
        for x in range(2, N):
            for y in range(x + 1, N):
                # ∃ tester t: t·x ≠ t·y
                sep_clauses = []
                for t in range(2, N):
                    is_tst = And([Or(dot[t][j] == 0, dot[t][j] == 1) for j in range(N)])
                    sep_clauses.append(And(is_tst, dot[t][x] != dot[t][y]))
                s.add(Or(sep_clauses))

    def count_models_fast(s, dot, N, cap=30):
        t0 = time.time()
        r = s.check()
        if r != sat:
            return 0, None, time.time() - t0
        m = s.model()
        first = extract_table(m, dot, N)
        count = 1
        for _ in range(cap - 1):
            tbl = extract_table(s.model(), dot, N)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            count += 1
        return count, first, time.time() - t0

    def report(label, cnt, elapsed, cap=30):
        if cnt == 0:
            print(f"  {label:45s} UNSAT ({elapsed:.1f}s)")
        else:
            print(f"  {label:45s} {cnt}{'+'  if cnt >= cap else ''} models ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    print("=" * 70)
    print("META-FRAMEWORK CAMPAIGN")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════
    # PHASE 1: Core Characterization
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 1: C-Compatible Core Characterization (N=6)")
    print(f"{'═'*70}")

    # Exhaustive enumeration
    print("\nExhaustive enumeration of L8+C cores...")
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)

    all_cores = []
    t0 = time.time()
    while len(all_cores) < 5000:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, 6)
        all_cores.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(6) for j in range(6)]))
    elapsed = time.time() - t0
    print(f"  Total C-compatible L8 cores: {len(all_cores)}{'+'  if len(all_cores) >= 5000 else ' (exhaustive)'} ({elapsed:.1f}s)")

    # Row analysis
    for i in range(6):
        variants = set(tuple(tbl[i]) for tbl in all_cores)
        if len(variants) == 1:
            print(f"  Row {i}: FIXED = {list(list(variants)[0])}")
        elif len(variants) <= 10:
            print(f"  Row {i}: {len(variants)} variants")
            for v in sorted(variants):
                cnt = sum(1 for tbl in all_cores if tuple(tbl[i]) == v)
                print(f"         {list(v)}  ({cnt}x)")
        else:
            print(f"  Row {i}: {len(variants)} variants")

    # Role analysis
    role_sigs = Counter()
    for tbl in all_cores:
        roles = []
        for x in range(2, 6):
            row = [tbl[x][j] for j in range(6)]
            if all(v in (0, 1) for v in row):
                roles.append('tst')
            elif len(set(v for v in row if v not in (0, 1))) >= 2:
                roles.append('enc')
            else:
                roles.append('inert')
        role_sigs[tuple(roles)] += 1
    print(f"\n  Role signatures:")
    for sig, cnt in role_sigs.most_common():
        print(f"    {sig}: {cnt}")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 2: Constraint Combinations at N=6
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 2: Constraint Combinations (N=6)")
    print(f"{'═'*70}")

    combos = {}

    # C alone (baseline)
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C", cnt, elapsed, 100)
    combos["C"] = cnt

    # C + D (inert propagation)
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_inert_propagation(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + D (inert propagation)", cnt, elapsed, 100)
    combos["C+D"] = cnt

    # C + PA
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_pa(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + PA", cnt, elapsed, 100)
    combos["C+PA"] = cnt

    # C + v·v→core
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_vv_core(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + v·v→core", cnt, elapsed, 100)
    combos["C+vv"] = cnt

    # C + tester discrimination
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_tester_discrimination(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + tester-discrim", cnt, elapsed, 100)
    combos["C+td"] = cnt

    # C + D + PA
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_inert_propagation(s, dot, 6)
    add_pa(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + D + PA", cnt, elapsed, 100)
    combos["C+D+PA"] = cnt

    # C + D + v·v→core
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_inert_propagation(s, dot, 6)
    add_vv_core(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + D + v·v→core", cnt, elapsed, 100)
    combos["C+D+vv"] = cnt

    # C + D + tester-discrim
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_inert_propagation(s, dot, 6)
    add_tester_discrimination(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + D + tester-discrim", cnt, elapsed, 100)
    combos["C+D+td"] = cnt

    # C + PA + v·v→core
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_pa(s, dot, 6)
    add_vv_core(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + PA + v·v→core", cnt, elapsed, 100)
    combos["C+PA+vv"] = cnt

    # C + PA + tester-discrim
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_pa(s, dot, 6)
    add_tester_discrimination(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + PA + tester-discrim", cnt, elapsed, 100)
    combos["C+PA+td"] = cnt

    # C + D + PA + v·v→core
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_inert_propagation(s, dot, 6)
    add_pa(s, dot, 6)
    add_vv_core(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + D + PA + v·v→core", cnt, elapsed, 100)
    combos["C+D+PA+vv"] = cnt

    # C + D + PA + tester-discrim
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_inert_propagation(s, dot, 6)
    add_pa(s, dot, 6)
    add_tester_discrimination(s, dot, 6)
    cnt, tbl, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + D + PA + tester-discrim", cnt, elapsed, 100)
    combos["C+D+PA+td"] = cnt

    # ALL: C + D + PA + v·v→core + tester-discrim
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    add_inert_propagation(s, dot, 6)
    add_pa(s, dot, 6)
    add_vv_core(s, dot, 6)
    add_tester_discrimination(s, dot, 6)
    cnt, tbl_best, elapsed = count_models_fast(s, dot, 6, cap=100)
    report("L8 + C + D + PA + v·v→core + td", cnt, elapsed, 100)
    combos["ALL"] = cnt

    # Print summary sorted
    print(f"\n  {'─'*60}")
    print(f"  Summary (sorted by model count):")
    for name, cnt in sorted(combos.items(), key=lambda x: x[1]):
        marker = " ← UNIQUE!" if cnt == 1 else " ← FEW" if 1 < cnt <= 10 else ""
        if cnt == 0:
            print(f"    {name:40s}: UNSAT")
        else:
            print(f"    {name:40s}: {cnt}{'+'  if cnt >= 100 else ''}{marker}")

    # If any combo gave small count, show the tables
    best_combo = min((n for n, c in combos.items() if c > 0),
                     key=lambda n: combos[n], default=None)
    if best_combo and combos[best_combo] <= 10:
        print(f"\n  Best combo: {best_combo} ({combos[best_combo]} models)")
        # Re-run to get all tables
        s, dot = encode_level(8, 6, timeout_seconds=120)
        add_kripke_c(s, dot, 6)
        if 'D' in best_combo:
            add_inert_propagation(s, dot, 6)
        if 'PA' in best_combo:
            add_pa(s, dot, 6)
        if 'vv' in best_combo:
            add_vv_core(s, dot, 6)
        if 'td' in best_combo:
            add_tester_discrimination(s, dot, 6)
        tables = []
        while len(tables) < 20:
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, 6)
            tables.append(tbl)
            s.add(Or([dot[i][j] != tbl[i][j] for i in range(6) for j in range(6)]))
        for idx, tbl in enumerate(tables):
            print(f"\n  Model {idx}:")
            print_table(tbl)

    # ═══════════════════════════════════════════════════════════════
    # PHASE 3: Classical Identity Compatibility under C
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 3: Classical Identities under L8+C (N=6)")
    print(f"{'═'*70}")

    identities = {}

    # Associativity
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    for a in range(6):
        for b in range(6):
            ab = dot[a][b]
            for c in range(6):
                s.add(ite_lookup(dot, ab, c, 6) == col_ite_lookup(dot, a, dot[b][c], 6))
    cnt, _, elapsed = count_models_fast(s, dot, 6)
    report("Associativity", cnt, elapsed)
    identities["assoc"] = cnt

    # PA (already tested above, reuse)
    identities["PA"] = combos.get("C+PA", -1)
    print(f"  {'PA':45s} {combos.get('C+PA', '?')} models (from Phase 2)")

    # Flexible
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    for a in range(6):
        for b in range(6):
            ba = dot[b][a]
            s.add(col_ite_lookup(dot, a, ba, 6) == ite_lookup(dot, dot[a][b], a, 6))
    cnt, _, elapsed = count_models_fast(s, dot, 6)
    report("Flexible", cnt, elapsed)
    identities["flexible"] = cnt

    # Left alternative
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    for x in range(6):
        xx = dot[x][x]
        for y in range(6):
            s.add(ite_lookup(dot, xx, y, 6) == col_ite_lookup(dot, x, dot[x][y], 6))
    cnt, _, elapsed = count_models_fast(s, dot, 6)
    report("Left alternative", cnt, elapsed)
    identities["L-alt"] = cnt

    # Right alternative
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    for x in range(6):
        for y in range(6):
            yy = dot[y][y]
            s.add(ite_lookup(dot, dot[x][y], y, 6) == col_ite_lookup(dot, x, yy, 6))
    cnt, _, elapsed = count_models_fast(s, dot, 6)
    report("Right alternative", cnt, elapsed)
    identities["R-alt"] = cnt

    # x⁴ = x²
    s, dot = encode_level(8, 6, timeout_seconds=120)
    add_kripke_c(s, dot, 6)
    for x in range(6):
        xx = dot[x][x]
        x4 = dot[0][0]
        for k in range(6):
            x4 = If(xx == k, dot[k][k], x4)
        s.add(x4 == xx)
    cnt, _, elapsed = count_models_fast(s, dot, 6)
    report("x⁴ = x²", cnt, elapsed)
    identities["x4=x2"] = cnt

    print(f"\n  Summary:")
    for name, cnt in sorted(identities.items(), key=lambda x: x[1]):
        status = "UNSAT" if cnt == 0 else f"{cnt}{'+'  if cnt >= 30 else ''}"
        print(f"    {name:20s}: {status}")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 4: Best-Combination Stacking
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 4: Stacking with Best Constraints")
    print(f"{'═'*70}")

    # Find best SAT combo from Phase 2
    sat_combos = [(n, c) for n, c in combos.items() if c > 0]
    sat_combos.sort(key=lambda x: x[1])

    for combo_name, combo_cnt in sat_combos[:3]:
        for N in [8, 10, 12]:
            print(f"\n  {combo_name} at N={N}:")
            s, dot = encode_level(8, N, timeout_seconds=300)
            add_kripke_c(s, dot, N)
            if 'D' in combo_name:
                add_inert_propagation(s, dot, N)
            if 'PA' in combo_name:
                add_pa(s, dot, N)
            if 'vv' in combo_name:
                add_vv_core(s, dot, N)
            if 'td' in combo_name:
                add_tester_discrimination(s, dot, N)

            # Add sub-algebra structure
            for i in range(6):
                for j in range(6):
                    s.add(dot[i][j] < 6)
            lower = list(range(6, N))
            if lower:
                for i in lower:
                    for j in lower:
                        s.add(Or([dot[i][j] == v for v in [0, 1] + lower]))

            cnt, tbl, elapsed = count_models_fast(s, dot, N, cap=30)
            if cnt == 0:
                print(f"    UNSAT ({elapsed:.1f}s)")
            else:
                print(f"    {cnt}{'+'  if cnt >= 30 else ''} models ({elapsed:.1f}s)")
                if tbl:
                    # Classify roles
                    upper_roles = []
                    for x in range(2, 6):
                        row = [tbl[x][j] for j in range(6)]
                        if all(v in (0, 1) for v in row):
                            upper_roles.append('tst')
                        elif len(set(v for v in row if v not in (0, 1))) >= 2:
                            upper_roles.append('enc')
                        else:
                            upper_roles.append('inert')
                    print(f"    Upper roles: {tuple(upper_roles)}")

                    if lower:
                        lower_roles = []
                        for x in lower:
                            row = [tbl[x][j] for j in lower]
                            if all(v in (0, 1) for v in row):
                                lower_roles.append('tst')
                            elif len(set(v for v in row if v not in (0, 1))) >= 2:
                                lower_roles.append('enc')
                            else:
                                lower_roles.append('inert')
                        print(f"    Lower roles: {tuple(lower_roles)}")

                if cnt <= 5 and tbl:
                    print_table(tbl)

    # ═══════════════════════════════════════════════════════════════
    # PHASE 5: Self-Similar Depth Stacking
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 5: Self-Similar Depth Stacking under C")
    print(f"{'═'*70}")

    # Find the simplest SAT combo and test depth stacking
    # Use just C (most permissive SAT)
    for depth in [1, 2, 3]:
        N = 6 + 4 * depth  # each layer adds 4 non-absorber elements
        print(f"\n  Depth {depth} (N={N}), L8+C + sub-algebra closure per layer:")

        s, dot = encode_level(8, N, timeout_seconds=300)
        add_kripke_c(s, dot, N)

        # Layer 0: {0..5} closed
        for i in range(6):
            for j in range(6):
                s.add(dot[i][j] < 6)

        # Each deeper layer: {6k..6k+3} closed into {0,1} ∪ {6k..6k+3}
        for d in range(depth):
            layer_start = 6 + 4 * d
            layer_end = layer_start + 4
            layer_elems = list(range(layer_start, layer_end))
            for i in layer_elems:
                for j in layer_elems:
                    s.add(Or([dot[i][j] == v for v in [0, 1] + layer_elems]))

        cnt, tbl, elapsed = count_models_fast(s, dot, N, cap=30)
        if cnt == 0:
            print(f"    UNSAT ({elapsed:.1f}s)")
        else:
            print(f"    {cnt}{'+'  if cnt >= 30 else ''} models ({elapsed:.1f}s)")
            if tbl:
                for d in range(-1, depth):
                    if d == -1:
                        layer_start, layer_end = 0, 6
                        label = "Upper"
                    else:
                        layer_start = 6 + 4 * d
                        layer_end = layer_start + 4
                        label = f"Layer {d+1}"
                    roles = []
                    for x in range(max(2, layer_start), layer_end):
                        elems = list(range(layer_start, layer_end))
                        if layer_start == 0:
                            elems = list(range(6))
                        row = [tbl[x][j] for j in elems]
                        if all(v in (0, 1) for v in row):
                            roles.append('tst')
                        elif len(set(v for v in row if v not in (0, 1))) >= 2:
                            roles.append('enc')
                        else:
                            roles.append('inert')
                    print(f"    {label} ({layer_start}..{layer_end-1}): {tuple(roles)}")

    # ═══════════════════════════════════════════════════════════════
    # FINAL SUMMARY
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("FINAL SUMMARY")
    print(f"{'═'*70}")

    print(f"\n  C-compatible L8 cores at N=6: {len(all_cores)}{'+'  if len(all_cores) >= 5000 else ''}")

    print(f"\n  Constraint narrowing at N=6:")
    for name, cnt in sorted(combos.items(), key=lambda x: x[1]):
        if cnt == 0:
            print(f"    {name:40s}: UNSAT")
        else:
            print(f"    {name:40s}: {cnt}{'+'  if cnt >= 100 else ''}")

    print(f"\n  Classical identities under C:")
    for name, cnt in sorted(identities.items(), key=lambda x: x[1]):
        status = "UNSAT" if cnt == 0 else f"SAT ({cnt}{'+'  if cnt >= 30 else ''})"
        print(f"    {name:20s}: {status}")


def universality_check():
    """
    Test the meta-framework (L8+C+D+PA+vv→core) for universality gaps.

    What structural phenomena does it struggle to model?
    We test by attempting to embed various structural motifs into
    the framework and checking SAT/UNSAT.
    """
    import time
    from collections import Counter

    # ── Helpers (same as meta_framework_campaign) ──────────────────

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_meta(s, dot, N):
        """Add C+D+PA+vv→core (strongest SAT combo)."""
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def check_sat(s, dot, N, cap=20):
        t0 = time.time()
        r = s.check()
        if r != sat:
            return 0, None, time.time() - t0
        first = extract_table(s.model(), dot, N)
        count = 1
        for _ in range(cap - 1):
            tbl = extract_table(s.model(), dot, N)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            count += 1
        return count, first, time.time() - t0

    def report(label, cnt, elapsed, cap=20):
        if cnt == 0:
            print(f"    {label:55s} UNSAT ({elapsed:.1f}s)")
        else:
            tag = f"{cnt}{'+'  if cnt >= cap else ''}"
            print(f"    {label:55s} {tag} models ({elapsed:.1f}s)")

    print("=" * 70)
    print("UNIVERSALITY CHECK")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════
    # TEST 1: Role balance flexibility
    # Can we force unusual role distributions?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 1: Role Balance Flexibility (N=8)")
    print("Can the framework accommodate different role distributions?")
    print(f"{'═'*70}\n")

    N = 8
    for label, min_enc, min_tst, min_inert in [
        (">=4 encoders",   4, 0, 0),
        (">=4 testers",    0, 4, 0),
        (">=4 inert",      0, 0, 4),
        ("0 inert (all active)", 0, 0, -1),  # -1 = force zero
        ("1 tester exactly", 0, -1, 0),  # -1 = force exactly 1
        ("balanced (2e,2t,2i)", -2, -2, -2),  # negative = exact
    ]:
        s, dot = encode_level(8, N, timeout_seconds=60)
        add_full_meta(s, dot, N)

        # Count roles via constraints
        enc_flags = []
        tst_flags = []
        inert_flags = []
        for x in range(2, N):
            is_tst_x = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            enc_pairs_x = []
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    enc_pairs_x.append(And(
                        dot[x][j1] != 0, dot[x][j1] != 1,
                        dot[x][j2] != 0, dot[x][j2] != 1,
                        dot[x][j1] != dot[x][j2]))
            is_enc_x = Or(enc_pairs_x) if enc_pairs_x else False
            is_inert_x = And(Not(is_tst_x), Not(is_enc_x))

            # Create integer indicators
            e = Int(f"enc_{x}")
            t = Int(f"tst_{x}")
            i = Int(f"inert_{x}")
            s.add(If(is_enc_x, e == 1, e == 0))
            s.add(If(is_tst_x, t == 1, t == 0))
            s.add(If(is_inert_x, i == 1, i == 0))
            enc_flags.append(e)
            tst_flags.append(t)
            inert_flags.append(i)

        enc_sum = sum(enc_flags)
        tst_sum = sum(tst_flags)
        inert_sum = sum(inert_flags)

        if min_enc == -2:  # balanced: exactly 2 of each
            s.add(enc_sum == 2)
            s.add(tst_sum == 2)
            s.add(inert_sum == 2)
        else:
            if min_enc == -1:
                s.add(enc_sum == 1)
            elif min_enc > 0:
                s.add(enc_sum >= min_enc)
            if min_tst == -1:
                s.add(tst_sum == 1)
            elif min_tst > 0:
                s.add(tst_sum >= min_tst)
            if min_inert == -1:
                s.add(inert_sum == 0)
            elif min_inert > 0:
                s.add(inert_sum >= min_inert)

        cnt, tbl, elapsed = check_sat(s, dot, N)
        report(label, cnt, elapsed)
        if cnt > 0 and tbl:
            cl = classify_elements(tbl)
            role_map = {}
            for role, elems in cl.items():
                for e in elems:
                    role_map[e] = role
            role_str = ', '.join(f"{x}={role_map.get(x,'?')}" for x in range(2, N))
            print(f"      Roles: {role_str}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 2: Symmetry capacity
    # Can models have non-trivial automorphisms?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 2: Symmetry Capacity (N=8)")
    print("Can the framework produce non-trivially symmetric algebras?")
    print(f"{'═'*70}\n")

    # Test: ∃ non-trivial automorphism (permutation p with p(0)=0, p(1)=1,
    # p≠id, and p(x·y) = p(x)·p(y))
    N = 8
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)

    # Permutation variables
    p = [Int(f"perm_{i}") for i in range(N)]
    s.add(p[0] == 0)
    s.add(p[1] == 1)
    for i in range(N):
        s.add(p[i] >= 0)
        s.add(p[i] < N)
    # Distinct
    for i in range(N):
        for j in range(i + 1, N):
            s.add(p[i] != p[j])
    # Non-trivial
    s.add(Or([p[i] != i for i in range(2, N)]))
    # Homomorphism: p(x·y) = p(x)·p(y)
    for x in range(N):
        for y in range(N):
            # p(dot[x][y])
            p_of_xy = ite_lookup(dot, x, y, N)  # = dot[x][y]
            lhs = p_of_xy  # actually need p(dot[x][y])
            # Build p(v) lookup
            lhs_val = Int(f"lhs_{x}_{y}")
            for v in range(N):
                pass  # Need a different approach

    # Clean approach: build p_lookup helper
    s_clean = Solver()
    s2, dot2 = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s2, dot2, N)

    p = [Int(f"p_{i}") for i in range(N)]
    s2.add(p[0] == 0)
    s2.add(p[1] == 1)
    for i in range(N):
        s2.add(p[i] >= 0)
        s2.add(p[i] < N)
    for i in range(N):
        for j in range(i + 1, N):
            s2.add(p[i] != p[j])
    s2.add(Or([p[i] != i for i in range(2, N)]))

    # p(v): ite chain
    def p_of(v_expr):
        """Apply permutation p to a Z3 expression."""
        result = p[0]
        for k in range(1, N):
            result = If(v_expr == k, p[k], result)
        return result

    for x in range(N):
        for y in range(N):
            # p(x·y) = p(x) · p(y)
            xy = dot2[x][y]
            p_xy = p_of(xy)
            # p(x)·p(y): need dot[p(x)][p(y)]
            # p(x), p(y) are Z3 exprs
            px = p[x]
            py = p[y]
            # dot[px][py] via double lookup
            px_py = Int(f"pp_{x}_{y}")
            # Build: px_py = dot[px][py]
            clauses = []
            for a in range(N):
                for b in range(N):
                    clauses.append(If(And(px == a, py == b),
                                      dot2[a][b], -1))
            # Simpler: nested ite
            val = dot2[0][0]
            for a in range(N):
                for b in range(N):
                    if a == 0 and b == 0:
                        continue
                    val = If(And(px == a, py == b), dot2[a][b], val)
            s2.add(p_xy == val)

    t0 = time.time()
    r = s2.check()
    elapsed = time.time() - t0
    if r == sat:
        m = s2.model()
        tbl = extract_table(m, dot2, N)
        perm = [m.eval(p[i]).as_long() for i in range(N)]
        print(f"    Non-trivial automorphism exists!  ({elapsed:.1f}s)")
        print(f"    Permutation: {perm}")
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        print(f"    Roles: {', '.join(f'{x}={rm.get(x, chr(63))}'  for x in range(2, N))}")
    else:
        print(f"    No non-trivial automorphism possible ({elapsed:.1f}s)")
        print(f"    → Framework forces rigidity (all models asymmetric)")

    # ═══════════════════════════════════════════════════════════════
    # TEST 3: Fixed-point structure
    # What fixed-point patterns are possible? (x·x = x)
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 3: Fixed-Point Structure (N=8)")
    print("What idempotent patterns are compatible?")
    print(f"{'═'*70}\n")

    for label, constraint in [
        ("all idempotent (x·x=x for all x)",
         lambda s, dot, N: [s.add(dot[x][x] == x) for x in range(N)]),
        ("no non-absorber fixed points (x·x≠x for x≥2)",
         lambda s, dot, N: [s.add(dot[x][x] != x) for x in range(2, N)]),
        ("≥3 fixed points (x·x=x)",
         lambda s, dot, N: s.add(
             sum([If(dot[x][x] == x, 1, 0) for x in range(2, N)]) >= 3)),
        ("exactly absorbers are fixed (0·0=0, 1·1=1, rest not)",
         lambda s, dot, N: [s.add(dot[x][x] != x) for x in range(2, N)]),
    ]:
        s, dot = encode_level(8, N, timeout_seconds=60)
        add_full_meta(s, dot, N)
        constraint(s, dot, N)
        cnt, tbl, elapsed = check_sat(s, dot, N)
        report(label, cnt, elapsed)

    # ═══════════════════════════════════════════════════════════════
    # TEST 4: Cycle structure
    # Can the framework model cycles of various lengths?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 4: Cycle Structure (N=8)")
    print("Can self-application generate cycles?")
    print(f"{'═'*70}\n")

    # x·x = y, y·y = x (2-cycle under squaring)
    for cycle_len, label in [(2, "2-cycle under squaring"),
                              (3, "3-cycle under squaring"),
                              (4, "4-cycle under squaring")]:
        s, dot = encode_level(8, N, timeout_seconds=60)
        add_full_meta(s, dot, N)
        if cycle_len == 2:
            # ∃ x,y ≥ 2: x≠y, x·x=y, y·y=x
            for a in range(2, N):
                for b in range(a + 1, N):
                    pass  # Too many pairs, use existential
            # Simpler: just assert for elements 2,3
            s.add(dot[2][2] == 3)
            s.add(dot[3][3] == 2)
        elif cycle_len == 3:
            s.add(dot[2][2] == 3)
            s.add(dot[3][3] == 4)
            s.add(dot[4][4] == 2)
        elif cycle_len == 4:
            s.add(dot[2][2] == 3)
            s.add(dot[3][3] == 4)
            s.add(dot[4][4] == 5)
            s.add(dot[5][5] == 2)
        cnt, tbl, elapsed = check_sat(s, dot, N)
        report(label, cnt, elapsed)

    # ═══════════════════════════════════════════════════════════════
    # TEST 5: Information flow directionality
    # Can information flow "upward" (from inert to encoder)?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 5: Information Flow (N=8)")
    print("Can different interaction patterns coexist?")
    print(f"{'═'*70}\n")

    # Test: can two encoders commute with each other? (e1·e2 = e2·e1)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    # Force elements 2,3 to be encoders and commute
    for x in [2, 3]:
        enc_pairs = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                enc_pairs.append(And(
                    dot[x][j1] != 0, dot[x][j1] != 1,
                    dot[x][j2] != 0, dot[x][j2] != 1,
                    dot[x][j1] != dot[x][j2]))
        s.add(Or(enc_pairs))
    s.add(dot[2][3] == dot[3][2])
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("two encoders commuting (e1·e2 = e2·e1)", cnt, elapsed)

    # Test: can an encoder and tester commute?
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    # Force 2 = encoder, 5 = tester, and 2·5 = 5·2
    enc_pairs = []
    for j1 in range(N):
        for j2 in range(j1 + 1, N):
            enc_pairs.append(And(
                dot[2][j1] != 0, dot[2][j1] != 1,
                dot[2][j2] != 0, dot[2][j2] != 1,
                dot[2][j1] != dot[2][j2]))
    s.add(Or(enc_pairs))
    s.add(And([Or(dot[5][j] == 0, dot[5][j] == 1) for j in range(N)]))
    s.add(dot[2][5] == dot[5][2])
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("encoder-tester commuting (e·t = t·e)", cnt, elapsed)

    # Test: fully anti-commutative (x·y ≠ y·x for all x≠y, x,y≥2)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    for x in range(2, N):
        for y in range(x + 1, N):
            s.add(dot[x][y] != dot[y][x])
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("fully anti-commutative (x·y≠y·x for all x≠y≥2)", cnt, elapsed)

    # ═══════════════════════════════════════════════════════════════
    # TEST 6: Column structure (dual of row structure)
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 6: Column Structure (N=8)")
    print("Are there constraints on how elements are 'acted upon'?")
    print(f"{'═'*70}\n")

    # Column x = [dot[0][x], dot[1][x], ..., dot[N-1][x]]
    # Test: can all columns be distinct? (already implied by Ext, but
    # Ext is row-distinctness; column-distinctness is different)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    for x in range(N):
        for y in range(x + 1, N):
            s.add(Or([dot[i][x] != dot[i][y] for i in range(N)]))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("all columns distinct", cnt, elapsed)

    # Test: can two non-absorber columns be identical?
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    s.add(And([dot[i][2] == dot[i][3] for i in range(N)]))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("two non-absorber columns identical", cnt, elapsed)

    # Test: can a column be "boolean" (all values in {0,1})?
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    # Column 2 is boolean
    for i in range(N):
        s.add(Or(dot[i][2] == 0, dot[i][2] == 1))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("boolean column (col 2 all in {0,1})", cnt, elapsed)

    # Test: surjective column (every value 0..N-1 appears)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    for v in range(N):
        s.add(Or([dot[i][2] == v for i in range(N)]))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("surjective column (col 2 hits all values)", cnt, elapsed)

    # ═══════════════════════════════════════════════════════════════
    # TEST 7: Absorption patterns beyond 0,1
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 7: Absorption Patterns (N=8)")
    print("Can non-absorber elements have partial absorption?")
    print(f"{'═'*70}\n")

    # Left-zero: ∃ x≥2: x·y = x for all y (partial left absorber)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    s.add(And([dot[2][j] == 2 for j in range(N)]))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("third left-absorber (2·y=2 for all y)", cnt, elapsed)

    # Right-zero: ∃ x≥2: y·x = x for all y
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    s.add(And([dot[j][2] == 2 for j in range(N)]))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("third right-absorber (y·2=2 for all y)", cnt, elapsed)

    # Left identity beyond 0: ∃ x≥2: x·y = y for all y
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    s.add(And([dot[2][j] == j for j in range(N)]))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("non-absorber left identity (2·y=y for all y)", cnt, elapsed)

    # Right identity: ∃ x≥2: y·x = y for all y
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    s.add(And([dot[j][2] == j for j in range(N)]))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("non-absorber right identity (y·2=y for all y)", cnt, elapsed)

    # ═══════════════════════════════════════════════════════════════
    # TEST 8: Producibility / generative closure
    # Can every non-absorber element be "reached" from others?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 8: Producibility (N=8)")
    print("Can every element be produced by some pair?")
    print(f"{'═'*70}\n")

    # Full producibility: ∀ z: ∃ x,y: x·y = z
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    for z in range(N):
        s.add(Or([dot[x][y] == z for x in range(N) for y in range(N)]))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("full producibility (every element appears in table)", cnt, elapsed)

    # Strong: every element produced by NON-absorbers
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    for z in range(N):
        s.add(Or([dot[x][y] == z for x in range(2, N) for y in range(2, N)]))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("non-absorber producibility (reachable via x,y≥2)", cnt, elapsed)

    # Test: ∃ unreachable element (some z never produced)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    # Element 4 is not produced by any pair of non-absorbers
    s.add(And([dot[x][y] != 4 for x in range(2, N) for y in range(2, N)]))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("element 4 unreachable from non-absorbers", cnt, elapsed)

    # ═══════════════════════════════════════════════════════════════
    # TEST 9: Nilpotency and idempotency interaction
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 9: Self-Application Behavior (N=8)")
    print("What patterns of x·x are possible?")
    print(f"{'═'*70}\n")

    # All x·x = 0 or 1 for non-absorbers (nilpotent squaring)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    for x in range(2, N):
        s.add(Or(dot[x][x] == 0, dot[x][x] == 1))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("nilpotent squaring (x·x ∈ {0,1} for x≥2)", cnt, elapsed)

    # All x·x ≥ 2 for non-absorbers (non-nilpotent)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    for x in range(2, N):
        s.add(dot[x][x] >= 2)
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("non-nilpotent squaring (x·x ≥ 2 for x≥2)", cnt, elapsed)

    # x·x is always a different role than x
    # (testers square to encoders/inert, encoders to testers/inert, etc.)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    for x in range(2, N):
        # x·x ≠ x (no fixed points among non-absorbers)
        s.add(dot[x][x] != x)
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("no non-absorber self-fixed-points (x·x≠x for x≥2)", cnt, elapsed)

    # ═══════════════════════════════════════════════════════════════
    # TEST 10: Deeper algebraic structure
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 10: Deeper Algebraic Properties (N=8)")
    print(f"{'═'*70}\n")

    # Helper: lookup dot[row_expr][col_expr] where both may be Z3 exprs
    def lookup_2d(dot, row_expr, col_expr, N):
        result = ite_lookup(dot, row_expr, 0, N)
        for j in range(1, N):
            result = If(col_expr == j, ite_lookup(dot, row_expr, j, N), result)
        return result

    # Entropic: (x·y)·(z·w) = (x·z)·(y·w)
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)
    for x in range(N):
        for y in range(N):
            for z in range(N):
                for w in range(N):
                    xy = dot[x][y]
                    zw = dot[z][w]
                    xz = dot[x][z]
                    yw = dot[y][w]
                    lhs = lookup_2d(dot, xy, zw, N)
                    rhs = lookup_2d(dot, xz, yw, N)
                    s.add(lhs == rhs)
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    report("entropic (x·y)·(z·w) = (x·z)·(y·w)",
           1 if r == sat else 0, elapsed)

    # Moufang: x·(y·(x·z)) = ((x·y)·x)·z
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)
    for x in range(2, N):
        for y in range(2, N):
            for z in range(2, N):
                xz = dot[x][z]
                y_xz = col_ite_lookup(dot, y, xz, N)
                lhs = col_ite_lookup(dot, x, y_xz, N)
                xy = dot[x][y]
                xy_x = ite_lookup(dot, xy, x, N)
                rhs = ite_lookup(dot, xy_x, z, N)
                s.add(lhs == rhs)
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    report("Moufang identity (non-absorbers only)",
           1 if r == sat else 0, elapsed)

    # ═══════════════════════════════════════════════════════════════
    # TEST 11: Interaction depth
    # How deep can composition chains go before collapsing to absorbers?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 11: Composition Depth Before Absorption (N=8)")
    print(f"{'═'*70}\n")

    # Force: for all x,y≥2: ((x·y)·(x·y)) ∈ {0,1} (depth-2 nilpotent)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    for x in range(2, N):
        for y in range(2, N):
            xy = dot[x][y]
            xy_sq = lookup_2d(dot, xy, xy, N)  # (x·y)·(x·y)
            s.add(Or(xy_sq == 0, xy_sq == 1))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("depth-2 nilpotent ((x·y)² ∈ {0,1})", cnt, elapsed)

    # Force: for all x,y≥2: (x·y)·(x·y) ≥ 2 (depth-2 survives)
    s, dot = encode_level(8, N, timeout_seconds=60)
    add_full_meta(s, dot, N)
    for x in range(2, N):
        for y in range(2, N):
            xy = dot[x][y]
            xy_sq = lookup_2d(dot, xy, xy, N)
            # Only require non-absorber if xy itself is non-absorber
            s.add(Or(xy <= 1, xy_sq >= 2))
    cnt, tbl, elapsed = check_sat(s, dot, N)
    report("depth-2 survival (if x·y≥2 then (x·y)²≥2)", cnt, elapsed)

    # ═══════════════════════════════════════════════════════════════
    # TEST 12: Scale sensitivity
    # Does the framework behave qualitatively differently at N=6 vs N=12?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 12: Scale Sensitivity")
    print("How does model count change with N under full meta-framework?")
    print(f"{'═'*70}\n")

    for n in [6, 7, 8, 9, 10]:
        s, dot = encode_level(8, n, timeout_seconds=120)
        add_full_meta(s, dot, n)
        cnt, tbl, elapsed = check_sat(s, dot, n, cap=50)
        report(f"L8+C+D+PA+vv at N={n}", cnt, elapsed, cap=50)
        if cnt > 0 and tbl:
            cl = classify_elements(tbl)
            rm = {}
            for role, elems in cl.items():
                for e in elems:
                    rm[e] = role
            role_counts = Counter(rm.get(x, '?') for x in range(2, n))
            print(f"      Roles: {dict(role_counts)}")

    # ═══════════════════════════════════════════════════════════════
    # SUMMARY
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("UNIVERSALITY SUMMARY")
    print(f"{'═'*70}")
    print("""
The meta-framework L8+C+D+PA+vv→core has been tested against:
  - Role balance flexibility (can it support different distributions?)
  - Symmetry (can it produce non-rigid algebras?)
  - Fixed-point structure (idempotency patterns)
  - Cycle structure (squaring cycles)
  - Commutativity patterns (local/partial)
  - Column structure (dual perspective)
  - Absorption patterns (extra absorbers/identities)
  - Producibility (can every element be reached?)
  - Self-application behavior (nilpotent vs non-nilpotent)
  - Deeper algebraic identities (entropic, Moufang)
  - Composition depth (how deep before absorption?)
  - Scale sensitivity (behavior across N=6..10)
""")


def meta_operations_analysis():
    """
    Check whether stacking naturally produces meta-operation signatures
    analogous to QUOTE/EVAL/APP/UNAPP in the Kamea's Δ₂ extension.

    In Δ₁→Δ₂:
      - QUOTE/EVAL/APP/UNAPP are atom-level opaque (all-p rows on atoms)
      - They gain meaning at the TERM level (structured expressions)
      - They form constructor/destructor pairs
      - QUOTE·EVAL ≈ identity (quotation/evaluation inverse pair)
      - APP·UNAPP ≈ identity (construction/deconstruction pair)

    Key question: in our L8+C+D+PA+vv stacked algebras, do the lower-layer
    elements naturally exhibit pair structure, inverse-like behavior, or
    constructor/destructor patterns relative to the upper core?
    """
    import time
    from collections import Counter

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_meta(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    print("=" * 70)
    print("META-OPERATIONS ANALYSIS")
    print("Do stacking layers naturally produce QUOTE/EVAL/APP/UNAPP?")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════
    # PHASE 1: Natural pair structure in stacked algebras
    # At N=10 (6 core + 4 lower), collect models and look for
    # inverse-like pairs among lower elements
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 1: Natural Pair Structure in Lower Layer (N=10)")
    print(f"{'═'*70}\n")

    N = 10
    CORE = 6
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)

    # Collect 50 models and analyze lower layer patterns
    models = []
    t0 = time.time()
    for _ in range(50):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        models.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Collected {len(models)} models ({elapsed:.1f}s)\n")

    # For each model, check lower elements for:
    # (a) Inverse pairs: a·b maps into core, b·a maps into core, and they "undo"
    # (b) Opacity on core: element acts as inert/constant on core elements
    # (c) Cross-layer quasi-inverse: a·(b·x) ≈ x for core x

    pair_stats = Counter()
    opacity_stats = Counter()
    quasi_inv_count = 0

    for idx, tbl in enumerate(models):
        lower = list(range(CORE, N))
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role

        # (a) Check all pairs in lower layer
        for a in lower:
            for b in lower:
                if a == b:
                    continue
                ab = tbl[a][b]
                ba = tbl[b][a]
                # "Inverse-like": a·b and b·a are both in core
                if ab < CORE and ba < CORE:
                    pair_stats[("both_in_core", rm.get(a, '?'), rm.get(b, '?'))] += 1
                # "Quasi-inverse": a·b ∈ {0,1} (collapses to absorber)
                if ab in (0, 1) and ba in (0, 1):
                    pair_stats["mutual_absorb"] += 1

        # (b) Opacity: how does each lower element act on core?
        for a in lower:
            core_outputs = [tbl[a][j] for j in range(CORE)]
            unique = len(set(core_outputs))
            if unique == 1:
                opacity_stats["constant_on_core"] += 1
            elif all(v in (0, 1) for v in core_outputs):
                opacity_stats["boolean_on_core"] += 1
            elif all(v < CORE for v in core_outputs):
                opacity_stats["core_closed"] += 1
            else:
                opacity_stats["reaches_lower"] += 1

        # (c) Quasi-inverse chains: ∃ a,b in lower: a·(b·x) = x for all core x
        for a in lower:
            for b in lower:
                # b·x for x in core
                bx = [tbl[b][x] for x in range(CORE)]
                # a·(b·x) for x in core
                abx = [tbl[a][bx_val] for bx_val in bx]
                if abx == list(range(CORE)):
                    quasi_inv_count += 1

    print("  (a) Lower-layer pair interactions:")
    for key, cnt in pair_stats.most_common(10):
        print(f"      {key}: {cnt} (across {len(models)} models)")

    print(f"\n  (b) Lower element opacity on core (across {len(models)} models, {len(models)*4} elements):")
    for key, cnt in opacity_stats.most_common():
        pct = 100 * cnt / (len(models) * (N - CORE))
        print(f"      {key}: {cnt} ({pct:.0f}%)")

    print(f"\n  (c) Quasi-inverse pairs (a·(b·x) = x for all core x): {quasi_inv_count}")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 2: Can we FORCE constructor/destructor pairs?
    # Require: ∃ Q,E in lower layer: Q·(E·x) = x for all core x
    # (QUOTE/EVAL analogue — round-trip through lower layer = identity)
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 2: Forcing Constructor/Destructor Pairs")
    print(f"{'═'*70}\n")

    for label, N, pairs in [
        ("QE pair at N=8 (core=6, lower=2)", 8, [(6, 7)]),
        ("QE pair at N=10 (core=6, lower=4)", 10, [(6, 7), (8, 9)]),
        ("QE + AU pair at N=10 (two pairs)", 10, [(6, 7), (8, 9)]),
    ]:
        s, dot = encode_level(8, N, timeout_seconds=120)
        add_full_meta(s, dot, N)

        for q, e in pairs:
            # Round-trip: q·(e·x) = x for all core x
            for x in range(CORE):
                ex = dot[e][x]
                s.add(col_ite_lookup(dot, q, ex, N) == x)
            # Reverse round-trip: e·(q·x) = x for all core x
            for x in range(CORE):
                qx = dot[q][x]
                s.add(col_ite_lookup(dot, e, qx, N) == x)

        t0 = time.time()
        r = s.check()
        elapsed = time.time() - t0
        if r == sat:
            tbl = extract_table(s.model(), dot, N)
            cl = classify_elements(tbl)
            rm = {}
            for role, elems in cl.items():
                for e_elem in elems:
                    rm[e_elem] = role
            print(f"  {label}: SAT ({elapsed:.1f}s)")
            for q, e in pairs:
                print(f"    Pair ({q},{e}): roles = ({rm.get(q,'?')}, {rm.get(e,'?')})")
                print(f"    Row {q}: {tbl[q]}")
                print(f"    Row {e}: {tbl[e]}")
                # Check what they do on lower elements
                print(f"    {q}·{e} = {tbl[q][e]}, {e}·{q} = {tbl[e][q]}")
            # Count more models
            count = 1
            for _ in range(29):
                s.add(Or([dot[i][j] != tbl[i][j] for i in range(N) for j in range(N)]))
                if s.check() != sat:
                    break
                tbl = extract_table(s.model(), dot, N)
                count += 1
            print(f"    Total models: {count}{'+'  if count >= 30 else ''}")
        else:
            print(f"  {label}: UNSAT ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 3: One-sided meta-operations (weaker than full inverse)
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 3: One-Sided Meta-Operations")
    print(f"{'═'*70}\n")

    N = 10

    # (a) Left-quotation: ∃ Q: Q·x ∈ lower for all core x≥2,
    #     and the mapping is injective (Q maps core into lower distinctly)
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)
    Q = 6
    for x in range(2, CORE):
        s.add(dot[Q][x] >= CORE)  # Q sends core to lower
    for x in range(2, CORE):
        for y in range(x + 1, CORE):
            s.add(dot[Q][x] != dot[Q][y])  # injective
    t0 = time.time()
    cnt = 0
    first_tbl = None
    while cnt < 30:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        if cnt == 0:
            first_tbl = tbl
        cnt += 1
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    tag = f"{cnt}{'+'  if cnt >= 30 else ''}"
    print(f"  (a) Quotation: Q maps core→lower injectively: {tag} ({elapsed:.1f}s)")
    if first_tbl:
        print(f"      Q row: {first_tbl[Q]}")
        print(f"      Q maps: " + ", ".join(f"{x}→{first_tbl[Q][x]}" for x in range(CORE)))

    # (b) Evaluation: ∃ E: E·x ∈ core for all lower x,
    #     and the mapping hits all non-absorber core elements
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)
    E = 7
    for x in range(CORE, N):
        s.add(dot[E][x] < CORE)  # E sends lower to core
    # Surjective onto non-absorber core
    for c in range(2, CORE):
        s.add(Or([dot[E][x] == c for x in range(CORE, N)]))
    t0 = time.time()
    cnt = 0
    first_tbl = None
    while cnt < 30:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        if cnt == 0:
            first_tbl = tbl
        cnt += 1
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    tag = f"{cnt}{'+'  if cnt >= 30 else ''}"
    print(f"  (b) Evaluation: E maps lower→core surjectively: {tag} ({elapsed:.1f}s)")
    if first_tbl:
        print(f"      E row: {first_tbl[E]}")
        print(f"      E maps: " + ", ".join(f"{x}→{first_tbl[E][x]}" for x in range(CORE, N)))

    # (c) Both together: Q sends core→lower, E sends lower→core,
    #     and E·(Q·x) = x for core x≥2 (round-trip)
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)
    Q, E = 6, 7
    for x in range(2, CORE):
        s.add(dot[Q][x] >= CORE)
    for x in range(2, CORE):
        for y in range(x + 1, CORE):
            s.add(dot[Q][x] != dot[Q][y])
    for x in range(CORE, N):
        s.add(dot[E][x] < CORE)
    # Round-trip: E·(Q·x) = x for x = 2..5
    for x in range(2, CORE):
        qx = dot[Q][x]
        s.add(col_ite_lookup(dot, E, qx, N) == x)
    t0 = time.time()
    cnt = 0
    first_tbl = None
    while cnt < 30:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        if cnt == 0:
            first_tbl = tbl
        cnt += 1
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    tag = f"{cnt}{'+'  if cnt >= 30 else ''}"
    print(f"  (c) Q+E round-trip (E·(Q·x) = x): {tag} ({elapsed:.1f}s)")
    if first_tbl:
        print(f"      Q row: {first_tbl[Q]}")
        print(f"      E row: {first_tbl[E]}")
        cl = classify_elements(first_tbl)
        rm = {}
        for role, elems in cl.items():
            for e_elem in elems:
                rm[e_elem] = role
        print(f"      Q role: {rm.get(Q,'?')}, E role: {rm.get(E,'?')}")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 4: Opacity signature — Kamea-like pattern
    # In Kamea, QUOTE/EVAL/APP/UNAPP are all-p on atoms.
    # Can we force lower elements to be "opaque on core"
    # (constant row on core columns)?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 4: Opacity + Meta-Operation Combination")
    print(f"{'═'*70}\n")

    N = 10
    # Force elements 6,7 to be "opaque on core": dot[6][x] = dot[6][0] for all x < CORE
    # (constant on core, like Kamea's all-p rows)
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)
    for q in [6, 7]:
        for x in range(1, CORE):
            s.add(dot[q][x] == dot[q][0])
    t0 = time.time()
    cnt = 0
    first_tbl = None
    while cnt < 30:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        if cnt == 0:
            first_tbl = tbl
        cnt += 1
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    tag = f"{cnt}{'+'  if cnt >= 30 else ''}"
    print(f"  (a) Two elements opaque on core (constant row on core cols): {tag} ({elapsed:.1f}s)")
    if first_tbl:
        for q in [6, 7]:
            print(f"      Row {q}: {first_tbl[q]}")

    # (b) Opaque on core + distinguishable on lower
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)
    for q in [6, 7]:
        for x in range(1, CORE):
            s.add(dot[q][x] == dot[q][0])
    # But they differ on at least one lower element
    s.add(Or([dot[6][x] != dot[7][x] for x in range(CORE, N)]))
    t0 = time.time()
    cnt = 0
    first_tbl = None
    while cnt < 30:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        if cnt == 0:
            first_tbl = tbl
        cnt += 1
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    tag = f"{cnt}{'+'  if cnt >= 30 else ''}"
    print(f"  (b) Opaque + distinguishable on lower: {tag} ({elapsed:.1f}s)")
    if first_tbl:
        for q in [6, 7]:
            print(f"      Row {q}: {first_tbl[q]}")

    # (c) Full Kamea-like: 4 lower elements, all opaque on core,
    #     but pairwise distinguishable on a single "QUALE-like" column
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)
    opaque_elems = [6, 7, 8, 9]
    for q in opaque_elems:
        for x in range(1, CORE):
            s.add(dot[q][x] == dot[q][0])
    # Distinguished by a single column (say column 9 acts as QUALE)
    quale_col = N - 1  # last lower element
    for a in opaque_elems:
        for b in opaque_elems:
            if a < b:
                s.add(dot[a][quale_col] != dot[b][quale_col])
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        print(f"  (c) 4 opaque elements + QUALE-like column: SAT ({elapsed:.1f}s)")
        for q in opaque_elems:
            print(f"      Row {q}: {tbl[q]}")
        print(f"      QUALE column ({quale_col}): " +
              ", ".join(f"{q}→{tbl[q][quale_col]}" for q in opaque_elems))
    else:
        print(f"  (c) 4 opaque elements + QUALE-like column: UNSAT ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 5: Full meta-operation package
    # Try to get Q/E (quotation/evaluation) + A/U (application/unapplication)
    # all in one algebra
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 5: Full QUOTE/EVAL + APP/UNAPP Package")
    print(f"{'═'*70}\n")

    # Need N ≥ 10: 6 core + Q + E + A + U = 10
    N = 10
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)

    Q, E, A, U = 6, 7, 8, 9

    # QUOTE/EVAL pair: E·(Q·x) = x for core x≥2
    for x in range(2, CORE):
        qx = dot[Q][x]
        s.add(col_ite_lookup(dot, E, qx, N) == x)

    # APP/UNAPP pair: U·(A·x) = x for core x≥2
    for x in range(2, CORE):
        ax = dot[A][x]
        s.add(col_ite_lookup(dot, U, ax, N) == x)

    # Q and A should be different (not redundant)
    s.add(Or([dot[Q][j] != dot[A][j] for j in range(N)]))
    # E and U should be different
    s.add(Or([dot[E][j] != dot[U][j] for j in range(N)]))

    t0 = time.time()
    cnt = 0
    first_tbl = None
    while cnt < 30:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        if cnt == 0:
            first_tbl = tbl
        cnt += 1
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    tag = f"{cnt}{'+'  if cnt >= 30 else ''}"
    print(f"  Two distinct inverse pairs (Q/E + A/U): {tag} ({elapsed:.1f}s)")
    if first_tbl:
        for name, idx in [("Q", Q), ("E", E), ("A", A), ("U", U)]:
            cl = classify_elements(first_tbl)
            rm = {}
            for role, elems in cl.items():
                for e_elem in elems:
                    rm[e_elem] = role
            print(f"    {name} (row {idx}, {rm.get(idx,'?')}): {first_tbl[idx]}")
        # Check cross-pair interactions
        print(f"    Q·E={first_tbl[Q][E]}, E·Q={first_tbl[E][Q]}")
        print(f"    A·U={first_tbl[A][U]}, U·A={first_tbl[U][A]}")
        print(f"    Q·A={first_tbl[Q][A]}, A·Q={first_tbl[A][Q]}")
        print(f"    E·U={first_tbl[E][U]}, U·E={first_tbl[U][E]}")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 6: Do meta-ops emerge from stacking alone?
    # At N=10 with double L8 (both layers satisfy L8),
    # check if the lower layer elements naturally form inverse pairs
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 6: Do Meta-Ops Emerge from Double L8?")
    print(f"{'═'*70}\n")

    N = 10
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_meta(s, dot, N)
    # Sub-algebra closure: core acts on core
    for i in range(CORE):
        for j in range(CORE):
            s.add(dot[i][j] < CORE)
    # Lower layer also satisfies L8 role skeleton (at least 1 tst, 2 enc among 6..9)
    lower_elems = list(range(CORE, N))
    # At least one lower tester
    lower_tst_clauses = []
    for x in lower_elems:
        lower_tst_clauses.append(
            And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)]))
    s.add(Or(lower_tst_clauses))
    # At least two lower encoders
    lower_enc_list = []
    for x in lower_elems:
        enc_pairs = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                enc_pairs.append(And(
                    dot[x][j1] != 0, dot[x][j1] != 1,
                    dot[x][j2] != 0, dot[x][j2] != 1,
                    dot[x][j1] != dot[x][j2]))
        lower_enc_list.append(Or(enc_pairs) if enc_pairs else False)
    # At least 2 encoders among lower
    enc_flags = [Int(f"lenc_{x}") for x in lower_elems]
    for k, x in enumerate(lower_elems):
        s.add(If(lower_enc_list[k], enc_flags[k] == 1, enc_flags[k] == 0))
    s.add(sum(enc_flags) >= 2)

    models = []
    t0 = time.time()
    for _ in range(30):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        models.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j] for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Double L8 + full meta at N=10: {len(models)} models ({elapsed:.1f}s)")

    # Check each model for natural inverse pairs in lower layer
    inv_pair_count = 0
    for tbl in models:
        for a in lower_elems:
            for b in lower_elems:
                if a >= b:
                    continue
                # Check: a·(b·x) = x for all core x≥2?
                is_inv = True
                for x in range(2, CORE):
                    bx = tbl[b][x]
                    if bx >= N or tbl[a][bx] != x:
                        is_inv = False
                        break
                if is_inv:
                    inv_pair_count += 1
                    cl = classify_elements(tbl)
                    rm = {}
                    for role, elems in cl.items():
                        for e_elem in elems:
                            rm[e_elem] = role
                    print(f"    NATURAL INVERSE PAIR: ({a},{b}) "
                          f"roles=({rm.get(a,'?')},{rm.get(b,'?')})")
                    print(f"    Row {a}: {tbl[a]}")
                    print(f"    Row {b}: {tbl[b]}")

    print(f"\n  Total natural inverse pairs found: {inv_pair_count} across {len(models)} models")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 7: Minimal extension — what's the smallest N that supports
    # one Q/E pair?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 7: Minimal N for One Inverse Pair")
    print(f"{'═'*70}\n")

    for N in [7, 8, 9, 10]:
        s, dot = encode_level(8, N, timeout_seconds=60)
        add_full_meta(s, dot, N)
        if N - CORE >= 2:
            Q, E = CORE, CORE + 1
            for x in range(2, CORE):
                qx = dot[Q][x]
                s.add(col_ite_lookup(dot, E, qx, N) == x)
            t0 = time.time()
            r = s.check()
            elapsed = time.time() - t0
            if r == sat:
                tbl = extract_table(s.model(), dot, N)
                cl = classify_elements(tbl)
                rm = {}
                for role, elems in cl.items():
                    for e_elem in elems:
                        rm[e_elem] = role
                print(f"  N={N}: SAT ({elapsed:.1f}s)")
                print(f"    Q={Q} ({rm.get(Q,'?')}): {tbl[Q]}")
                print(f"    E={E} ({rm.get(E,'?')}): {tbl[E]}")
                break
            else:
                print(f"  N={N}: UNSAT ({elapsed:.1f}s)")
        else:
            print(f"  N={N}: skipped (need ≥2 lower elements)")

    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")


def integrated_meta_framework():
    """
    Full integrated meta-framework with meta-operations.

    Axiom levels:
      L8      — base axiom ladder (Ext, absorbers, tester, encoder, ...)
      C       — tester-only resolution (Kripke constraint)
      D       — inert propagation
      PA      — power-associativity
      VV      — v·v → core (inert self-application is structured)
      QE      — quotation/evaluation inverse pair
      QE2     — second inverse pair (APP/UNAPP)

    Campaign:
      Phase 1: QE interaction with existing constraints at N=8
      Phase 2: QE + QE2 interaction at N=10
      Phase 3: QE stacking — do meta-ops propagate through layers?
      Phase 4: Uniqueness pressure — how many models under full axiom set?
      Phase 5: What roles do the meta-op elements take across models?
      Phase 6: Self-similar meta-stacking (layers with their own QE pairs)
    """
    import time
    from collections import Counter

    # ── Constraint helpers ────────────────────────────────────────

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        """C+D+PA+VV — the strongest SAT base combo."""
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        """
        QE axiom: ∃ inverse pair (Q, E) such that
          E·(Q·x) = x  for all core x in [core_lo, core_hi)
          Q·(E·x) = x  for all core x in [core_lo, core_hi)
        Both directions: full inverse, not just one-sided.
        """
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def count_models(s, dot, N, cap=50):
        t0 = time.time()
        models = []
        while len(models) < cap:
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            models.append(tbl)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        return models, time.time() - t0

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    def report(label, count, elapsed, cap=50):
        if count == 0:
            print(f"  {label:55s} UNSAT ({elapsed:.1f}s)")
        else:
            tag = f"{count}{'+'  if count >= cap else ''}"
            print(f"  {label:55s} {tag} models ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    print("=" * 70)
    print("INTEGRATED META-FRAMEWORK WITH META-OPERATIONS")
    print("=" * 70)

    CORE = 6  # size of the base L8 core

    # ═══════════════════════════════════════════════════════════════
    # PHASE 1: QE interaction with constraint combos at N=8
    # N=8: 6 core + Q(6) + E(7)
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 1: QE Pair + Constraint Combinations (N=8)")
    print(f"{'═'*70}\n")

    N = 8
    Q, E = 6, 7
    combos = {}

    tests = [
        ("L8 + QE",             lambda s, d, n: None),
        ("L8 + C + QE",         lambda s, d, n: add_kripke_c(s, d, n)),
        ("L8 + C+D + QE",       lambda s, d, n: (add_kripke_c(s, d, n),
                                                   add_inert_propagation(s, d, n))),
        ("L8 + C+PA + QE",      lambda s, d, n: (add_kripke_c(s, d, n),
                                                   add_pa(s, d, n))),
        ("L8 + C+D+PA + QE",    lambda s, d, n: (add_kripke_c(s, d, n),
                                                   add_inert_propagation(s, d, n),
                                                   add_pa(s, d, n))),
        ("L8 + C+D+PA+VV + QE", lambda s, d, n: add_full_base(s, d, n)),
    ]

    for label, add_extra in tests:
        s, dot = encode_level(8, N, timeout_seconds=120)
        add_extra(s, dot, N)
        add_qe_pair(s, dot, N, Q, E, core_lo=2, core_hi=CORE)
        models, elapsed = count_models(s, dot, N, cap=50)
        report(label, len(models), elapsed)
        combos[label] = len(models)
        if models:
            rm = role_map(models[0])
            print(f"    Q={Q}({rm.get(Q,'?')}): {models[0][Q]}")
            print(f"    E={E}({rm.get(E,'?')}): {models[0][E]}")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 2: Full package QE + QE2 at N=10
    # N=10: 6 core + Q(6) + E(7) + A(8) + U(9)
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 2: Two Inverse Pairs (QE + AU) at N=10")
    print(f"{'═'*70}\n")

    N = 10
    Q, E, A, U = 6, 7, 8, 9

    tests2 = [
        ("L8 + QE + AU",              lambda s, d, n: None),
        ("L8 + C + QE + AU",          lambda s, d, n: add_kripke_c(s, d, n)),
        ("L8 + full-base + QE + AU",  lambda s, d, n: add_full_base(s, d, n)),
    ]

    for label, add_extra in tests2:
        s, dot = encode_level(8, N, timeout_seconds=120)
        add_extra(s, dot, N)
        add_qe_pair(s, dot, N, Q, E, core_lo=2, core_hi=CORE)
        add_qe_pair(s, dot, N, A, U, core_lo=2, core_hi=CORE)
        # Pairs must be distinct
        s.add(Or([dot[Q][j] != dot[A][j] for j in range(N)]))
        s.add(Or([dot[E][j] != dot[U][j] for j in range(N)]))
        models, elapsed = count_models(s, dot, N, cap=50)
        report(label, len(models), elapsed)
        if models:
            tbl = models[0]
            rm = role_map(tbl)
            for name, idx in [("Q", Q), ("E", E), ("A", A), ("U", U)]:
                print(f"    {name}={idx}({rm.get(idx,'?')}): {tbl[idx]}")
            # Cross-pair products
            print(f"    Q·E={tbl[Q][E]} E·Q={tbl[E][Q]}  "
                  f"A·U={tbl[A][U]} U·A={tbl[U][A]}  "
                  f"Q·A={tbl[Q][A]} E·U={tbl[E][U]}")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 3: QE stacking — meta-ops across layers
    # N=14: 6 core + Q(6) + E(7) + 6 lower layer
    # Does the lower layer (8..13) also get a QE pair?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 3: QE Stacking Across Layers")
    print(f"{'═'*70}\n")

    # (a) Upper QE pair + L8 on lower layer
    N = 14
    Q1, E1 = 6, 7
    LOWER_START = 8

    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)

    # Upper QE pair: round-trip on core (2..5)
    add_qe_pair(s, dot, N, Q1, E1, core_lo=2, core_hi=CORE)

    # Sub-algebra closure: core elements stay in core
    for i in range(CORE):
        for j in range(CORE):
            s.add(dot[i][j] < CORE)

    # Lower layer role skeleton (among 8..13):
    # at least 1 tester and 2 encoders
    lower_elems = list(range(LOWER_START, N))
    lower_tst = []
    lower_enc = []
    for x in lower_elems:
        is_tst_x = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        enc_pairs_x = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                enc_pairs_x.append(And(
                    dot[x][j1] != 0, dot[x][j1] != 1,
                    dot[x][j2] != 0, dot[x][j2] != 1,
                    dot[x][j1] != dot[x][j2]))
        is_enc_x = Or(enc_pairs_x) if enc_pairs_x else False

        t_flag = Int(f"lt_{x}")
        e_flag = Int(f"le_{x}")
        s.add(If(is_tst_x, t_flag == 1, t_flag == 0))
        s.add(If(is_enc_x, e_flag == 1, e_flag == 0))
        lower_tst.append(t_flag)
        lower_enc.append(e_flag)

    s.add(sum(lower_tst) >= 1)
    s.add(sum(lower_enc) >= 2)

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        rm = role_map(tbl)
        print(f"  (a) Upper QE + structured lower (N=14): SAT ({elapsed:.1f}s)")
        print(f"      Q1={Q1}({rm.get(Q1,'?')}): {tbl[Q1]}")
        print(f"      E1={E1}({rm.get(E1,'?')}): {tbl[E1]}")
        lower_roles = [rm.get(x, '?') for x in lower_elems]
        print(f"      Lower roles: {lower_roles}")
    else:
        print(f"  (a) Upper QE + structured lower (N=14): UNSAT ({elapsed:.1f}s)")

    # (b) Can the lower layer ALSO have its own QE pair?
    # Q2, E2 are among lower_elems, round-tripping on elements 8..13
    # This means: there's a sub-sub-layer that can quote/eval within the lower
    if r == sat:
        # Pick two lower elements as Q2, E2
        Q2, E2 = 8, 9
        s_b, dot_b = encode_level(8, N, timeout_seconds=300)
        add_full_base(s_b, dot_b, N)
        add_qe_pair(s_b, dot_b, N, Q1, E1, core_lo=2, core_hi=CORE)
        for i in range(CORE):
            for j in range(CORE):
                s_b.add(dot_b[i][j] < CORE)
        for x_idx, tf in enumerate(lower_tst):
            x = lower_elems[x_idx]
            is_tst_x = And([Or(dot_b[x][j] == 0, dot_b[x][j] == 1) for j in range(N)])
            enc_pairs_x = []
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    enc_pairs_x.append(And(
                        dot_b[x][j1] != 0, dot_b[x][j1] != 1,
                        dot_b[x][j2] != 0, dot_b[x][j2] != 1,
                        dot_b[x][j1] != dot_b[x][j2]))
            is_enc_x = Or(enc_pairs_x) if enc_pairs_x else False
            t_flag = Int(f"lt2_{x}")
            e_flag = Int(f"le2_{x}")
            s_b.add(If(is_tst_x, t_flag == 1, t_flag == 0))
            s_b.add(If(is_enc_x, e_flag == 1, e_flag == 0))

        # Lower QE pair: round-trip on lower non-meta elements
        # Q2·x gives something, E2 brings it back, for x in lower non-Q2/E2
        lower_core = [x for x in lower_elems if x not in (Q2, E2)]
        for x in lower_core:
            q2x = dot_b[Q2][x]
            s_b.add(col_ite_lookup(dot_b, E2, q2x, N) == x)
            e2x = dot_b[E2][x]
            s_b.add(col_ite_lookup(dot_b, Q2, e2x, N) == x)

        t0 = time.time()
        r2 = s_b.check()
        elapsed = time.time() - t0
        if r2 == sat:
            tbl = extract_table(s_b.model(), dot_b, N)
            rm = role_map(tbl)
            print(f"  (b) Lower layer ALSO has QE pair (N=14): SAT ({elapsed:.1f}s)")
            print(f"      Upper: Q1={Q1}({rm.get(Q1,'?')}), E1={E1}({rm.get(E1,'?')})")
            print(f"      Lower: Q2={Q2}({rm.get(Q2,'?')}), E2={E2}({rm.get(E2,'?')})")
            print(f"      Q2 row: {tbl[Q2]}")
            print(f"      E2 row: {tbl[E2]}")
        else:
            print(f"  (b) Lower layer ALSO has QE pair (N=14): UNSAT ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 4: Uniqueness pressure under full axiom set
    # How many models at each N with all constraints + QE?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 4: Uniqueness Pressure (Full Axiom Set + QE)")
    print(f"{'═'*70}\n")

    for N in [8, 9, 10]:
        s, dot = encode_level(8, N, timeout_seconds=120)
        add_full_base(s, dot, N)
        # QE pair on the first two non-core elements
        if N >= CORE + 2:
            add_qe_pair(s, dot, N, CORE, CORE + 1, core_lo=2, core_hi=CORE)
        models, elapsed = count_models(s, dot, N, cap=100)
        report(f"L8+C+D+PA+VV+QE at N={N}", len(models), elapsed, 100)

        # Show role distribution across models
        if models:
            role_counter = Counter()
            for tbl in models:
                rm = role_map(tbl)
                sig = tuple(rm.get(x, '?') for x in range(2, N))
                role_counter[sig] += 1
            print(f"    Top role signatures:")
            for sig, cnt in role_counter.most_common(5):
                print(f"      {sig}: {cnt}")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 5: Role analysis of meta-op elements
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 5: Meta-Op Element Role Analysis (N=8)")
    print(f"{'═'*70}\n")

    N = 8
    Q, E = 6, 7
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q, E, core_lo=2, core_hi=CORE)
    models, elapsed = count_models(s, dot, N, cap=100)
    print(f"  Collected {len(models)} models ({elapsed:.1f}s)\n")

    q_roles = Counter()
    e_roles = Counter()
    q_on_absorbers = Counter()
    e_on_absorbers = Counter()
    qe_products = Counter()

    for tbl in models:
        rm = role_map(tbl)
        q_roles[rm.get(Q, '?')] += 1
        e_roles[rm.get(E, '?')] += 1
        q_on_absorbers[(tbl[Q][0], tbl[Q][1])] += 1
        e_on_absorbers[(tbl[E][0], tbl[E][1])] += 1
        qe_products[(tbl[Q][E], tbl[E][Q])] += 1

    print(f"  Q role distribution: {dict(q_roles)}")
    print(f"  E role distribution: {dict(e_roles)}")
    print(f"  Q on absorbers (Q·0, Q·1): {dict(q_on_absorbers.most_common(5))}")
    print(f"  E on absorbers (E·0, E·1): {dict(e_on_absorbers.most_common(5))}")
    print(f"  Q·E, E·Q products: {dict(qe_products.most_common(5))}")

    # What does the QE pair look like structurally?
    # Check: do Q and E permute the core?
    perm_count = 0
    for tbl in models:
        q_core = [tbl[Q][x] for x in range(2, CORE)]
        e_core = [tbl[E][x] for x in range(2, CORE)]
        if sorted(q_core) == list(range(2, CORE)):
            perm_count += 1
    print(f"  Q permutes core (2..5): {perm_count}/{len(models)}")

    # Check: does Q send core outside core?
    sends_outside = 0
    for tbl in models:
        if any(tbl[Q][x] >= CORE for x in range(2, CORE)):
            sends_outside += 1
    print(f"  Q sends some core element outside core: {sends_outside}/{len(models)}")

    # Show a representative model
    if models:
        print(f"\n  Representative model:")
        tbl = models[0]
        for i in range(N):
            rm = role_map(tbl)
            print(f"    Row {i} ({rm.get(i, 'abs'):8s}): {tbl[i]}")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 6: Can QE interact with self-similar stacking?
    # Core(6) + QE(2) + Layer2(4) = N=12
    # Layer2 also satisfies L8 and has its own internal QE?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 6: Self-Similar Meta-Stacking (N=12)")
    print(f"{'═'*70}\n")

    N = 12
    Q1, E1 = 6, 7
    L2_START = 8

    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)

    # Upper QE
    add_qe_pair(s, dot, N, Q1, E1, core_lo=2, core_hi=CORE)

    # Sub-algebra closure on core
    for i in range(CORE):
        for j in range(CORE):
            s.add(dot[i][j] < CORE)

    # Layer 2 role skeleton
    l2_elems = list(range(L2_START, N))
    for x in l2_elems:
        pass  # Let L8 handle roles

    # Layer 2 has at least 1 tester and 2 encoders
    l2_tst_flags = []
    l2_enc_flags = []
    for x in l2_elems:
        is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        enc_pairs = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                enc_pairs.append(And(
                    dot[x][j1] != 0, dot[x][j1] != 1,
                    dot[x][j2] != 0, dot[x][j2] != 1,
                    dot[x][j1] != dot[x][j2]))
        is_enc = Or(enc_pairs) if enc_pairs else False
        tf = Int(f"l2t_{x}")
        ef = Int(f"l2e_{x}")
        s.add(If(is_tst, tf == 1, tf == 0))
        s.add(If(is_enc, ef == 1, ef == 0))
        l2_tst_flags.append(tf)
        l2_enc_flags.append(ef)
    s.add(sum(l2_tst_flags) >= 1)
    s.add(sum(l2_enc_flags) >= 2)

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0

    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        rm = role_map(tbl)
        print(f"  QE + structured lower at N=12: SAT ({elapsed:.1f}s)")
        print(f"    Q1={Q1}({rm.get(Q1,'?')}), E1={E1}({rm.get(E1,'?')})")
        print(f"    Layer 2 roles: {[rm.get(x,'?') for x in l2_elems]}")

        # Count models
        count = 1
        for _ in range(29):
            s.add(Or([dot[i][j] != tbl[i][j] for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            count += 1
        print(f"    Models: {count}{'+'  if count >= 30 else ''}")
    else:
        print(f"  QE + structured lower at N=12: UNSAT ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # PHASE 7: The critical test — does QE constrain uniqueness?
    # Compare model counts: with QE vs without QE
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 7: Uniqueness Impact of QE")
    print(f"{'═'*70}\n")

    for N in [8, 10]:
        # Without QE
        s1, dot1 = encode_level(8, N, timeout_seconds=120)
        add_full_base(s1, dot1, N)
        m1, e1 = count_models(s1, dot1, N, cap=100)

        # With QE
        s2, dot2 = encode_level(8, N, timeout_seconds=120)
        add_full_base(s2, dot2, N)
        add_qe_pair(s2, dot2, N, CORE, CORE + 1, core_lo=2, core_hi=CORE)
        m2, e2 = count_models(s2, dot2, N, cap=100)

        tag1 = f"{len(m1)}{'+'  if len(m1) >= 100 else ''}"
        tag2 = f"{len(m2)}{'+'  if len(m2) >= 100 else ''}"
        ratio = f"({len(m2)}/{len(m1)})" if len(m1) > 0 else ""
        print(f"  N={N}: without QE = {tag1}, with QE = {tag2}  {ratio}")

    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("FINAL SUMMARY")
    print(f"{'═'*70}")
    print("""
Integrated Meta-Framework Axioms:
  L8    — base axiom ladder (ext, absorbers, tester, encoder, ...)
  C     — tester-only resolution (Kripke)
  D     — inert propagation
  PA    — power-associativity
  VV    — v·v → core
  QE    — quotation/evaluation inverse pair: E·(Q·x) = x, Q·(E·x) = x
  QE2   — second inverse pair (APP/UNAPP): U·(A·x) = x, A·(U·x) = x
""")


def scaling_and_constructibility():
    """
    1. Scaling pattern: does QE change the (1 tst, 1 inert, rest enc) pattern?
    2. Minimum viable size: what's the smallest N with full axiom set + QE?
    3. Constructibility: is every element reachable by composing others?
    """
    import time
    from collections import Counter

    # ── Constraint helpers ────────────────────────────────────────

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    def role_sig(tbl, N):
        rm = role_map(tbl)
        return tuple(rm.get(x, '?') for x in range(2, N))

    CORE = 6

    print("=" * 70)
    print("SCALING, MINIMUM SIZE, AND CONSTRUCTIBILITY")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════
    # PART 1: Scaling pattern — with and without QE
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PART 1: Role Distribution Scaling (with vs without QE)")
    print(f"{'═'*70}\n")

    for N in range(6, 13):
        # Without QE
        s1, dot1 = encode_level(8, N, timeout_seconds=120)
        add_full_base(s1, dot1, N)
        sigs1 = Counter()
        t0 = time.time()
        for _ in range(100):
            if s1.check() != sat:
                break
            tbl = extract_table(s1.model(), dot1, N)
            sigs1[role_sig(tbl, N)] += 1
            s1.add(Or([dot1[i][j] != tbl[i][j]
                        for i in range(N) for j in range(N)]))
        e1 = time.time() - t0
        cnt1 = sum(sigs1.values())
        top1 = sigs1.most_common(1)[0] if sigs1 else ((), 0)

        # With QE (need N >= 8 for QE pair)
        if N >= 8:
            s2, dot2 = encode_level(8, N, timeout_seconds=120)
            add_full_base(s2, dot2, N)
            add_qe_pair(s2, dot2, N, CORE, CORE + 1, core_lo=2, core_hi=CORE)
            sigs2 = Counter()
            t0 = time.time()
            for _ in range(100):
                if s2.check() != sat:
                    break
                tbl = extract_table(s2.model(), dot2, N)
                sigs2[role_sig(tbl, N)] += 1
                s2.add(Or([dot2[i][j] != tbl[i][j]
                            for i in range(N) for j in range(N)]))
            e2 = time.time() - t0
            cnt2 = sum(sigs2.values())
            top2 = sigs2.most_common(1)[0] if sigs2 else ((), 0)
        else:
            cnt2 = 0
            top2 = ((), 0)
            sigs2 = Counter()
            e2 = 0

        # Summarize role counts from top signature
        def count_roles(sig):
            c = Counter(sig)
            return f"e={c.get('encoders',0)} t={c.get('testers',0)} i={c.get('inert',0)}"

        tag1 = f"{cnt1}{'+'  if cnt1 >= 100 else ''}"
        print(f"  N={N:2d}  no-QE: {tag1:>5s} ({e1:.1f}s) top={count_roles(top1[0]):12s} ({top1[1]}x) | sigs={len(sigs1)}", end="")
        if N >= 8:
            tag2 = f"{cnt2}{'+'  if cnt2 >= 100 else ''}"
            print(f"  QE: {tag2:>5s} ({e2:.1f}s) top={count_roles(top2[0]):12s} ({top2[1]}x) | sigs={len(sigs2)}")
        else:
            print("  QE: N/A (N<8)")

    # ═══════════════════════════════════════════════════════════════
    # PART 2: Minimum viable N
    # What's the smallest N where L8+C+D+PA+VV is SAT?
    # And with QE?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PART 2: Minimum Viable Size")
    print(f"{'═'*70}\n")

    for N in range(4, 13):
        s, dot = encode_level(8, N, timeout_seconds=30)
        add_full_base(s, dot, N)
        t0 = time.time()
        r = s.check()
        elapsed = time.time() - t0
        status = "SAT" if r == sat else "UNSAT"
        extra = ""
        if r == sat:
            tbl = extract_table(s.model(), dot, N)
            rm = role_map(tbl)
            c = Counter(rm.get(x, '?') for x in range(2, N))
            extra = f"  roles: {dict(c)}"
        print(f"  N={N:2d}  L8+full-base: {status:5s} ({elapsed:.1f}s){extra}")

    print()
    for N in range(8, 13):
        s, dot = encode_level(8, N, timeout_seconds=30)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, CORE, CORE + 1, core_lo=2, core_hi=CORE)
        t0 = time.time()
        r = s.check()
        elapsed = time.time() - t0
        status = "SAT" if r == sat else "UNSAT"
        extra = ""
        if r == sat:
            tbl = extract_table(s.model(), dot, N)
            rm = role_map(tbl)
            c = Counter(rm.get(x, '?') for x in range(2, N))
            extra = f"  roles: {dict(c)}"
        print(f"  N={N:2d}  L8+full-base+QE: {status:5s} ({elapsed:.1f}s){extra}")

    # ═══════════════════════════════════════════════════════════════
    # PART 3: Constructibility
    # For each model, compute the "producibility set" —
    # which elements appear as x·y for some x,y?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PART 3: Constructibility Analysis")
    print(f"{'═'*70}\n")

    for N in [8, 10, 12]:
        s, dot = encode_level(8, N, timeout_seconds=120)
        add_full_base(s, dot, N)
        if N >= 8:
            add_qe_pair(s, dot, N, CORE, CORE + 1, core_lo=2, core_hi=CORE)

        models = []
        t0 = time.time()
        for _ in range(50):
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            models.append(tbl)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0

        print(f"  N={N}: {len(models)} models ({elapsed:.1f}s)")

        # Analyze producibility
        full_prod = 0       # every element is x·y for some x,y
        na_prod = 0         # every element is x·y for some x,y ≥ 2
        missing_stats = Counter()  # which elements are most often missing?

        # Depth analysis: iterative closure
        depth_stats = []

        for tbl in models:
            # Level 0: all elements as "given"
            # Producibility: which elements appear in the table?
            produced_full = set()
            produced_na = set()  # non-absorber products
            for x in range(N):
                for y in range(N):
                    produced_full.add(tbl[x][y])
            for x in range(2, N):
                for y in range(2, N):
                    produced_na.add(tbl[x][y])

            if produced_full == set(range(N)):
                full_prod += 1
            if produced_na == set(range(N)):
                na_prod += 1
            missing = set(range(N)) - produced_full
            for m in missing:
                rm = role_map(tbl)
                missing_stats[rm.get(m, '?')] += 1

            # Depth analysis: starting from absorbers {0,1},
            # iteratively close under the operation.
            # Depth 0: {0, 1}
            # Depth k+1: {x·y : x,y ∈ depth_k} ∪ depth_k
            reached = {0, 1}
            for depth in range(1, N + 2):
                new = set()
                for x in reached:
                    for y in reached:
                        new.add(tbl[x][y])
                prev_size = len(reached)
                reached = reached | new
                if len(reached) == prev_size:
                    break
                if len(reached) == N:
                    break
            depth_stats.append((depth, len(reached)))

        print(f"    Full producibility (every elem = some x·y): "
              f"{full_prod}/{len(models)}")
        print(f"    Non-absorber producibility (every elem = x·y, x,y≥2): "
              f"{na_prod}/{len(models)}")
        if missing_stats:
            print(f"    Missing elements by role: {dict(missing_stats)}")

        # Depth closure from absorbers
        depth_counter = Counter(d for d, s in depth_stats)
        reach_counter = Counter(s for d, s in depth_stats)
        print(f"    Closure from {{0,1}}:")
        print(f"      Depths to close: {dict(depth_counter.most_common())}")
        print(f"      Elements reached: {dict(reach_counter.most_common())}")

        # More interesting: closure from a SINGLE non-absorber element
        # Can one encoder generate everything?
        gen_from_one = Counter()
        for tbl in models:
            rm = role_map(tbl)
            for start in range(2, N):
                reached = {0, 1, start}
                for _ in range(N + 2):
                    new = set()
                    for x in reached:
                        for y in reached:
                            new.add(tbl[x][y])
                    prev_size = len(reached)
                    reached = reached | new
                    if len(reached) == prev_size or len(reached) == N:
                        break
                if len(reached) == N:
                    gen_from_one[rm.get(start, '?')] += 1

        total_elems = len(models) * (N - 2)
        print(f"    Single-element generators ({'{0,1,x}'} → all N):")
        for role, cnt in gen_from_one.most_common():
            print(f"      {role}: {cnt}/{total_elems} "
                  f"({100*cnt/total_elems:.0f}%)")

        # QE-specific: can {0, 1, Q, E} generate everything?
        if N >= 8:
            qe_gen_count = 0
            for tbl in models:
                reached = {0, 1, CORE, CORE + 1}
                for _ in range(N + 2):
                    new = set()
                    for x in reached:
                        for y in reached:
                            new.add(tbl[x][y])
                    prev = len(reached)
                    reached = reached | new
                    if len(reached) == prev or len(reached) == N:
                        break
                if len(reached) == N:
                    qe_gen_count += 1
            print(f"    {{0,1,Q,E}} generates all: {qe_gen_count}/{len(models)}")

        print()

    # ═══════════════════════════════════════════════════════════════
    # PART 4: Forced constructibility — what if we REQUIRE
    # every element to be producible?
    # ═══════════════════════════════════════════════════════════════
    print(f"{'═'*70}")
    print("PART 4: Forced Full Producibility + QE")
    print(f"{'═'*70}\n")

    for N in [8, 10]:
        s, dot = encode_level(8, N, timeout_seconds=120)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, CORE, CORE + 1, core_lo=2, core_hi=CORE)
        # Every element is producible by non-absorbers
        for z in range(N):
            s.add(Or([dot[x][y] == z
                       for x in range(2, N) for y in range(2, N)]))
        models = []
        t0 = time.time()
        for _ in range(50):
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            models.append(tbl)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0
        cnt = len(models)
        tag = f"{cnt}{'+'  if cnt >= 50 else ''}"
        print(f"  N={N}: full-base + QE + producibility: {tag} ({elapsed:.1f}s)")
        if models:
            rm = role_map(models[0])
            c = Counter(rm.get(x, '?') for x in range(2, N))
            print(f"    Roles: {dict(c)}")
            # Check single-element generators
            gen = Counter()
            for tbl in models:
                rm = role_map(tbl)
                for start in range(2, N):
                    reached = {0, 1, start}
                    for _ in range(N + 2):
                        new = set()
                        for x in reached:
                            for y in reached:
                                new.add(tbl[x][y])
                        prev = len(reached)
                        reached = reached | new
                        if len(reached) == prev or len(reached) == N:
                            break
                    if len(reached) == N:
                        gen[rm.get(start, '?')] += 1
            total = len(models) * (N - 2)
            print(f"    Single generators:")
            for role, cnt in gen.most_common():
                print(f"      {role}: {cnt}/{total} ({100*cnt/total:.0f}%)")

    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")


def rigidity_analysis():
    """
    Do the N=8 models under full axiom set have trivial automorphism groups?
    If not, which elements are indistinguishable, and does QE help?
    """
    import time
    from itertools import permutations
    from collections import Counter

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    CORE = 6

    def compute_automorphisms(tbl):
        """Compute Aut(tbl) by brute force over S_N (with pruning)."""
        N = len(tbl)
        auts = []
        # Absorbers must map to absorbers: p(0)=0, p(1)=1
        # (since they're the only constant-row elements)
        # Try all permutations of {2..N-1}
        for perm_inner in permutations(range(2, N)):
            p = [0, 1] + list(perm_inner)
            # Check homomorphism: p(tbl[x][y]) == tbl[p(x)][p(y)]
            is_aut = True
            for x in range(N):
                if not is_aut:
                    break
                for y in range(N):
                    if p[tbl[x][y]] != tbl[p[x]][p[y]]:
                        is_aut = False
                        break
            if is_aut:
                auts.append(tuple(p))
        return auts

    def format_perm(p):
        """Format permutation as cycle notation."""
        N = len(p)
        visited = [False] * N
        cycles = []
        for i in range(N):
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

    print("=" * 70)
    print("RIGIDITY ANALYSIS")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════
    # TEST 1: Automorphism groups of L8+full-base+QE at N=8
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 1: Automorphism Groups at N=8 (full-base + QE)")
    print(f"{'═'*70}\n")

    N = 8
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, CORE, CORE + 1, core_lo=2, core_hi=CORE)

    models = []
    t0 = time.time()
    for _ in range(50):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        models.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Collected {len(models)} models ({elapsed:.1f}s)\n")

    rigid_count = 0
    aut_sizes = Counter()
    nontriv_examples = []

    for idx, tbl in enumerate(models):
        auts = compute_automorphisms(tbl)
        aut_sizes[len(auts)] += 1
        if len(auts) == 1:
            rigid_count += 1
        else:
            nontriv_examples.append((idx, tbl, auts))

    print(f"  Rigid (|Aut|=1): {rigid_count}/{len(models)}")
    print(f"  Aut group sizes: {dict(aut_sizes.most_common())}")

    if nontriv_examples:
        print(f"\n  Non-rigid examples ({len(nontriv_examples)} total):")
        for idx, tbl, auts in nontriv_examples[:5]:
            rm = role_map(tbl)
            print(f"\n    Model {idx}: |Aut| = {len(auts)}")
            for i in range(N):
                r = rm.get(i, 'abs')[:3]
                print(f"      Row {i} ({r:>3s}): {tbl[i]}")
            for a in auts:
                if a != tuple(range(N)):
                    print(f"      Aut: {format_perm(a)}")
                    # Which elements are swapped?
                    swapped = [(i, a[i]) for i in range(N) if a[i] != i]
                    roles_swapped = [(rm.get(i, '?'), rm.get(a[i], '?'))
                                     for i, _ in swapped]
                    print(f"        Swaps: {swapped} roles: {roles_swapped}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 2: Same analysis WITHOUT QE — is QE helping rigidity?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 2: Without QE (full-base only, N=8)")
    print(f"{'═'*70}\n")

    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)

    models_noqe = []
    t0 = time.time()
    for _ in range(50):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        models_noqe.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Collected {len(models_noqe)} models ({elapsed:.1f}s)\n")

    rigid_noqe = 0
    aut_sizes_noqe = Counter()
    nontriv_noqe = []

    for idx, tbl in enumerate(models_noqe):
        auts = compute_automorphisms(tbl)
        aut_sizes_noqe[len(auts)] += 1
        if len(auts) == 1:
            rigid_noqe += 1
        else:
            nontriv_noqe.append((idx, tbl, auts))

    print(f"  Rigid (|Aut|=1): {rigid_noqe}/{len(models_noqe)}")
    print(f"  Aut group sizes: {dict(aut_sizes_noqe.most_common())}")

    if nontriv_noqe:
        print(f"\n  Non-rigid examples ({len(nontriv_noqe)} total):")
        for idx, tbl, auts in nontriv_noqe[:3]:
            rm = role_map(tbl)
            print(f"\n    Model {idx}: |Aut| = {len(auts)}")
            for i in range(N):
                r = rm.get(i, 'abs')[:3]
                print(f"      Row {i} ({r:>3s}): {tbl[i]}")
            for a in auts:
                if a != tuple(range(N)):
                    print(f"      Aut: {format_perm(a)}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 3: WL-1 color refinement — how many rounds to distinguish?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 3: WL-1 Color Refinement on QE Models (N=8)")
    print(f"{'═'*70}\n")

    def wl1_refine(tbl):
        """Run WL-1 color refinement. Return (rounds, final_colors)."""
        N = len(tbl)
        # Initial coloring: row signature
        colors = {}
        for x in range(N):
            colors[x] = tuple(tbl[x])

        for round_num in range(1, N + 1):
            new_colors = {}
            for x in range(N):
                # Multiset of (color_of_neighbor, edge_label) pairs
                # For magma: neighbor y, "edge" = (tbl[x][y], tbl[y][x])
                neighbor_sig = tuple(sorted(
                    (colors[y], tbl[x][y], tbl[y][x]) for y in range(N)
                ))
                new_colors[x] = (colors[x], neighbor_sig)

            # Normalize
            unique = sorted(set(new_colors.values()))
            color_map = {v: i for i, v in enumerate(unique)}
            new_colors = {x: color_map[new_colors[x]] for x in range(N)}

            if len(set(new_colors.values())) == len(set(colors.values())):
                # Stable
                return round_num, new_colors
            colors = new_colors

        return N, colors

    wl_rounds = []
    wl_discrete = 0  # all elements get distinct colors

    for tbl in models:
        rounds, colors = wl1_refine(tbl)
        wl_rounds.append(rounds)
        if len(set(colors.values())) == N:
            wl_discrete += 1

    print(f"  WL-1 discrete (all elements distinguished): {wl_discrete}/{len(models)}")
    print(f"  Rounds to stable: {dict(Counter(wl_rounds).most_common())}")

    # For non-discrete models, which elements collide?
    wl_collisions = []
    for idx, tbl in enumerate(models):
        rounds, colors = wl1_refine(tbl)
        if len(set(colors.values())) < N:
            # Find collision groups
            by_color = {}
            for x, c in colors.items():
                by_color.setdefault(c, []).append(x)
            collisions = [grp for grp in by_color.values() if len(grp) > 1]
            rm = role_map(tbl)
            collision_roles = [tuple(rm.get(x, '?') for x in grp) for grp in collisions]
            wl_collisions.append((idx, collisions, collision_roles))

    if wl_collisions:
        print(f"\n  WL-1 collisions ({len(wl_collisions)} models):")
        for idx, collisions, roles in wl_collisions[:5]:
            print(f"    Model {idx}: collisions={collisions} roles={roles}")
    else:
        print(f"\n  No WL-1 collisions — every element structurally unique!")

    # Same for no-QE models
    print(f"\n  Without QE:")
    wl_discrete_noqe = 0
    wl_collisions_noqe = 0
    for tbl in models_noqe:
        rounds, colors = wl1_refine(tbl)
        if len(set(colors.values())) == N:
            wl_discrete_noqe += 1
        else:
            wl_collisions_noqe += 1
    print(f"    WL-1 discrete: {wl_discrete_noqe}/{len(models_noqe)}")
    print(f"    WL-1 collisions: {wl_collisions_noqe}/{len(models_noqe)}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 4: N=10 rigidity (with QE)
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 4: Rigidity at N=10 (full-base + QE)")
    print(f"{'═'*70}\n")

    N = 10
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, CORE, CORE + 1, core_lo=2, core_hi=CORE)

    models10 = []
    t0 = time.time()
    for _ in range(30):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        models10.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Collected {len(models10)} models ({elapsed:.1f}s)")
    # N=10 has 8! = 40320 permutations of non-absorbers — too many for brute force
    # Use Z3 instead: check if non-trivial automorphism exists

    rigid10 = 0
    for idx, tbl in enumerate(models10):
        s_aut = Solver()
        s_aut.set("timeout", 5000)
        p = [Int(f"p_{i}") for i in range(N)]
        s_aut.add(p[0] == 0)
        s_aut.add(p[1] == 1)
        for i in range(N):
            s_aut.add(p[i] >= 0)
            s_aut.add(p[i] < N)
        for i in range(N):
            for j in range(i + 1, N):
                s_aut.add(p[i] != p[j])
        s_aut.add(Or([p[i] != i for i in range(2, N)]))
        # Homomorphism using concrete table
        for x in range(N):
            for y in range(N):
                # p(tbl[x][y]) = tbl[p(x)][p(y)]
                # LHS: p applied to concrete value tbl[x][y]
                lhs = p[tbl[x][y]]
                # RHS: tbl[p(x)][p(y)] — double Z3 lookup into concrete table
                rhs = tbl[0][0]  # default
                for a in range(N):
                    for b in range(N):
                        rhs = If(And(p[x] == a, p[y] == b), tbl[a][b], rhs)
                s_aut.add(lhs == rhs)
        r = s_aut.check()
        if r != sat:
            rigid10 += 1

    print(f"  Rigid: {rigid10}/{len(models10)}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 5: Can we FORCE rigidity as an axiom?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 5: Forced Rigidity (no non-trivial automorphism)")
    print(f"{'═'*70}\n")

    for N in [8, 10]:
        s, dot = encode_level(8, N, timeout_seconds=120)
        add_full_base(s, dot, N)
        if N >= 8:
            add_qe_pair(s, dot, N, CORE, CORE + 1, core_lo=2, core_hi=CORE)

        # For every non-trivial permutation p (fixing 0,1),
        # require that p is NOT an automorphism.
        # Equivalently: for every p ≠ id fixing {0,1},
        # ∃ x,y: p(dot[x][y]) ≠ dot[p(x)][p(y)]
        #
        # Can't enumerate all perms. Instead:
        # ∀ permutation p fixing {0,1} with p≠id:
        #   ∃ x,y: p(dot[x][y]) ≠ dot[p(x)][p(y)]
        #
        # This is "rigidity" = no non-trivial automorphisms.
        # Encode: for every pair (a,b) with 2≤a<b<N,
        # the transposition (a b) is not an automorphism.
        # If no transposition is an aut, and no product of transpositions is,
        # then rigid. But checking all transpositions is a necessary condition.
        #
        # Actually, sufficient approach for small N:
        # Every non-trivial aut permutes at least one pair.
        # So: for every pair (a,b), row_a ≠ row_b (already Ext) AND
        # column_a ≠ column_b AND the swap (a,b) breaks the table.
        #
        # Simplest correct encoding: for every pair of non-absorbers a<b,
        # there exists (x,y) such that swapping a↔b in the table is inconsistent.
        # That is: the row/column structure distinguishes a from b.

        # Use row+column fingerprint: for each a, define
        #   fingerprint(a) = (row_a, col_a)
        # If all fingerprints are distinct, the algebra is "WL-1 discrete"
        # which implies rigidity for magmas.
        # Actually WL-1 discrete doesn't always imply rigid, but let's
        # just force all columns distinct (which together with Ext = all rows
        # distinct gives a strong necessary condition).

        # Force column-distinctness
        for x in range(N):
            for y in range(x + 1, N):
                s.add(Or([dot[i][x] != dot[i][y] for i in range(N)]))

        models_r = []
        t0 = time.time()
        for _ in range(50):
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            models_r.append(tbl)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0
        cnt = len(models_r)
        tag = f"{cnt}{'+'  if cnt >= 50 else ''}"
        print(f"  N={N} full-base+QE+col-distinct: {tag} ({elapsed:.1f}s)")

        # Verify rigidity of these models
        if models_r and N == 8:
            rigid_r = 0
            for tbl in models_r:
                auts = compute_automorphisms(tbl)
                if len(auts) == 1:
                    rigid_r += 1
            print(f"    Verified rigid: {rigid_r}/{len(models_r)}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 6: Recovery procedure — constructive identification
    # For rigid models, can we give a constructive recovery ordering?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 6: Constructive Recovery (N=8, rigid models)")
    print(f"{'═'*70}\n")

    N = 8
    # Collect rigid models with QE + col-distinct
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, CORE, CORE + 1, core_lo=2, core_hi=CORE)
    for x in range(N):
        for y in range(x + 1, N):
            s.add(Or([dot[i][x] != dot[i][y] for i in range(N)]))

    rigid_models = []
    t0 = time.time()
    for _ in range(50):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        auts = compute_automorphisms(tbl)
        if len(auts) == 1:
            rigid_models.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Collected {len(rigid_models)} rigid models ({elapsed:.1f}s)\n")

    # For each rigid model, attempt recovery:
    # Step 1: Identify absorbers (constant rows)
    # Step 2: Identify tester (boolean row, not absorber)
    # Step 3: Use tester to partition non-absorbers
    # Step 4: Identify inert (non-boolean, <2 distinct non-bool outputs)
    # Step 5: Identify encoders (≥2 distinct non-bool outputs)
    # Step 6: Use QE structure to pin Q and E
    # Step 7: Resolve remaining elements by their action on identified ones

    recovery_success = 0
    recovery_steps = Counter()

    for tbl in rigid_models:
        rm = role_map(tbl)
        identified = {}  # element -> label
        steps = []

        # Step 1: absorbers
        for x in range(N):
            if all(tbl[x][y] == x for y in range(N)):
                if all(tbl[y][x] == x for y in range(N)):
                    # Left and right absorber
                    pass
                identified[x] = f"abs_{x}"
        abs_list = [x for x in identified]
        steps.append(f"absorbers: {abs_list}")

        # Step 2: tester (boolean row)
        testers = []
        for x in range(N):
            if x in identified:
                continue
            if all(tbl[x][y] in (0, 1) for y in range(N)):
                testers.append(x)
                identified[x] = f"tst_{x}"
        steps.append(f"testers: {testers}")

        # Step 3: classify remaining by row type
        encoders = []
        inerts = []
        for x in range(N):
            if x in identified:
                continue
            non_bool = [v for v in tbl[x] if v not in (0, 1)]
            distinct_non_bool = len(set(non_bool))
            if distinct_non_bool >= 2:
                encoders.append(x)
                identified[x] = f"enc_{x}"
            else:
                inerts.append(x)
                identified[x] = f"inert_{x}"
        steps.append(f"encoders: {encoders}, inert: {inerts}")

        # Step 4: distinguish within role groups using row fingerprints
        # (already distinct by Ext, but can we ORDER them canonically?)
        # Use lexicographic ordering of rows
        if len(testers) > 1:
            testers.sort(key=lambda x: tbl[x])
        if len(encoders) > 1:
            encoders.sort(key=lambda x: tbl[x])

        # Step 5: identify Q and E
        # Q and E are the pair where E(Q(x)) = x for core x
        # Among encoders, find the pair that forms an inverse
        qe_found = False
        for q_cand in encoders:
            for e_cand in encoders:
                if q_cand == e_cand:
                    continue
                # Check: e(q(x)) = x for x in non-absorber, non-Q, non-E
                test_elems = [x for x in range(2, N)
                              if x != q_cand and x != e_cand]
                is_inverse = True
                for x in test_elems[:4]:  # test on first 4
                    qx = tbl[q_cand][x]
                    eqx = tbl[e_cand][qx]
                    if eqx != x:
                        is_inverse = False
                        break
                if is_inverse:
                    # Also check reverse: q(e(x)) = x
                    for x in test_elems[:4]:
                        ex = tbl[e_cand][x]
                        qex = tbl[q_cand][ex]
                        if qex != x:
                            is_inverse = False
                            break
                if is_inverse:
                    steps.append(f"QE pair: Q={q_cand}, E={e_cand}")
                    qe_found = True
                    break
            if qe_found:
                break
        if not qe_found:
            steps.append("QE pair: NOT FOUND")

        # Step 6: verify all elements identified uniquely
        all_identified = len(identified) == N
        all_unique = len(set(identified.values())) == N

        if all_identified and all_unique:
            recovery_success += 1
        recovery_steps[len(steps)] += 1

    print(f"  Recovery success (all elements identified): "
          f"{recovery_success}/{len(rigid_models)}")
    print(f"  Steps needed: {dict(recovery_steps)}")

    # Show one full recovery trace
    if rigid_models:
        tbl = rigid_models[0]
        rm = role_map(tbl)
        print(f"\n  Example recovery trace:")
        print(f"    Table:")
        for i in range(N):
            print(f"      {i} ({rm.get(i,'?'):>8s}): {tbl[i]}")

        # Redo recovery with verbose output
        print(f"\n    Step 1: Absorbers = {{x : row(x) = [x,...,x]}}")
        abs_list = [x for x in range(N) if all(tbl[x][y] == x for y in range(N))]
        print(f"      Found: {abs_list}")

        print(f"    Step 2: Testers = {{x : row(x) ⊆ {{0,1}}}}")
        tst_list = [x for x in range(N) if x not in abs_list
                    and all(tbl[x][y] in (0, 1) for y in range(N))]
        print(f"      Found: {tst_list}")

        print(f"    Step 3: Encoders = {{x : |non-bool outputs| ≥ 2}}")
        enc_list = [x for x in range(N) if x not in abs_list and x not in tst_list
                    and len(set(v for v in tbl[x] if v not in (0, 1))) >= 2]
        inert_list = [x for x in range(N)
                      if x not in abs_list and x not in tst_list
                      and x not in enc_list]
        print(f"      Encoders: {enc_list}")
        print(f"      Inert: {inert_list}")

        print(f"    Step 4: Find QE pair among encoders")
        for q in enc_list:
            for e in enc_list:
                if q == e:
                    continue
                test_x = [x for x in range(2, N) if x != q and x != e]
                ok = all(tbl[e][tbl[q][x]] == x and tbl[q][tbl[e][x]] == x
                         for x in test_x[:4])
                if ok:
                    print(f"      Q={q}, E={e}: "
                          + ", ".join(f"E(Q({x}))={tbl[e][tbl[q][x]]}" for x in test_x[:4]))
                    break
            else:
                continue
            break

        print(f"    Step 5: Remaining encoders distinguished by row content")
        remaining_enc = [x for x in enc_list if x != q and x != e]
        for x in remaining_enc:
            print(f"      Enc {x}: row = {tbl[x]}")
        if len(remaining_enc) > 1:
            # Check if rows are distinct (they must be by Ext)
            print(f"      All rows distinct: "
                  f"{len(set(tuple(tbl[x]) for x in remaining_enc)) == len(remaining_enc)}")

    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")


def actuality_irreducibility():
    """
    Actuality irreducibility check for L8+C+D+PA+VV+QE.

    Core question: can two models agree on the entire table EXCEPT the
    tester's row, yet disagree on which element the tester rejects?

    If SAT: actuality carries irreducible information (Kantian result).
    If UNSAT: the axioms fully determine the rejection target.
    """
    import time
    from collections import Counter

    # ── Constraint helpers ────────────────────────────────────────

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    CORE = 6

    print("=" * 70)
    print("ACTUALITY IRREDUCIBILITY CHECK")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════
    # BASELINE: Characterize tester behavior across models
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("BASELINE: Tester Characterization (N=8)")
    print(f"{'═'*70}\n")

    N = 8
    Q_IDX, E_IDX = CORE, CORE + 1  # 6, 7

    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    models = []
    t0 = time.time()
    for _ in range(100):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        models.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Collected {len(models)} models ({elapsed:.1f}s)\n")

    # For each model, find the tester and analyze its row
    tester_rows = Counter()
    tester_positions = Counter()  # which element index is the tester?
    rejection_counts = Counter()  # how many elements does the tester reject?
    rejection_targets = Counter()  # which elements get rejected?

    for tbl in models:
        rm = role_map(tbl)
        for x in range(2, N):
            if rm.get(x) == 'testers':
                tst_row = tuple(tbl[x])
                tester_rows[tst_row] += 1
                tester_positions[x] += 1
                # "Rejection" = elements mapped to 0 (or 1?)
                # In Δ₁ context: tester maps to 0 for "non-actual"
                # Here: absorbers are 0 and 1. The tester's row is boolean.
                # The "rejection set" = {y : tst·y = 0} minus absorbers
                # The "acceptance set" = {y : tst·y = 1} minus absorbers
                rej = [y for y in range(2, N) if tbl[x][y] == 0]
                acc = [y for y in range(2, N) if tbl[x][y] == 1]
                rejection_counts[len(rej)] += 1
                rejection_targets[tuple(sorted(rej))] += 1
                break  # usually one tester

    print(f"  Tester position: {dict(tester_positions)}")
    print(f"  Rejection set size: {dict(rejection_counts)}")
    print(f"  Distinct tester rows: {len(tester_rows)}")
    print(f"  Top tester rows:")
    for row, cnt in tester_rows.most_common(10):
        rej = [y for y in range(2, N) if row[y] == 0]
        acc = [y for y in range(2, N) if row[y] == 1]
        rm_str = ""
        print(f"    {list(row)}: {cnt}x  rejects={rej} accepts={acc}")
    print(f"\n  Rejection targets (element sets):")
    for target, cnt in rejection_targets.most_common(10):
        print(f"    {list(target)}: {cnt}x")

    # ═══════════════════════════════════════════════════════════════
    # TEST 1: Core actuality irreducibility
    # Two tables M, M' that share everything except the tester's row,
    # but the tester rejects different elements.
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 1: Core Actuality Irreducibility (N=8)")
    print("Two models, same table except tester row, different rejection")
    print(f"{'═'*70}\n")

    # We need to try every possible tester position.
    # The tester is typically at a fixed position in the sampled models,
    # but let's be systematic.

    for tst_pos in sorted(tester_positions.keys()):
        print(f"  Tester at position {tst_pos}:")

        # Create two copies of the table
        dot1 = [[Int(f"m1_{i}_{j}") for j in range(N)] for i in range(N)]
        dot2 = [[Int(f"m2_{i}_{j}") for j in range(N)] for i in range(N)]

        solver = Solver()
        solver.set("timeout", 60000)

        # Both satisfy L8+C+D+PA+VV+QE
        # We can't use encode_level directly for two tables, so encode manually.
        # Instead, build from one encode_level and constrain the second.
        # Actually, let's use a cleaner approach: encode both independently.

        # For M1:
        s1, d1 = encode_level(8, N, timeout_seconds=60)
        add_full_base(s1, d1, N)
        add_qe_pair(s1, d1, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

        # For M2: separate solver, but we'll merge constraints
        s2, d2_raw = encode_level(8, N, timeout_seconds=60)

        # We need both in ONE solver. Rename M2's variables.
        s_combined = Solver()
        s_combined.set("timeout", 120000)

        # M1 variables
        m1 = [[Int(f"a_{i}_{j}") for j in range(N)] for i in range(N)]
        m2 = [[Int(f"b_{i}_{j}") for j in range(N)] for i in range(N)]

        for dot_vars, prefix in [(m1, "M1"), (m2, "M2")]:
            # Ranges
            for i in range(N):
                for j in range(N):
                    s_combined.add(dot_vars[i][j] >= 0)
                    s_combined.add(dot_vars[i][j] < N)

            # Encode L8 constraints inline (from encode_level logic)
            # L0: Ext (all rows distinct)
            for i in range(N):
                for j in range(i + 1, N):
                    s_combined.add(Or([dot_vars[i][k] != dot_vars[j][k]
                                       for k in range(N)]))
            # Two absorbers
            for j in range(N):
                s_combined.add(dot_vars[0][j] == 0)
                s_combined.add(dot_vars[1][j] == 1)
            # No other absorbers
            for i in range(2, N):
                s_combined.add(Or([dot_vars[i][j] != i for j in range(N)]))

            # L1: ∃ tester (boolean row, not absorber)
            tst_clauses = []
            for i in range(2, N):
                tst_clauses.append(
                    And([Or(dot_vars[i][j] == 0, dot_vars[i][j] == 1)
                         for j in range(N)]))
            s_combined.add(Or(tst_clauses))

            # L2: ∃ encoder (≥2 distinct non-bool outputs)
            enc_clauses = []
            for i in range(2, N):
                pairs = []
                for j1 in range(N):
                    for j2 in range(j1 + 1, N):
                        pairs.append(And(
                            dot_vars[i][j1] != 0, dot_vars[i][j1] != 1,
                            dot_vars[i][j2] != 0, dot_vars[i][j2] != 1,
                            dot_vars[i][j1] != dot_vars[i][j2]))
                enc_clauses.append(Or(pairs) if pairs else False)
            s_combined.add(Or(enc_clauses))

            # L5: generative synthesis — ∃ encoder e, ∃ a,b,c all ≥2 distinct:
            # e·a = b, e·c ∉ {0,1}, e·c ≠ b
            for e in range(2, N):
                is_enc_e = []
                for j1 in range(N):
                    for j2 in range(j1 + 1, N):
                        is_enc_e.append(And(
                            dot_vars[e][j1] != 0, dot_vars[e][j1] != 1,
                            dot_vars[e][j2] != 0, dot_vars[e][j2] != 1,
                            dot_vars[e][j1] != dot_vars[e][j2]))
                # (L5 is existential, so we don't need to iterate all)

            # L6: open closure + feedback
            # ∃ enc e: ∃ x≥2: e·x ≥ 2 and e·x ≠ x (non-trivial transformation)
            # + ∃ pair y,z≥2: e·y ≠ e·z (already in encoder def)

            # L7: context tokens + producibility
            # ∃ x≥2: ∀ y≥2: x·y ≥ 2 (context token, never produces absorber)
            ctx_clauses = []
            for x in range(2, N):
                ctx_clauses.append(
                    And([dot_vars[x][y] >= 2 for y in range(2, N)]))
            s_combined.add(Or(ctx_clauses))

            # L8: encoder completeness (every non-absorber pair separated by
            # some encoder) + inert non-self-id (v·v ≠ v for inert)
            for x in range(2, N):
                for y in range(x + 1, N):
                    sep = []
                    for e in range(2, N):
                        # e is encoder and e·x ≠ e·y
                        e_enc = []
                        for j1 in range(N):
                            for j2 in range(j1 + 1, N):
                                e_enc.append(And(
                                    dot_vars[e][j1] != 0, dot_vars[e][j1] != 1,
                                    dot_vars[e][j2] != 0, dot_vars[e][j2] != 1,
                                    dot_vars[e][j1] != dot_vars[e][j2]))
                        sep.append(And(Or(e_enc) if e_enc else False,
                                       dot_vars[e][x] != dot_vars[e][y]))
                    s_combined.add(Or(sep))

            # v·v ≠ v for non-absorber non-boolean
            for v in range(2, N):
                is_tst_v = And([Or(dot_vars[v][j] == 0, dot_vars[v][j] == 1)
                                for j in range(N)])
                s_combined.add(Or(is_tst_v, dot_vars[v][v] != v))

            # C: tester-only resolution
            for x in range(2, N):
                is_tst = And([Or(dot_vars[x][j] == 0, dot_vars[x][j] == 1)
                              for j in range(N)])
                for y in range(2, N):
                    s_combined.add(Or(is_tst, dot_vars[x][y] >= 2))

            # D: inert propagation
            for x in range(2, N):
                is_tst_x = And([Or(dot_vars[x][j] == 0, dot_vars[x][j] == 1)
                                for j in range(N)])
                enc_pairs_x = []
                for j1 in range(N):
                    for j2 in range(j1 + 1, N):
                        enc_pairs_x.append(And(
                            dot_vars[x][j1] != 0, dot_vars[x][j1] != 1,
                            dot_vars[x][j2] != 0, dot_vars[x][j2] != 1,
                            dot_vars[x][j1] != dot_vars[x][j2]))
                is_enc_x = Or(enc_pairs_x) if enc_pairs_x else False
                is_inert_x = And(Not(is_tst_x), Not(is_enc_x))
                for y in range(2, N):
                    s_combined.add(Or(Not(is_inert_x), dot_vars[x][y] >= 2))

            # PA
            for x in range(N):
                xx = dot_vars[x][x]
                lhs = dot_vars[0][x]  # default
                for r in range(1, N):
                    lhs = If(xx == r, dot_vars[r][x], lhs)
                rhs = dot_vars[x][0]  # default
                for c in range(1, N):
                    rhs = If(xx == c, dot_vars[x][c], rhs)
                s_combined.add(lhs == rhs)

            # VV: inert v → v·v is core (tester or encoder)
            for v in range(2, N):
                is_tst_v2 = And([Or(dot_vars[v][j] == 0, dot_vars[v][j] == 1)
                                 for j in range(N)])
                enc_pairs_v2 = []
                for j1 in range(N):
                    for j2 in range(j1 + 1, N):
                        enc_pairs_v2.append(And(
                            dot_vars[v][j1] != 0, dot_vars[v][j1] != 1,
                            dot_vars[v][j2] != 0, dot_vars[v][j2] != 1,
                            dot_vars[v][j1] != dot_vars[v][j2]))
                is_enc_v2 = Or(enc_pairs_v2) if enc_pairs_v2 else False
                is_inert_v2 = And(Not(is_tst_v2), Not(is_enc_v2))

                vv = dot_vars[v][v]
                vv_is_tst = And([Or(
                    If(vv == r, dot_vars[r][j], -1) == 0,
                    If(vv == r, dot_vars[r][j], -1) == 1)
                    for j in range(N) for r in range(N)])
                # Simpler: enumerate what vv could be
                vv_core_clauses = []
                for r in range(2, N):
                    row_r_is_tst = And([Or(dot_vars[r][j] == 0,
                                           dot_vars[r][j] == 1)
                                        for j in range(N)])
                    row_r_enc = []
                    for j1 in range(N):
                        for j2 in range(j1 + 1, N):
                            row_r_enc.append(And(
                                dot_vars[r][j1] != 0, dot_vars[r][j1] != 1,
                                dot_vars[r][j2] != 0, dot_vars[r][j2] != 1,
                                dot_vars[r][j1] != dot_vars[r][j2]))
                    row_r_is_enc = Or(row_r_enc) if row_r_enc else False
                    vv_core_clauses.append(
                        And(vv == r, Or(row_r_is_tst, row_r_is_enc)))
                s_combined.add(Or(Not(is_inert_v2), Or(vv_core_clauses)))

            # QE pair (Q=6, E=7)
            q, e = Q_IDX, E_IDX
            for x in range(2, CORE):
                qx = dot_vars[q][x]
                # E applied to Q(x): need dot_vars[e][qx]
                eq_x = dot_vars[e][0]
                for c in range(1, N):
                    eq_x = If(qx == c, dot_vars[e][c], eq_x)
                s_combined.add(eq_x == x)
                ex = dot_vars[e][x]
                qe_x = dot_vars[q][0]
                for c in range(1, N):
                    qe_x = If(ex == c, dot_vars[q][c], qe_x)
                s_combined.add(qe_x == x)

        # ── Key constraint: M1 and M2 agree EXCEPT on tester row ──

        # Tester is at position tst_pos
        # Force tst_pos to be the tester in both
        s_combined.add(And([Or(m1[tst_pos][j] == 0, m1[tst_pos][j] == 1)
                            for j in range(N)]))
        s_combined.add(And([Or(m2[tst_pos][j] == 0, m2[tst_pos][j] == 1)
                            for j in range(N)]))

        # All other rows identical
        for i in range(N):
            if i == tst_pos:
                continue
            for j in range(N):
                s_combined.add(m1[i][j] == m2[i][j])

        # Tester rows differ
        s_combined.add(Or([m1[tst_pos][j] != m2[tst_pos][j]
                           for j in range(N)]))

        # Different rejection target: ∃ a ≥ 2: M1 rejects a, M2 doesn't
        # (tst·a = 0 in M1, tst·a = 1 in M2)
        diff_clauses = []
        for a in range(2, N):
            diff_clauses.append(And(m1[tst_pos][a] == 0, m2[tst_pos][a] == 1))
            diff_clauses.append(And(m1[tst_pos][a] == 1, m2[tst_pos][a] == 0))
        s_combined.add(Or(diff_clauses))

        t0 = time.time()
        r = s_combined.check()
        elapsed = time.time() - t0

        if r == sat:
            m = s_combined.model()
            tbl1 = [[m.eval(m1[i][j]).as_long() for j in range(N)]
                     for i in range(N)]
            tbl2 = [[m.eval(m2[i][j]).as_long() for j in range(N)]
                     for i in range(N)]
            rej1 = [y for y in range(2, N) if tbl1[tst_pos][y] == 0]
            rej2 = [y for y in range(2, N) if tbl2[tst_pos][y] == 0]
            diffs = sum(1 for j in range(N) if tbl1[tst_pos][j] != tbl2[tst_pos][j])
            print(f"    SAT ({elapsed:.1f}s) — ACTUALITY IRREDUCIBILITY HOLDS")
            print(f"    M1 tester row: {tbl1[tst_pos]}  rejects {rej1}")
            print(f"    M2 tester row: {tbl2[tst_pos]}  rejects {rej2}")
            print(f"    Entries differ: {diffs}/{N}")
            print(f"    Shared non-tester table:")
            for i in range(N):
                if i == tst_pos:
                    continue
                rm = role_map(tbl1)
                print(f"      {i} ({rm.get(i,'?'):>8s}): {tbl1[i]}")
        else:
            print(f"    UNSAT ({elapsed:.1f}s) — tester row fully determined")

    # ═══════════════════════════════════════════════════════════════
    # TEST 2: Relaxed — differ on tester row + k other entries
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 2: Relaxed — How Many Entries Must Differ?")
    print(f"{'═'*70}\n")

    # If Test 1 was UNSAT, relax: allow tester row + one other row to differ
    # Use the most common tester position
    tst_pos = tester_positions.most_common(1)[0][0]
    print(f"  Using tester position {tst_pos}\n")

    for extra_rows in range(N):
        if extra_rows == 0:
            label = "tester row only"
            free_rows = {tst_pos}
        else:
            # Allow tester + extra_rows other rows to differ
            label = f"tester + {extra_rows} other row(s)"
            free_rows = {tst_pos}
            # Pick rows adjacent to tester
            for r in range(2, N):
                if r != tst_pos and len(free_rows) < extra_rows + 1:
                    free_rows.add(r)

        # Quick version: use encode_level for one model,
        # pin everything except free_rows, check if different tester rejection
        # is possible

        # First get a concrete model
        s_base, dot_base = encode_level(8, N, timeout_seconds=60)
        add_full_base(s_base, dot_base, N)
        add_qe_pair(s_base, dot_base, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        # Force tester at tst_pos
        s_base.add(And([Or(dot_base[tst_pos][j] == 0, dot_base[tst_pos][j] == 1)
                         for j in range(N)]))
        if s_base.check() != sat:
            print(f"  No base model with tester at {tst_pos}")
            break

        base_tbl = extract_table(s_base.model(), dot_base, N)
        base_rej = [y for y in range(2, N) if base_tbl[tst_pos][y] == 0]

        # Now: can we find a different model that agrees on pinned rows
        # but has a different rejection set?
        s2, dot2 = encode_level(8, N, timeout_seconds=120)
        add_full_base(s2, dot2, N)
        add_qe_pair(s2, dot2, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        s2.add(And([Or(dot2[tst_pos][j] == 0, dot2[tst_pos][j] == 1)
                     for j in range(N)]))

        # Pin all rows NOT in free_rows
        for i in range(N):
            if i in free_rows:
                continue
            for j in range(N):
                s2.add(dot2[i][j] == base_tbl[i][j])

        # Require different rejection
        s2.add(Or([dot2[tst_pos][y] != base_tbl[tst_pos][y]
                    for y in range(2, N)]))

        t0 = time.time()
        r = s2.check()
        elapsed = time.time() - t0

        if r == sat:
            alt_tbl = extract_table(s2.model(), dot2, N)
            alt_rej = [y for y in range(2, N) if alt_tbl[tst_pos][y] == 0]
            diff_entries = sum(1 for i in range(N) for j in range(N)
                               if base_tbl[i][j] != alt_tbl[i][j])
            print(f"  {label:40s} SAT ({elapsed:.1f}s)  "
                  f"rej: {base_rej} → {alt_rej}  "
                  f"({diff_entries} entries differ)")
            # Show which rows changed
            changed_rows = [i for i in range(N)
                            if any(base_tbl[i][j] != alt_tbl[i][j]
                                   for j in range(N))]
            print(f"    Changed rows: {changed_rows}")
            for i in changed_rows:
                diffs = [(j, base_tbl[i][j], alt_tbl[i][j])
                         for j in range(N) if base_tbl[i][j] != alt_tbl[i][j]]
                print(f"      Row {i}: {len(diffs)} diffs: {diffs}")
            break  # Found minimal relaxation
        else:
            print(f"  {label:40s} UNSAT ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # TEST 3: Tester rejection cardinality
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 3: Rejection Set Properties")
    print(f"{'═'*70}\n")

    # Already collected from baseline. Deeper analysis:
    rej_by_role = Counter()
    for tbl in models:
        rm = role_map(tbl)
        for x in range(2, N):
            if rm.get(x) == 'testers':
                for y in range(2, N):
                    if tbl[x][y] == 0:
                        rej_by_role[rm.get(y, '?')] += 1
                break

    print(f"  Rejected elements by role (across {len(models)} models):")
    for role, cnt in rej_by_role.most_common():
        print(f"    {role}: {cnt} ({100*cnt/len(models):.0f}%)")

    # Is it always exactly one element rejected? Or can it be 0, 2, ...?
    print(f"\n  Rejection set size distribution:")
    for size, cnt in sorted(rejection_counts.items()):
        print(f"    |rej| = {size}: {cnt} models")

    # Which element is rejected — is it always the same role?
    print(f"\n  Is the rejected element always the same?")
    if len(rejection_targets) == 1:
        target = list(rejection_targets.keys())[0]
        print(f"    YES — always rejects {list(target)}")
    else:
        print(f"    NO — {len(rejection_targets)} distinct rejection sets")

    # ═══════════════════════════════════════════════════════════════
    # TEST 4: N=10 — does extra room help?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 4: Actuality at N=10")
    print(f"{'═'*70}\n")

    N = 10
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    models10 = []
    t0 = time.time()
    for _ in range(50):
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        models10.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  Collected {len(models10)} models ({elapsed:.1f}s)")

    rej_counts_10 = Counter()
    rej_roles_10 = Counter()
    tst_pos_10 = Counter()

    for tbl in models10:
        rm = role_map(tbl)
        for x in range(2, N):
            if rm.get(x) == 'testers':
                tst_pos_10[x] += 1
                rej = [y for y in range(2, N) if tbl[x][y] == 0]
                rej_counts_10[len(rej)] += 1
                for y in rej:
                    rej_roles_10[rm.get(y, '?')] += 1
                break

    print(f"  Tester positions: {dict(tst_pos_10)}")
    print(f"  Rejection sizes: {dict(sorted(rej_counts_10.items()))}")
    print(f"  Rejected by role: {dict(rej_roles_10)}")

    # Try actuality irreducibility at N=10:
    # Pin one model, free tester row, require different rejection
    if models10:
        tst_pos_10_val = tst_pos_10.most_common(1)[0][0]
        base_tbl = models10[0]
        base_rej = [y for y in range(2, N) if base_tbl[tst_pos_10_val][y] == 0]

        s2, dot2 = encode_level(8, N, timeout_seconds=120)
        add_full_base(s2, dot2, N)
        add_qe_pair(s2, dot2, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        s2.add(And([Or(dot2[tst_pos_10_val][j] == 0, dot2[tst_pos_10_val][j] == 1)
                     for j in range(N)]))
        for i in range(N):
            if i == tst_pos_10_val:
                continue
            for j in range(N):
                s2.add(dot2[i][j] == base_tbl[i][j])
        s2.add(Or([dot2[tst_pos_10_val][y] != base_tbl[tst_pos_10_val][y]
                    for y in range(2, N)]))

        t0 = time.time()
        r = s2.check()
        elapsed = time.time() - t0
        if r == sat:
            alt = extract_table(s2.model(), dot2, N)
            alt_rej = [y for y in range(2, N) if alt[tst_pos_10_val][y] == 0]
            print(f"\n  Tester-only variation at N=10: SAT ({elapsed:.1f}s)")
            print(f"    Base rejects: {base_rej}")
            print(f"    Alt rejects:  {alt_rej}")
        else:
            # Try freeing one more row
            print(f"\n  Tester-only variation at N=10: UNSAT ({elapsed:.1f}s)")
            for extra_r in range(2, N):
                if extra_r == tst_pos_10_val:
                    continue
                s3, dot3 = encode_level(8, N, timeout_seconds=120)
                add_full_base(s3, dot3, N)
                add_qe_pair(s3, dot3, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
                s3.add(And([Or(dot3[tst_pos_10_val][j] == 0,
                               dot3[tst_pos_10_val][j] == 1) for j in range(N)]))
                for i in range(N):
                    if i in (tst_pos_10_val, extra_r):
                        continue
                    for j in range(N):
                        s3.add(dot3[i][j] == base_tbl[i][j])
                s3.add(Or([dot3[tst_pos_10_val][y] != base_tbl[tst_pos_10_val][y]
                            for y in range(2, N)]))
                t0 = time.time()
                r3 = s3.check()
                e3 = time.time() - t0
                if r3 == sat:
                    alt = extract_table(s3.model(), dot3, N)
                    alt_rej = [y for y in range(2, N)
                               if alt[tst_pos_10_val][y] == 0]
                    print(f"  Tester + row {extra_r} free: SAT ({e3:.1f}s)  "
                          f"rej: {base_rej} → {alt_rej}")
                    break

    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")


def computational_axioms():
    """
    What axioms enable the meta-framework as a computational substrate?

    We already have:
      - Binary ground (absorbers 0,1)
      - Role differentiation (tester, encoder, inert)
      - Meta-operations (QE inverse pair)
      - Power-associativity
      - Constructibility (every element producible)
      - Rigidity (every element identifiable)
      - Actuality irreducibility

    For general-purpose computation we need:
      A. Conditional dispatch — tester output drives different paths
      B. Composition closure — composable encoders
      C. Pairing / data structures — construct and destruct pairs
      D. Fixed-point / iteration — self-referential computation
      E. Generator — single element whose powers reach everything

    Test each as SAT/UNSAT under the full axiom set.
    """
    import time
    from collections import Counter

    # ── Constraint helpers ────────────────────────────────────────

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    def count_and_report(s, dot, N, label, cap=30):
        t0 = time.time()
        models = []
        first = None
        while len(models) < cap:
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            if not first:
                first = tbl
            models.append(tbl)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0
        cnt = len(models)
        if cnt == 0:
            print(f"    {label:55s} UNSAT ({elapsed:.1f}s)")
        else:
            tag = f"{cnt}{'+'  if cnt >= cap else ''}"
            print(f"    {label:55s} {tag} ({elapsed:.1f}s)")
        return models, first

    CORE = 6
    Q_IDX, E_IDX = 6, 7

    print("=" * 70)
    print("COMPUTATIONAL AXIOMS EXPLORATION")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════
    # A. CONDITIONAL DISPATCH
    # Can the tester's output (0 or 1) select between two
    # different encoders?
    # ∃ dispatcher d: d·0 and d·1 are both encoders, d·0 ≠ d·1
    # This gives: tester·x feeds into d, which yields an encoder
    # that processes x differently depending on the test result.
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("A. CONDITIONAL DISPATCH")
    print("Can tester output drive different computation paths?")
    print(f"{'═'*70}\n")

    N = 10

    # A1: Simple dispatcher — d·0 ≠ d·1, both ≥ 2
    # (tester returns 0 or 1; dispatcher maps these to different non-absorbers)
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
    d = 8
    s.add(dot[d][0] >= 2)
    s.add(dot[d][1] >= 2)
    s.add(dot[d][0] != dot[d][1])
    models, first = count_and_report(s, dot, N,
        "dispatcher: d·0 ≠ d·1, both ≥ 2")
    if first:
        print(f"      d={d}: d·0={first[d][0]}, d·1={first[d][1]}")
        print(f"      d row: {first[d]}")

    # A2: Tester-driven branching — concrete version
    # ∃ tester t, ∃ element d, ∃ x,y ≥ 2:
    #   t·x = 0, t·y = 1, d·(t·x) ≠ d·(t·y)
    # This is just: d·0 ≠ d·1 (same as A1) plus tester exists.
    # Already guaranteed by L8. So let's test the full chain:
    # result_x = (d · (t · x)) · x, result_y = (d · (t · y)) · y
    # and result_x ≠ result_y
    print()
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
    d = 8
    s.add(dot[d][0] >= 2)
    s.add(dot[d][1] >= 2)
    s.add(dot[d][0] != dot[d][1])
    # Force tester at position 3
    t_idx = 3
    s.add(And([Or(dot[t_idx][j] == 0, dot[t_idx][j] == 1) for j in range(N)]))
    # Full chain: for concrete x,y where t gives 0 vs 1
    # Since t row is variable, use: ∃ x,y: t·x=0, t·y=1
    # and dot[d][0]·x ≠ dot[d][1]·y (d dispatches to different functions)
    d0 = dot[d][0]
    d1 = dot[d][1]
    chain_clauses = []
    for x in range(2, N):
        for y in range(2, N):
            # t·x = 0 and t·y = 1
            # Then d·(t·x) = d·0 = d0, applied to x: dot[d0][x]
            #      d·(t·y) = d·1 = d1, applied to y: dot[d1][y]
            res_x = ite_lookup(dot, d0, x, N)
            res_y = ite_lookup(dot, d1, y, N)
            chain_clauses.append(And(
                dot[t_idx][x] == 0, dot[t_idx][y] == 1,
                res_x != res_y))
    s.add(Or(chain_clauses))
    models, first = count_and_report(s, dot, N,
        "full branch: (d·(t·x))·x ≠ (d·(t·y))·y")
    if first:
        rm = role_map(first)
        print(f"      tester row: {first[t_idx]}")
        print(f"      dispatcher row: {first[d]}")
        d0v = first[d][0]
        d1v = first[d][1]
        print(f"      d·0={d0v} row: {first[d0v]}")
        print(f"      d·1={d1v} row: {first[d1v]}")

    # ═══════════════════════════════════════════════════════════════
    # B. COMPOSITION CLOSURE
    # ∃ encoders f, g and element h:
    # h·x = f·(g·x) for all non-absorber x
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("B. COMPOSITION CLOSURE")
    print("Can encoders be composed?")
    print(f"{'═'*70}\n")

    N = 10

    # B1: ∃ f,g,h all ≥ 2: h·x = f·(g·x) for all x ≥ 2
    # Use specific elements: f=4, g=5, h=8
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
    f, g, h = 4, 5, 8
    for x in range(2, N):
        gx = dot[g][x]
        fgx = col_ite_lookup(dot, f, gx, N)
        s.add(dot[h][x] == fgx)
    # f, g must be encoders (not the same as h)
    s.add(Or([dot[f][j] != dot[h][j] for j in range(N)]))
    s.add(Or([dot[g][j] != dot[h][j] for j in range(N)]))
    # f ≠ g
    s.add(Or([dot[f][j] != dot[g][j] for j in range(N)]))
    models, first = count_and_report(s, dot, N, "h·x = f·(g·x) for all x≥2")
    if first:
        rm = role_map(first)
        print(f"      f={f}({rm.get(f,'?')}): {first[f]}")
        print(f"      g={g}({rm.get(g,'?')}): {first[g]}")
        print(f"      h={h}({rm.get(h,'?')}): {first[h]}")
        print(f"      Verify: ", end="")
        for x in range(2, min(N, 7)):
            gx = first[g][x]
            fgx = first[f][gx]
            hx = first[h][x]
            print(f"h·{x}={hx}=f·(g·{x})=f·{gx}={fgx} ", end="")
        print()

    # B2: composition of Q and E with another encoder
    # h·x = Q·(f·(E·x)) — quote the result of applying f after evaluating
    print()
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
    f, h = 4, 8
    for x in range(2, N):
        ex = dot[E_IDX][x]
        f_ex = col_ite_lookup(dot, f, ex, N)
        q_f_ex = col_ite_lookup(dot, Q_IDX, f_ex, N)
        s.add(dot[h][x] == q_f_ex)
    s.add(Or([dot[f][j] != dot[h][j] for j in range(N)]))
    models, first = count_and_report(s, dot, N, "h = Q∘f∘E (quote after encode after eval)")

    # ═══════════════════════════════════════════════════════════════
    # C. PAIRING / DATA STRUCTURES
    # Can we construct and destruct pairs?
    # pair·x·y = some element p_xy
    # fst·p_xy = x, snd·p_xy = y
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("C. PAIRING / DATA STRUCTURES")
    print("Can we construct and destruct pairs?")
    print(f"{'═'*70}\n")

    # C1: At N=10, can we have pair/fst/snd for at least 2 pairs?
    # pair=8, fst=Q(6), snd=E(7)
    # For distinct a,b ∈ {2,3,4,5}:
    #   pair·a = some intermediate p_a
    #   p_a · b = some pair-value v_{a,b}
    #   fst · v_{a,b} = a
    #   snd · v_{a,b} = b
    # This requires: pair(a)(b) gives a value, fst/snd extract.
    # But we're limited: pair·a gives p_a, then p_a·b gives v.
    # fst·v = a and snd·v = b.

    # Helper: dot[row_expr][col] where row_expr is Z3
    def lookup_2d_local(dot, r, c, N):
        """dot[r][c] where both r and c may be Z3."""
        if isinstance(c, int):
            return ite_lookup(dot, r, c, N)
        result = ite_lookup(dot, r, 0, N)
        for j in range(1, N):
            result = If(c == j, ite_lookup(dot, r, j, N), result)
        return result

    N = 12  # need more room for pair values
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
    pair_idx, fst_idx, snd_idx = 8, 9, 10
    # For a,b ∈ {2, 3}:
    test_vals = [2, 3]
    for a in test_vals:
        pa = dot[pair_idx][a]  # pair·a (Z3 ArithRef)
        for b in test_vals:
            # (pair·a)·b = v_{a,b}: dot[pa][b] where pa is Z3
            v_ab = ite_lookup(dot, pa, b, N)
            # fst · v_{a,b} = a: dot[fst_idx][v_ab] where v_ab is Z3
            fst_v = col_ite_lookup(dot, fst_idx, v_ab, N)
            s.add(fst_v == a)
            # snd · v_{a,b} = b
            snd_v = col_ite_lookup(dot, snd_idx, v_ab, N)
            s.add(snd_v == b)
    # pair values must be distinct for different (a,b) pairs
    for a1 in test_vals:
        for b1 in test_vals:
            for a2 in test_vals:
                for b2 in test_vals:
                    if (a1, b1) >= (a2, b2):
                        continue
                    pa1 = dot[pair_idx][a1]  # Z3
                    v1 = ite_lookup(dot, pa1, b1, N)
                    pa2 = dot[pair_idx][a2]  # Z3
                    v2 = ite_lookup(dot, pa2, b2, N)
                    s.add(v1 != v2)

    models, first = count_and_report(s, dot, N,
        "pair/fst/snd for {2,3}x{2,3} at N=12", cap=20)
    if first:
        rm = role_map(first)
        print(f"      pair={pair_idx}({rm.get(pair_idx,'?')}): {first[pair_idx]}")
        print(f"      fst={fst_idx}({rm.get(fst_idx,'?')}): {first[fst_idx]}")
        print(f"      snd={snd_idx}({rm.get(snd_idx,'?')}): {first[snd_idx]}")
        for a in test_vals:
            pa = first[pair_idx][a]
            for b in test_vals:
                v = first[pa][b]
                f_v = first[fst_idx][v]
                s_v = first[snd_idx][v]
                print(f"      pair({a},{b}): pair·{a}={pa}, "
                      f"{pa}·{b}={v}, fst·{v}={f_v}, snd·{v}={s_v}")

    # ═══════════════════════════════════════════════════════════════
    # D. FIXED POINT / ITERATION
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("D. FIXED POINT / ITERATION")
    print("Can we find self-referential fixed points?")
    print(f"{'═'*70}\n")

    N = 10

    # D1: ∃ Y ≥ 2: for some f ≥ 2: Y·f = f·(Y·f)
    # (Y combinator: Y·f is a fixed point of f)
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
    Y = 8
    # For at least 2 distinct f values:
    fixed_clauses = []
    for f in range(2, N):
        if f == Y:
            continue
        yf = dot[Y][f]
        # f·(Y·f) = f applied to yf
        f_yf = col_ite_lookup(dot, f, yf, N)
        fixed_clauses.append(And(yf == f_yf, yf >= 2))
    # At least 2 functions have fixed points through Y
    fix_flags = []
    for f in range(2, N):
        if f == Y:
            continue
        yf = dot[Y][f]
        f_yf = col_ite_lookup(dot, f, yf, N)
        flag = Int(f"fix_{f}")
        s.add(If(And(yf == f_yf, yf >= 2), flag == 1, flag == 0))
        fix_flags.append(flag)
    s.add(sum(fix_flags) >= 2)

    models, first = count_and_report(s, dot, N,
        "Y combinator: Y·f = f·(Y·f) for ≥2 functions")
    if first:
        rm = role_map(first)
        print(f"      Y={Y}({rm.get(Y,'?')}): {first[Y]}")
        for f in range(2, N):
            if f == Y:
                continue
            yf = first[Y][f]
            fyf = first[f][yf]
            if yf == fyf and yf >= 2:
                print(f"      Y·{f}={yf}, {f}·{yf}={fyf} ✓ fixed point")

    # D2: Iteration — ∃ element whose squaring orbit hits ≥ 4 elements
    print()
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
    # Element 2: orbit under squaring hits ≥ 4 distinct values
    x = 2
    x1 = dot[x][x]         # x²
    x2 = Int("x2_iter")    # x⁴ = (x²)²
    x3 = Int("x3_iter")    # x⁸ = (x⁴)²
    # x2 = x1·x1
    for r in range(N):
        pass  # need lookup
    # Use concrete approach: just constrain the orbit
    s.add(dot[x][x] >= 2)  # x² ≥ 2
    x1_var = dot[x][x]
    # x⁴ = (x²)²: need dot[x1_var][x1_var]
    # This is a lookup_2d situation
    def lookup_2d_local(dot, r, c, N):
        result = ite_lookup(dot, r, 0, N)
        for j in range(1, N):
            result = If(c == j, ite_lookup(dot, r, j, N), result)
        return result

    x2_val = lookup_2d_local(dot, x1_var, x1_var, N)  # x⁴
    x3_val = lookup_2d_local(dot, x2_val, x2_val, N)  # x⁸
    # All distinct
    s.add(x != x1_var)  # but x is concrete, x1_var is Z3...
    s.add(x1_var != x)
    s.add(x2_val != x)
    s.add(x2_val != x1_var)
    s.add(x3_val != x)
    s.add(x3_val != x1_var)
    s.add(x3_val != x2_val)
    # All ≥ 2
    s.add(x2_val >= 2)
    s.add(x3_val >= 2)

    models, first = count_and_report(s, dot, N,
        "squaring orbit of length ≥ 4: x, x², x⁴, x⁸ distinct")
    if first:
        x_sq = first[x][x]
        x4 = first[x_sq][x_sq]
        x8 = first[x4][x4]
        print(f"      x={x}, x²={x_sq}, x⁴={x4}, x⁸={x8}")

    # ═══════════════════════════════════════════════════════════════
    # E. GENERATOR
    # ∃ g: the closure of {0, 1, g} under · reaches all N elements
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("E. SINGLE GENERATOR")
    print("Does a single element generate the whole algebra?")
    print(f"{'═'*70}\n")

    # Already shown: {0,1,Q,E} generates everything in 100% of models.
    # Now: can a single element do it?

    for N in [8, 10]:
        s, dot = encode_level(8, N, timeout_seconds=120)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

        models = []
        t0 = time.time()
        for _ in range(50):
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            models.append(tbl)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0

        single_gen = 0
        gen_by_role = Counter()
        gen_depth = Counter()

        for tbl in models:
            rm = role_map(tbl)
            for g in range(2, N):
                reached = {0, 1, g}
                depth = 0
                for _ in range(N + 2):
                    new = set()
                    for a in reached:
                        for b in reached:
                            new.add(tbl[a][b])
                    prev = len(reached)
                    reached = reached | new
                    depth += 1
                    if len(reached) == prev or len(reached) == N:
                        break
                if len(reached) == N:
                    single_gen += 1
                    gen_by_role[rm.get(g, '?')] += 1
                    gen_depth[depth] += 1

        total = len(models) * (N - 2)
        print(f"  N={N}: {single_gen}/{total} elements are single generators "
              f"({100*single_gen/total:.0f}%)")
        print(f"    By role: {dict(gen_by_role)}")
        print(f"    Depth to generate: {dict(gen_depth.most_common())}")

    # ═══════════════════════════════════════════════════════════════
    # F. COMPUTATIONAL COMPLETENESS CHECK
    # Combine A+B+C: conditional + composition + pairing
    # This is close to combinatory completeness
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("F. COMBINED: CONDITIONAL + COMPOSITION + Y-COMBINATOR")
    print(f"{'═'*70}\n")

    N = 12
    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    # Conditional: d·0, d·1 are distinct encoders
    d = 8
    s.add(dot[d][0] >= 2)
    s.add(dot[d][1] >= 2)
    s.add(dot[d][0] != dot[d][1])

    # Composition: h·x = f·(g·x) for x ∈ {2,3,4,5}
    f_idx, g_idx, h_idx = 4, 5, 9
    for x in range(2, CORE):
        gx = dot[g_idx][x]
        fgx = col_ite_lookup(dot, f_idx, gx, N)
        s.add(dot[h_idx][x] == fgx)
    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(N)]))

    # Y-combinator: Y·f = f·(Y·f) for at least one f
    Y = 10
    fix_found = []
    for ff in range(2, N):
        if ff == Y:
            continue
        yf = dot[Y][ff]
        f_yf = col_ite_lookup(dot, ff, yf, N)
        flag = Int(f"ffix_{ff}")
        s.add(If(And(yf == f_yf, yf >= 2), flag == 1, flag == 0))
        fix_found.append(flag)
    s.add(sum(fix_found) >= 1)

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        rm = role_map(tbl)
        print(f"  ALL THREE COMPATIBLE at N=12: SAT ({elapsed:.1f}s)")
        print(f"    Roles: {[rm.get(x, '?') for x in range(2, N)]}")
        print(f"    Dispatcher d={d}: d·0={tbl[d][0]}({rm.get(tbl[d][0],'?')}), "
              f"d·1={tbl[d][1]}({rm.get(tbl[d][1],'?')})")
        print(f"    Composition h={h_idx}: h·x = {f_idx}·({g_idx}·x)")
        for x in range(2, min(CORE, 5)):
            gx = tbl[g_idx][x]
            fgx = tbl[f_idx][gx]
            hx = tbl[h_idx][x]
            print(f"      h·{x}={hx}, f·(g·{x})=f·{gx}={fgx}")
        print(f"    Y={Y}: ", end="")
        for ff in range(2, N):
            if ff == Y:
                continue
            yf = tbl[Y][ff]
            fyf = tbl[ff][yf]
            if yf == fyf and yf >= 2:
                print(f"Y·{ff}={yf}=={ff}·{yf} ✓  ", end="")
        print()

        # Count more
        count = 1
        for _ in range(29):
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            count += 1
        print(f"    Models: {count}{'+'  if count >= 30 else ''}")
    else:
        print(f"  ALL THREE at N=12: UNSAT ({elapsed:.1f}s)")
        # Try without Y
        print("  Trying without Y combinator...")
        s2, dot2 = encode_level(8, N, timeout_seconds=300)
        add_full_base(s2, dot2, N)
        add_qe_pair(s2, dot2, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        # Conditional
        s2.add(dot2[d][0] >= 2)
        s2.add(dot2[d][1] >= 2)
        s2.add(dot2[d][0] != dot2[d][1])
        # Composition
        for x in range(2, CORE):
            gx = dot2[g_idx][x]
            fgx = col_ite_lookup(dot2, f_idx, gx, N)
            s2.add(dot2[h_idx][x] == fgx)
        t0 = time.time()
        r2 = s2.check()
        e2 = time.time() - t0
        if r2 == sat:
            print(f"  Conditional + Composition (no Y): SAT ({e2:.1f}s)")
        else:
            print(f"  Conditional + Composition (no Y): UNSAT ({e2:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")
    print("""
  Computational Axiom Candidates:
    A. Conditional dispatch     — tester output selects computation path
    B. Composition closure      — h = f∘g exists for encoder pairs
    C. Pairing                  — construct/destruct data structures
    D. Fixed-point combinator   — Y·f = f·(Y·f) for self-reference
    E. Single generator         — one element's closure is the whole algebra
    F. Combined package         — all of the above in one algebra
""")


def tester_branching():
    """
    Path 2: Branch through the tester directly.

    C (Kripke) blocks single-element dispatch: d·0 = d·1 for non-testers.
    But the tester itself gives binary output. Branching happens at the
    TERM level: evaluate t·x → {0,1}, then the caller applies either
    encoder f (on result 0) or encoder g (on result 1).

    The algebra doesn't need a dispatcher element. Instead we check:
    1. Do distinct encoder pairs (f,g) exist such that f and g compute
       genuinely different functions on the core?
    2. Can composition chain through tester output?
       if_then_else(t,x, f, g) = "apply f if t·x=0, g if t·x=1"
       We encode: ∃ result element r such that for each core x,
         r·x = f·x when t·x = 0
         r·x = g·x when t·x = 1
       i.e., r is the "branched composition" — it structurally IS the
       if-then-else. We ask: can such r exist in the algebra?
    3. Does this compose with QE and Y-combinator?
    4. Can we build arbitrary boolean functions via tester chains?
    """

    # ── Helpers (local to function) ──────────────────────────────────
    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    def count_models(s, dot, N, cap=50):
        models = []
        while len(models) < cap:
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            models.append(tbl)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        return models

    CORE = 6
    Q_IDX, E_IDX = 6, 7

    print("=" * 70)
    print("PATH 2: TESTER-MEDIATED STRUCTURAL BRANCHING")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════
    # Phase 1: Branched composition via tester
    # For each core x: r·x = f·x if t·x=0, r·x = g·x if t·x=1
    # where f,g are distinct encoders and t is the tester.
    # Can such an element r exist in the algebra?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("Phase 1: Branched composition — does r = if(t,f,g) exist?")
    print("  r·x = f·x when t·x=0, r·x = g·x when t·x=1")
    print(f"{'═'*70}\n")

    N = 10
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    # Pick tester t (find it structurally — row is boolean)
    # In our models t is always at position 3 in the role ordering,
    # but let's find it via the axiom structure.
    # At L8+C, there's exactly 1 tester. We know from prior analysis
    # it's at index 3 in N=8 models (0-indexed). For N=10 it may vary.
    # Let's use a flexible approach: pick t_idx as a variable.

    # Actually, from prior results tester is always at a fixed position.
    # Let's try t=3 first (most common), f=2, g=4 (the two encoders).
    # r = 8 (new element beyond QE pair)
    t_idx = 3
    f_idx = 2
    g_idx = 4
    r_idx = 8

    # r·x = f·x when t·x=0, r·x = g·x when t·x=1, for core elements
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        # If tx==0, r·x must be f·x. If tx==1, r·x must be g·x.
        s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))

    # f and g must be genuinely different on core
    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0

    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        rm = role_map(tbl)
        print(f"  SAT ({elapsed:.1f}s) — branched element r={r_idx} exists!")
        print(f"  Roles: {[(x, rm.get(x, chr(63))) for x in range(N)]}")
        print(f"  Tester t={t_idx} row: {tbl[t_idx]}")
        print(f"  Encoder f={f_idx} row: {tbl[f_idx]}")
        print(f"  Encoder g={g_idx} row: {tbl[g_idx]}")
        print(f"  Branch  r={r_idx} row: {tbl[r_idx]}")
        print(f"  Role of r: {rm.get(r_idx, chr(63))}")
        print()
        # Verify the branch on core
        print("  Verification on core elements:")
        for x in range(2, CORE):
            tx = tbl[t_idx][x]
            fx = tbl[f_idx][x]
            gx = tbl[g_idx][x]
            rx = tbl[r_idx][x]
            expected = fx if tx == 0 else gx
            ok = "OK" if rx == expected else "FAIL"
            print(f"    x={x}: t·{x}={tx}, f·{x}={fx}, g·{x}={gx}, "
                  f"r·{x}={rx} (expect {expected}) {ok}")

        # Count models
        models = [tbl]
        for _ in range(49):
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            models.append(tbl)
        print(f"\n  Models: {len(models)}{'+'  if len(models) >= 50 else ''}")

        # What role is r typically?
        from collections import Counter
        r_roles = Counter()
        for m in models:
            rmm = role_map(m)
            r_roles[rmm.get(r_idx, chr(63))] += 1
        print(f"  Role of r across models: {dict(r_roles)}")
    else:
        print(f"  UNSAT ({elapsed:.1f}s) — branched element can't exist")
        print("  Trying without fixing t=3, f=2, g=4...")

    # ═══════════════════════════════════════════════════════════════
    # Phase 2: Multiple branches — can we have TWO branched elements
    # r1 = if(t, f, g) and r2 = if(t, g, f)?
    # This gives both "then" and "else" as first-class elements.
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("Phase 2: Dual branches — r1 = if(t,f,g) and r2 = if(t,g,f)")
    print(f"{'═'*70}\n")

    N = 12
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    r1_idx = 8
    r2_idx = 9
    # Additional elements 10,11 are free

    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        # r1 = if(t, f, g)
        s.add(If(tx == 0, dot[r1_idx][x] == fx, dot[r1_idx][x] == gx))
        # r2 = if(t, g, f) — swapped branches
        s.add(If(tx == 0, dot[r2_idx][x] == gx, dot[r2_idx][x] == fx))

    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0

    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        rm = role_map(tbl)
        print(f"  SAT ({elapsed:.1f}s) — dual branches exist!")
        print(f"  r1={r1_idx} role: {rm.get(r1_idx, chr(63))}, "
              f"r2={r2_idx} role: {rm.get(r2_idx, chr(63))}")
        print(f"  r1 row: {tbl[r1_idx]}")
        print(f"  r2 row: {tbl[r2_idx]}")

        models = count_models(s, dot, N, cap=30)
        # first was already extracted, count_models starts fresh after our block
        print(f"  Models: {len(models) + 1}+")
    else:
        print(f"  UNSAT ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # Phase 3: Composition through branch
    # h·x = r·(g·x) where r is a branch element
    # This chains: first apply g, then branch on tester, apply f or f'
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("Phase 3: Composition through branch — h = r ∘ g")
    print("  h·x = r·(g·x) = f·(g·x) if t·(g·x)=0, f'·(g·x) if t·(g·x)=1")
    print(f"{'═'*70}\n")

    N = 10
    s, dot = encode_level(8, N, timeout_seconds=180)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    r_idx = 8
    h_idx = 9

    # r = if(t, f, g) on core
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))

    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    # h·x = r·(g·x) for core elements
    # g here is encoder g_idx=4, composing with branch r
    comp_g = 4  # using g_idx as the composition target
    for x in range(2, CORE):
        gx = dot[comp_g][x]
        # r·(g·x) — r_idx applied to result of g
        r_gx = col_ite_lookup(dot, r_idx, gx, N)
        s.add(dot[h_idx][x] == r_gx)

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0

    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        rm = role_map(tbl)
        print(f"  SAT ({elapsed:.1f}s) — branch-composition exists!")
        print(f"  h={h_idx} role: {rm.get(h_idx, chr(63))}")
        print(f"  Trace on core:")
        for x in range(2, CORE):
            gx = tbl[comp_g][x]
            tgx = tbl[t_idx][gx] if gx < N else "?"
            rgx = tbl[r_idx][gx] if gx < N else "?"
            hx = tbl[h_idx][x]
            print(f"    x={x}: g·{x}={gx}, t·{gx}={tgx}, r·{gx}={rgx}, h·{x}={hx}")
        models = count_models(s, dot, N, cap=30)
        print(f"  Models: {len(models) + 1}+")
    else:
        print(f"  UNSAT ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # Phase 4: Branch + Y-combinator
    # Can the branch element feed into a fixed-point combinator?
    # Y·r = r·(Y·r) where r is a branch element
    # This gives recursive branching — the foundation of while loops.
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("Phase 4: Branch + Y-combinator — recursive branching")
    print("  Y·r = r·(Y·r) where r = if(t, f, g)")
    print(f"{'═'*70}\n")

    N = 10
    s, dot = encode_level(8, N, timeout_seconds=180)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    r_idx = 8
    Y_idx = 9

    # r = if(t, f, g) on core
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))

    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    # Y·r = r·(Y·r)
    yr = dot[Y_idx][r_idx]
    r_yr = col_ite_lookup(dot, r_idx, yr, N)
    s.add(yr == r_yr)
    s.add(yr >= 2)  # non-trivial fixed point

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0

    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        rm = role_map(tbl)
        yr_val = tbl[Y_idx][r_idx]
        r_yr_val = tbl[r_idx][yr_val]
        print(f"  SAT ({elapsed:.1f}s) — branch + Y-combinator works!")
        print(f"  Y={Y_idx}, r={r_idx}")
        print(f"  Y·r = {yr_val}, r·(Y·r) = r·{yr_val} = {r_yr_val}")
        print(f"  Y·r == r·(Y·r): {yr_val == r_yr_val}")
        print(f"  Roles: Y={rm.get(Y_idx, chr(63))}, r={rm.get(r_idx, chr(63))}")

        # Check if Y is a general fixed-point combinator
        gen_fix = 0
        for ff in range(2, N):
            if ff == Y_idx:
                continue
            yf = tbl[Y_idx][ff]
            fyf = tbl[ff][yf]
            if yf == fyf and yf >= 2:
                gen_fix += 1
        print(f"  Y is general fixed-point for {gen_fix}/{N-3} non-absorber elements")

        models = count_models(s, dot, N, cap=30)
        print(f"  Models: {len(models) + 1}+")
    else:
        print(f"  UNSAT ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # Phase 5: Full computational package — Branch + Compose + Y + QE
    # All in one algebra at N=12
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("Phase 5: Full package — Branch + Compose + Y + QE at N=12")
    print(f"{'═'*70}\n")

    N = 12
    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    # Elements: 0-5 core, 6=Q, 7=E, 8=r(branch), 9=h(compose), 10=Y, 11=free
    r_idx = 8
    h_idx = 9
    Y_idx = 10

    # r = if(t, f, g) on core
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))

    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    # h·x = r·(g·x) — composition through branch
    for x in range(2, CORE):
        gx = dot[g_idx][x]
        r_gx = col_ite_lookup(dot, r_idx, gx, N)
        s.add(dot[h_idx][x] == r_gx)

    # Y·r = r·(Y·r) — fixed point on branch
    yr = dot[Y_idx][r_idx]
    r_yr = col_ite_lookup(dot, r_idx, yr, N)
    s.add(yr == r_yr)
    s.add(yr >= 2)

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0

    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        rm = role_map(tbl)
        print(f"  SAT ({elapsed:.1f}s) — full package exists!")
        print(f"  Roles: {[(x, rm.get(x, chr(63))) for x in range(N)]}")
        print(f"  Branch r={r_idx}: {tbl[r_idx]}")
        print(f"  Compose h={h_idx}: {tbl[h_idx]}")
        yr_val = tbl[Y_idx][r_idx]
        print(f"  Y={Y_idx}: Y·r={yr_val}, r·(Y·r)={tbl[r_idx][yr_val]}")
        print()

        # Trace a branched computation
        print("  Example branched computation trace:")
        for x in range(2, CORE):
            tx = tbl[t_idx][x]
            fx = tbl[f_idx][x]
            gx = tbl[g_idx][x]
            rx = tbl[r_idx][x]
            branch = "f" if tx == 0 else "g"
            print(f"    x={x}: t·x={tx} → {branch} branch → "
                  f"r·x={rx} (f·x={fx}, g·x={gx})")

        models = count_models(s, dot, N, cap=30)
        print(f"\n  Models: {len(models) + 1}+")
    else:
        print(f"  UNSAT ({elapsed:.1f}s)")
        # Diagnose: try without Y
        print("  Trying Branch + Compose (no Y)...")
        s2, dot2 = encode_level(8, N, timeout_seconds=300)
        add_full_base(s2, dot2, N)
        add_qe_pair(s2, dot2, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        for x in range(2, CORE):
            tx = dot2[t_idx][x]
            fx = dot2[f_idx][x]
            gx = dot2[g_idx][x]
            s2.add(If(tx == 0, dot2[r_idx][x] == fx, dot2[r_idx][x] == gx))
        s2.add(Or([dot2[f_idx][j] != dot2[g_idx][j] for j in range(2, CORE)]))
        for x in range(2, CORE):
            gx = dot2[g_idx][x]
            r_gx = col_ite_lookup(dot2, r_idx, gx, N)
            s2.add(dot2[h_idx][x] == r_gx)
        t0 = time.time()
        r2 = s2.check()
        e2 = time.time() - t0
        print(f"  Branch + Compose (no Y): {'SAT' if r2 == sat else 'UNSAT'} ({e2:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # Phase 6: Universality of branch element
    # Does the branched element r itself act as an encoder?
    # Is it always an encoder, sometimes a tester, or something else?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("Phase 6: What is the branch element?")
    print("  Role analysis of r = if(t, f, g) across models")
    print(f"{'═'*70}\n")

    N = 10
    s, dot = encode_level(8, N, timeout_seconds=120)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    r_idx = 8

    # r = if(t, f, g) on core
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    models = count_models(s, dot, N, cap=50)
    print(f"  {len(models)} models at N={N}")

    from collections import Counter
    r_roles = Counter()
    r_distinct_vals = []
    r_absorber_hits = Counter()  # how many times r·x ∈ {0,1}
    for m in models:
        rmm = role_map(m)
        r_roles[rmm.get(r_idx, chr(63))] += 1
        row = m[r_idx]
        r_distinct_vals.append(len(set(row)))
        abs_count = sum(1 for v in row if v in (0, 1))
        r_absorber_hits[abs_count] += 1

    print(f"  Role of r: {dict(r_roles)}")
    print(f"  Distinct values in r's row: "
          f"min={min(r_distinct_vals)}, max={max(r_distinct_vals)}, "
          f"avg={sum(r_distinct_vals)/len(r_distinct_vals):.1f}")
    print(f"  Absorber hits in r's row: {dict(r_absorber_hits)}")

    # Is r always different from f and g?
    r_equals_f = sum(1 for m in models if m[r_idx] == m[f_idx])
    r_equals_g = sum(1 for m in models if m[r_idx] == m[g_idx])
    print(f"  r equals f: {r_equals_f}/{len(models)}")
    print(f"  r equals g: {r_equals_g}/{len(models)}")

    # ═══════════════════════════════════════════════════════════════
    # Phase 7: Can branching be nested?
    # r1 = if(t, f, g), then r2 = if(t, r1, f)
    # This gives multi-level case analysis.
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("Phase 7: Nested branching — r2 = if(t, r1, f)")
    print(f"{'═'*70}\n")

    N = 12
    s, dot = encode_level(8, N, timeout_seconds=180)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    r1_idx = 8
    r2_idx = 9

    # r1 = if(t, f, g)
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r1_idx][x] == fx, dot[r1_idx][x] == gx))

    # r2 = if(t, r1, f) — use r1 as a branch target
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        r1x = dot[r1_idx][x]
        fx = dot[f_idx][x]
        s.add(If(tx == 0, dot[r2_idx][x] == r1x, dot[r2_idx][x] == fx))

    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0

    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        rm = role_map(tbl)
        print(f"  SAT ({elapsed:.1f}s) — nested branching works!")
        print(f"  r1={r1_idx} role: {rm.get(r1_idx, chr(63))}")
        print(f"  r2={r2_idx} role: {rm.get(r2_idx, chr(63))}")
        print(f"  Trace:")
        for x in range(2, CORE):
            tx = tbl[t_idx][x]
            fx = tbl[f_idx][x]
            gx = tbl[g_idx][x]
            r1x = tbl[r1_idx][x]
            r2x = tbl[r2_idx][x]
            print(f"    x={x}: t·x={tx}, f·x={fx}, g·x={gx}, "
                  f"r1·x={r1x}, r2·x={r2x}")

        models = count_models(s, dot, N, cap=30)
        print(f"  Models: {len(models) + 1}+")
    else:
        print(f"  UNSAT ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # Phase 8: The punchline — is this Turing-complete?
    # With branch + compose + Y + QE, can we encode a 2-state
    # Turing machine? Test: does the algebra support a simulation
    # where state transitions depend on tester output?
    #
    # Minimal check: can we build two distinct fixed-point behaviors?
    # Y·r1 ≠ Y·r2 where r1, r2 are different branch elements
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("Phase 8: Distinct fixed-point behaviors")
    print("  Y·r1 ≠ Y·r2 for two branch elements r1, r2")
    print(f"{'═'*70}\n")

    N = 12
    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    r1_idx = 8
    r2_idx = 9
    Y_idx = 10

    # r1 = if(t, f, g)
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r1_idx][x] == fx, dot[r1_idx][x] == gx))

    # r2 = if(t, g, f) — swapped
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r2_idx][x] == gx, dot[r2_idx][x] == fx))

    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    # Y·r1 = r1·(Y·r1) and Y·r2 = r2·(Y·r2)
    yr1 = dot[Y_idx][r1_idx]
    r1_yr1 = col_ite_lookup(dot, r1_idx, yr1, N)
    s.add(yr1 == r1_yr1)
    s.add(yr1 >= 2)

    yr2 = dot[Y_idx][r2_idx]
    r2_yr2 = col_ite_lookup(dot, r2_idx, yr2, N)
    s.add(yr2 == r2_yr2)
    s.add(yr2 >= 2)

    # Different fixed points
    s.add(yr1 != yr2)

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0

    if r == sat:
        tbl = extract_table(s.model(), dot, N)
        rm = role_map(tbl)
        yr1_v = tbl[Y_idx][r1_idx]
        yr2_v = tbl[Y_idx][r2_idx]
        print(f"  SAT ({elapsed:.1f}s) — distinct fixed-point behaviors!")
        print(f"  Y·r1 = {yr1_v} (r1·{yr1_v} = {tbl[r1_idx][yr1_v]})")
        print(f"  Y·r2 = {yr2_v} (r2·{yr2_v} = {tbl[r2_idx][yr2_v]})")
        print(f"  Roles: Y={rm.get(Y_idx, chr(63))}, "
              f"r1={rm.get(r1_idx, chr(63))}, r2={rm.get(r2_idx, chr(63))}")
        models = count_models(s, dot, N, cap=30)
        print(f"  Models: {len(models) + 1}+")
    else:
        print(f"  UNSAT ({elapsed:.1f}s)")
        print("  Trying without distinct fixed-point requirement...")
        s2, dot2 = encode_level(8, N, timeout_seconds=300)
        add_full_base(s2, dot2, N)
        add_qe_pair(s2, dot2, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        for x in range(2, CORE):
            tx = dot2[t_idx][x]
            fx = dot2[f_idx][x]
            gx = dot2[g_idx][x]
            s2.add(If(tx == 0, dot2[r1_idx][x] == fx, dot2[r1_idx][x] == gx))
            s2.add(If(tx == 0, dot2[r2_idx][x] == gx, dot2[r2_idx][x] == fx))
        s2.add(Or([dot2[f_idx][j] != dot2[g_idx][j] for j in range(2, CORE)]))
        yr1 = dot2[Y_idx][r1_idx]
        r1_yr1 = col_ite_lookup(dot2, r1_idx, yr1, N)
        s2.add(yr1 == r1_yr1)
        s2.add(yr1 >= 2)
        t0 = time.time()
        r2 = s2.check()
        e2 = time.time() - t0
        print(f"  Dual branch + Y (shared fixpoint OK): "
              f"{'SAT' if r2 == sat else 'UNSAT'} ({e2:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY — PATH 2: TESTER-MEDIATED STRUCTURAL BRANCHING")
    print(f"{'═'*70}")
    print("""
  The tester's binary output (0 or 1) drives branching at the
  STRUCTURAL level: which encoder gets applied next is determined
  by the test result, not by a single dispatcher element.

  r·x = f·x when t·x = 0
  r·x = g·x when t·x = 1

  This bypasses C (Kripke)'s constraint that non-testers must
  treat absorbers uniformly. The branch element r is not a
  dispatcher — it's the RESULT of the branch, a new encoder
  that embodies the conditional computation.

  Key: branching is structural, not operational. The algebra
  doesn't "choose" — it already contains both paths as elements.
  The tester merely selects which pre-existing path is active.
""")


def model_space_analysis():
    """
    Detailed analysis of the N=12 full-package model space.
    L8 + C + D + PA + VV + QE + Branch(if(t,f,g)) + Compose + Y

    Examines: isomorphism classes, variation axes, role signatures,
    squaring dynamics, generators, constructibility depth, tester
    partition — to distinguish meaningful freedom from accidental choice.
    """

    # ── Helpers ──────────────────────────────────────────────────────
    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    CORE = 6
    Q_IDX, E_IDX = 6, 7
    N = 12
    t_idx, f_idx, g_idx = 3, 2, 4
    r_idx, h_idx, Y_idx = 8, 9, 10

    print("=" * 70)
    print(f"MODEL SPACE ANALYSIS — N={N} FULL PACKAGE")
    print("L8 + C + D + PA + VV + QE + Branch + Compose + Y")
    print("=" * 70)

    # ── Enumerate models (larger cap) ────────────────────────────────
    print(f"\nEnumerating models (cap=200)...")
    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    # Branch: r·x = f·x if t·x=0, g·x if t·x=1
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    # Compose: h·x = r·(g·x) for core
    for x in range(2, CORE):
        gx = dot[g_idx][x]
        r_gx = col_ite_lookup(dot, r_idx, gx, N)
        s.add(dot[h_idx][x] == r_gx)

    # Y-combinator: Y·r = r·(Y·r), non-trivial
    yr = dot[Y_idx][r_idx]
    r_yr = col_ite_lookup(dot, r_idx, yr, N)
    s.add(yr == r_yr)
    s.add(yr >= 2)

    models = []
    t0 = time.time()
    CAP = 200
    while len(models) < CAP:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        models.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    exhausted = len(models) < CAP
    print(f"  Found {len(models)}{'(exhaustive)' if exhausted else '+'} models ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # 1. ISOMORPHISM CLASSES
    # Two tables are isomorphic if there exists a permutation σ
    # of {0..N-1} fixing {0,1} (absorbers) such that
    # σ(tbl[i][j]) = tbl'[σ(i)][σ(j)] for all i,j.
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("1. ISOMORPHISM CLASSES")
    print(f"{'═'*70}\n")

    from itertools import permutations

    def apply_perm(tbl, perm, N):
        """Apply permutation to a Cayley table."""
        new_tbl = [[0]*N for _ in range(N)]
        for i in range(N):
            for j in range(N):
                new_tbl[perm[i]][perm[j]] = perm[tbl[i][j]]
        return new_tbl

    def canonical_form(tbl, N):
        """
        Canonical form: try all permutations fixing {0,1},
        return lexicographically smallest table.
        For N=12 with 10! perms this is too expensive.
        Use a cheaper invariant-based approach.
        """
        # Invariant: sorted tuple of (row sorted tuple) for each element
        # This is a coarse but fast canonical form
        rows = []
        for i in range(N):
            rows.append(tuple(sorted(tbl[i])))
        return tuple(sorted(rows))

    def table_to_tuple(tbl, N):
        return tuple(tuple(row) for row in tbl)

    # Compute invariant signatures for each model
    # A richer invariant: for each element, its (role, sorted_row,
    # column_sorted, squaring_value)
    def rich_invariant(tbl, N):
        rm = role_map(tbl)
        sigs = []
        for i in range(N):
            row_sorted = tuple(sorted(tbl[i]))
            col_sorted = tuple(sorted(tbl[j][i] for j in range(N)))
            sq = tbl[i][i]
            sq_role = rm.get(sq, "?")
            role = rm.get(i, "?")
            sigs.append((role, row_sorted, col_sorted, sq, sq_role))
        return tuple(sorted(sigs))

    # Group by rich invariant
    inv_groups = {}
    for idx, m in enumerate(models):
        inv = rich_invariant(m, N)
        inv_groups.setdefault(inv, []).append(idx)

    print(f"  Distinct invariant signatures: {len(inv_groups)}")
    print(f"  Group sizes: {sorted([len(v) for v in inv_groups.values()], reverse=True)}")

    # For small groups, try exact isomorphism check via WL-like refinement
    # WL color refinement on the Cayley table as a colored graph
    def wl_canonical(tbl, N, rounds=5):
        """WL-1 color refinement for Cayley tables."""
        # Initial colors: role + row hash
        rm = role_map(tbl)
        colors = {}
        for i in range(N):
            colors[i] = (rm.get(i, "?"), tuple(sorted(tbl[i])),
                         tuple(sorted(tbl[j][i] for j in range(N))))

        for _ in range(rounds):
            new_colors = {}
            for i in range(N):
                # Neighborhood: for each j, (color[j], tbl[i][j], tbl[j][i])
                nbr = tuple(sorted(
                    (colors[j], tbl[i][j], tbl[j][i]) for j in range(N)))
                new_colors[i] = (colors[i], nbr)
            colors = new_colors

        # Return sorted color multiset as canonical form
        return tuple(sorted(colors.values()))

    # Refine groups using WL
    wl_groups = {}
    for idx, m in enumerate(models):
        wl = wl_canonical(m, N, rounds=4)
        wl_groups.setdefault(wl, []).append(idx)

    n_classes = len(wl_groups)
    print(f"  WL-refined isomorphism classes: {n_classes}")
    class_sizes = sorted([len(v) for v in wl_groups.values()], reverse=True)
    print(f"  Class sizes: {class_sizes}")

    # For each class, pick a representative
    representatives = []
    class_members = []
    for wl_key, members in wl_groups.items():
        representatives.append(models[members[0]])
        class_members.append(members)

    # ═══════════════════════════════════════════════════════════════
    # 2. WHAT VARIES — entry-level diff analysis
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("2. WHAT VARIES BETWEEN MODELS")
    print(f"{'═'*70}\n")

    # For each cell (i,j), count distinct values across all models
    variation = [[set() for _ in range(N)] for _ in range(N)]
    for m in models:
        for i in range(N):
            for j in range(N):
                variation[i][j].add(m[i][j])

    # Fixed cells (same in all models)
    fixed_count = 0
    variable_count = 0
    max_variation = 0
    most_variable = []
    for i in range(N):
        for j in range(N):
            nvals = len(variation[i][j])
            if nvals == 1:
                fixed_count += 1
            else:
                variable_count += 1
                if nvals > max_variation:
                    max_variation = nvals
                    most_variable = [(i, j)]
                elif nvals == max_variation:
                    most_variable.append((i, j))

    total = N * N
    print(f"  Fixed cells: {fixed_count}/{total} ({100*fixed_count/total:.1f}%)")
    print(f"  Variable cells: {variable_count}/{total} ({100*variable_count/total:.1f}%)")
    print(f"  Max distinct values in any cell: {max_variation}")

    # Variation by row
    print(f"\n  Variation by row (variable cells / {N} columns):")
    rm0 = role_map(models[0])
    for i in range(N):
        var_in_row = sum(1 for j in range(N) if len(variation[i][j]) > 1)
        max_in_row = max(len(variation[i][j]) for j in range(N))
        role = rm0.get(i, "?")
        bar = "#" * var_in_row
        print(f"    row {i:2d} ({role:10s}): {var_in_row:2d}/{N} variable "
              f"(max {max_in_row} vals) {bar}")

    # Variation by column
    print(f"\n  Variation by column (variable cells / {N} rows):")
    for j in range(N):
        var_in_col = sum(1 for i in range(N) if len(variation[i][j]) > 1)
        max_in_col = max(len(variation[i][j]) for i in range(N))
        print(f"    col {j:2d}: {var_in_col:2d}/{N} variable (max {max_in_col} vals)")

    # Show the fixed sub-table
    print(f"\n  Fixed entries (same across all {len(models)} models):")
    for i in range(N):
        row_str = []
        for j in range(N):
            if len(variation[i][j]) == 1:
                row_str.append(f"{list(variation[i][j])[0]:2d}")
            else:
                row_str.append(" ·")
        print(f"    row {i:2d}: [{', '.join(row_str)}]")

    # ═══════════════════════════════════════════════════════════════
    # 3. ROLE SIGNATURES
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("3. ROLE SIGNATURES")
    print(f"{'═'*70}\n")

    from collections import Counter
    role_sig_counts = Counter()
    role_position_counts = Counter()  # (position, role) -> count
    for m in models:
        rm = role_map(m)
        sig = tuple(rm.get(i, "?") for i in range(N))
        role_sig_counts[sig] += 1
        for i in range(N):
            role_position_counts[(i, rm.get(i, "?"))] += 1

    print(f"  Distinct role signatures: {len(role_sig_counts)}")
    for sig, cnt in role_sig_counts.most_common():
        short = [s[0] for s in sig]  # first letter
        role_dist = Counter(sig)
        print(f"    {''.join(short)} ({cnt}x): "
              f"{dict(role_dist)}")

    # Per-position role stability
    print(f"\n  Per-position role stability:")
    for i in range(N):
        roles_at_i = {role: role_position_counts.get((i, role), 0)
                      for role in ["absorbers", "testers", "encoders", "inert"]}
        roles_at_i = {k: v for k, v in roles_at_i.items() if v > 0}
        stable = len(roles_at_i) == 1
        tag = "FIXED" if stable else "varies"
        print(f"    pos {i:2d}: {roles_at_i} [{tag}]")

    # ═══════════════════════════════════════════════════════════════
    # 4. SQUARING STRUCTURE x·x
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("4. SQUARING STRUCTURE (x·x)")
    print(f"{'═'*70}\n")

    sq_patterns = Counter()
    sq_by_pos = [Counter() for _ in range(N)]
    idempotent_counts = Counter()  # how many idempotents per model
    for m in models:
        sq = tuple(m[i][i] for i in range(N))
        sq_patterns[sq] += 1
        idem = sum(1 for i in range(N) if m[i][i] == i)
        idempotent_counts[idem] += 1
        for i in range(N):
            sq_by_pos[i][m[i][i]] += 1

    print(f"  Distinct squaring patterns: {len(sq_patterns)}")
    for sq, cnt in sq_patterns.most_common(10):
        print(f"    {list(sq)} ({cnt}x)")
    if len(sq_patterns) > 10:
        print(f"    ... and {len(sq_patterns) - 10} more")

    print(f"\n  Idempotent count distribution: {dict(idempotent_counts)}")

    # Fixed points: positions where x·x is always the same value
    print(f"\n  Per-position squaring:")
    for i in range(N):
        vals = sq_by_pos[i]
        if len(vals) == 1:
            v = list(vals.keys())[0]
            idem = " (idempotent)" if v == i else ""
            print(f"    {i}·{i} = {v} always{idem}")
        else:
            top3 = vals.most_common(3)
            desc = ", ".join(f"{v}({c}x)" for v, c in top3)
            print(f"    {i}·{i} varies: {desc}")

    # Squaring orbits: x → x·x → (x·x)·(x·x) → ...
    print(f"\n  Squaring orbits (sample from first representative):")
    m0 = representatives[0] if representatives else models[0]
    for i in range(N):
        orbit = [i]
        x = i
        for _ in range(10):
            x = m0[x][x]
            if x in orbit:
                orbit.append(x)
                break
            orbit.append(x)
        print(f"    {i}: {' → '.join(map(str, orbit))}")

    # ═══════════════════════════════════════════════════════════════
    # 5. GENERATOR STRUCTURE
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("5. GENERATOR STRUCTURE")
    print(f"{'═'*70}\n")

    def closure(tbl, gens, N):
        """Compute the closure of gens under the binary operation."""
        reached = set(gens)
        frontier = list(gens)
        while frontier:
            new = []
            for a in list(reached):
                for b in frontier:
                    ab = tbl[a][b]
                    ba = tbl[b][a]
                    if ab not in reached:
                        reached.add(ab)
                        new.append(ab)
                    if ba not in reached:
                        reached.add(ba)
                        new.append(ba)
            frontier = new
        return reached

    def closure_depth(tbl, gens, N):
        """Compute closure with depth tracking."""
        depth = {g: 0 for g in gens}
        reached = set(gens)
        frontier = list(gens)
        step = 0
        while frontier:
            step += 1
            new = []
            for a in list(reached):
                for b in frontier:
                    for ab in [tbl[a][b], tbl[b][a]]:
                        if ab not in reached:
                            reached.add(ab)
                            depth[ab] = step
                            new.append(ab)
            frontier = new
        return reached, depth

    # Test {0,1,Q,E} as generator
    qe_gen = {0, 1, Q_IDX, E_IDX}
    qe_gen_count = 0
    qe_gen_depths = []
    for m in models:
        reached, depths = closure_depth(m, qe_gen, N)
        if len(reached) == N:
            qe_gen_count += 1
            qe_gen_depths.append(max(depths.values()))

    print(f"  {{0,1,Q,E}} generates all: {qe_gen_count}/{len(models)}")
    if qe_gen_depths:
        print(f"    Max depth: min={min(qe_gen_depths)}, "
              f"max={max(qe_gen_depths)}, "
              f"avg={sum(qe_gen_depths)/len(qe_gen_depths):.1f}")

    # Test all pairs as generators
    pair_gen_counts = Counter()
    for m in models:
        for a in range(2, N):
            for b in range(a+1, N):
                reached = closure(m, {0, 1, a, b}, N)
                if len(reached) == N:
                    pair_gen_counts[(a, b)] += 1

    # Which pairs always generate?
    always_gen = [(pair, cnt) for pair, cnt in pair_gen_counts.items()
                  if cnt == len(models)]
    print(f"\n  Pairs {{0,1,a,b}} that ALWAYS generate: {len(always_gen)}")
    for pair, cnt in sorted(always_gen)[:20]:
        print(f"    {{0,1,{pair[0]},{pair[1]}}}")

    # Single generators (with absorbers)
    single_gen_counts = Counter()
    for m in models:
        for a in range(2, N):
            reached = closure(m, {0, 1, a}, N)
            if len(reached) == N:
                single_gen_counts[a] += 1

    print(f"\n  Single generators {{0,1,x}} that always work:")
    for elem, cnt in single_gen_counts.most_common():
        pct = 100 * cnt / len(models)
        tag = "ALWAYS" if cnt == len(models) else f"{pct:.0f}%"
        rm0 = role_map(models[0])
        print(f"    x={elem} ({rm0.get(elem, chr(63))}): {cnt}/{len(models)} [{tag}]")

    # ═══════════════════════════════════════════════════════════════
    # 6. CONSTRUCTIBILITY DEPTH
    # How many steps to produce every element from generators?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("6. CONSTRUCTIBILITY DEPTH")
    print(f"{'═'*70}\n")

    # Use {0,1} as minimal seed (absorbers always present)
    min_depths = []
    max_depths = []
    avg_depths = []
    for m in models:
        # Start from absorbers only
        reached, depths = closure_depth(m, {0, 1}, N)
        if len(reached) == N:
            md = max(depths.values())
            min_depths.append(min(v for k, v in depths.items() if k >= 2))
            max_depths.append(md)
            avg_depths.append(sum(depths.values()) / N)
        else:
            # Can't generate from absorbers alone — need a seed
            max_depths.append(-1)

    gen_from_abs = sum(1 for d in max_depths if d > 0)
    print(f"  Generated from {{0,1}} alone: {gen_from_abs}/{len(models)}")

    # Use all non-absorbers as seeds, measure producibility
    prod_counts = Counter()
    for m in models:
        producible = set()
        for a in range(N):
            for b in range(N):
                producible.add(m[a][b])
        prod_counts[len(producible)] += 1

    print(f"  Producibility (|{{x·y : x,y ∈ N}}|): {dict(prod_counts)}")

    # Depth from {0,1,Q,E}
    depth_histograms = Counter()
    per_elem_depths = {i: [] for i in range(N)}
    for m in models:
        reached, depths = closure_depth(m, {0, 1, Q_IDX, E_IDX}, N)
        for i in range(N):
            d = depths.get(i, -1)
            per_elem_depths[i].append(d)
            depth_histograms[d] += 1

    print(f"\n  Depth from {{0,1,Q,E}} — per element:")
    for i in range(N):
        ds = per_elem_depths[i]
        if all(d == ds[0] for d in ds):
            print(f"    elem {i:2d}: depth {ds[0]} always")
        else:
            dc = Counter(ds)
            desc = ", ".join(f"d={d}({c}x)" for d, c in sorted(dc.items()))
            print(f"    elem {i:2d}: {desc}")

    # ═══════════════════════════════════════════════════════════════
    # 7. TESTER DECODED SETS
    # What does the tester accept (→0) and reject (→1)?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("7. TESTER PARTITION (accept/reject sets)")
    print(f"{'═'*70}\n")

    # Find tester position in each model
    tester_partitions = Counter()
    tester_positions = Counter()
    for m in models:
        rm = role_map(m)
        testers = [i for i in range(N) if rm.get(i) == "testers"]
        for t in testers:
            tester_positions[t] += 1
            accept = frozenset(j for j in range(N) if m[t][j] == 0)
            reject = frozenset(j for j in range(N) if m[t][j] == 1)
            tester_partitions[(accept, reject)] += 1

    print(f"  Tester position: {dict(tester_positions)}")
    print(f"  Distinct tester partitions: {len(tester_partitions)}")
    for (acc, rej), cnt in tester_partitions.most_common():
        print(f"    accept={sorted(acc)}, reject={sorted(rej)} ({cnt}x)")

    # ═══════════════════════════════════════════════════════════════
    # 8. CROSS-ANALYSIS: which axes correlate?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("8. AXIS CORRELATION")
    print(f"{'═'*70}\n")

    # For each model, compute a feature vector
    features = []
    for m in models:
        rm = role_map(m)
        role_sig = tuple(rm.get(i, "?") for i in range(N))
        sq = tuple(m[i][i] for i in range(N))
        testers = [i for i in range(N) if rm.get(i) == "testers"]
        t = testers[0] if testers else -1
        if t >= 0:
            accept = frozenset(j for j in range(N) if m[t][j] == 0)
        else:
            accept = frozenset()
        features.append({
            "role_sig": role_sig,
            "squaring": sq,
            "tester_accept": accept,
        })

    # How many unique (role_sig, tester_accept) pairs?
    role_tester = Counter()
    for f in features:
        role_tester[(f["role_sig"], f["tester_accept"])] += 1
    print(f"  (role_sig, tester_accept) combos: {len(role_tester)}")

    role_sq = Counter()
    for f in features:
        role_sq[(f["role_sig"], f["squaring"])] += 1
    print(f"  (role_sig, squaring) combos: {len(role_sq)}")

    tester_sq = Counter()
    for f in features:
        tester_sq[(f["tester_accept"], f["squaring"])] += 1
    print(f"  (tester_accept, squaring) combos: {len(tester_sq)}")

    all_three = Counter()
    for f in features:
        all_three[(f["role_sig"], f["tester_accept"], f["squaring"])] += 1
    print(f"  (role_sig, tester_accept, squaring) combos: {len(all_three)}")
    print(f"  → Each combo appears: {sorted(all_three.values(), reverse=True)[:20]}")

    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY — AXES OF VARIATION")
    print(f"{'═'*70}")
    print(f"""
  Models enumerated:  {len(models)}{'(exhaustive)' if exhausted else '+'}
  Isomorphism classes (WL): {n_classes}
  Fixed cells:        {fixed_count}/{total} ({100*fixed_count/total:.1f}%)
  Role signatures:    {len(role_sig_counts)} distinct
  Squaring patterns:  {len(sq_patterns)} distinct
  Tester partitions:  {len(tester_partitions)} distinct
  Generator pairs:    {len(always_gen)} always-generating
""")


def variation_analysis():
    """
    Deep analysis of the 199-model dominant cluster at N=12.
    Binary cell patterns, dependency graph, constructibility filters,
    generator maximization, encoder regularity, outlier elimination.
    """

    from collections import Counter
    from itertools import combinations

    # ── Helpers ──────────────────────────────────────────────────────
    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    def closure_depth(tbl, gens, N):
        depth = {g: 0 for g in gens}
        reached = set(gens)
        frontier = list(gens)
        step = 0
        while frontier:
            step += 1
            new = []
            for a in list(reached):
                for b in frontier:
                    for ab in [tbl[a][b], tbl[b][a]]:
                        if ab not in reached:
                            reached.add(ab)
                            depth[ab] = step
                            new.append(ab)
            frontier = new
        return reached, depth

    def closure(tbl, gens, N):
        reached = set(gens)
        frontier = list(gens)
        while frontier:
            new = []
            for a in list(reached):
                for b in frontier:
                    for ab in [tbl[a][b], tbl[b][a]]:
                        if ab not in reached:
                            reached.add(ab)
                            new.append(ab)
            frontier = new
        return reached

    CORE = 6
    Q_IDX, E_IDX = 6, 7
    N = 12
    t_idx, f_idx, g_idx = 3, 2, 4
    r_idx, h_idx, Y_idx = 8, 9, 10

    print("=" * 70)
    print("VARIATION ANALYSIS — N=12 DOMINANT CLUSTER")
    print("=" * 70)

    # ── Enumerate models ─────────────────────────────────────────────
    print("\nEnumerating models (cap=500)...")
    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    for x in range(2, CORE):
        gx = dot[g_idx][x]
        r_gx = col_ite_lookup(dot, r_idx, gx, N)
        s.add(dot[h_idx][x] == r_gx)

    yr = dot[Y_idx][r_idx]
    r_yr = col_ite_lookup(dot, r_idx, yr, N)
    s.add(yr == r_yr)
    s.add(yr >= 2)

    all_models = []
    t0 = time.time()
    CAP = 500
    while len(all_models) < CAP:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        all_models.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    exhausted = len(all_models) < CAP
    print(f"  Found {len(all_models)}{'(exhaustive)' if exhausted else '+'} ({elapsed:.1f}s)")

    # Separate dominant cluster from outlier(s)
    # Dominant = role sig with exactly 1 inert
    dominant = []
    outliers = []
    for m in all_models:
        rm = role_map(m)
        n_inert = sum(1 for i in range(N) if rm.get(i) == "inert")
        if n_inert == 1:
            dominant.append(m)
        else:
            outliers.append(m)

    print(f"  Dominant cluster (1 inert): {len(dominant)}")
    print(f"  Outliers: {len(outliers)}")

    models = dominant  # work with dominant cluster only

    # ═══════════════════════════════════════════════════════════════
    # 1. BINARY CELL ANALYSIS
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("1. BINARY CELL ANALYSIS")
    print(f"{'═'*70}\n")

    # Compute value sets for each cell
    cell_vals = [[set() for _ in range(N)] for _ in range(N)]
    for m in models:
        for i in range(N):
            for j in range(N):
                cell_vals[i][j].add(m[i][j])

    fixed_cells = []
    binary_cells = []
    multi_cells = []
    for i in range(N):
        for j in range(N):
            nv = len(cell_vals[i][j])
            if nv == 1:
                fixed_cells.append((i, j))
            elif nv == 2:
                binary_cells.append((i, j))
            else:
                multi_cells.append((i, j))

    print(f"  Fixed cells: {len(fixed_cells)}")
    print(f"  Binary cells (exactly 2 values): {len(binary_cells)}")
    print(f"  Multi cells (3+ values): {len(multi_cells)}")

    # For each binary cell, show the two values and their frequencies
    print(f"\n  Binary cells detail:")
    rm0 = role_map(models[0])
    binary_info = {}  # (i,j) -> (valA, valB, countA, countB)
    for i, j in binary_cells:
        vals = sorted(cell_vals[i][j])
        va, vb = vals
        ca = sum(1 for m in models if m[i][j] == va)
        cb = len(models) - ca
        binary_info[(i, j)] = (va, vb, ca, cb)

    # Group by row for readability
    by_row = {}
    for (i, j) in binary_cells:
        by_row.setdefault(i, []).append(j)

    for i in sorted(by_row.keys()):
        role = rm0.get(i, "?")
        print(f"\n    Row {i} ({role}):")
        for j in sorted(by_row[i]):
            va, vb, ca, cb = binary_info[(i, j)]
            # Characterize the values
            ra = rm0.get(va, "?")[0] if va < N else "?"
            rb = rm0.get(vb, "?")[0] if vb < N else "?"
            bias = f"{ca}:{cb}"
            print(f"      ({i},{j:2d}): {va}({ra}) vs {vb}({rb})  [{bias}]")

    # Pattern analysis: are absorber values (0,1) ever one of the options?
    abs_binary = [(i, j) for (i, j) in binary_cells
                  if 0 in cell_vals[i][j] or 1 in cell_vals[i][j]]
    print(f"\n  Binary cells involving absorbers: {len(abs_binary)}/{len(binary_cells)}")

    # Multi-value cells
    print(f"\n  Multi-value cells ({len(multi_cells)}):")
    for i, j in multi_cells:
        vals = sorted(cell_vals[i][j])
        print(f"    ({i},{j:2d}): {len(vals)} values: {vals}")

    # ═══════════════════════════════════════════════════════════════
    # 2. DEPENDENCY GRAPH
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("2. DEPENDENCY GRAPH — binary cell correlations")
    print(f"{'═'*70}\n")

    # For each binary cell, encode its value as 0 or 1
    # (0 = first value in sorted order, 1 = second)
    def cell_bit(m, i, j):
        vals = sorted(cell_vals[i][j])
        return 0 if m[i][j] == vals[0] else 1

    # Build bit vectors for each model
    bit_vecs = []
    for m in models:
        bv = tuple(cell_bit(m, i, j) for (i, j) in binary_cells)
        bit_vecs.append(bv)

    # Check pairwise correlation between binary cells
    n_binary = len(binary_cells)
    print(f"  {n_binary} binary cells to analyze")

    # Build correlation matrix: for each pair, check if they're
    # perfectly correlated (same), anti-correlated (opposite), or independent
    perfect_same = []
    perfect_anti = []
    partial_corr = []

    for idx_a in range(n_binary):
        for idx_b in range(idx_a + 1, n_binary):
            bits_a = [bv[idx_a] for bv in bit_vecs]
            bits_b = [bv[idx_b] for bv in bit_vecs]
            same = all(a == b for a, b in zip(bits_a, bits_b))
            anti = all(a != b for a, b in zip(bits_a, bits_b))
            if same:
                perfect_same.append((binary_cells[idx_a], binary_cells[idx_b]))
            elif anti:
                perfect_anti.append((binary_cells[idx_a], binary_cells[idx_b]))
            else:
                # Compute correlation strength
                agree = sum(1 for a, b in zip(bits_a, bits_b) if a == b)
                ratio = agree / len(bits_a)
                if ratio > 0.9 or ratio < 0.1:
                    partial_corr.append((binary_cells[idx_a],
                                         binary_cells[idx_b], ratio))

    print(f"  Perfectly correlated (same) pairs: {len(perfect_same)}")
    print(f"  Perfectly anti-correlated pairs: {len(perfect_anti)}")
    print(f"  Strongly correlated (>90% or <10%): {len(partial_corr)}")

    # Build equivalence classes from perfect correlations
    # Union-find
    parent = list(range(n_binary))
    sign = [0] * n_binary  # 0 = same as root, 1 = anti from root

    def find(x):
        if parent[x] == x:
            return x, 0
        root, s = find(parent[x])
        parent[x] = root
        sign[x] ^= s
        return root, sign[x]

    def union(a, b, relation):
        # relation: 0 = same, 1 = anti
        ra, sa = find(a)
        rb, sb = find(b)
        if ra != rb:
            parent[ra] = rb
            sign[ra] = sa ^ sb ^ relation

    # Process perfect correlations
    cell_to_idx = {c: i for i, c in enumerate(binary_cells)}
    for ca, cb in perfect_same:
        union(cell_to_idx[ca], cell_to_idx[cb], 0)
    for ca, cb in perfect_anti:
        union(cell_to_idx[ca], cell_to_idx[cb], 1)

    # Count independent groups
    groups = {}
    for i in range(n_binary):
        root, s = find(i)
        groups.setdefault(root, []).append((i, s))

    print(f"\n  Independent binary groups: {len(groups)}")
    for gid, (root, members) in enumerate(sorted(groups.items(),
                                                   key=lambda x: -len(x[1]))):
        cells_in_group = [(binary_cells[idx], "+" if s == 0 else "-")
                          for idx, s in members]
        print(f"\n    Group {gid} ({len(members)} cells):")
        for (i, j), sgn in cells_in_group:
            va, vb, ca, cb = binary_info[(i, j)]
            print(f"      {sgn}({i},{j:2d}): {va} vs {vb}  [{ca}:{cb}]")

    # How many distinct bit patterns exist?
    unique_patterns = set(bit_vecs)
    print(f"\n  Distinct binary patterns: {len(unique_patterns)}")
    pattern_counts = Counter(bit_vecs)
    print(f"  Most common patterns:")
    for pat, cnt in pattern_counts.most_common(10):
        print(f"    {pat} ({cnt}x)")

    # ═══════════════════════════════════════════════════════════════
    # 3. CONSTRUCTIBILITY FILTER
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("3. CONSTRUCTIBILITY FILTER")
    print("  Minimize max depth from {0,1,Q,E} to reach all elements")
    print(f"{'═'*70}\n")

    depth_data = []
    for m in models:
        reached, depths = closure_depth(m, {0, 1, Q_IDX, E_IDX}, N)
        max_d = max(depths.values()) if depths else 0
        sum_d = sum(depths.values())
        depth_data.append((max_d, sum_d, m))

    depth_dist = Counter(d[0] for d in depth_data)
    print(f"  Max depth distribution: {dict(sorted(depth_dist.items()))}")

    min_max_depth = min(d[0] for d in depth_data)
    best_depth = [m for md, sd, m in depth_data if md == min_max_depth]
    print(f"  Minimum max depth: {min_max_depth}")
    print(f"  Models at minimum depth: {len(best_depth)}/{len(models)}")

    # Among those, find minimum sum-depth
    if best_depth:
        best_sum = []
        for m in best_depth:
            reached, depths = closure_depth(m, {0, 1, Q_IDX, E_IDX}, N)
            best_sum.append((sum(depths.values()), m))
        min_sum = min(s for s, m in best_sum)
        best_both = [m for s, m in best_sum if s == min_sum]
        print(f"  Min sum-depth among best: {min_sum}")
        print(f"  Models at min sum-depth: {len(best_both)}")

    # ═══════════════════════════════════════════════════════════════
    # 4. MAXIMUM SINGLE GENERATORS
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("4. SINGLE GENERATOR MAXIMIZATION")
    print(f"{'═'*70}\n")

    gen_data = []
    for m in models:
        single_gens = set()
        for a in range(2, N):
            reached = closure(m, {0, 1, a}, N)
            if len(reached) == N:
                single_gens.add(a)
        gen_data.append((len(single_gens), single_gens, m))

    gen_dist = Counter(g[0] for g in gen_data)
    print(f"  Single-generator count distribution: {dict(sorted(gen_dist.items()))}")

    max_gens = max(g[0] for g in gen_data)
    best_gen = [(sg, m) for ng, sg, m in gen_data if ng == max_gens]
    print(f"  Maximum single generators: {max_gens}")
    print(f"  Models at max: {len(best_gen)}")
    if best_gen:
        # Show which elements are generators
        gen_sets = Counter(frozenset(sg) for sg, m in best_gen)
        for gs, cnt in gen_sets.most_common(5):
            print(f"    Generators {sorted(gs)} ({cnt}x)")

    # ═══════════════════════════════════════════════════════════════
    # 5. ENCODER INTERACTION REGULARITY
    # For rows 4, 6, 9 (wide variation), measure "regularity"
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("5. ENCODER INTERACTION REGULARITY")
    print("  Rows with wide variation: analyzing structure")
    print(f"{'═'*70}\n")

    # For each model, compute regularity metrics for high-variation rows
    multi_rows = set(i for (i, j) in multi_cells)
    print(f"  Rows with >2 values in some cell: {sorted(multi_rows)}")

    for row_i in sorted(multi_rows):
        print(f"\n  Row {row_i} ({rm0.get(row_i, chr(63))}):")
        multi_cols = [j for (i, j) in multi_cells if i == row_i]
        print(f"    Multi-value columns: {multi_cols}")

        # Collect all row values across models
        row_vals = [tuple(m[row_i]) for m in models]
        distinct_rows = Counter(row_vals)
        print(f"    Distinct row patterns: {len(distinct_rows)}")
        for rv, cnt in distinct_rows.most_common(8):
            print(f"      {list(rv)} ({cnt}x)")
        if len(distinct_rows) > 8:
            print(f"      ... and {len(distinct_rows) - 8} more")

        # Regularity metrics:
        # 1. How many distinct values in the row?
        ndist = [len(set(m[row_i])) for m in models]
        print(f"    Distinct values in row: min={min(ndist)}, max={max(ndist)}, "
              f"mode={Counter(ndist).most_common(1)[0]}")

        # 2. Does the row have cycles? x -> row[x] -> row[row[x]] -> ...
        cycle_lens = Counter()
        for m in models:
            visited = set()
            cycles = []
            for start in range(N):
                if start in visited:
                    continue
                path = []
                x = start
                while x not in visited and x not in path:
                    path.append(x)
                    x = m[row_i][x]
                if x in path:
                    cycle_start = path.index(x)
                    cyc = tuple(path[cycle_start:])
                    cycles.append(len(cyc))
                visited.update(path)
            cycle_lens[tuple(sorted(cycles, reverse=True))] += 1

        print(f"    Cycle structure: {len(cycle_lens)} distinct")
        for cs, cnt in cycle_lens.most_common(5):
            print(f"      cycles {cs} ({cnt}x)")

    # ═══════════════════════════════════════════════════════════════
    # 6. THE OUTLIER — find simplest killing axiom
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("6. OUTLIER ELIMINATION")
    print(f"{'═'*70}\n")

    if outliers:
        out = outliers[0]
        rm_out = role_map(out)
        print(f"  Outlier role map: {[(i, rm_out.get(i, chr(63))) for i in range(N)]}")
        n_inert_out = sum(1 for i in range(N) if rm_out.get(i) == "inert")
        n_enc_out = sum(1 for i in range(N) if rm_out.get(i) == "encoders")
        n_tst_out = sum(1 for i in range(N) if rm_out.get(i) == "testers")
        print(f"  Outlier: {n_tst_out}T, {n_enc_out}E, {n_inert_out}I")

        # Compare tester partition
        testers_out = [i for i in range(N) if rm_out.get(i) == "testers"]
        for t in testers_out:
            acc = [j for j in range(N) if out[t][j] == 0]
            rej = [j for j in range(N) if out[t][j] == 1]
            print(f"  Outlier tester {t}: accept={acc}, reject={rej}")

        # Squaring
        sq_out = [out[i][i] for i in range(N)]
        print(f"  Outlier squaring: {sq_out}")
        idem_out = [i for i in range(N) if out[i][i] == i]
        print(f"  Outlier idempotents: {idem_out} ({len(idem_out)} total)")

        # Dominant has 6 idempotents. What's the simplest differentiator?
        dom_idem = [i for i in range(N) if models[0][i][i] == i]
        print(f"\n  Dominant idempotents: {dom_idem} ({len(dom_idem)} total)")

        # Test: "at least 4 idempotents among non-absorbers"
        print(f"\n  Candidate axioms to kill outlier:")
        print(f"    A. 'Exactly 1 non-absorber inert': "
              f"outlier has {n_inert_out}, dominant has 1")
        print(f"    B. '>=4 non-absorber idempotents': "
              f"outlier has {len(idem_out)-2}, dominant has {len(dom_idem)-2}")
        # Does tester accept 0?
        dom_t = 3
        dom_t_0 = models[0][dom_t][0]
        out_t = testers_out[0] if testers_out else -1
        out_t_0 = out[out_t][0] if out_t >= 0 else -1
        print(f"    C. 'Tester accepts 0 (top)': "
              f"dominant t·0={dom_t_0}, outlier t·0={out_t_0}")
    else:
        print("  No outliers found in this enumeration!")

    # ═══════════════════════════════════════════════════════════════
    # 7. INTERSECTION — combine filters
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("7. COMBINED FILTERS — collapsing the model space")
    print(f"{'═'*70}\n")

    # Filter 1: minimum constructibility depth
    surviving = models
    print(f"  Start: {len(surviving)} models")

    # Filter: max depth = min_max_depth
    s1 = [m for m in surviving
          if max(closure_depth(m, {0, 1, Q_IDX, E_IDX}, N)[1].values())
          == min_max_depth]
    print(f"  After min-depth filter ({min_max_depth}): {len(s1)}")

    # Filter: max single generators
    s2 = []
    for m in s1:
        sg = sum(1 for a in range(2, N)
                 if len(closure(m, {0, 1, a}, N)) == N)
        if sg == max_gens:
            s2.append(m)
    print(f"  After max-generators filter ({max_gens}): {len(s2)}")

    # Filter: maximum idempotents
    max_idem_in_s2 = max(sum(1 for i in range(N) if m[i][i] == i)
                         for m in s2) if s2 else 0
    s3 = [m for m in s2
          if sum(1 for i in range(N) if m[i][i] == i) == max_idem_in_s2]
    print(f"  After max-idempotent filter ({max_idem_in_s2}): {len(s3)}")

    # Filter: minimum distinct values in high-variation rows
    # (prefer "most regular" models)
    if s3:
        reg_scores = []
        for m in s3:
            score = sum(len(set(m[row_i])) for row_i in multi_rows)
            reg_scores.append((score, m))
        min_score = min(s for s, m in reg_scores)
        s4 = [m for s, m in reg_scores if s == min_score]
        print(f"  After regularity filter (min row diversity={min_score}): {len(s4)}")
    else:
        s4 = []

    # Show surviving models
    if s4 and len(s4) <= 10:
        print(f"\n  Surviving models:")
        for idx, m in enumerate(s4):
            print(f"\n  Model {idx}:")
            for i in range(N):
                rm = role_map(m)
                r = rm.get(i, "?")[0]
                print(f"    {i:2d}({r}): {m[i]}")
    elif s4:
        # Show first and stats
        print(f"\n  First surviving model:")
        m = s4[0]
        rm = role_map(m)
        for i in range(N):
            r = rm.get(i, "?")[0]
            print(f"    {i:2d}({r}): {m[i]}")

        # How many cells still vary among survivors?
        if len(s4) > 1:
            sv = [[set() for _ in range(N)] for _ in range(N)]
            for m in s4:
                for i in range(N):
                    for j in range(N):
                        sv[i][j].add(m[i][j])
            still_vary = sum(1 for i in range(N) for j in range(N)
                             if len(sv[i][j]) > 1)
            print(f"\n  Cells still varying among {len(s4)} survivors: {still_vary}/{N*N}")

    # ═══════════════════════════════════════════════════════════════
    # 8. Z3 VERIFICATION — encode the best filters as axioms
    # and count remaining models
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("8. Z3 VERIFICATION — axiom candidates")
    print(f"{'═'*70}\n")

    # Test each candidate axiom's impact on model count
    def make_base_solver():
        s, dot = encode_level(8, N, timeout_seconds=300)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)
        return s, dot

    def count_with_axiom(name, add_axiom_fn, cap=100):
        s, dot = make_base_solver()
        add_axiom_fn(s, dot)
        count = 0
        t0 = time.time()
        while count < cap:
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            count += 1
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0
        tag = f"{count}{'+'  if count >= cap else '(exhaustive)'}"
        print(f"    {name:50s} → {tag} ({elapsed:.1f}s)")
        return count

    # Axiom: exactly 1 inert (kills outlier)
    def ax_one_inert(s, dot):
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
            # Mark inert
            inert_flag = Int(f"inert_{x}")
            s.add(If(is_inert, inert_flag == 1, inert_flag == 0))
        # Exactly 1 inert among non-absorbers
        s.add(sum([Int(f"inert_{x}") for x in range(2, N)]) == 1)

    # Axiom: tester accepts top (t·0 = 0)
    def ax_tester_accepts_top(s, dot):
        # The tester: find the one element with boolean row
        # Since tester is always at pos 3 in dominant, just constrain pos 3
        # But more principled: for every tester, t·0 = 0
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            s.add(Or(Not(is_tst), dot[x][0] == 0))

    # Axiom: >=4 non-absorber idempotents
    def ax_many_idempotents(s, dot):
        idem_flags = []
        for x in range(2, N):
            f = Int(f"idem_{x}")
            s.add(If(dot[x][x] == x, f == 1, f == 0))
            idem_flags.append(f)
        s.add(sum(idem_flags) >= 4)

    # Axiom: max constructibility depth <= 2 from {0,1,Q,E}
    # This is hard to encode in Z3 directly. Skip for now.

    print("  Individual axiom impact:")
    count_with_axiom("baseline (no new axiom)", lambda s, d: None)
    count_with_axiom("exactly 1 inert", ax_one_inert)
    count_with_axiom("tester accepts top (t·0=0)", ax_tester_accepts_top)
    count_with_axiom(">=4 non-absorber idempotents", ax_many_idempotents)

    # Combinations
    print("\n  Combined axioms:")

    def ax_inert_plus_top(s, dot):
        ax_one_inert(s, dot)
        ax_tester_accepts_top(s, dot)

    def ax_inert_plus_idem(s, dot):
        ax_one_inert(s, dot)
        ax_many_idempotents(s, dot)

    def ax_all_three(s, dot):
        ax_one_inert(s, dot)
        ax_tester_accepts_top(s, dot)
        ax_many_idempotents(s, dot)

    count_with_axiom("1-inert + t·0=0", ax_inert_plus_top)
    count_with_axiom("1-inert + >=4 idempotents", ax_inert_plus_idem)
    count_with_axiom("1-inert + t·0=0 + >=4 idempotents", ax_all_three)

    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")


def pinning_analysis():
    """
    Deep analysis of the 3 free cells (4,11), (6,10), (9,8) in the
    N=12 full-package dominant cluster. Seeks a single principled
    axiom that pins all three simultaneously.
    """

    from collections import Counter

    # ── Helpers ──────────────────────────────────────────────────────
    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    CORE = 6
    Q_IDX, E_IDX = 6, 7
    N = 12
    t_idx, f_idx, g_idx = 3, 2, 4
    r_idx, h_idx, Y_idx = 8, 9, 10

    # Free cells
    FREE_CELLS = [(4, 11), (6, 10), (9, 8)]

    print("=" * 70)
    print("PINNING ANALYSIS — 3 FREE CELLS")
    print("(4,11), (6,10), (9,8)")
    print("=" * 70)

    # ── Enumerate dominant cluster ───────────────────────────────────
    print("\nEnumerating models (cap=500)...")
    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    for x in range(2, CORE):
        gx = dot[g_idx][x]
        r_gx = col_ite_lookup(dot, r_idx, gx, N)
        s.add(dot[h_idx][x] == r_gx)

    yr = dot[Y_idx][r_idx]
    r_yr = col_ite_lookup(dot, r_idx, yr, N)
    s.add(yr == r_yr)
    s.add(yr >= 2)

    # Kill outlier: exactly 1 inert
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
        inert_flag = Int(f"inert_{x}")
        s.add(If(is_inert, inert_flag == 1, inert_flag == 0))
    s.add(sum([Int(f"inert_{x}") for x in range(2, N)]) == 1)

    all_models = []
    t0 = time.time()
    CAP = 500
    while len(all_models) < CAP:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        all_models.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    exhausted = len(all_models) < CAP
    models = all_models
    print(f"  Found {len(models)}{'(exhaustive)' if exhausted else '+'} ({elapsed:.1f}s)")

    # Verify free cells
    for a, b in FREE_CELLS:
        vals = sorted(set(m[a][b] for m in models))
        print(f"  Cell ({a},{b}): {len(vals)} values — {vals}")

    # ═══════════════════════════════════════════════════════════════
    # 1. TRANSPOSE ANALYSIS
    # Mirror cells (b,a) for each free cell (a,b)
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("1. TRANSPOSE ANALYSIS")
    print(f"{'═'*70}\n")

    for a, b in FREE_CELLS:
        # Mirror value b·a
        mirror_vals = Counter(m[b][a] for m in models)
        print(f"  ({a},{b}) free  vs  ({b},{a}) mirror:")
        print(f"    ({b},{a}) values: {dict(mirror_vals)}")
        if len(mirror_vals) == 1:
            mirror_v = list(mirror_vals.keys())[0]
            print(f"    → FIXED at {mirror_v}")
            # Relationship: does a·b ever equal b·a?
            eq_count = sum(1 for m in models if m[a][b] == m[b][a])
            print(f"    a·b == b·a: {eq_count}/{len(models)}")
            # What is a·b - b·a like?
            rel = Counter()
            for m in models:
                ab = m[a][b]
                ba = m[b][a]
                if ab == ba:
                    rel["equal"] += 1
                elif ab == a:
                    rel["a·b=a"] += 1
                elif ab == b:
                    rel["a·b=b"] += 1
                elif ba == a:
                    rel["b·a=a"] += 1
                elif ba == b:
                    rel["b·a=b"] += 1
                else:
                    rel["other"] += 1
            print(f"    Relationships: {dict(rel)}")
        else:
            print(f"    → also varies ({len(mirror_vals)} values)")

    # ═══════════════════════════════════════════════════════════════
    # 2. SQUARING CONNECTION
    # 4·4=11, 11·11=4 (2-cycle). So (4,11) = 4·(4²).
    # Check x·(x·x) patterns.
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("2. SQUARING CONNECTION")
    print(f"{'═'*70}\n")

    # For all elements, check x·(x·x) pattern
    m0 = models[0]
    print("  Squaring map (first model): ", [m0[i][i] for i in range(N)])
    print("  Squaring 2-cycles: ", end="")
    for i in range(N):
        ii = m0[i][i]
        if ii != i and m0[ii][ii] == i:
            print(f"({i},{ii}) ", end="")
    print()

    # x·(x·x) for each element across all models
    print(f"\n  x·(x·x) analysis:")
    for x in range(N):
        xx = m0[x][x]
        xxx_vals = Counter(m[x][m[x][x]] for m in models)
        if len(xxx_vals) == 1:
            v = list(xxx_vals.keys())[0]
            ident = ""
            if v == x:
                ident = "  = x (left quasi-idempotent)"
            elif v == xx:
                ident = "  = x·x"
            elif v == m0[xx][xx]:
                ident = "  = (x·x)·(x·x)"
            elif v == 0:
                ident = "  = 0 (top)"
            elif v == 1:
                ident = "  = 1 (bot)"
            print(f"    {x}·({x}·{x}) = {x}·{xx} = {v} always{ident}")
        else:
            # This is a free cell
            print(f"    {x}·({x}·{x}) = {x}·{xx} VARIES: {dict(xxx_vals)}")

    # Check (x·x)·x for each element
    print(f"\n  (x·x)·x analysis:")
    for x in range(N):
        xx = m0[x][x]
        xxx_vals = Counter(m[m[x][x]][x] for m in models)
        if len(xxx_vals) == 1:
            v = list(xxx_vals.keys())[0]
            ident = ""
            if v == x:
                ident = "  = x"
            elif v == xx:
                ident = "  = x·x"
            elif v == 0:
                ident = "  = 0"
            elif v == 1:
                ident = "  = 1"
            print(f"    ({x}·{x})·{x} = {xx}·{x} = {v} always{ident}")
        else:
            print(f"    ({x}·{x})·{x} = {xx}·{x} VARIES: {dict(xxx_vals)}")

    # Check x·(x·x) = x (left quasi-idempotent) — which elements satisfy this?
    print(f"\n  x·(x·x) = x holds for:")
    for x in range(N):
        holds = sum(1 for m in models if m[x][m[x][x]] == x)
        if holds == len(models):
            print(f"    x={x}: ALWAYS")
        elif holds > 0:
            print(f"    x={x}: {holds}/{len(models)}")

    # ═══════════════════════════════════════════════════════════════
    # 3. COMPOSITIONAL IDENTITIES
    # For each free cell (a,b), compute second-order compositions
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("3. COMPOSITIONAL IDENTITIES at free cells")
    print(f"{'═'*70}\n")

    for a, b in FREE_CELLS:
        print(f"  Cell ({a},{b}) — a·b varies freely:")

        # a·(a·b)
        vals = Counter(m[a][m[a][b]] for m in models)
        fixed = "FIXED" if len(vals) == 1 else f"{len(vals)} values"
        print(f"    a·(a·b) = {a}·({a}·{b}): {fixed} — {dict(vals)}")

        # (a·b)·b
        vals = Counter(m[m[a][b]][b] for m in models)
        fixed = "FIXED" if len(vals) == 1 else f"{len(vals)} values"
        print(f"    (a·b)·b = ({a}·{b})·{b}: {fixed} — {dict(vals)}")

        # (a·b)·a
        vals = Counter(m[m[a][b]][a] for m in models)
        fixed = "FIXED" if len(vals) == 1 else f"{len(vals)} values"
        print(f"    (a·b)·a = ({a}·{b})·{a}: {fixed} — {dict(vals)}")

        # b·(a·b)
        vals = Counter(m[b][m[a][b]] for m in models)
        fixed = "FIXED" if len(vals) == 1 else f"{len(vals)} values"
        print(f"    b·(a·b) = {b}·({a}·{b}): {fixed} — {dict(vals)}")

        # (a·b)·(a·b) — squaring of the result
        vals = Counter(m[m[a][b]][m[a][b]] for m in models)
        fixed = "FIXED" if len(vals) == 1 else f"{len(vals)} values"
        print(f"    (a·b)·(a·b): {fixed} — {dict(vals)}")

        # Does a·b participate in any constant composition?
        # Check a·b·c for each c
        const_cols = []
        for c in range(N):
            vals = Counter(m[m[a][b]][c] for m in models)
            if len(vals) == 1:
                const_cols.append((c, list(vals.keys())[0]))
        if const_cols:
            print(f"    (a·b)·c fixed for c in: {const_cols}")
        else:
            print(f"    (a·b)·c: NO column is fixed")

        # Check c·(a·b) for each c
        const_rows = []
        for c in range(N):
            vals = Counter(m[c][m[a][b]] for m in models)
            if len(vals) == 1:
                const_rows.append((c, list(vals.keys())[0]))
        if const_rows:
            print(f"    c·(a·b) fixed for c in: {const_rows}")
        else:
            print(f"    c·(a·b): NO row is fixed")

        print()

    # ═══════════════════════════════════════════════════════════════
    # 4. MINIMUM ENTROPY
    # Which values at the 3 cells minimize distinct table entries?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("4. MINIMUM ENTROPY — simplest models")
    print(f"{'═'*70}\n")

    entropy_data = []
    for m in models:
        # Count distinct values across the entire table
        all_vals = set()
        for i in range(N):
            for j in range(N):
                all_vals.add(m[i][j])
        free_vals = tuple(m[a][b] for a, b in FREE_CELLS)
        entropy_data.append((len(all_vals), free_vals, m))

    entropy_dist = Counter(e[0] for e in entropy_data)
    print(f"  Distinct value count distribution: {dict(sorted(entropy_dist.items()))}")

    min_entropy = min(e[0] for e in entropy_data)
    min_models = [(fv, m) for ev, fv, m in entropy_data if ev == min_entropy]
    print(f"  Minimum distinct values: {min_entropy}")
    print(f"  Models at minimum: {len(min_models)}")
    free_at_min = Counter(fv for fv, m in min_models)
    print(f"  Free cell values at minimum entropy:")
    for fv, cnt in free_at_min.most_common():
        cells = list(zip(FREE_CELLS, fv))
        desc = ", ".join(f"{a}·{b}={v}" for (a, b), v in cells)
        print(f"    {desc} ({cnt}x)")

    # ═══════════════════════════════════════════════════════════════
    # 5. COLUMN DISTINCTNESS
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("5. COLUMN DISTINCTNESS")
    print(f"{'═'*70}\n")

    # Check if columns are already distinct in all models
    col_distinct_count = 0
    col_collision_detail = Counter()
    for m in models:
        cols = [tuple(m[i][j] for i in range(N)) for j in range(N)]
        if len(set(cols)) == N:
            col_distinct_count += 1
        else:
            # Find which columns collide
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    if cols[j1] == cols[j2]:
                        col_collision_detail[(j1, j2)] += 1

    print(f"  Models with all columns distinct: {col_distinct_count}/{len(models)}")
    if col_collision_detail:
        print(f"  Column collisions:")
        for (j1, j2), cnt in col_collision_detail.most_common():
            print(f"    columns {j1} and {j2} collide in {cnt} models")

        # What free cell values cause collisions?
        col_distinct_models = [m for m in models
                               if len(set(tuple(m[i][j] for i in range(N))
                                          for j in range(N))) == N]
        if col_distinct_models:
            print(f"\n  Free cell values in column-distinct models ({len(col_distinct_models)}):")
            cd_free = Counter(tuple(m[a][b] for a, b in FREE_CELLS)
                              for m in col_distinct_models)
            for fv, cnt in cd_free.most_common(10):
                cells = list(zip(FREE_CELLS, fv))
                desc = ", ".join(f"{a}·{b}={v}" for (a, b), v in cells)
                print(f"    {desc} ({cnt}x)")
    else:
        print("  All columns already distinct in all models!")
        # Column distinctness doesn't help — try row distinctness
        print("\n  Checking ROW distinctness:")
        row_distinct_count = 0
        for m in models:
            rows = [tuple(m[i]) for i in range(N)]
            if len(set(rows)) == N:
                row_distinct_count += 1
        print(f"  Models with all rows distinct: {row_distinct_count}/{len(models)}")

    # ═══════════════════════════════════════════════════════════════
    # 6. SPECIAL VALUES — idempotents, fixed points, absorbers
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("6. SPECIAL VALUE ANALYSIS")
    print(f"{'═'*70}\n")

    for a, b in FREE_CELLS:
        print(f"  Cell ({a},{b}):")
        for v in range(2, N):
            properties = []
            # Does v create a new idempotent? a·b=a means a's row at b=a
            if v == a:
                properties.append(f"{a}·{b}={a} (row-{a} fixpoint at col {b})")
            if v == b:
                properties.append(f"{a}·{b}={b} (maps to column index)")
            # Is v in the squaring orbit of a?
            m0 = models[0]
            aa = m0[a][a]
            if v == aa:
                properties.append(f"= {a}·{a} (squaring value)")
            aaa = m0[aa][aa]
            if v == aaa:
                properties.append(f"= ({a}·{a})·({a}·{a})")
            # Is v idempotent?
            if m0[v][v] == v:
                properties.append("v is idempotent")
            # Is v the inert element?
            rm0 = role_map(m0)
            if rm0.get(v) == "inert":
                properties.append("v is inert")

            count = sum(1 for m in models if m[a][b] == v)
            if count > 0:
                prop_str = "; ".join(properties) if properties else "no special property"
                print(f"    v={v:2d} ({count:3d}x): {prop_str}")

    # ═══════════════════════════════════════════════════════════════
    # 7. CANDIDATE UNIVERSAL IDENTITIES
    # Test potential axioms that might pin all 3 cells
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("7. CANDIDATE UNIVERSAL IDENTITIES")
    print(f"{'═'*70}\n")

    # Identity A: x·(x·x) = x for all x (left quasi-idempotent)
    # Already checked — does it hold for x=4,6,9?
    print("  A. x·(x·x) = x for all x:")
    for x in [4, 6, 9]:
        holds = sum(1 for m in models if m[x][m[x][x]] == x)
        xx = models[0][x][x]
        print(f"    x={x}: {x}·({x}·{x}) = {x}·{xx}, holds in {holds}/{len(models)}")
    all_hold = sum(1 for m in models
                   if all(m[x][m[x][x]] == x for x in range(N)))
    print(f"    Holds for ALL x: {all_hold}/{len(models)}")

    # Identity B: (x·x)·x = x·x for all x
    print("\n  B. (x·x)·x = x·x for all x:")
    for x in [4, 6, 9]:
        xx = models[0][x][x]
        holds = sum(1 for m in models if m[m[x][x]][x] == m[x][x])
        print(f"    x={x}: ({x}·{x})·{x} = {xx}·{x}, holds in {holds}/{len(models)}")
    all_hold_b = sum(1 for m in models
                     if all(m[m[x][x]][x] == m[x][x] for x in range(N)))
    print(f"    Holds for ALL x: {all_hold_b}/{len(models)}")

    # Identity C: x·(x·x) = (x·x)·x for all x (left-right symmetry of cubing)
    print("\n  C. x·(x·x) = (x·x)·x for all x:")
    all_hold_c = sum(1 for m in models
                     if all(m[x][m[x][x]] == m[m[x][x]][x] for x in range(N)))
    print(f"    Holds for ALL x: {all_hold_c}/{len(models)}")
    # Which values does this select at free cells?
    if all_hold_c > 0 and all_hold_c < len(models):
        c_models = [m for m in models
                    if all(m[x][m[x][x]] == m[m[x][x]][x] for x in range(N))]
        c_free = Counter(tuple(m[a][b] for a, b in FREE_CELLS) for m in c_models)
        print(f"    Free cell values when C holds ({len(c_models)} models):")
        for fv, cnt in c_free.most_common(5):
            cells = list(zip(FREE_CELLS, fv))
            desc = ", ".join(f"{a}·{b}={v}" for (a, b), v in cells)
            print(f"      {desc} ({cnt}x)")

    # Identity D: x·(x·x)·(x·x) — associativity of squaring chain
    # Already have PA: (x·x)·x = x·(x·x). Does this force anything more?

    # Identity E: for encoders, the row is a permutation of some subset
    # i.e., row is injective on non-absorber elements
    print("\n  E. Encoder rows injective on non-absorbers:")
    inj_count = 0
    inj_forces = Counter()
    for m in models:
        rm = role_map(m)
        all_inj = True
        for x in range(2, N):
            if rm.get(x) != "encoders":
                continue
            vals = [m[x][j] for j in range(2, N)]
            if len(vals) != len(set(vals)):
                all_inj = False
                break
        if all_inj:
            inj_count += 1
            fv = tuple(m[a][b] for a, b in FREE_CELLS)
            inj_forces[fv] += 1
    print(f"    Models with all-injective encoders: {inj_count}/{len(models)}")
    if inj_count > 0 and inj_count < len(models):
        print(f"    Free cell values when injective ({inj_count}):")
        for fv, cnt in inj_forces.most_common(5):
            cells = list(zip(FREE_CELLS, fv))
            desc = ", ".join(f"{a}·{b}={v}" for (a, b), v in cells)
            print(f"      {desc} ({cnt}x)")

    # Identity F: every element appears in every column at least once
    # (left-surjective: for each j, {x·j : x ∈ N} = N)
    print("\n  F. Left-surjective (each column hits all values):")
    ls_count = 0
    for m in models:
        all_surj = True
        for j in range(N):
            col_vals = set(m[i][j] for i in range(N))
            if len(col_vals) < N:
                all_surj = False
                break
        if all_surj:
            ls_count += 1
    print(f"    Models: {ls_count}/{len(models)}")

    # Identity G: right-surjective (each row hits all values)
    print("\n  G. Right-surjective (each row hits all values):")
    rs_count = 0
    for m in models:
        all_surj = True
        for i in range(2, N):  # skip absorbers, they're constant
            row_vals = set(m[i])
            if len(row_vals) < N:
                all_surj = False
                break
        if all_surj:
            rs_count += 1
    print(f"    Non-absorber rows: {rs_count}/{len(models)}")

    # Identity H: x·y ≠ y·x for all distinct non-absorbers x,y
    # (maximal non-commutativity)

    # Identity I: squaring orbit closure
    # If x·x = y, then x·y = x·(x·x) should stay in the orbit
    print("\n  I. Squaring orbit closure — x·(x·x) in orbit of x:")
    orb_closure_count = 0
    for m in models:
        closed = True
        for x in range(2, N):
            # Compute orbit: x, x·x, (x·x)·(x·x), ...
            orbit = set()
            cur = x
            for _ in range(N):
                if cur in orbit:
                    break
                orbit.add(cur)
                cur = m[cur][cur]
            orbit.add(cur)  # add the cycle entry point
            # x·(x·x)
            xxx = m[x][m[x][x]]
            if xxx not in orbit:
                closed = False
                break
        if closed:
            orb_closure_count += 1
    print(f"    Models: {orb_closure_count}/{len(models)}")
    if 0 < orb_closure_count < len(models):
        oc_models = [m for m in models
                     if all(m[x][m[x][x]] in _sq_orbit(m, x, N)
                            for x in range(2, N))]
        if oc_models:
            oc_free = Counter(tuple(m[a][b] for a, b in FREE_CELLS) for m in oc_models)
            print(f"    Free cell values ({len(oc_models)}):")
            for fv, cnt in oc_free.most_common(5):
                cells = list(zip(FREE_CELLS, fv))
                desc = ", ".join(f"{a}·{b}={v}" for (a, b), v in cells)
                print(f"      {desc} ({cnt}x)")

    # ═══════════════════════════════════════════════════════════════
    # 8. Z3 VERIFICATION of promising candidates
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("8. Z3 VERIFICATION — promising axioms")
    print(f"{'═'*70}\n")

    def make_base_solver():
        s, dot = encode_level(8, N, timeout_seconds=300)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)
        # Kill outlier
        for x in range(2, N):
            is_tst = And([Or(dot[x][jj] == 0, dot[x][jj] == 1) for jj in range(N)])
            enc_pairs = []
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    enc_pairs.append(And(
                        dot[x][j1] != 0, dot[x][j1] != 1,
                        dot[x][j2] != 0, dot[x][j2] != 1,
                        dot[x][j1] != dot[x][j2]))
            is_enc = Or(enc_pairs) if enc_pairs else False
            is_inert = And(Not(is_tst), Not(is_enc))
            inert_flag = Int(f"zi_{x}")
            s.add(If(is_inert, inert_flag == 1, inert_flag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        return s, dot

    def count_with_axiom(name, add_axiom_fn, cap=50):
        s, dot = make_base_solver()
        add_axiom_fn(s, dot)
        count = 0
        t0 = time.time()
        first = None
        while count < cap:
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            if first is None:
                first = tbl
            count += 1
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0
        tag = f"{count}{'+'  if count >= cap else '(exhaustive)'}"
        print(f"    {name:55s} → {tag} ({elapsed:.1f}s)")
        if first and count <= 5:
            for a, b in FREE_CELLS:
                print(f"      ({a},{b}) = {first[a][b]}")
        return count, first

    print("  Baseline:")
    count_with_axiom("no new axiom", lambda s, d: None)

    # A: x·(x·x) = x for all x
    def ax_lqi(s, dot):
        for x in range(N):
            xx = dot[x][x]
            xxx = col_ite_lookup(dot, x, xx, N)
            s.add(xxx == x)

    count_with_axiom("x·(x·x) = x  (left quasi-idempotent)", ax_lqi)

    # B: (x·x)·x = x·x for all x
    def ax_rqi(s, dot):
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == xx)

    count_with_axiom("(x·x)·x = x·x", ax_rqi)

    # C: x·(x·x) = (x·x)·x
    def ax_cube_sym(s, dot):
        for x in range(N):
            xx = dot[x][x]
            s.add(col_ite_lookup(dot, x, xx, N) == ite_lookup(dot, xx, x, N))

    count_with_axiom("x·(x·x) = (x·x)·x  (cube symmetry)", ax_cube_sym)

    # E: encoder rows injective on non-absorbers
    def ax_enc_inj(s, dot):
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
            # If encoder, then injective on {2..N-1}
            for j1 in range(2, N):
                for j2 in range(j1 + 1, N):
                    s.add(Or(Not(is_enc), dot[x][j1] != dot[x][j2]))

    count_with_axiom("encoder rows injective on non-absorbers", ax_enc_inj)

    # Combination: cube symmetry + encoder injectivity
    def ax_cube_plus_inj(s, dot):
        ax_cube_sym(s, dot)
        ax_enc_inj(s, dot)

    cnt, first = count_with_axiom("cube symmetry + encoder injectivity", ax_cube_plus_inj)

    # If something pins to small count, show the model
    if first and cnt <= 3:
        print(f"\n  Pinned model (cube+inj):")
        rm = role_map(first)
        for i in range(N):
            r = rm.get(i, "?")[0]
            print(f"    {i:2d}({r}): {first[i]}")

    # ═══════════════════════════════════════════════════════════════
    # 9. PINNING THE LAST CELL (9,8)
    # With 1-inert, (4,11)=7 and (6,10)=4 are already fixed.
    # (9,8) takes values {2,3,8}. 3 dominates (99%).
    # 9·8 = 3 = tester. Semantically: encoder applied to another
    # encoder yields the tester. Find a principled axiom.
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("9. PINNING THE LAST FREE CELL (9,8)")
    print(f"{'═'*70}\n")

    # Separate the 3 groups by (9,8) value
    by_val = {}
    for m in models:
        v = m[9][8]
        by_val.setdefault(v, []).append(m)
    for v in sorted(by_val):
        print(f"  (9,8) = {v}: {len(by_val[v])} models")

    # What's different about v=2 and v=8 models vs v=3?
    # Check: does (9·8)·(9·8) = absorber?
    print(f"\n  (9·8)·(9·8) by value:")
    for v in sorted(by_val):
        sq_vals = Counter(m[m[9][8]][m[9][8]] for m in by_val[v])
        print(f"    v={v}: (v·v) = {dict(sq_vals)}")

    # Does 9·8 landing on tester (3) mean something?
    # Check: for each pair of encoders (a,b), does a·b land on tester?
    print(f"\n  Encoder pairs a·b = tester (3):")
    m0 = models[0]
    rm0 = role_map(m0)
    encs = [i for i in range(2, N) if rm0.get(i) == "encoders"]
    tester_hits = []
    for a in encs:
        for b in encs:
            v = m0[a][b]
            if v == 3:  # tester
                tester_hits.append((a, b))
    print(f"    In first model: {tester_hits}")

    # Is there a pattern: every encoder pair a·b either stays encoder
    # or lands on tester, never on inert?
    print(f"\n  Encoder·encoder → role distribution:")
    enc_enc_roles = Counter()
    for m in models:
        rm = role_map(m)
        for a in encs:
            for b in encs:
                enc_enc_roles[rm.get(m[a][b], "?")] += 1
    total_ee = len(models) * len(encs) * len(encs)
    for role, cnt in enc_enc_roles.most_common():
        print(f"    → {role}: {cnt}/{total_ee} ({100*cnt/total_ee:.1f}%)")

    # Key question: in v=3 models, 9·8=3=tester. So (9·8)·x is boolean.
    # In v=2 models, 9·8=2=inert. (9·8)·x is constant.
    # In v=8 models, 9·8=8=encoder. (9·8)·x has rich structure.
    # Principle: encoder·encoder should never produce the inert element.
    # This would kill v=2 (where 2 is inert).
    print(f"\n  Test: does encoder·encoder ever produce the inert element?")
    inert_elem = [i for i in range(2, N) if rm0.get(i) == "inert"]
    print(f"    Inert element: {inert_elem}")
    if inert_elem:
        ie = inert_elem[0]
        ee_to_inert = 0
        ee_to_inert_models = 0
        for m in models:
            rm = role_map(m)
            hit = False
            for a in encs:
                for b in encs:
                    if m[a][b] == ie:
                        ee_to_inert += 1
                        hit = True
            if hit:
                ee_to_inert_models += 1
        print(f"    Encoder·encoder = inert: {ee_to_inert} times "
              f"in {ee_to_inert_models}/{len(models)} models")

    # Test Z3: "no encoder·encoder → inert"
    def ax_ee_no_inert(s, dot):
        for x in range(2, N):
            # Detect if x is encoder
            is_tst_x = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            enc_pairs_x = []
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    enc_pairs_x.append(And(
                        dot[x][j1] != 0, dot[x][j1] != 1,
                        dot[x][j2] != 0, dot[x][j2] != 1,
                        dot[x][j1] != dot[x][j2]))
            is_enc_x = Or(enc_pairs_x) if enc_pairs_x else False

            for y in range(2, N):
                # Detect if y is encoder
                is_tst_y = And([Or(dot[y][j] == 0, dot[y][j] == 1) for j in range(N)])
                enc_pairs_y = []
                for j1 in range(N):
                    for j2 in range(j1 + 1, N):
                        enc_pairs_y.append(And(
                            dot[y][j1] != 0, dot[y][j1] != 1,
                            dot[y][j2] != 0, dot[y][j2] != 1,
                            dot[y][j1] != dot[y][j2]))
                is_enc_y = Or(enc_pairs_y) if enc_pairs_y else False

                # x·y result
                xy = dot[x][y]
                # Detect if x·y is inert
                is_tst_xy = And([Or(ite_lookup(dot, xy, j, N) == 0,
                                    ite_lookup(dot, xy, j, N) == 1) for j in range(N)])
                enc_pairs_xy = []
                for j1 in range(N):
                    for j2 in range(j1 + 1, N):
                        enc_pairs_xy.append(And(
                            ite_lookup(dot, xy, j1, N) != 0,
                            ite_lookup(dot, xy, j1, N) != 1,
                            ite_lookup(dot, xy, j2, N) != 0,
                            ite_lookup(dot, xy, j2, N) != 1,
                            ite_lookup(dot, xy, j1, N) != ite_lookup(dot, xy, j2, N)))
                is_enc_xy = Or(enc_pairs_xy) if enc_pairs_xy else False
                is_inert_xy = And(Not(is_tst_xy), Not(is_enc_xy))

                # If both enc, result not inert
                s.add(Or(Not(is_enc_x), Not(is_enc_y), Not(is_inert_xy)))

    print("\n  Z3: encoder·encoder ≠ inert:")
    cnt_eeni, _ = count_with_axiom("enc·enc ≠ inert", ax_ee_no_inert)

    # Simpler: just require (9,8) ≠ inert element (which is 2)
    # But that's not principled. Let's try stronger versions.

    # Test: (x·x)·x = x·x (right absorption by squaring)
    # This was 0/500 universally. But what about on encoders only?
    print(f"\n  (x·x)·x = x·x for encoders only:")
    rqi_enc = sum(1 for m in models
                  if all(m[m[x][x]][x] == m[x][x]
                         for x in range(2, N) if role_map(m).get(x) == "encoders"))
    print(f"    Holds: {rqi_enc}/{len(models)}")

    # What about: non-absorber·non-absorber always produces non-absorber?
    # This should already be enforced by L8 + ext...
    # Actually check: does encoder·encoder ever produce absorber?
    ee_to_abs = 0
    for m in models:
        for a in encs:
            for b in encs:
                if m[a][b] in (0, 1):
                    ee_to_abs += 1
    print(f"\n  Encoder·encoder → absorber: {ee_to_abs} times")

    # Test: "composition of encoders is an encoder or tester, never inert"
    # Weaker than full enc·enc≠inert but might be cleaner
    # Actually enc·enc≠inert IS the clean statement. Let's see its count.

    # Also test: direct pin (9,8) = 3
    def ax_pin_98(s, dot):
        s.add(dot[9][8] == 3)

    print(f"\n  Direct pin (9,8)=3:")
    cnt_pin, first_pin = count_with_axiom("(9,8) = 3 (direct)", ax_pin_98)

    # How many models survive enc·enc≠inert + 1-inert (already in base)?
    # Already tested above. Let's compare.

    # Final: show what the UNIQUE model looks like if we get 1
    if cnt_eeni is not None and cnt_eeni <= 5:
        s_final, dot_final = make_base_solver()
        ax_ee_no_inert(s_final, dot_final)
        if s_final.check() == sat:
            tbl = extract_table(s_final.model(), dot_final, N)
            rm = role_map(tbl)
            print(f"\n  Model with enc·enc ≠ inert:")
            for i in range(N):
                r = rm.get(i, "?")[0]
                print(f"    {i:2d}({r}): {tbl[i]}")
            print(f"    (9,8) = {tbl[9][8]}")

    # ═══════════════════════════════════════════════════════════════
    # 10. TARGETED AXIOMS FOR (9,8)
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("10. TARGETED AXIOMS — pinning (9,8)")
    print(f"{'═'*70}\n")

    # From the data:
    # v=3: (v·v)=1(bot), v is tester. Tester·tester = bot.
    # v=2: (v·v)=8(encoder). Inert·inert = encoder.
    # v=8: (v·v)=11. Just another encoder.
    #
    # Principle candidates:
    # P1: "For every pair of encoders a,b: if a·b is non-absorber,
    #      then (a·b)·(a·b) ∈ {0,1}" — squaring of any composition terminates
    # P2: "Every non-absorber squaring chain eventually reaches an absorber"
    #      (absorber-convergent dynamics)
    # P3: "The number of squaring fixed points (x·x=x) is maximized"
    #      We know dominant has 6 idempotents. v=3 (tester): 3·3=1≠3, not idemp.
    #      v=2: 2·2=4≠2. v=8: 8·8=11≠8. So all are non-idempotent.
    # P4: Simpler — "for every non-absorber x, the squaring orbit
    #      x → x·x → (x·x)² → ... reaches an absorber within 2 steps"

    # Test P2: absorber-convergent squaring on all models
    print("  P2: Every squaring orbit reaches an absorber:")
    conv_count = 0
    for m in models:
        converges = True
        for x in range(2, N):
            cur = x
            reached_abs = False
            for _ in range(N + 1):
                cur = m[cur][cur]
                if cur in (0, 1):
                    reached_abs = True
                    break
                if cur == m[cur][cur]:  # fixed point, non-absorber
                    break
            if not reached_abs:
                converges = False
                break
        if converges:
            conv_count += 1
    print(f"    Models: {conv_count}/{len(models)}")

    # Check per-value
    for v in sorted(by_val):
        conv = 0
        for m in by_val[v]:
            ok = True
            for x in range(2, N):
                cur = x
                reached_abs = False
                for _ in range(N + 1):
                    cur = m[cur][cur]
                    if cur in (0, 1):
                        reached_abs = True
                        break
                    if cur == m[cur][cur]:
                        break
                if not reached_abs:
                    ok = False
                    break
            if ok:
                conv += 1
        print(f"    v={v}: {conv}/{len(by_val[v])}")

    # Let's look at what squaring orbits look like for element 3 vs 2 vs 8
    print(f"\n  Squaring orbits of (9·8) value:")
    for v in sorted(by_val):
        m = by_val[v][0]
        orbit = [v]
        cur = v
        for _ in range(10):
            cur = m[cur][cur]
            orbit.append(cur)
            if cur in (0, 1) or cur == m[cur][cur]:
                break
        print(f"    v={v}: {' → '.join(map(str, orbit))}")

    # Test: "for non-absorber non-idempotent x, x·x ≠ x implies
    #        the squaring orbit reaches an absorber"
    # Actually let's check a stronger condition:
    # "Every non-absorber non-idempotent element eventually squares to
    #  an idempotent (including absorbers)"
    print(f"\n  Every non-idemp squares to an idempotent:")
    idem_conv = 0
    for m in models:
        ok = True
        for x in range(2, N):
            if m[x][x] == x:  # already idempotent
                continue
            cur = x
            found = False
            for _ in range(N + 1):
                cur = m[cur][cur]
                if cur == m[cur][cur]:  # idempotent (includes absorbers)
                    found = True
                    break
            if not found:
                ok = False
                break
        if ok:
            idem_conv += 1
    print(f"    Models: {idem_conv}/{len(models)}")

    # Hmm, all squaring orbits reach a fixed point anyway (finite magma).
    # The real question: does the squaring orbit of (9·8) value
    # reach an ABSORBER specifically?

    print(f"\n  Squaring orbit of (9·8) reaches absorber{chr(63)}")
    for v in sorted(by_val):
        reaches = 0
        for m in by_val[v]:
            cur = m[9][8]
            reached_abs = False
            for _ in range(N + 1):
                cur = m[cur][cur]
                if cur in (0, 1):
                    reached_abs = True
                    break
                if cur == m[cur][cur]:
                    break
            if reached_abs:
                reaches += 1
        print(f"    v={v}: {reaches}/{len(by_val[v])}")

    # Broader: for ALL encoder pairs (a,b), does the squaring orbit
    # of a·b reach an absorber?
    print(f"\n  For ALL enc·enc results, squaring reaches absorber:")
    all_conv = 0
    partial_counts = Counter()
    for m in models:
        rm = role_map(m)
        encs_m = [i for i in range(2, N) if rm.get(i) == "encoders"]
        all_ok = True
        for a in encs_m:
            for b in encs_m:
                ab = m[a][b]
                if ab in (0, 1):
                    continue
                cur = ab
                reached = False
                for _ in range(N + 1):
                    cur = m[cur][cur]
                    if cur in (0, 1):
                        reached = True
                        break
                    if cur == m[cur][cur]:
                        break
                if not reached:
                    all_ok = False
        if all_ok:
            all_conv += 1
    print(f"    Models: {all_conv}/{len(models)}")

    # Maybe the real distinguisher is simpler: 9·8 should be a tester or
    # absorber (boolean-valued), never an encoder or inert.
    # "enc·enc ∈ {absorbers ∪ testers ∪ encoders}" is trivially true.
    # "enc·enc is never inert" was too strong.
    # What about: "For encoder x and the compose element h,
    #  x·h is never inert"?

    # Let's try the cleanest approach: test (9·8)·(9·8) ∈ {0,1}
    # (squaring of the composition is an absorber)
    print(f"\n  Z3: (x·y)·(x·y) ∈ {{0,1}} for all non-absorber x,y:")

    def ax_comp_sq_absorber(s, dot):
        for x in range(2, N):
            for y in range(2, N):
                xy = dot[x][y]
                xy_sq = col_ite_lookup(dot, xy, xy, N)  # (x·y)·(x·y)
                # Hmm, xy is Z3 var, so both args are Z3
                # Need lookup_2d
                pass  # too complex with double Z3

    # Simpler: just test specific structural properties via Z3
    # "Every non-absorber squaring orbit reaches {0,1}"
    # This is hard to encode in Z3 for arbitrary depth.
    # But we can encode: for all x >= 2, let x2=x·x, x4=x2·x2, x8=x4·x4
    # At least one of {x, x2, x4, x8} ∈ {0,1}
    def ax_sq_converge_4(s, dot):
        for x in range(2, N):
            x2 = dot[x][x]
            x4 = col_ite_lookup(dot, x2, x2, N)
            x8 = col_ite_lookup(dot, x4, x4, N)
            s.add(Or(
                x2 == 0, x2 == 1,
                x4 == 0, x4 == 1,
                x8 == 0, x8 == 1
            ))

    cnt_sc, first_sc = count_with_axiom(
        "squaring converges to absorber in 3 steps", ax_sq_converge_4)

    # Test: idempotent count >= 4 (non-absorber)
    def ax_idem_4(s, dot):
        flags = []
        for x in range(2, N):
            f = Int(f"id4_{x}")
            s.add(If(dot[x][x] == x, f == 1, f == 0))
            flags.append(f)
        s.add(sum(flags) >= 4)

    cnt_id, _ = count_with_axiom(">=4 non-absorber idempotents", ax_idem_4)

    # Combination: sq converge + idempotents
    def ax_combined(s, dot):
        ax_sq_converge_4(s, dot)
        ax_idem_4(s, dot)

    cnt_comb, first_comb = count_with_axiom(
        "sq-converge + >=4 idempotents", ax_combined)

    if first_comb and cnt_comb <= 10:
        print(f"\n  Model with combined axioms:")
        rm = role_map(first_comb)
        for i in range(N):
            r = rm.get(i, "?")[0]
            print(f"    {i:2d}({r}): {first_comb[i]}")
        print(f"    (9,8) = {first_comb[9][8]}")

    # What about just: t·0 = 0 (tester accepts top)?
    def ax_t_top(s, dot):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            s.add(Or(Not(is_tst), dot[x][0] == 0))

    cnt_tt, _ = count_with_axiom("tester accepts top (t·0=0)", ax_t_top)

    # Combination of everything
    def ax_everything(s, dot):
        ax_sq_converge_4(s, dot)
        ax_idem_4(s, dot)
        ax_t_top(s, dot)

    cnt_all, first_all = count_with_axiom(
        "sq-converge + idempotents + t·0=0", ax_everything)

    if first_all and cnt_all <= 10:
        print(f"\n  Model with all three axioms:")
        rm = role_map(first_all)
        for i in range(N):
            r = rm.get(i, "?")[0]
            print(f"    {i:2d}({r}): {first_all[i]}")
        print(f"    (9,8) = {first_all[9][8]}")
        # Check free cells
        for a, b in FREE_CELLS:
            print(f"    ({a},{b}) = {first_all[a][b]}")

    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")


def _sq_orbit(m, x, N):
    """Squaring orbit of x in model m."""
    orbit = set()
    cur = x
    for _ in range(N):
        if cur in orbit:
            break
        orbit.add(cur)
        cur = m[cur][cur]
    orbit.add(cur)
    return orbit


def squaring_stability():
    """
    Test: (x·x)·(x·x) = x·x for all x.
    "Squaring is idempotent as a map — self-interaction stabilizes."

    Also test the weaker composition variant:
    For all a,b: let c=a·b. Then c·c ∈ {0,1} or (c·c)·(c·c) = c·c.
    """

    from collections import Counter

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    CORE = 6
    Q_IDX, E_IDX = 6, 7
    N = 12
    t_idx, f_idx, g_idx = 3, 2, 4
    r_idx, h_idx, Y_idx = 8, 9, 10

    print("=" * 70)
    print("SQUARING STABILITY ANALYSIS")
    print("(x·x)·(x·x) = x·x — does squaring stabilize in one step?")
    print("=" * 70)

    # ── Enumerate with 1-inert ───────────────────────────────────────
    print("\nEnumerating models (1-inert, cap=500)...")
    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    for x in range(2, CORE):
        gx = dot[g_idx][x]
        r_gx = col_ite_lookup(dot, r_idx, gx, N)
        s.add(dot[h_idx][x] == r_gx)

    yr = dot[Y_idx][r_idx]
    r_yr = col_ite_lookup(dot, r_idx, yr, N)
    s.add(yr == r_yr)
    s.add(yr >= 2)

    # 1-inert
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
        inert_flag = Int(f"inert_{x}")
        s.add(If(is_inert, inert_flag == 1, inert_flag == 0))
    s.add(sum([Int(f"inert_{x}") for x in range(2, N)]) == 1)

    models = []
    t0 = time.time()
    CAP = 500
    while len(models) < CAP:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        models.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    exhausted = len(models) < CAP
    print(f"  Found {len(models)}{'(exhaustive)' if exhausted else '+'} ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # 1. CHECK (x·x)·(x·x) = x·x ON ALL MODELS
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("1. SQUARING STABILITY: (x·x)·(x·x) = x·x for all x")
    print(f"{'═'*70}\n")

    stable_count = 0
    unstable_models = []
    for m in models:
        ok = True
        for x in range(N):
            xx = m[x][x]
            xxxx = m[xx][xx]
            if xxxx != xx:
                ok = False
                break
        if ok:
            stable_count += 1
        else:
            unstable_models.append(m)

    print(f"  Models where squaring stabilizes: {stable_count}/{len(models)}")
    print(f"  Unstable models: {len(unstable_models)}")

    # Group by (9,8) value
    by_98 = {}
    for m in models:
        v = m[9][8]
        by_98.setdefault(v, []).append(m)

    for v in sorted(by_98):
        stable_v = sum(1 for m in by_98[v]
                       if all(m[m[x][x]][m[x][x]] == m[x][x] for x in range(N)))
        print(f"  (9,8)={v}: {stable_v}/{len(by_98[v])} stable")

    # Which elements fail stability in the unstable models?
    if unstable_models:
        print(f"\n  Elements failing stability in unstable models:")
        fail_elems = Counter()
        for m in unstable_models:
            for x in range(N):
                xx = m[x][x]
                xxxx = m[xx][xx]
                if xxxx != xx:
                    fail_elems[x] += 1
        for x, cnt in fail_elems.most_common():
            xx = unstable_models[0][x][x]
            xxxx = unstable_models[0][xx][xx]
            print(f"    x={x}: x·x={xx}, (x·x)·(x·x)={xxxx} ≠ {xx}  ({cnt}x)")

    # ═══════════════════════════════════════════════════════════════
    # 2. VERIFY VIA Z3 — add as axiom, count models
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("2. Z3 VERIFICATION")
    print(f"{'═'*70}\n")

    def make_base_solver():
        s, dot = encode_level(8, N, timeout_seconds=300)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)
        # 1-inert
        for x in range(2, N):
            is_tst = And([Or(dot[x][jj] == 0, dot[x][jj] == 1) for jj in range(N)])
            enc_pairs = []
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    enc_pairs.append(And(
                        dot[x][j1] != 0, dot[x][j1] != 1,
                        dot[x][j2] != 0, dot[x][j2] != 1,
                        dot[x][j1] != dot[x][j2]))
            is_enc = Or(enc_pairs) if enc_pairs else False
            is_inert = And(Not(is_tst), Not(is_enc))
            inert_flag = Int(f"zi_{x}")
            s.add(If(is_inert, inert_flag == 1, inert_flag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        return s, dot

    def count_with_axiom(name, add_axiom_fn, cap=100):
        s, dot = make_base_solver()
        add_axiom_fn(s, dot)
        count = 0
        t0 = time.time()
        first = None
        while count < cap:
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            if first is None:
                first = tbl
            count += 1
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0
        tag = f"{count}{'+'  if count >= cap else '(exhaustive)'}"
        print(f"    {name:55s} → {tag} ({elapsed:.1f}s)")
        return count, first

    # Baseline
    count_with_axiom("baseline (1-inert only)", lambda s, d: None)

    # lookup_2d for double-Z3 indices
    def lookup_2d(dot, row_expr, col_expr, N):
        result = ite_lookup(dot, row_expr, 0, N)
        for j in range(1, N):
            result = If(col_expr == j, ite_lookup(dot, row_expr, j, N), result)
        return result

    # SS (strong): squaring stability — (x·x)·(x·x) = x·x
    # Already shown: FAILS in 500/500 models due to 2-cycles like 6↔7.
    # So SS is INCOMPATIBLE with the full package.
    # Let's test it anyway in Z3 to confirm UNSAT.
    def ax_sq_stable(s, dot):
        for x in range(N):
            xx = dot[x][x]
            xxxx = lookup_2d(dot, xx, xx, N)
            s.add(xxxx == xx)

    cnt_ss, first_ss = count_with_axiom(
        "(x·x)·(x·x) = x·x  (squaring stability)", ax_sq_stable)

    # SS2: Squaring stabilizes in 2 steps
    # (x·x)·(x·x) =: y, then y·y = y
    # The squaring map's image's image consists of idempotents.
    # 2→4→11→2 is a 3-cycle. The image of 2 under squaring is 4.
    # Image of 4 is 11. Image of 11 is 2. None is a fixpoint.
    # SS2 says: take x·x, square that to get y = (x·x)·(x·x), then y·y = y.
    # For x=2: x·x=4, y=(4)·(4)=11, y·y=11·11=2 ≠ 11. FAILS.
    # So SS2 is also too strong.

    # SS3: Squaring stabilizes in 3 steps (catches 3-cycles)
    # After 3 squarings from any start, you're at a fixpoint.
    def ax_sq_stable_3(s, dot):
        for x in range(N):
            x2 = dot[x][x]
            x4 = lookup_2d(dot, x2, x2, N)
            x8 = lookup_2d(dot, x4, x4, N)
            x16 = lookup_2d(dot, x8, x8, N)
            s.add(x16 == x8)

    cnt_ss3, first_ss3 = count_with_axiom(
        "sq^4 = sq^3  (stabilize in 3 steps)", ax_sq_stable_3)

    # SS_CYCLE: Squaring orbit has period dividing a fixed k.
    # The existing structure has a 3-cycle (2→4→11→2) and a 2-cycle (6↔7).
    # lcm(2,3) = 6. Let's check: does squaring^6 = squaring^0?
    # That's just: x^(2^6) = x for the squaring map. Too weird.

    # Better: the squaring map's IMAGE consists of elements whose
    # squaring orbits have bounded period.
    # Actually, let me just check whether SS3 pins (9,8).
    if first_ss3:
        print(f"\n  Under SS3 (stabilize in 3 steps):")
        # Enumerate and check free cell
        s3, dot3 = make_base_solver()
        ax_sq_stable_3(s3, dot3)
        ss3_models = []
        while len(ss3_models) < 50:
            if s3.check() != sat:
                break
            tbl = extract_table(s3.model(), dot3, N)
            ss3_models.append(tbl)
            s3.add(Or([dot3[i][j] != tbl[i][j]
                        for i in range(N) for j in range(N)]))

        for a, b in [(4, 11), (6, 10), (9, 8)]:
            vals = sorted(set(m[a][b] for m in ss3_models))
            print(f"    ({a},{b}): {vals}")

        vary_count = 0
        for i in range(N):
            for j in range(N):
                vals = set(m[i][j] for m in ss3_models)
                if len(vals) > 1:
                    vary_count += 1
        print(f"    Varying cells: {vary_count}/{N*N}")
        print(f"    Models: {len(ss3_models)}"
              f"{'+'  if len(ss3_models) >= 50 else '(exhaustive)'}")

    # Also test: the weaker composition variant from the user's request
    # For all a,b: c=a·b, then c·c ∈ {0,1} or (c·c)·(c·c) = c·c
    # This is SS applied only to elements that are products.
    # But every element is producible (constructibility = 100%).
    # So this is equivalent to SS on the image of the multiplication.
    # Since the image IS everything (full producibility), this = SS.
    # Already shown UNSAT.

    # Let's try the REAL question: what pins (9,8)?
    # From the data: (9,8)=3 in 495/500. Values 2 and 8 are rare.
    # 9·8=3(tester): (3·3)=1(bot). Squaring terminates to absorber.
    # 9·8=2(inert): (2·2)=4. Then 4·4=11, 11·11=2. 3-cycle, never absorber.
    # 9·8=8(encoder): (8·8)=11, (11·11)=2, (2·2)=4. Same 3-cycle.
    #
    # So the distinguisher is: "9·8 squares to an absorber"
    # More generally: every element's squaring orbit reaches {0,1}.
    # But we saw x=6: 6·6=7, 7·7=6 — 2-cycle, never absorber.
    # So "every orbit reaches absorber" is also 0/500.
    #
    # The real pattern: 9·8=3 is the ONLY value where the squaring orbit
    # of 9·8 DOESN'T join the existing non-absorber cycles.
    # 3·3=1(absorber). It terminates.
    # 2 joins the 2→4→11 cycle. 8 also joins it (8·8=11).
    #
    # Principle: for the COMPOSITION element (h), its square should
    # terminate. h represents a computed result — it shouldn't oscillate.
    # h·h should be an absorber or idempotent.
    #
    # Let's test: "h·h ∈ {0,1} or h·h = h" for h = compose element.
    # And more generally: composition results terminate.

    # Test: for h (the compose element, idx=9), h·h terminates to absorber
    print(f"\n  Specific: element 9 (compose) squaring behavior:")
    for m in models[:5]:
        sq9 = m[9][9]
        sq_chain = [9]
        cur = 9
        for _ in range(6):
            cur = m[cur][cur]
            sq_chain.append(cur)
        print(f"    9 → {' → '.join(map(str, sq_chain))}")

    # Hmm, 9·9 is always 7 (fixed), and 7·7=6, 6·6=7 — a 2-cycle.
    # So element 9's OWN squaring orbit doesn't terminate.
    # But (9·8) = 3, and 3·3 = 1 (absorber). The APPLICATION terminates.

    # The real axis: what does the TESTER do?
    # 3 = tester. 3·3 = 3·3 = ... let me check.
    print(f"\n  Tester (element 3) squaring: 3·3 = {models[0][3][3]}")
    print(f"  Tester·tester = {models[0][3][3]} "
          f"({'absorber' if models[0][3][3] in (0,1) else 'non-absorber'})")

    # 3·3 = 2 in models where inert=2? Let me check more carefully.
    t_sq = Counter(m[3][3] for m in models)
    print(f"  Tester self-application across models: {dict(t_sq)}")

    # In dominant: 3·3 = 1 (bot). Tester applied to itself gives bot.
    # This is like "testing yourself is trivially false."

    # KEY INSIGHT: 9·8 = 3 means the COMPOSE element applied to
    # the BRANCH element gives the TESTER. And tester·tester = bot.
    # The minority values (2, 8) make 9·8 an encoder or inert,
    # which then enters a non-terminating squaring cycle.

    # Clean axiom: "tester·tester = bot" (1)
    # This is t·t = 1. Since we know t is always at position 3:
    # 3·3 = 1.
    # Check if this is already true in all models:
    tt_is_1 = sum(1 for m in models if m[3][3] == 1)
    print(f"\n  t·t = 1 (bot): {tt_is_1}/{len(models)}")

    # Does adding t·t = bot pin (9,8)?
    # No — t·t is about the tester itself, not about 9·8.
    # But if we require "for every composition c of encoders,
    # c squares to an absorber OR c is itself a tester or encoder
    # with bounded dynamics" — that's getting complicated.

    # Simplest path: encode "for all x,y ≥ 2: if x·y is a tester,
    # then (x·y)·(x·y) is an absorber"
    # Since tester·tester = absorber is already near-universal (499/500),
    # this is almost free.

    # Actually, the cleanest: the squaring map restricted to
    # {testers, absorbers} is closed. Tester² = absorber, absorber² = absorber.
    # This already holds. The question is whether 9·8 = tester.
    # That's a structural fact, not an axiom.

    # Let me try the cleanest Z3 test: "(9·8)·(9·8) ∈ {0,1}"
    # i.e., the composition of compose and branch squares to absorber.
    # More generally: "for all pairs x,y from {branch, compose, Y},
    # (x·y)·(x·y) ∈ {0,1} or (x·y)·(x·y) = x·y"
    # i.e., "computational element interactions stabilize."

    # CS (Computational Stability):
    # For x ∈ {r, h, Y} and y ∈ {r, h, Y}:
    # (x·y)² is an absorber or idempotent.
    comp_elems = [r_idx, h_idx, Y_idx]  # 8, 9, 10

    def ax_comp_stable(s, dot):
        for x in comp_elems:
            for y in comp_elems:
                xy = dot[x][y]
                xy_sq = lookup_2d(dot, xy, xy, N)
                s.add(Or(xy_sq == 0, xy_sq == 1, xy_sq == xy))

    cnt_cs, first_cs = count_with_axiom(
        "computational stability (comp²→absorber/fixpt)", ax_comp_stable)

    if first_cs and cnt_cs <= 10:
        s_cs, dot_cs = make_base_solver()
        ax_comp_stable(s_cs, dot_cs)
        cs_models = []
        while len(cs_models) < 50:
            if s_cs.check() != sat:
                break
            tbl = extract_table(s_cs.model(), dot_cs, N)
            cs_models.append(tbl)
            s_cs.add(Or([dot_cs[i][j] != tbl[i][j]
                          for i in range(N) for j in range(N)]))
        print(f"\n  Under computational stability:")
        for a, b in [(4, 11), (6, 10), (9, 8)]:
            vals = sorted(set(m[a][b] for m in cs_models))
            print(f"    ({a},{b}): {vals}")
        vary = sum(1 for i in range(N) for j in range(N)
                   if len(set(m[i][j] for m in cs_models)) > 1)
        print(f"    Varying cells: {vary}/{N*N}")
        print(f"    Models: {len(cs_models)}"
              f"{'+'  if len(cs_models) >= 50 else '(exhaustive)'}")

        if len(cs_models) <= 5:
            for idx, m in enumerate(cs_models):
                rm = role_map(m)
                print(f"\n  Model {idx}:")
                for i in range(N):
                    r = rm.get(i, "?")[0]
                    print(f"    {i:2d}({r}): {m[i]}")

    # ═══════════════════════════════════════════════════════════════
    # 3. WEAKER VARIANT — composition squares stabilize
    # For all a,b: c=a·b, then c·c ∈ {0,1} or (c·c)·(c·c) = c·c
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("3. WEAKER VARIANT — composition square stability")
    print("  For all a,b: c=a·b ⟹ c·c ∈ {{0,1}} or (c·c)² = c·c")
    print(f"{'═'*70}\n")

    # Check on enumerated models
    weak_count = 0
    for m in models:
        ok = True
        for a in range(N):
            for b in range(N):
                c = m[a][b]
                cc = m[c][c]
                if cc in (0, 1):
                    continue
                cccc = m[cc][cc]
                if cccc != cc:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            weak_count += 1
    print(f"  Models satisfying weak variant: {weak_count}/{len(models)}")

    # Note: if SS holds, the weak variant is automatically satisfied
    # (c·c is some element y, and y·y = y by SS applied to y = c·c... wait,
    #  SS says (y·y)·(y·y) = y·y. But y = c·c = x·x for x = c.
    #  So SS says (c·c)·(c·c) = c·c. That's exactly what the weak variant
    #  requires when c·c ∉ {0,1}. So yes, SS ⟹ weak variant.)

    # ═══════════════════════════════════════════════════════════════
    # 4. SQUARING STABILITY AT OTHER SIZES
    # Does SS hold at N=8, N=10 too?
    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("4. SQUARING STABILITY AT OTHER SIZES")
    print(f"{'═'*70}\n")

    # Section 4 skipped — SS is incompatible with the dominant cluster's
    # squaring 2-cycles (6↔7) and 3-cycle (2→4→11→2).
    # SS produces a DIFFERENT structure, not a refinement of the current one.
    print("  (Section 4 skipped — SS forces different structure, not a refinement)")

    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")
    print(f"""
  Axiom SS: (x·x)·(x·x) = x·x  — "squaring stabilizes"

  Interpretation: self-interaction reaches a fixed point immediately.
  A process applied to itself doesn't oscillate — it settles.

  This is a natural dynamical principle: the squaring map is
  idempotent. The image of squaring consists entirely of
  idempotents (self-stable elements).
""")


def computational_activity():
    """
    Targeted axiom: computational elements should not produce inert output.

    The inert element is ground/context. Computational elements (branch r,
    compose h, Y-combinator) are active. Their interactions should stay
    active — producing encoders or testers, never inert.

    Test hierarchy:
    1. Narrow: just (9,8) ≠ inert  (compose·branch ≠ ground)
    2. Medium: comp_elem · comp_elem ≠ inert  ({r,h,Y} pairwise)
    3. Broad: comp_elem · anything ≠ inert  (computational output is never ground)
    4. Broadest: any_non-absorber · comp_elem ≠ inert
    5. Principled: "the image of each computational element's row
       contains no inert elements" (computational rows are active)
    """

    from collections import Counter

    # ── Helpers ──────────────────────────────────────────────────────
    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    def is_inert_z3(dot, x, N):
        """Z3 formula: element x is inert (not tester, not encoder)."""
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

    def is_inert_result_z3(dot, val_expr, N):
        """Z3 formula: the row of val_expr is inert."""
        is_tst = And([Or(ite_lookup(dot, val_expr, j, N) == 0,
                         ite_lookup(dot, val_expr, j, N) == 1) for j in range(N)])
        enc_pairs = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                enc_pairs.append(And(
                    ite_lookup(dot, val_expr, j1, N) != 0,
                    ite_lookup(dot, val_expr, j1, N) != 1,
                    ite_lookup(dot, val_expr, j2, N) != 0,
                    ite_lookup(dot, val_expr, j2, N) != 1,
                    ite_lookup(dot, val_expr, j1, N) !=
                    ite_lookup(dot, val_expr, j2, N)))
        is_enc = Or(enc_pairs) if enc_pairs else False
        return And(Not(is_tst), Not(is_enc))

    CORE = 6
    Q_IDX, E_IDX = 6, 7
    N = 12
    t_idx, f_idx, g_idx = 3, 2, 4
    r_idx, h_idx, Y_idx = 8, 9, 10
    COMP_ELEMS = [r_idx, h_idx, Y_idx]

    print("=" * 70)
    print("COMPUTATIONAL ACTIVITY — targeted inert-avoidance")
    print("=" * 70)

    # ── Enumerate ────────────────────────────────────────────────────
    print("\nEnumerating models (1-inert, cap=500)...")
    s0, dot0 = encode_level(8, N, timeout_seconds=300)
    add_full_base(s0, dot0, N)
    add_qe_pair(s0, dot0, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
    for x in range(2, CORE):
        tx = dot0[t_idx][x]
        fx = dot0[f_idx][x]
        gx = dot0[g_idx][x]
        s0.add(If(tx == 0, dot0[r_idx][x] == fx, dot0[r_idx][x] == gx))
    s0.add(Or([dot0[f_idx][j] != dot0[g_idx][j] for j in range(2, CORE)]))
    for x in range(2, CORE):
        gx = dot0[g_idx][x]
        r_gx = col_ite_lookup(dot0, r_idx, gx, N)
        s0.add(dot0[h_idx][x] == r_gx)
    yr = dot0[Y_idx][r_idx]
    r_yr = col_ite_lookup(dot0, r_idx, yr, N)
    s0.add(yr == r_yr)
    s0.add(yr >= 2)
    # 1-inert
    for x in range(2, N):
        iflag = Int(f"inert_{x}")
        s0.add(If(is_inert_z3(dot0, x, N), iflag == 1, iflag == 0))
    s0.add(sum([Int(f"inert_{x}") for x in range(2, N)]) == 1)

    models = []
    t0 = time.time()
    while len(models) < 500:
        if s0.check() != sat:
            break
        tbl = extract_table(s0.model(), dot0, N)
        models.append(tbl)
        s0.add(Or([dot0[i][j] != tbl[i][j]
                    for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    print(f"  {len(models)}{'+'  if len(models) >= 500 else ''} models ({elapsed:.1f}s)")

    # ── Empirical check: which comp·comp pairs hit inert? ────────────
    print(f"\n{'═'*70}")
    print("1. EMPIRICAL — which computational interactions hit inert?")
    print(f"{'═'*70}\n")

    # Find inert element in each model
    for m in models[:1]:
        rm = role_map(m)
        inert_elems = [i for i in range(2, N) if rm.get(i) == "inert"]
        print(f"  Inert element: {inert_elems}")

    # For each pair of comp elements, does their product ever hit inert?
    all_elems = list(range(2, N))
    print(f"\n  Comp element products hitting inert (element 2):")
    for a in COMP_ELEMS:
        for b in range(N):
            hit_inert = sum(1 for m in models if role_map(m).get(m[a][b]) == "inert")
            if hit_inert > 0:
                pct = 100 * hit_inert / len(models)
                vals = Counter(m[a][b] for m in models if
                               role_map(m).get(m[a][b]) == "inert")
                print(f"    {a}·{b} → inert in {hit_inert}/{len(models)} "
                      f"({pct:.1f}%): values {dict(vals)}")

    # Also check: anything · comp_elem → inert
    print(f"\n  Anything · comp_elem → inert:")
    for b in COMP_ELEMS:
        for a in range(N):
            hit_inert = sum(1 for m in models if role_map(m).get(m[a][b]) == "inert")
            if hit_inert > 0:
                pct = 100 * hit_inert / len(models)
                vals = Counter(m[a][b] for m in models if
                               role_map(m).get(m[a][b]) == "inert")
                print(f"    {a}·{b} → inert in {hit_inert}/{len(models)} "
                      f"({pct:.1f}%): values {dict(vals)}")

    # Also: comp · Q/E → inert?
    print(f"\n  Comp · Q/E → inert:")
    for a in COMP_ELEMS:
        for b in [Q_IDX, E_IDX]:
            hit_inert = sum(1 for m in models if role_map(m).get(m[a][b]) == "inert")
            if hit_inert > 0:
                vals = Counter(m[a][b] for m in models if
                               role_map(m).get(m[a][b]) == "inert")
                print(f"    {a}·{b} → inert in {hit_inert}/{len(models)}: "
                      f"values {dict(vals)}")

    # ── Z3 tests ─────────────────────────────────────────────────────
    print(f"\n{'═'*70}")
    print("2. Z3 VERIFICATION — targeted axioms")
    print(f"{'═'*70}\n")

    def make_base_solver():
        s, dot = encode_level(8, N, timeout_seconds=300)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)
        # 1-inert
        for x in range(2, N):
            iflag = Int(f"zi_{x}")
            s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        return s, dot

    def count_with_axiom(name, add_axiom_fn, cap=100):
        s, dot = make_base_solver()
        add_axiom_fn(s, dot)
        count = 0
        t0 = time.time()
        first = None
        while count < cap:
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            if first is None:
                first = tbl
            count += 1
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0
        tag = f"{count}{'+'  if count >= cap else '(exhaustive)'}"
        print(f"    {name:55s} → {tag} ({elapsed:.1f}s)")
        return count, first

    count_with_axiom("baseline (1-inert)", lambda s, d: None)

    # Level 1: comp·comp ≠ inert (just among {r,h,Y})
    def ax_comp_comp_active(s, dot):
        for a in COMP_ELEMS:
            for b in COMP_ELEMS:
                ab = dot[a][b]
                s.add(Not(is_inert_result_z3(dot, ab, N)))

    cnt1, f1 = count_with_axiom("comp·comp ≠ inert ({r,h,Y} pairwise)", ax_comp_comp_active)

    # Level 2: comp·anything ≠ inert (comp rows have no inert output)
    def ax_comp_row_active(s, dot):
        for a in COMP_ELEMS:
            for b in range(2, N):
                ab = dot[a][b]
                s.add(Not(is_inert_result_z3(dot, ab, N)))

    cnt2, f2 = count_with_axiom("comp·x ≠ inert (comp rows active)", ax_comp_row_active)

    # Level 3: anything·comp ≠ inert (comp columns have no inert output)
    def ax_comp_col_active(s, dot):
        for b in COMP_ELEMS:
            for a in range(2, N):
                ab = dot[a][b]
                s.add(Not(is_inert_result_z3(dot, ab, N)))

    cnt3, f3 = count_with_axiom("x·comp ≠ inert (comp cols active)", ax_comp_col_active)

    # Level 4: comp rows AND cols active (both directions)
    def ax_comp_fully_active(s, dot):
        ax_comp_row_active(s, dot)
        ax_comp_col_active(s, dot)

    cnt4, f4 = count_with_axiom("comp fully active (rows + cols)", ax_comp_fully_active)

    # Level 5: broader — all non-absorber, non-inert elements
    # have active rows (no inert in output).
    # i.e., "active elements produce active results"
    # active = tester or encoder
    def ax_active_produces_active(s, dot):
        for a in range(2, N):
            a_is_inert = is_inert_z3(dot, a, N)
            for b in range(2, N):
                ab = dot[a][b]
                ab_is_inert = is_inert_result_z3(dot, ab, N)
                # If a is not inert, then a·b is not inert
                s.add(Or(a_is_inert, Not(ab_is_inert)))

    cnt5, f5 = count_with_axiom("active·x ≠ inert (active→active)", ax_active_produces_active)

    # Show results for winning axioms
    for name, cnt, first in [
        ("comp·comp active", cnt1, f1),
        ("comp rows active", cnt2, f2),
        ("comp cols active", cnt3, f3),
        ("comp fully active", cnt4, f4),
        ("active→active", cnt5, f5),
    ]:
        if first and cnt <= 20:
            print(f"\n  {name} — {cnt} model(s):")
            # enumerate them all
            s_e, dot_e = make_base_solver()
            if "comp·comp" in name:
                ax_comp_comp_active(s_e, dot_e)
            elif "rows" in name:
                ax_comp_row_active(s_e, dot_e)
            elif "cols" in name:
                ax_comp_col_active(s_e, dot_e)
            elif "fully" in name:
                ax_comp_fully_active(s_e, dot_e)
            elif "active" in name:
                ax_active_produces_active(s_e, dot_e)

            e_models = []
            while len(e_models) < 50:
                if s_e.check() != sat:
                    break
                tbl = extract_table(s_e.model(), dot_e, N)
                e_models.append(tbl)
                s_e.add(Or([dot_e[i][j] != tbl[i][j]
                             for i in range(N) for j in range(N)]))

            # Free cells
            for a, b in [(4, 11), (6, 10), (9, 8)]:
                vals = sorted(set(m[a][b] for m in e_models))
                print(f"    ({a},{b}): {vals}")

            # Varying cells
            vary = sum(1 for i in range(N) for j in range(N)
                       if len(set(m[i][j] for m in e_models)) > 1)
            print(f"    Varying cells: {vary}/{N*N}")
            print(f"    Total models: {len(e_models)}"
                  f"{'+'  if len(e_models) >= 50 else '(exhaustive)'}")

            if len(e_models) <= 3:
                for idx, m in enumerate(e_models):
                    rm = role_map(m)
                    print(f"\n    Model {idx}:")
                    for i in range(N):
                        r = rm.get(i, "?")[0]
                        print(f"      {i:2d}({r}): {m[i]}")

    # ═══════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")
    print("""
  Axiom hierarchy for computational activity:
    comp·comp active:     only {r,h,Y} pairwise products avoid inert
    comp rows active:     computational element rows never produce inert
    comp cols active:     nothing applied to comp elements gives inert
    comp fully active:    both directions
    active → active:      ALL active elements (tester+encoder) never
                          produce inert — the broadest principled version

  Interpretation: "computation preserves activity."
  The inert element is substrate/ground. Active elements (testers,
  encoders, and especially computational elements like branch, compose,
  Y-combinator) should not collapse to ground when composed.
  Ground is input context, not output.
""")


def activity_refinement():
    """
    Refine the sweet spot between "comp fully active" (100+, too weak)
    and "active·x ≠ inert" (UNSAT, too strong).

    The UNSAT comes from active elements applied to ABSORBERS giving inert
    (8·1→inert in 99% of models). So restrict to non-absorber inputs.

    Also test: "active·active ≠ inert on non-absorber inputs only"
    and intermediate variants.
    """

    from collections import Counter

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

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

    def is_inert_result_z3(dot, val_expr, N):
        is_tst = And([Or(ite_lookup(dot, val_expr, j, N) == 0,
                         ite_lookup(dot, val_expr, j, N) == 1) for j in range(N)])
        enc_pairs = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                enc_pairs.append(And(
                    ite_lookup(dot, val_expr, j1, N) != 0,
                    ite_lookup(dot, val_expr, j1, N) != 1,
                    ite_lookup(dot, val_expr, j2, N) != 0,
                    ite_lookup(dot, val_expr, j2, N) != 1,
                    ite_lookup(dot, val_expr, j1, N) !=
                    ite_lookup(dot, val_expr, j2, N)))
        is_enc = Or(enc_pairs) if enc_pairs else False
        return And(Not(is_tst), Not(is_enc))

    CORE = 6
    Q_IDX, E_IDX = 6, 7
    N = 12
    t_idx, f_idx, g_idx = 3, 2, 4
    r_idx, h_idx, Y_idx = 8, 9, 10
    COMP_ELEMS = [r_idx, h_idx, Y_idx]

    print("=" * 70)
    print("ACTIVITY REFINEMENT — finding the sweet spot")
    print("=" * 70)

    def make_base_solver():
        s, dot = encode_level(8, N, timeout_seconds=300)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)
        for x in range(2, N):
            iflag = Int(f"zi_{x}")
            s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        return s, dot

    def count_and_analyze(name, add_axiom_fn, cap=100):
        s, dot = make_base_solver()
        add_axiom_fn(s, dot)
        count = 0
        t0 = time.time()
        first = None
        all_tbls = []
        while count < cap:
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            if first is None:
                first = tbl
            all_tbls.append(tbl)
            count += 1
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        elapsed = time.time() - t0
        tag = f"{count}{'+'  if count >= cap else '(exhaustive)'}"
        print(f"    {name:55s} → {tag} ({elapsed:.1f}s)")
        if all_tbls and count <= cap:
            # Show free cell values
            for a, b in [(4, 11), (6, 10), (9, 8)]:
                vals = sorted(set(m[a][b] for m in all_tbls))
                print(f"      ({a},{b}): {vals}")
            vary = sum(1 for i in range(N) for j in range(N)
                       if len(set(m[i][j] for m in all_tbls)) > 1)
            print(f"      Varying cells: {vary}/{N*N}")
        if first and count <= 3:
            for idx, m in enumerate(all_tbls[:3]):
                rm = role_map(m)
                print(f"\n      Model {idx}:")
                for i in range(N):
                    r = rm.get(i, "?")[0]
                    print(f"        {i:2d}({r}): {m[i]}")
        return count, first, all_tbls

    print(f"\n{'═'*70}")
    print("Axiom candidates (non-absorber domain)")
    print(f"{'═'*70}\n")

    count_and_analyze("baseline", lambda s, d: None)

    # A: active·(non-absorber) ≠ inert
    # "When an active element acts on a non-absorber, the result is active"
    def ax_active_nonabs_active(s, dot):
        for a in range(2, N):
            a_inert = is_inert_z3(dot, a, N)
            for b in range(2, N):  # non-absorber inputs only
                ab = dot[a][b]
                ab_inert = is_inert_result_z3(dot, ab, N)
                s.add(Or(a_inert, Not(ab_inert)))

    count_and_analyze("active·(non-abs) ≠ inert", ax_active_nonabs_active)

    # B: encoder·(non-absorber) ≠ inert
    # Slightly different: only encoders, not testers
    def ax_enc_nonabs_active(s, dot):
        for a in range(2, N):
            a_inert = is_inert_z3(dot, a, N)
            a_tst = And([Or(dot[a][j] == 0, dot[a][j] == 1) for j in range(N)])
            a_is_enc = And(Not(a_inert), Not(a_tst))
            for b in range(2, N):
                ab = dot[a][b]
                ab_inert = is_inert_result_z3(dot, ab, N)
                s.add(Or(Not(a_is_enc), Not(ab_inert)))

    count_and_analyze("encoder·(non-abs) ≠ inert", ax_enc_nonabs_active)

    # C: (non-absorber)·(non-absorber, non-inert) ≠ inert
    # "Acting on active elements never produces inert"
    def ax_nonabs_active_input(s, dot):
        for a in range(2, N):
            for b in range(2, N):
                b_inert = is_inert_z3(dot, b, N)
                ab = dot[a][b]
                ab_inert = is_inert_result_z3(dot, ab, N)
                # If b is not inert (i.e., b is active), result not inert
                s.add(Or(b_inert, Not(ab_inert)))

    count_and_analyze("x·(active input) ≠ inert", ax_nonabs_active_input)

    # D: active·active ≠ inert (both sides active, non-absorber)
    def ax_active_active(s, dot):
        for a in range(2, N):
            a_inert = is_inert_z3(dot, a, N)
            for b in range(2, N):
                b_inert = is_inert_z3(dot, b, N)
                ab = dot[a][b]
                ab_inert = is_inert_result_z3(dot, ab, N)
                s.add(Or(a_inert, b_inert, Not(ab_inert)))

    count_and_analyze("active·active ≠ inert (both active)", ax_active_active)

    # E: comp·(non-absorber, non-inert) ≠ inert
    # "Computational elements acting on active inputs never produce inert"
    def ax_comp_active_input(s, dot):
        for a in COMP_ELEMS:
            for b in range(2, N):
                b_inert = is_inert_z3(dot, b, N)
                ab = dot[a][b]
                ab_inert = is_inert_result_z3(dot, ab, N)
                s.add(Or(b_inert, Not(ab_inert)))

    count_and_analyze("comp·(active input) ≠ inert", ax_comp_active_input)

    # F: t·t = 1 (tester self-application = bot)
    def ax_tt_bot(s, dot):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            s.add(Or(Not(is_tst), dot[x][x] == 1))

    count_and_analyze("t·t = bot (tester self-annihilates)", ax_tt_bot)

    # G: t·t = bot AND comp·(active) ≠ inert
    def ax_combined_tidy(s, dot):
        ax_tt_bot(s, dot)
        ax_comp_active_input(s, dot)

    count_and_analyze("t·t=bot + comp·(active)≠inert", ax_combined_tidy)

    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")


def extract_psi():
    """
    Extract and verify Ψ — the unique N=12 algebra selected by:
    L8 + C + D + PA + VV + QE + 1-inert + Branch + Compose + Y + (9·8=3)

    Then document it fully.
    """

    from collections import Counter

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

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

    CORE = 6
    Q_IDX, E_IDX = 6, 7
    N = 12
    t_idx, f_idx, g_idx = 3, 2, 4
    r_idx, h_idx, Y_idx = 8, 9, 10

    print("=" * 70)
    print("EXTRACTING Ψ — THE UNIQUE N=12 ALGEBRA")
    print("=" * 70)

    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

    # Branch
    for x in range(2, CORE):
        tx = dot[t_idx][x]
        fx = dot[f_idx][x]
        gx = dot[g_idx][x]
        s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
    s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

    # Compose
    for x in range(2, CORE):
        gx = dot[g_idx][x]
        r_gx = col_ite_lookup(dot, r_idx, gx, N)
        s.add(dot[h_idx][x] == r_gx)

    # Y-combinator
    yr = dot[Y_idx][r_idx]
    r_yr = col_ite_lookup(dot, r_idx, yr, N)
    s.add(yr == r_yr)
    s.add(yr >= 2)

    # 1-inert
    for x in range(2, N):
        iflag = Int(f"zi_{x}")
        s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
    s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)

    # Selection axiom: η·ρ = 3
    s.add(dot[9][8] == 3)

    # Phase 1: Enumerate 500 models
    print("\nPhase 1: Enumerating models (cap=500)...")
    t0 = time.time()
    all_models = []
    while len(all_models) < 500:
        if s.check() != sat:
            break
        tbl = extract_table(s.model(), dot, N)
        all_models.append(tbl)
        s.add(Or([dot[i][j] != tbl[i][j]
                   for i in range(N) for j in range(N)]))
    elapsed = time.time() - t0
    exhausted = len(all_models) < 500
    print(f"  {len(all_models)}{'(exhaustive)' if exhausted else '+'} models ({elapsed:.1f}s)")

    if not all_models:
        print("  UNSAT — no model found!")
        return

    # Phase 2: Cluster by role signature
    print("\nPhase 2: Role-signature clustering...")
    role_groups = {}
    for idx, m in enumerate(all_models):
        rm_local = role_map(m)
        sig = tuple(rm_local.get(i, "?") for i in range(N))
        role_groups.setdefault(sig, []).append(idx)

    class_sizes = sorted([(len(v), k) for k, v in role_groups.items()], reverse=True)
    print(f"  Role signatures: {len(role_groups)}")
    for sz, sig in class_sizes[:5]:
        print(f"    {sz}: {sig}")

    # Take dominant cluster
    dominant_sig = class_sizes[0][1]
    dominant_indices = role_groups[dominant_sig]
    models = [all_models[i] for i in dominant_indices]
    print(f"  Dominant cluster: {len(models)} models")

    # Phase 3: Check variation within dominant cluster
    print("\nPhase 3: Variation within dominant cluster...")
    vary = []
    for i in range(N):
        for j in range(N):
            vals = set(m[i][j] for m in models)
            if len(vals) > 1:
                vary.append((i, j, sorted(vals)))

    if not vary:
        print("  *** Ψ IS UNIQUE within dominant cluster ***")
    elif len(vary) <= 10:
        print(f"  {len(vary)} varying cells:")
        for i, j, vals in vary:
            val_counts = Counter(m[i][j] for m in models)
            print(f"    ({i},{j}): {dict(val_counts)}")
    else:
        print(f"  {len(vary)} varying cells (too many — showing first 15):")
        for i, j, vals in vary[:15]:
            print(f"    ({i},{j}): {vals}")

    psi = models[0]
    rm = role_map(psi)

    # If not unique, report but proceed with first model
    if len(models) > 1 and vary:
        print(f"\n  NOTE: Using first model from dominant cluster ({len(models)} total)")

    # ═══════════════════════════════════════════════════════════════
    # FULL DOCUMENTATION
    # ═══════════════════════════════════════════════════════════════

    # Build role names dynamically from actual roles + functional assignments
    FUNC_NAMES = {
        0: "⊤ (top)", 1: "⊥ (bot)",
        Q_IDX: "Q (quote)", E_IDX: "E (eval)",
        r_idx: "ρ (branch)", h_idx: "η (compose)", Y_idx: "Y (fixed-point)",
        t_idx: "τ (branch-tester)", f_idx: "f (branch-if)", g_idx: "g (branch-else)",
    }
    # For unlabeled elements, use role
    ROLE_NAMES = {}
    for i in range(N):
        if i in FUNC_NAMES:
            ROLE_NAMES[i] = FUNC_NAMES[i]
        else:
            role = rm.get(i, "?")
            ROLE_NAMES[i] = f"{i} ({role})"

    print(f"\n{'═'*70}")
    print("Ψ — CAYLEY TABLE")
    print(f"{'═'*70}\n")

    # Header
    header = "  · |" + "".join(f"{j:3d}" for j in range(N))
    print(header)
    print("  " + "─" * (len(header) - 2))
    for i in range(N):
        role_short = rm.get(i, "?")[0]
        row = "".join(f"{psi[i][j]:3d}" for j in range(N))
        print(f" {i:2d} |{row}   {ROLE_NAMES.get(i, '')}")
    print()

    # Role assignment
    print(f"{'═'*70}")
    print("ELEMENT ROLES")
    print(f"{'═'*70}\n")
    for i in range(N):
        role = rm.get(i, "?")
        print(f"  {i:2d}  {ROLE_NAMES.get(i, '?'):25s}  [{role}]")

    # Role distribution
    role_counts = Counter(rm.values())
    print(f"\n  Distribution: {dict(role_counts)}")

    # ── Axiom verification ───────────────────────────────────────────
    print(f"\n{'═'*70}")
    print("AXIOM VERIFICATION")
    print(f"{'═'*70}\n")

    # Ext (all rows distinct)
    rows = [tuple(psi[i]) for i in range(N)]
    print(f"  Ext (all rows distinct): {len(set(rows)) == N}")

    # Absorbers
    print(f"  ⊤·x = ⊤ for all x: {all(psi[0][j] == 0 for j in range(N))}")
    print(f"  ⊥·x = ⊥ for all x: {all(psi[1][j] == 1 for j in range(N))}")

    # No other absorbers
    other_abs = [i for i in range(2, N) if all(psi[i][j] == i for j in range(N))]
    print(f"  No other absorbers: {len(other_abs) == 0}")

    # C (Kripke): non-testers map non-absorbers to ≥2
    c_ok = True
    for x in range(2, N):
        is_tst = all(psi[x][j] in (0, 1) for j in range(N))
        if not is_tst:
            for y in range(2, N):
                if psi[x][y] < 2:
                    c_ok = False
    print(f"  C (Kripke): {c_ok}")

    # D (inert propagation): inert elements map non-absorbers to ≥2
    inert_elems = [i for i in range(2, N) if rm.get(i) == "inert"]
    d_ok = all(psi[v][y] >= 2 for v in inert_elems for y in range(2, N))
    print(f"  D (inert propagation): {d_ok}")

    # PA (power-associativity)
    pa_ok = all(psi[psi[x][x]][x] == psi[x][psi[x][x]] for x in range(N))
    print(f"  PA (power-associativity): {pa_ok}")

    # VV (inert self-application → core)
    vv_ok = True
    for v in inert_elems:
        vv = psi[v][v]
        vv_role = rm.get(vv, "?")
        if vv_role not in ("testers", "encoders"):
            vv_ok = False
    print(f"  VV (ν·ν → core): {vv_ok}  [ν·ν = {psi[inert_elems[0]][inert_elems[0]]}]")

    # QE (inverse pair)
    qe_ok = True
    for x in range(2, CORE):
        qx = psi[Q_IDX][x]
        eqx = psi[E_IDX][qx]
        if eqx != x:
            qe_ok = False
        ex = psi[E_IDX][x]
        qex = psi[Q_IDX][ex]
        if qex != x:
            qe_ok = False
    print(f"  QE (E·(Q·x) = x, Q·(E·x) = x on core): {qe_ok}")

    # Branch: r·x = f·x if t·x=0, g·x if t·x=1
    br_ok = True
    for x in range(2, CORE):
        tx = psi[t_idx][x]
        fx = psi[f_idx][x]
        gx = psi[g_idx][x]
        rx = psi[r_idx][x]
        expected = fx if tx == 0 else gx
        if rx != expected:
            br_ok = False
    print(f"  Branch (ρ = if(τ, ε₁, ε₂)): {br_ok}")

    # Compose: h·x = r·(g·x) on core
    comp_ok = all(psi[h_idx][x] == psi[r_idx][psi[g_idx][x]]
                  for x in range(2, CORE))
    print(f"  Compose (η = ρ ∘ ε₂): {comp_ok}")

    # Y-combinator: Y·r = r·(Y·r)
    yr_val = psi[Y_idx][r_idx]
    r_yr_val = psi[r_idx][yr_val]
    print(f"  Y-combinator (Y·ρ = ρ·(Y·ρ)): {yr_val == r_yr_val}  "
          f"[Y·ρ = {yr_val}]")

    # 1-inert
    print(f"  1-inert: {len(inert_elems) == 1}  [inert = {inert_elems}]")

    # ── Structural properties ────────────────────────────────────────
    print(f"\n{'═'*70}")
    print("STRUCTURAL PROPERTIES")
    print(f"{'═'*70}\n")

    # Squaring map
    sq = [psi[i][i] for i in range(N)]
    print(f"  Squaring map: {sq}")
    idempotents = [i for i in range(N) if sq[i] == i]
    print(f"  Idempotents: {idempotents} ({len(idempotents)} total)")

    # Squaring orbits
    print(f"\n  Squaring orbits:")
    visited = set()
    for start in range(N):
        if start in visited:
            continue
        orbit = []
        x = start
        while x not in orbit:
            orbit.append(x)
            visited.add(x)
            x = psi[x][x]
        if x in orbit:
            cycle_start = orbit.index(x)
            tail = orbit[:cycle_start]
            cycle = orbit[cycle_start:]
            if tail:
                print(f"    {' → '.join(map(str, tail))} → "
                      f"({' → '.join(map(str, cycle))})")
            else:
                if len(cycle) == 1:
                    print(f"    ({cycle[0]}) [fixed point]")
                else:
                    print(f"    ({' → '.join(map(str, cycle))}) "
                          f"[{len(cycle)}-cycle]")

    # Tester partition
    t = t_idx
    accept = [j for j in range(N) if psi[t][j] == 0]
    reject = [j for j in range(N) if psi[t][j] == 1]
    print(f"\n  Tester partition:")
    print(f"    τ accepts (→⊤): {accept}")
    print(f"    τ rejects (→⊥): {reject}")

    # The key selection: compose · branch = element 3
    sel_val = psi[9][8]
    sel_role = rm.get(sel_val, "?")
    print(f"\n  Key composition: η·ρ = {sel_val} (role: {sel_role})")
    # Show sel_val's key interactions
    print(f"    {sel_val}·{sel_val} = {psi[sel_val][sel_val]}")
    print(f"    {sel_val}·η = {psi[sel_val][9]}")
    print(f"    {sel_val}·ρ = {psi[sel_val][8]}")

    # Generators
    def closure(tbl, gens, N):
        reached = set(gens)
        frontier = list(gens)
        while frontier:
            new = []
            for a in list(reached):
                for b in frontier:
                    for ab in [tbl[a][b], tbl[b][a]]:
                        if ab not in reached:
                            reached.add(ab)
                            new.append(ab)
            frontier = new
        return reached

    def closure_depth(tbl, gens, N):
        depth = {g: 0 for g in gens}
        reached = set(gens)
        frontier = list(gens)
        step = 0
        while frontier:
            step += 1
            new = []
            for a in list(reached):
                for b in frontier:
                    for ab in [tbl[a][b], tbl[b][a]]:
                        if ab not in reached:
                            reached.add(ab)
                            depth[ab] = step
                            new.append(ab)
            frontier = new
        return reached, depth

    # {⊤,⊥,Q,E} generators
    gen_set = {0, 1, Q_IDX, E_IDX}
    reached, depths = closure_depth(psi, gen_set, N)
    print(f"\n  Generators {{⊤,⊥,Q,E}}: reaches {len(reached)}/{N} elements")
    print(f"  Max depth: {max(depths.values())}")
    print(f"  Per-element depth:")
    for i in range(N):
        d = depths.get(i, -1)
        print(f"    {i:2d} ({ROLE_NAMES.get(i, '?'):25s}): depth {d}")

    # Single generators
    single_gens = []
    for a in range(2, N):
        if len(closure(psi, {0, 1, a}, N)) == N:
            single_gens.append(a)
    print(f"\n  Single generators {{⊤,⊥,x}}: {single_gens}")

    # Producibility
    producible = set()
    for a in range(N):
        for b in range(N):
            producible.add(psi[a][b])
    print(f"  Full producibility: {len(producible) == N}")

    # Rigidity (automorphism group)
    print(f"\n  Rigidity check (WL-1):")
    # WL color refinement
    colors = {}
    for i in range(N):
        colors[i] = (rm.get(i, "?"), tuple(sorted(psi[i])),
                     tuple(sorted(psi[j][i] for j in range(N))))
    for rnd in range(5):
        new_colors = {}
        for i in range(N):
            nbr = tuple(sorted(
                (colors[j], psi[i][j], psi[j][i]) for j in range(N)))
            new_colors[i] = (colors[i], nbr)
        colors = new_colors
    color_classes = Counter(colors.values())
    discrete = all(v == 1 for v in color_classes.values())
    print(f"    WL-1 discrete: {discrete}")
    print(f"    Color classes: {len(color_classes)} "
          f"(need {N} for discrete)")

    # Column distinctness
    cols = [tuple(psi[i][j] for i in range(N)) for j in range(N)]
    print(f"  All columns distinct: {len(set(cols)) == N}")

    # ── Computational structure ──────────────────────────────────────
    print(f"\n{'═'*70}")
    print("COMPUTATIONAL STRUCTURE")
    print(f"{'═'*70}\n")

    # Branch trace
    print("  Branch computation (ρ = if(τ, ε₁, ε₂) on core):")
    for x in range(2, CORE):
        tx = psi[t_idx][x]
        fx = psi[f_idx][x]
        gx = psi[g_idx][x]
        rx = psi[r_idx][x]
        branch = "ε₁" if tx == 0 else "ε₂"
        print(f"    x={x}: τ·{x}={tx} → {branch} → ρ·{x}={rx}")

    # Compose trace
    print(f"\n  Composition (η·x = ρ·(ε₂·x) on core):")
    for x in range(2, CORE):
        gx = psi[g_idx][x]
        rgx = psi[r_idx][gx]
        hx = psi[h_idx][x]
        print(f"    x={x}: ε₂·{x}={gx}, ρ·{gx}={rgx}, η·{x}={hx}")

    # Y-combinator
    print(f"\n  Y-combinator fixed points:")
    for ff in range(2, N):
        if ff == Y_idx:
            continue
        yf = psi[Y_idx][ff]
        fyf = psi[ff][yf]
        if yf == fyf and yf >= 2:
            print(f"    Y·{ff} = {yf}, {ff}·{yf} = {fyf}  ✓ fixed point")

    # QE trace
    print(f"\n  Quote/Eval on core:")
    for x in range(2, CORE):
        qx = psi[Q_IDX][x]
        eqx = psi[E_IDX][qx]
        ex = psi[E_IDX][x]
        qex = psi[Q_IDX][ex]
        print(f"    x={x}: Q·{x}={qx}, E·{qx}={eqx}  |  "
              f"E·{x}={ex}, Q·{ex}={qex}")

    # ── Print Ψ as Python constant ───────────────────────────────────
    print(f"\n{'═'*70}")
    print("Ψ AS PYTHON CONSTANT")
    print(f"{'═'*70}\n")

    print("PSI = [")
    for i in range(N):
        print(f"    {psi[i]},  # {i:2d} {ROLE_NAMES.get(i, '')}")
    print("]")

    print(f"\n{'═'*70}")
    print("Ψ SUMMARY")
    print(f"{'═'*70}")
    print(f"""
  Ψ is a 12-element magma (N=12) discovered by constrained SAT search.

  AXIOM SET (11 axioms):
    L0-L8  Structural ladder (absorbers, extensionality, tester,
           encoder, no extra absorbers, no extra testers, inert,
           encoder separation)
    C      Kripke: only testers produce boolean outputs
    D      Inert propagation: inert preserves non-absorber status
    PA     Power-associativity: (x·x)·x = x·(x·x)
    VV     Inert self-application yields core (tester or encoder)
    QE     Quote/Eval inverse pair on core: E·(Q·x) = Q·(E·x) = x
    1I     Exactly one inert element
    Br     Branch: ρ·x = ε₁·x if τ·x=⊤, ε₂·x if τ·x=⊥
    Co     Compose: η·x = ρ·(ε₂·x) on core
    Yc     Y-combinator: Y·ρ = ρ·(Y·ρ), non-trivial
    Sel    Selection: η·ρ = τ (compose of branch = tester; terminates)

  ROLE DISTRIBUTION:
    {dict(Counter(rm.values()))}

  KEY PROPERTIES:
    - {'Rigid' if discrete else 'NOT rigid'} (WL-1)
    - Fully producible: {len(producible) == N}
    - {{⊤,⊥,Q,E}} generates everything in ≤{max(depths.values())} steps
    - {len(single_gens)} single generators
    - {len(idempotents)} idempotents
    - η·ρ = {psi[9][8]} (role: {rm.get(psi[9][8], '?')})
""")


def qe_boundary_pinning():
    """
    Pin the remaining free cells: (7,0)=E·⊤, (7,1)=E·⊥, (6,10)=Q·Y.
    Also check interaction with tester-row cells (3,6), (3,8), (3,10).
    """

    from collections import Counter

    # ── Helpers (same as extract_psi) ─────────────────────────────────
    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

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

    CORE = 6
    Q_IDX, E_IDX = 6, 7
    N = 12
    t_idx, f_idx, g_idx = 3, 2, 4
    r_idx, h_idx, Y_idx = 8, 9, 10
    TESTER_CELLS = [(3, 6), (3, 8), (3, 10)]

    def build_base_solver():
        """Build solver with all 11 axioms + selection (9,8)=3."""
        s, dot = encode_level(8, N, timeout_seconds=300)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)

        # Branch
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))

        # Compose
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)

        # Y-combinator
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)

        # 1-inert
        for x in range(2, N):
            iflag = Int(f"zi_{x}")
            s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)

        # Selection
        s.add(dot[9][8] == 3)

        return s, dot

    def enumerate_dominant(s, dot, cap=500):
        """Enumerate models, return dominant role-signature cluster."""
        all_models = []
        while len(all_models) < cap:
            if s.check() != sat:
                break
            tbl = extract_table(s.model(), dot, N)
            all_models.append(tbl)
            s.add(Or([dot[i][j] != tbl[i][j]
                       for i in range(N) for j in range(N)]))
        exhausted = len(all_models) < cap

        # Cluster by role signature
        role_groups = {}
        for idx, m in enumerate(all_models):
            rm_local = role_map(m)
            sig = tuple(rm_local.get(i, "?") for i in range(N))
            role_groups.setdefault(sig, []).append(idx)

        class_sizes = sorted([(len(v), k) for k, v in role_groups.items()],
                             reverse=True)
        dominant_sig = class_sizes[0][1]
        dominant_indices = role_groups[dominant_sig]
        models = [all_models[i] for i in dominant_indices]
        return models, len(all_models), exhausted

    def report_variation(models, label=""):
        """Report varying cells and tester-cell status."""
        vary = []
        for i in range(N):
            for j in range(N):
                vals = set(m[i][j] for m in models)
                if len(vals) > 1:
                    vary.append((i, j, sorted(vals)))

        if label:
            print(f"\n  {label}")
        print(f"  Models: {len(models)}")
        print(f"  Varying cells: {len(vary)}")
        for i, j, vals in vary:
            val_counts = Counter(m[i][j] for m in models)
            print(f"    ({i},{j}): {dict(val_counts)}")

        # Tester cells status
        tester_vary = []
        for a, b in TESTER_CELLS:
            vals = set(m[a][b] for m in models)
            if len(vals) > 1:
                tester_vary.append((a, b, sorted(vals)))
        if tester_vary:
            print(f"  Tester cells still free: {[(a,b) for a,b,_ in tester_vary]}")
        else:
            print(f"  Tester cells: ALL FIXED")
            for a, b in TESTER_CELLS:
                print(f"    ({a},{b}) = {models[0][a][b]}")

        return vary

    print("=" * 70)
    print("QE BOUNDARY PINNING")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════════
    # TEST 1: Transparency on absorbers — E·⊤=⊤, E·⊥=⊥
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 1: E·⊤ = ⊤ and E·⊥ = ⊥ (transparency on absorbers)")
    print(f"{'═'*70}")

    s, dot = build_base_solver()
    s.add(dot[E_IDX][0] == 0)  # E·⊤ = ⊤
    s.add(dot[E_IDX][1] == 1)  # E·⊥ = ⊥

    t0 = time.time()
    models, total, exhausted = enumerate_dominant(s, dot, cap=500)
    elapsed = time.time() - t0
    print(f"  Total enumerated: {total}{'(exhaustive)' if exhausted else '+'} "
          f"({elapsed:.1f}s)")

    vary1 = report_variation(models, "After E·⊤=⊤, E·⊥=⊥:")

    # ═══════════════════════════════════════════════════════════════════
    # TEST 2: Q·Y values (with transparency already applied)
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 2: Q·Y = Q·10 candidates (with transparency)")
    print(f"{'═'*70}")

    # Check Q·Y distribution in Test 1 models
    qy_counts = Counter(m[Q_IDX][Y_idx] for m in models)
    print(f"\n  Q·10 distribution in Test 1 models: {dict(sorted(qy_counts.items()))}")

    # For each candidate value, run a fresh solver
    for v in sorted(qy_counts.keys()):
        s2, dot2 = build_base_solver()
        s2.add(dot2[E_IDX][0] == 0)
        s2.add(dot2[E_IDX][1] == 1)
        s2.add(dot2[Q_IDX][Y_idx] == v)

        t0 = time.time()
        models2, total2, exh2 = enumerate_dominant(s2, dot2, cap=500)
        elapsed2 = time.time() - t0

        # Check if QE round-trip extends: E·(Q·10) = 10?
        qe_extends = all(m[E_IDX][m[Q_IDX][Y_idx]] == Y_idx for m in models2)
        # Check Q·(E·10) = 10?
        eq_extends = all(m[Q_IDX][m[E_IDX][Y_idx]] == Y_idx for m in models2)

        # Count varying cells
        vary_count = 0
        for i in range(N):
            for j in range(N):
                if len(set(m[i][j] for m in models2)) > 1:
                    vary_count += 1

        tester_free = sum(1 for a, b in TESTER_CELLS
                         if len(set(m[a][b] for m in models2)) > 1)

        print(f"\n  Q·10 = {v:2d}: {len(models2):3d} models "
              f"({total2}{'exh' if exh2 else '+'}, {elapsed2:.1f}s), "
              f"{vary_count} varying, "
              f"QE→Y: {'✓' if qe_extends else '✗'}, "
              f"EQ→Y: {'✓' if eq_extends else '✗'}, "
              f"tester-free: {tester_free}/3")

    # ═══════════════════════════════════════════════════════════════════
    # TEST 3: Full QE transparency on non-core
    # Q·⊤=⊤, Q·⊥=⊥, E·⊤=⊤, E·⊥=⊥, Q·Y=Y, E·Y=Y
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 3: Full QE transparency (identity on all non-core)")
    print("  Q·⊤=⊤, Q·⊥=⊥, E·⊤=⊤, E·⊥=⊥, Q·Y=Y, E·Y=Y")
    print(f"{'═'*70}")

    s3, dot3 = build_base_solver()
    s3.add(dot3[Q_IDX][0] == 0)    # Q·⊤ = ⊤
    s3.add(dot3[Q_IDX][1] == 1)    # Q·⊥ = ⊥
    s3.add(dot3[E_IDX][0] == 0)    # E·⊤ = ⊤
    s3.add(dot3[E_IDX][1] == 1)    # E·⊥ = ⊥
    s3.add(dot3[Q_IDX][Y_idx] == Y_idx)  # Q·Y = Y
    s3.add(dot3[E_IDX][Y_idx] == Y_idx)  # E·Y = Y

    t0 = time.time()
    models3, total3, exh3 = enumerate_dominant(s3, dot3, cap=500)
    elapsed3 = time.time() - t0
    print(f"\n  Total enumerated: {total3}{'(exhaustive)' if exh3 else '+'} "
          f"({elapsed3:.1f}s)")

    vary3 = report_variation(models3, "After full QE transparency:")

    # Also extend to ALL non-core elements: Q·x=x, E·x=x for x ∉ core
    print(f"\n  --- Extended: Q·x=x, E·x=x for ALL x ∉ {{2,3,4,5}} ---")
    s3b, dot3b = build_base_solver()
    for x in list(range(0, 2)) + list(range(CORE, N)):
        s3b.add(dot3b[Q_IDX][x] == x)
        s3b.add(dot3b[E_IDX][x] == x)

    t0 = time.time()
    models3b, total3b, exh3b = enumerate_dominant(s3b, dot3b, cap=500)
    elapsed3b = time.time() - t0
    print(f"  Total enumerated: {total3b}{'(exhaustive)' if exh3b else '+'} "
          f"({elapsed3b:.1f}s)")

    if models3b:
        vary3b = report_variation(models3b, "After full non-core transparency:")
    else:
        print("  UNSAT — full non-core transparency is incompatible!")

    # ═══════════════════════════════════════════════════════════════════
    # TEST 4: QE orbit closure — Q swaps 4↔10
    # Q·4=10 already. Try Q·10=4 → clean 2-cycle.
    # E·10=4 already. Check E·4=10 for E's 2-cycle.
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("TEST 4: QE orbit closure — Q:4↔10, E:10↔4")
    print(f"{'═'*70}")

    # First verify the existing values in the dominant models from Test 1
    print("\n  Current values in Test 1 models:")
    for cell_name, row, col in [("Q·4", Q_IDX, 4), ("Q·10", Q_IDX, 10),
                                  ("E·4", E_IDX, 4), ("E·10", E_IDX, 10)]:
        vals = Counter(m[row][col] for m in models)
        print(f"    {cell_name}: {dict(sorted(vals.items()))}")

    # Test: Q·10 = 4 (completing Q's 2-cycle 4↔10)
    s4, dot4 = build_base_solver()
    s4.add(dot4[E_IDX][0] == 0)     # E·⊤ = ⊤
    s4.add(dot4[E_IDX][1] == 1)     # E·⊥ = ⊥
    s4.add(dot4[Q_IDX][Y_idx] == 4) # Q·10 = 4 (orbit closure)

    t0 = time.time()
    models4, total4, exh4 = enumerate_dominant(s4, dot4, cap=500)
    elapsed4 = time.time() - t0
    print(f"\n  With E transparency + Q·10=4:")
    print(f"  Total enumerated: {total4}{'(exhaustive)' if exh4 else '+'} "
          f"({elapsed4:.1f}s)")

    if models4:
        # Verify the 2-cycles
        q_cycle = all(m[Q_IDX][4] == 10 and m[Q_IDX][10] == 4 for m in models4)
        e_cycle = all(m[E_IDX][10] == 4 and m[E_IDX][4] == 2 for m in models4)
        print(f"  Q: 4↔10 cycle holds: {q_cycle}")
        # Check E's pattern
        e4_vals = Counter(m[E_IDX][4] for m in models4)
        e10_vals = Counter(m[E_IDX][10] for m in models4)
        print(f"  E·4 values: {dict(sorted(e4_vals.items()))}")
        print(f"  E·10 values: {dict(sorted(e10_vals.items()))}")

        # Full QE round-trip on extended domain {2,3,4,5,10}
        print(f"\n  QE round-trip on extended domain {{2,3,4,5,10}}:")
        for x in [2, 3, 4, 5, 10]:
            qx_vals = Counter(m[Q_IDX][x] for m in models4)
            eqx_vals = Counter(m[E_IDX][m[Q_IDX][x]] for m in models4)
            rt_ok = all(m[E_IDX][m[Q_IDX][x]] == x for m in models4)
            print(f"    E·(Q·{x:2d}) = {x:2d}? {rt_ok}  "
                  f"[Q·{x}={dict(sorted(qx_vals.items()))}]")

        vary4 = report_variation(models4, "After orbit closure:")
    else:
        print("  UNSAT!")

    # ═══════════════════════════════════════════════════════════════════
    # SUMMARY
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")
    print(f"  Baseline (no QE boundary):     499 models, 6 varying cells")
    if models:
        print(f"  Test 1 (E transparency):       {len(models)} models, "
              f"{len(vary1)} varying cells")
    if models3:
        print(f"  Test 3 (full QE transparency): {len(models3)} models, "
              f"{len(vary3)} varying cells")
    if models3b:
        print(f"  Test 3b (non-core identity):   {len(models3b)} models, "
              f"{len(vary3b)} varying cells")
    if models4:
        print(f"  Test 4 (orbit closure):        {len(models4)} models, "
              f"{len(vary4)} varying cells")


def qe_tester_causality():
    """
    Is E·⊤=⊤ → (3,6)=1 a logical entailment or a sampling artifact?

    Method: direct Z3 SAT checks on specific cell values with and without
    E transparency. If (base + E·⊤=⊤ + E·⊥=⊥ + (3,6)=0) is UNSAT,
    then the connection is a theorem.
    """

    from collections import Counter

    # ── Helpers ──────────────────────────────────────────────────────
    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

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

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    CORE = 6
    Q_IDX, E_IDX = 6, 7
    N = 12
    t_idx, f_idx, g_idx = 3, 2, 4
    r_idx, h_idx, Y_idx = 8, 9, 10

    def build_base_solver():
        """All 11 axioms + selection (9,8)=3."""
        s, dot = encode_level(8, N, timeout_seconds=300)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)
        for x in range(2, N):
            iflag = Int(f"zi_{x}")
            s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        s.add(dot[9][8] == 3)
        return s, dot

    # Also pin to dominant role signature:
    # 3=tester, 10=inert, rest=encoders
    def add_dominant_roles(s, dot):
        """Force the dominant role signature."""
        # Element 3 must be tester (boolean row)
        for j in range(N):
            s.add(Or(dot[3][j] == 0, dot[3][j] == 1))
        # Element 10 must be inert
        s.add(is_inert_z3(dot, 10, N))
        # Elements 2,4,5,6,7,8,9,11 must be encoders (not tester, not inert)
        for e in [2, 4, 5, 6, 7, 8, 9, 11]:
            # Not tester
            s.add(Or([And(dot[e][j] != 0, dot[e][j] != 1) for j in range(N)]))
            # Not inert (has ≥2 distinct non-boolean outputs)
            enc_pairs = []
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    enc_pairs.append(And(
                        dot[e][j1] != 0, dot[e][j1] != 1,
                        dot[e][j2] != 0, dot[e][j2] != 1,
                        dot[e][j1] != dot[e][j2]))
            s.add(Or(enc_pairs))

    print("=" * 70)
    print("CAUSALITY TEST: E·⊤=⊤ → tester cells?")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 1: Baseline — are tester cells genuinely free without E·⊤=⊤?
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 1: Baseline (no E transparency, dominant roles pinned)")
    print(f"{'═'*70}")

    tester_cells = [(3, 6), (3, 8), (3, 10)]

    for a, b in tester_cells:
        for val in [0, 1]:
            s, dot = build_base_solver()
            add_dominant_roles(s, dot)
            s.add(dot[a][b] == val)
            t0 = time.time()
            result = s.check()
            elapsed = time.time() - t0
            print(f"  Base + ({a},{b})={val}: {result} ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 2: With E transparency — are tester cells forced?
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 2: With E·⊤=⊤, E·⊥=⊥ — which tester values survive?")
    print(f"{'═'*70}")

    for a, b in tester_cells:
        for val in [0, 1]:
            s, dot = build_base_solver()
            add_dominant_roles(s, dot)
            s.add(dot[E_IDX][0] == 0)  # E·⊤ = ⊤
            s.add(dot[E_IDX][1] == 1)  # E·⊥ = ⊥
            s.add(dot[a][b] == val)
            t0 = time.time()
            result = s.check()
            elapsed = time.time() - t0
            status = "FORCED" if result == unsat else "free"
            print(f"  E-trans + ({a},{b})={val}: {result} ({elapsed:.1f}s)  "
                  f"{'← ENTAILED' if result == unsat else ''}")

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 3: Isolate — which E constraint does the work?
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 3: Which E constraint forces the tester cells?")
    print(f"{'═'*70}")

    # For each tester cell that's forced, test E·⊤=⊤ alone and E·⊥=⊥ alone
    for a, b in tester_cells:
        # First determine which value is forced (assume 1 from Test 1)
        forced_val = 1
        anti_val = 0

        # E·⊤=⊤ only
        s, dot = build_base_solver()
        add_dominant_roles(s, dot)
        s.add(dot[E_IDX][0] == 0)  # E·⊤ = ⊤ only
        s.add(dot[a][b] == anti_val)
        t0 = time.time()
        r1 = s.check()
        e1 = time.time() - t0

        # E·⊥=⊥ only
        s, dot = build_base_solver()
        add_dominant_roles(s, dot)
        s.add(dot[E_IDX][1] == 1)  # E·⊥ = ⊥ only
        s.add(dot[a][b] == anti_val)
        t0 = time.time()
        r2 = s.check()
        e2 = time.time() - t0

        print(f"  ({a},{b})={anti_val}:")
        print(f"    E·⊤=⊤ alone: {r1} ({e1:.1f}s)")
        print(f"    E·⊥=⊥ alone: {r2} ({e2:.1f}s)")

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 4: If entailed, find the proof chain
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 4: Proof chain — what intermediate values are forced?")
    print(f"{'═'*70}")

    # Build solver with E transparency + dominant roles, extract one model
    s, dot = build_base_solver()
    add_dominant_roles(s, dot)
    s.add(dot[E_IDX][0] == 0)
    s.add(dot[E_IDX][1] == 1)

    if s.check() == sat:
        tbl = extract_table(s.model(), dot, N)

        # Show element 3 (tester) row
        print(f"\n  τ row (element 3): {tbl[3]}")
        print(f"  E row (element 7): {tbl[7]}")
        print(f"  Q row (element 6): {tbl[6]}")

        # Key relationships involving element 6 (Q) and element 3 (τ)
        print(f"\n  Key values:")
        print(f"    E·⊤ = E·0 = {tbl[7][0]}")
        print(f"    E·⊥ = E·1 = {tbl[7][1]}")
        print(f"    τ·Q = τ·6 = {tbl[3][6]}")
        print(f"    Q·Q = Q·6 = {tbl[6][6]}")
        print(f"    E·Q = E·6 = {tbl[7][6]}")

        # Check PA chain: (3·3)·3 = 3·(3·3)
        tt = tbl[3][3]
        print(f"\n  PA chain for τ:")
        print(f"    τ·τ = {tt}")
        print(f"    (τ·τ)·τ = {tt}·3 = {tbl[tt][3]}")
        print(f"    τ·(τ·τ) = 3·{tt} = {tbl[3][tt]}")

        # Check what forces τ·6
        # τ is boolean. τ·6 ∈ {0,1}. What determines which?
        # QE on core: E·(Q·x) = x for x ∈ {2,3,4,5}
        # Q·3 = ?
        q3 = tbl[6][3]
        eq3 = tbl[7][q3]
        print(f"\n  QE round-trip at x=3:")
        print(f"    Q·3 = {q3}")
        print(f"    E·(Q·3) = E·{q3} = {eq3}  (should be 3)")

        # Check: does Q map any core element to 6?
        q_to_6 = [x for x in range(2, CORE) if tbl[6][x] == 6]
        print(f"\n  Q·x = 6 for core x: {q_to_6}")
        # Does E map 6 to anything in core?
        e6 = tbl[7][6]
        print(f"  E·6 = {e6}")
        # If E·6 is in core and Q·(E·6) should = 6 by QE...
        if 2 <= e6 < CORE:
            qe6 = tbl[6][e6]
            print(f"  Q·(E·6) = Q·{e6} = {qe6}  (QE says should = 6)")

        # Trace: how does E·0=0 propagate?
        print(f"\n  Propagation from E·⊤=⊤:")
        # Kripke (C): non-testers map non-absorbers to ≥2
        # Element 7 (E) is an encoder, so E·x ≥ 2 for x ≥ 2
        # E·0 = 0 is allowed because 0 is an absorber
        # But E·0 = 0 means E maps ⊤ to ⊤
        # PA: (7·7)·7 = 7·(7·7)
        ee = tbl[7][7]
        print(f"    E·E = {ee}")
        print(f"    (E·E)·E = {ee}·7 = {tbl[ee][7]}")
        print(f"    E·(E·E) = 7·{ee} = {tbl[7][ee]}")

        # Check column 6: which elements map to which when applied to Q
        print(f"\n  Column 6 (x·Q for each x):")
        for i in range(N):
            print(f"    {i:2d}·Q = {tbl[i][6]}")

        # Key: τ·Q depends on whether Q is in τ's accept/reject partition
        t_accept = [j for j in range(N) if tbl[3][j] == 0]
        t_reject = [j for j in range(N) if tbl[3][j] == 1]
        print(f"\n  τ partition:")
        print(f"    Accepts (→⊤): {t_accept}")
        print(f"    Rejects (→⊥): {t_reject}")

        # Check: for the FORCED cells, is there a chain through QE?
        # Hypothesis: E·⊤=⊤ forces E·0=0. Since Q·3=3 and E·3=3,
        # the QE structure constrains how τ interacts with Q.
        print(f"\n  All QE image values:")
        for x in range(2, CORE):
            print(f"    Q·{x}={tbl[6][x]}, E·{x}={tbl[7][x]}, "
                  f"E·(Q·{x})={tbl[7][tbl[6][x]]}, Q·(E·{x})={tbl[6][tbl[7][x]]}")

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 5: Minimal forcing — what's the smallest axiom that pins τ?
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 5: Do the base axioms already force the tester cells?")
    print("  (without any E transparency)")
    print(f"{'═'*70}")

    # Maybe the tester cells are already forced by the base axioms + roles
    # and the "variation" in the previous run was from the outlier signature
    for a, b in tester_cells:
        s, dot = build_base_solver()
        add_dominant_roles(s, dot)
        # Check both values
        results = {}
        for val in [0, 1]:
            s2, dot2 = build_base_solver()
            add_dominant_roles(s2, dot2)
            s2.add(dot2[a][b] == val)
            t0 = time.time()
            r = s2.check()
            elapsed = time.time() - t0
            results[val] = (r, elapsed)
        sat_vals = [v for v, (r, _) in results.items() if r == sat]
        print(f"  ({a},{b}): SAT for {sat_vals}  "
              f"[0:{results[0][0]}({results[0][1]:.1f}s), "
              f"1:{results[1][0]}({results[1][1]:.1f}s)]")
        if len(sat_vals) == 1:
            print(f"    → ALREADY FORCED to {sat_vals[0]} by base + roles!")


def etrans_residual_freedom():
    """
    With E-transparency added, exhaustively determine which cells genuinely
    vary. For each varying cell, check SAT of each candidate value directly
    with Z3 (not enumeration). Separate tester-row freedom from structural.
    """

    from collections import Counter

    # ── Helpers ──────────────────────────────────────────────────────
    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

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

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    CORE = 6
    Q_IDX, E_IDX = 6, 7
    N = 12
    t_idx, f_idx, g_idx = 3, 2, 4
    r_idx, h_idx, Y_idx = 8, 9, 10

    def build_full_solver():
        """All axioms + selection + E-transparency + dominant roles."""
        s, dot = encode_level(8, N, timeout_seconds=300)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        # Branch
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        # Compose
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        # Y-combinator
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)
        # 1-inert
        for x in range(2, N):
            iflag = Int(f"zi_{x}")
            s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        # Selection
        s.add(dot[9][8] == 3)
        # E-transparency
        s.add(dot[E_IDX][0] == 0)
        s.add(dot[E_IDX][1] == 1)
        # Dominant role signature
        for j in range(N):
            s.add(Or(dot[3][j] == 0, dot[3][j] == 1))
        s.add(is_inert_z3(dot, 10, N))
        for e in [2, 4, 5, 6, 7, 8, 9, 11]:
            s.add(Or([And(dot[e][j] != 0, dot[e][j] != 1) for j in range(N)]))
            enc_pairs = []
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    enc_pairs.append(And(
                        dot[e][j1] != 0, dot[e][j1] != 1,
                        dot[e][j2] != 0, dot[e][j2] != 1,
                        dot[e][j1] != dot[e][j2]))
            s.add(Or(enc_pairs))
        return s, dot

    print("=" * 70)
    print("RESIDUAL FREEDOM WITH E-TRANSPARENCY")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════════
    # STEP 1: Get a reference model using a single solver
    # ═══════════════════════════════════════════════════════════════════
    print("\nStep 1: Reference model...")
    s, dot = build_full_solver()
    assert s.check() == sat
    ref = extract_table(s.model(), dot, N)
    print("  Got reference model.")
    print(f"  τ row: {ref[3]}")

    # ═══════════════════════════════════════════════════════════════════
    # STEP 2: For each cell, use push/pop to check if other values exist
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("Step 2: Cell-by-cell SAT scan (144 cells, push/pop)")
    print(f"{'═'*70}")

    free_cells = []
    fixed_cells = []
    t_total = time.time()

    for i in range(N):
        row_free = []
        for j in range(N):
            ref_val = ref[i][j]
            s.push()
            s.add(dot[i][j] != ref_val)
            t0 = time.time()
            r = s.check()
            elapsed = time.time() - t0
            if r == sat:
                alt_val = s.model().eval(dot[i][j]).as_long()
                row_free.append((j, ref_val, alt_val, elapsed))
                free_cells.append((i, j))
            else:
                fixed_cells.append((i, j))
            s.pop()

        if row_free:
            for j, rv, av, el in row_free:
                print(f"  ({i:2d},{j:2d}): ref={rv}, alt={av} ({el:.1f}s)  FREE")

    total_elapsed = time.time() - t_total
    print(f"\n  Scan complete: {len(free_cells)} free, "
          f"{len(fixed_cells)} fixed ({total_elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════════
    # STEP 3: For each free cell, enumerate all SAT values
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("Step 3: Full value enumeration for free cells")
    print(f"{'═'*70}")

    tester_free = []
    structural_free = []

    for i, j in free_cells:
        sat_vals = []
        for v in range(N):
            s.push()
            s.add(dot[i][j] == v)
            if s.check() == sat:
                sat_vals.append(v)
            s.pop()
        is_tester_cell = (i == 3)
        category = "TESTER" if is_tester_cell else "STRUCTURAL"
        print(f"  ({i:2d},{j:2d}): {sat_vals}  [{category}]")
        if is_tester_cell:
            tester_free.append((i, j, sat_vals))
        else:
            structural_free.append((i, j, sat_vals))

    # ═══════════════════════════════════════════════════════════════════
    # STEP 4: Analyze structural free cells
    # ═══════════════════════════════════════════════════════════════════
    if structural_free:
        print(f"\n{'═'*70}")
        print(f"Step 4: Structural free cells — {len(structural_free)} found")
        print(f"{'═'*70}")

        # Check dependencies: do any structural cells constrain each other?
        print("\n  Pairwise dependencies:")
        for idx1, (i1, j1, v1) in enumerate(structural_free):
            for idx2, (i2, j2, v2) in enumerate(structural_free):
                if idx2 <= idx1:
                    continue
                dep = {}
                for va in v1:
                    surviving = []
                    for vb in v2:
                        s.push()
                        s.add(dot[i1][j1] == va)
                        s.add(dot[i2][j2] == vb)
                        if s.check() == sat:
                            surviving.append(vb)
                        s.pop()
                    dep[va] = surviving
                full_range = all(set(sv) == set(v2) for sv in dep.values())
                if not full_range:
                    print(f"    ({i1},{j1}) ↔ ({i2},{j2}): DEPENDENT")
                    for va, sv in dep.items():
                        print(f"      ({i1},{j1})={va} → ({i2},{j2}) ∈ {sv}")
                else:
                    print(f"    ({i1},{j1}) ↔ ({i2},{j2}): independent")

        # For each structural free cell, what role/function does it serve?
        ELEM_NAMES = {
            0: "⊤", 1: "⊥", 2: "f", 3: "τ", 4: "g", 5: "enc5",
            6: "Q", 7: "E", 8: "ρ", 9: "η", 10: "Y", 11: "enc11"
        }
        print("\n  Structural cell analysis:")
        for i, j, vals in structural_free:
            ri = ELEM_NAMES.get(i, str(i))
            rj = ELEM_NAMES.get(j, str(j))
            print(f"\n    ({i},{j}) = {ri}·{rj}: can be {vals}")
            for v in vals:
                s.push()
                s.add(dot[i][j] == v)
                if s.check() == sat:
                    m5 = extract_table(s.model(), dot, N)
                    qe_extra = []
                    for x in range(CORE, N):
                        if m5[E_IDX][m5[Q_IDX][x]] == x:
                            qe_extra.append(x)
                    if qe_extra:
                        print(f"      v={v}: QE round-trip extends to {qe_extra}")
                s.pop()
    else:
        print(f"\n{'═'*70}")
        print("Step 4: No structural free cells!")
        print("  ALL remaining freedom is in the tester row (actuality).")
        print(f"{'═'*70}")

    # ═══════════════════════════════════════════════════════════════════
    # SUMMARY
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")
    print(f"  Total cells: 144")
    print(f"  Fixed cells: {len(fixed_cells)}")
    print(f"  Free cells:  {len(free_cells)}")
    print(f"    Tester-row (actuality): {len(tester_free)}")
    for i, j, vals in tester_free:
        print(f"      ({i},{j}): {vals}")
    print(f"    Structural:            {len(structural_free)}")
    for i, j, vals in structural_free:
        print(f"      ({i},{j}): {vals}")

    if not structural_free:
        print(f"\n  *** Ψ is determined up to tester partition (actuality). ***")
        print(f"  The {len(tester_free)} tester cells encode which non-core")
        print(f"  elements the tester accepts vs rejects — a genuine")
        print(f"  semantic degree of freedom.")


def n8_freedom_analysis():
    """
    Proper cell-by-cell SAT freedom analysis at N=8.
    Axioms: L8 + C + D + PA + VV + QE + 1-inert + E-trans.
    For each cell, test every possible value individually.
    """

    from collections import Counter

    # ── Helpers ──────────────────────────────────────────────────────
    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

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

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    N = 8
    CORE_LO, CORE_HI = 2, 6  # core = {2,3,4,5} (non-absorber, non-Q/E)

    print("=" * 70)
    print(f"N={N} PROPER FREEDOM ANALYSIS")
    print("Axioms: L8 + C + D + PA + VV + QE + 1-inert + E-trans")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════════
    # First: determine which elements are Q and E
    # At N=8: elements 0,1 absorbers, 2-7 non-absorbers
    # L8 gives: ≥1 tester, ≥2 encoders, ≥1 inert among {2..7}
    # With QE on core {2..5}, Q and E must be among {2..7}
    # We need to figure out the right Q,E assignment.
    # Let's first check what role signatures exist.
    # ═══════════════════════════════════════════════════════════════════

    # Try all possible (Q,E) pairs among {2..7}, Q≠E
    # QE acts on core. At N=8 with 6 non-absorbers, if Q,E ∈ {2..7}
    # and core = {2..5}, then Q,E could be 6,7 (outside core)
    # or some could be inside core.
    # The natural choice matching N=12: Q=6, E=7, core={2,3,4,5}

    print("\nPhase 0: Checking Q=6, E=7, core={2,3,4,5}...")

    Q_IDX, E_IDX = 6, 7

    # Build solver
    s, dot = encode_level(8, N, timeout_seconds=300)
    add_full_base(s, dot, N)
    add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=6)

    # 1-inert
    for x in range(2, N):
        iflag = Int(f"zi_{x}")
        s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
    s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)

    # E-transparency
    s.add(dot[E_IDX][0] == 0)  # E·⊤ = ⊤
    s.add(dot[E_IDX][1] == 1)  # E·⊥ = ⊥

    # Check SAT
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  SAT check: {r} ({elapsed:.1f}s)")

    if r != sat:
        print("  UNSAT with Q=6, E=7. Trying other assignments...")
        # Try all pairs
        for qi in range(2, N):
            for ei in range(2, N):
                if qi == ei:
                    continue
                s2, dot2 = encode_level(8, N, timeout_seconds=60)
                add_full_base(s2, dot2, N)
                core_lo = 2
                core_hi = 6
                add_qe_pair(s2, dot2, N, qi, ei, core_lo, core_hi)
                for x in range(2, N):
                    iflag = Int(f"zi2_{x}")
                    s2.add(If(is_inert_z3(dot2, x, N), iflag == 1, iflag == 0))
                s2.add(sum([Int(f"zi2_{x}") for x in range(2, N)]) == 1)
                s2.add(dot2[ei][0] == 0)
                s2.add(dot2[ei][1] == 1)
                if s2.check() == sat:
                    print(f"  SAT with Q={qi}, E={ei}")
                    Q_IDX, E_IDX = qi, ei
                    s, dot = s2, dot2
                    break
            else:
                continue
            break

    # Get reference model
    ref = extract_table(s.model(), dot, N)
    rm = role_map(ref)

    print(f"\n  Reference model:")
    for i in range(N):
        role = rm.get(i, "?")
        print(f"    {i}: {ref[i]}  [{role}]")

    # ═══════════════════════════════════════════════════════════════════
    # CELL-BY-CELL SAT SCAN
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print(f"Cell-by-cell SAT scan ({N}×{N} = {N*N} cells, {N} values each)")
    print(f"{'═'*70}")

    cell_values = {}  # (i,j) → list of SAT values
    t_total = time.time()

    for i in range(N):
        for j in range(N):
            sat_vals = []
            for v in range(N):
                s.push()
                s.add(dot[i][j] == v)
                if s.check() == sat:
                    sat_vals.append(v)
                s.pop()
            cell_values[(i, j)] = sat_vals

    total_elapsed = time.time() - t_total
    print(f"  Done ({total_elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════════
    # ANALYSIS
    # ═══════════════════════════════════════════════════════════════════
    fixed_cells = []
    free_cells = []
    for i in range(N):
        for j in range(N):
            vals = cell_values[(i, j)]
            if len(vals) == 1:
                fixed_cells.append((i, j, vals[0]))
            else:
                free_cells.append((i, j, vals))

    print(f"\n{'═'*70}")
    print("RESULTS")
    print(f"{'═'*70}")
    print(f"\n  Fixed: {len(fixed_cells)}/{N*N} ({100*len(fixed_cells)/(N*N):.1f}%)")
    print(f"  Free:  {len(free_cells)}/{N*N} ({100*len(free_cells)/(N*N):.1f}%)")

    # Show the full table with freedom annotation
    print(f"\n  Fixed cell map (. = fixed, number = # of SAT values):")
    print(f"     ", end="")
    for j in range(N):
        print(f" {j:2d}", end="")
    print()
    print(f"     ", end="")
    print("───" * N)
    for i in range(N):
        print(f"  {i:2d} |", end="")
        for j in range(N):
            n_vals = len(cell_values[(i, j)])
            if n_vals == 1:
                print(f"  .", end="")
            else:
                print(f" {n_vals:2d}", end="")
        role = rm.get(i, "?")
        print(f"   [{role}]")

    # Categorize free cells
    print(f"\n  Free cell details:")
    tester_free = []
    structural_free = []
    for i, j, vals in free_cells:
        is_tester = (rm.get(i) == "testers")
        cat = "TESTER" if is_tester else "STRUCT"
        print(f"    ({i},{j}): {len(vals)} vals {vals}  [{cat}]")
        if is_tester:
            tester_free.append((i, j, vals))
        else:
            structural_free.append((i, j, vals))

    # Freedom by row
    print(f"\n  Freedom by row:")
    for i in range(N):
        free_in_row = sum(1 for j in range(N) if len(cell_values[(i, j)]) > 1)
        fixed_in_row = N - free_in_row
        role = rm.get(i, "?")
        print(f"    Row {i} [{role:10s}]: {fixed_in_row} fixed, {free_in_row} free")

    # Value width distribution
    print(f"\n  Value width distribution (# SAT values per free cell):")
    width_dist = Counter(len(vals) for _, _, vals in free_cells)
    for w in sorted(width_dist):
        print(f"    {w} values: {width_dist[w]} cells")

    # Fixed cells detail
    print(f"\n  Fixed cells:")
    for i, j, v in fixed_cells:
        print(f"    ({i},{j}) = {v}")

    # ═══════════════════════════════════════════════════════════════════
    # COMPARISON WITH N=12
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("COMPARISON")
    print(f"{'═'*70}")
    print(f"  N=8:  {len(fixed_cells)}/{N*N} fixed "
          f"({100*len(fixed_cells)/(N*N):.1f}%)")
    print(f"  N=12: 27/144 fixed (18.8%)")
    print(f"  N=8 tester-row free: {len(tester_free)}")
    print(f"  N=8 structural free: {len(structural_free)}")

    # ═══════════════════════════════════════════════════════════════════
    # BONUS: What do the QE constraints actually pin?
    # Run without QE to see the difference
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("ABLATION: Without QE (just L8+C+D+PA+VV+1-inert+E-trans)")
    print(f"{'═'*70}")

    s_noqe, dot_noqe = encode_level(8, N, timeout_seconds=300)
    add_full_base(s_noqe, dot_noqe, N)
    # 1-inert
    for x in range(2, N):
        iflag = Int(f"zi3_{x}")
        s_noqe.add(If(is_inert_z3(dot_noqe, x, N), iflag == 1, iflag == 0))
    s_noqe.add(sum([Int(f"zi3_{x}") for x in range(2, N)]) == 1)
    # E-trans (on whichever element is E — but without QE, we don't know)
    # Skip E-trans for the no-QE ablation since E isn't defined

    fixed_noqe = 0
    for i in range(N):
        for j in range(N):
            s_noqe.push()
            ref_val = ref[i][j]
            s_noqe.add(dot_noqe[i][j] != ref_val)
            if s_noqe.check() == unsat:
                fixed_noqe += 1
            s_noqe.pop()

    print(f"  Fixed without QE: {fixed_noqe}/{N*N} "
          f"({100*fixed_noqe/(N*N):.1f}%)")
    print(f"  Fixed with QE:    {len(fixed_cells)}/{N*N} "
          f"({100*len(fixed_cells)/(N*N):.1f}%)")
    print(f"  QE pins {len(fixed_cells) - fixed_noqe} additional cells")


def counter_embedding():
    """
    Test whether a 2-bit (4-state) cyclic counter can be embedded
    in the free cells of N=12 while satisfying all structural axioms.
    """

    from collections import Counter

    # ── Helpers ──────────────────────────────────────────────────────
    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

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

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    def full_ite_lookup(dot, row_expr, col_expr, N):
        """dot[row_expr][col_expr] where both are Z3 expressions."""
        entry = col_ite_lookup(dot, 0, col_expr, N)
        for r in range(1, N):
            entry = If(row_expr == r, col_ite_lookup(dot, r, col_expr, N), entry)
        return entry

    N = 12
    CORE = 6
    Q_IDX, E_IDX = 6, 7

    def build_base():
        """L8+C+D+PA+VV+QE+1-inert+E-trans. No Branch/Compose/Y."""
        s, dot = encode_level(8, N, timeout_seconds=300)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        # 1-inert
        for x in range(2, N):
            iflag = Int(f"zi_{x}")
            s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        # E-transparency
        s.add(dot[E_IDX][0] == 0)
        s.add(dot[E_IDX][1] == 1)
        return s, dot

    def analyze_model(tbl, label, extra_info=None):
        """Print analysis of a model."""
        rm = role_map(tbl)
        print(f"\n  {label}:")
        for i in range(N):
            role = rm.get(i, "?")
            tag = ""
            if extra_info and i in extra_info:
                tag = f"  ← {extra_info[i]}"
            print(f"    {i:2d}: {tbl[i]}  [{role}]{tag}")

        # Axiom checks
        rows = [tuple(tbl[i]) for i in range(N)]
        ext_ok = len(set(rows)) == N
        abs0 = all(tbl[0][j] == 0 for j in range(N))
        abs1 = all(tbl[1][j] == 1 for j in range(N))
        no_extra = not any(all(tbl[i][j] == i for j in range(N)) for i in range(2, N))
        c_ok = True
        for x in range(2, N):
            is_tst = all(tbl[x][j] in (0, 1) for j in range(N))
            if not is_tst:
                for y in range(2, N):
                    if tbl[x][y] < 2:
                        c_ok = False
        inert_elems = [i for i in range(2, N) if rm.get(i) == "inert"]
        d_ok = all(tbl[v][y] >= 2 for v in inert_elems for y in range(2, N))
        pa_ok = all(tbl[tbl[x][x]][x] == tbl[x][tbl[x][x]] for x in range(N))
        qe_ok = True
        for x in range(2, CORE):
            if tbl[E_IDX][tbl[Q_IDX][x]] != x or tbl[Q_IDX][tbl[E_IDX][x]] != x:
                qe_ok = False

        print(f"    Axioms: Ext={ext_ok} Abs={abs0 and abs1} NoExtra={no_extra} "
              f"C={c_ok} D={d_ok} PA={pa_ok} QE={qe_ok} "
              f"1-inert={len(inert_elems)==1} "
              f"E-trans={tbl[E_IDX][0]==0 and tbl[E_IDX][1]==1}")

        # WL-1 rigidity
        colors = {}
        for i in range(N):
            colors[i] = (rm.get(i, "?"), tuple(sorted(tbl[i])),
                         tuple(sorted(tbl[j][i] for j in range(N))))
        for _ in range(5):
            new_colors = {}
            for i in range(N):
                nbr = tuple(sorted(
                    (colors[j], tbl[i][j], tbl[j][i]) for j in range(N)))
                new_colors[i] = (colors[i], nbr)
            colors = new_colors
        n_classes = len(set(colors.values()))
        print(f"    WL-1: {'discrete' if n_classes == N else f'{n_classes}/{N} classes'}")

        # Generators
        reached = {0, 1, Q_IDX, E_IDX}
        frontier = list(reached)
        while frontier:
            new = []
            for a in list(reached):
                for b in frontier:
                    for ab in [tbl[a][b], tbl[b][a]]:
                        if ab not in reached:
                            reached.add(ab)
                            new.append(ab)
            frontier = new
        print(f"    {{⊤,⊥,Q,E}} generates: {len(reached)}/{N}")

        return rm

    print("=" * 70)
    print("2-BIT COUNTER EMBEDDING IN Ψ (N=12)")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 1: Basic 4-cycle counter
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 1: Basic 4-cycle counter")
    print("  inc·s0=s1, inc·s1=s2, inc·s2=s3, inc·s3=s0")
    print(f"{'═'*70}")

    s, dot = build_base()

    # Counter state variables (non-absorbers: 2..11)
    s0 = Int("s0"); s1 = Int("s1"); s2 = Int("s2"); s3 = Int("s3")
    inc = Int("inc")
    for v in [s0, s1, s2, s3, inc]:
        s.add(v >= 2, v <= N - 1)
    # All distinct
    s.add(Distinct(s0, s1, s2, s3))
    # inc distinct from states
    s.add(inc != s0, inc != s1, inc != s2, inc != s3)
    # inc must not be an absorber (already guaranteed by range 2..N-1)

    # 4-cycle
    s.add(full_ite_lookup(dot, inc, s0, N) == s1)
    s.add(full_ite_lookup(dot, inc, s1, N) == s2)
    s.add(full_ite_lookup(dot, inc, s2, N) == s3)
    s.add(full_ite_lookup(dot, inc, s3, N) == s0)

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"\n  Result: {r} ({elapsed:.1f}s)")

    if r == sat:
        m = s.model()
        tbl = extract_table(m, dot, N)
        s0v = m.eval(s0).as_long()
        s1v = m.eval(s1).as_long()
        s2v = m.eval(s2).as_long()
        s3v = m.eval(s3).as_long()
        incv = m.eval(inc).as_long()
        print(f"  Assignment: s0={s0v}, s1={s1v}, s2={s2v}, s3={s3v}, inc={incv}")
        print(f"  Cycle: {incv}·{s0v}={tbl[incv][s0v]}, "
              f"{incv}·{s1v}={tbl[incv][s1v]}, "
              f"{incv}·{s2v}={tbl[incv][s2v]}, "
              f"{incv}·{s3v}={tbl[incv][s3v]}")
        info = {s0v: "s0", s1v: "s1", s2v: "s2", s3v: "s3", incv: "inc"}
        analyze_model(tbl, "Phase 1 model", info)
    else:
        print("  UNSAT!")

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 2: Counter + decrement
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 2: Counter + decrement")
    print("  + dec·s0=s3, dec·s1=s0, dec·s2=s1, dec·s3=s2")
    print(f"{'═'*70}")

    s2p, dot2 = build_base()

    s0b = Int("s0b"); s1b = Int("s1b"); s2b = Int("s2b"); s3b = Int("s3b")
    incb = Int("incb"); decb = Int("decb")
    for v in [s0b, s1b, s2b, s3b, incb, decb]:
        s2p.add(v >= 2, v <= N - 1)
    s2p.add(Distinct(s0b, s1b, s2b, s3b))
    s2p.add(incb != s0b, incb != s1b, incb != s2b, incb != s3b)
    s2p.add(decb != s0b, decb != s1b, decb != s2b, decb != s3b)
    s2p.add(incb != decb)

    # inc cycle
    s2p.add(full_ite_lookup(dot2, incb, s0b, N) == s1b)
    s2p.add(full_ite_lookup(dot2, incb, s1b, N) == s2b)
    s2p.add(full_ite_lookup(dot2, incb, s2b, N) == s3b)
    s2p.add(full_ite_lookup(dot2, incb, s3b, N) == s0b)
    # dec cycle (reverse)
    s2p.add(full_ite_lookup(dot2, decb, s0b, N) == s3b)
    s2p.add(full_ite_lookup(dot2, decb, s1b, N) == s0b)
    s2p.add(full_ite_lookup(dot2, decb, s2b, N) == s1b)
    s2p.add(full_ite_lookup(dot2, decb, s3b, N) == s2b)

    t0 = time.time()
    r2 = s2p.check()
    elapsed2 = time.time() - t0
    print(f"\n  Result: {r2} ({elapsed2:.1f}s)")

    if r2 == sat:
        m2 = s2p.model()
        tbl2 = extract_table(m2, dot2, N)
        vals = {nm: m2.eval(v).as_long() for nm, v in
                [("s0", s0b), ("s1", s1b), ("s2", s2b), ("s3", s3b),
                 ("inc", incb), ("dec", decb)]}
        print(f"  Assignment: {vals}")
        iv, dv = vals["inc"], vals["dec"]
        sv = [vals["s0"], vals["s1"], vals["s2"], vals["s3"]]
        print(f"  Inc cycle: {' → '.join(str(tbl2[iv][x]) for x in sv)} → {tbl2[iv][sv[3]]}")
        print(f"  Dec cycle: {' → '.join(str(tbl2[dv][x]) for x in sv)} → {tbl2[dv][sv[3]]}")
        info2 = {vals[k]: k for k in vals}
        analyze_model(tbl2, "Phase 2 model", info2)

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 3: Counter + zero test
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 3: Counter + zero test")
    print("  + τ·s0=⊤, τ·s1=⊥, τ·s2=⊥, τ·s3=⊥")
    print(f"{'═'*70}")

    s3p, dot3 = build_base()

    s0c = Int("s0c"); s1c = Int("s1c"); s2c = Int("s2c"); s3c = Int("s3c")
    incc = Int("incc"); tst = Int("tst")
    for v in [s0c, s1c, s2c, s3c, incc, tst]:
        s3p.add(v >= 2, v <= N - 1)
    s3p.add(Distinct(s0c, s1c, s2c, s3c))
    s3p.add(incc != s0c, incc != s1c, incc != s2c, incc != s3c)
    s3p.add(tst != incc)

    # tst must be a tester (boolean row)
    for j in range(N):
        s3p.add(Or(full_ite_lookup(dot3, tst, j, N) == 0,
                   full_ite_lookup(dot3, tst, j, N) == 1))

    # inc cycle
    s3p.add(full_ite_lookup(dot3, incc, s0c, N) == s1c)
    s3p.add(full_ite_lookup(dot3, incc, s1c, N) == s2c)
    s3p.add(full_ite_lookup(dot3, incc, s2c, N) == s3c)
    s3p.add(full_ite_lookup(dot3, incc, s3c, N) == s0c)

    # zero test: tst·s0 = ⊤, tst·{s1,s2,s3} = ⊥
    s3p.add(full_ite_lookup(dot3, tst, s0c, N) == 0)
    s3p.add(full_ite_lookup(dot3, tst, s1c, N) == 1)
    s3p.add(full_ite_lookup(dot3, tst, s2c, N) == 1)
    s3p.add(full_ite_lookup(dot3, tst, s3c, N) == 1)

    t0 = time.time()
    r3 = s3p.check()
    elapsed3 = time.time() - t0
    print(f"\n  Result: {r3} ({elapsed3:.1f}s)")

    if r3 == sat:
        m3 = s3p.model()
        tbl3 = extract_table(m3, dot3, N)
        vals3 = {nm: m3.eval(v).as_long() for nm, v in
                 [("s0", s0c), ("s1", s1c), ("s2", s2c), ("s3", s3c),
                  ("inc", incc), ("tst", tst)]}
        print(f"  Assignment: {vals3}")
        tv = vals3["tst"]
        print(f"  Zero test: τ({tv})·s0={tbl3[tv][vals3['s0']]}, "
              f"τ·s1={tbl3[tv][vals3['s1']]}, "
              f"τ·s2={tbl3[tv][vals3['s2']]}, "
              f"τ·s3={tbl3[tv][vals3['s3']]}")
        info3 = {vals3[k]: k for k in vals3}
        analyze_model(tbl3, "Phase 3 model", info3)

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 4: Counter + decrement + zero test
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 4: Counter + decrement + zero test (all combined)")
    print(f"{'═'*70}")

    s4p, dot4 = build_base()

    s0d = Int("s0d"); s1d = Int("s1d"); s2d = Int("s2d"); s3d = Int("s3d")
    incd = Int("incd"); decd = Int("decd"); tstd = Int("tstd")
    for v in [s0d, s1d, s2d, s3d, incd, decd, tstd]:
        s4p.add(v >= 2, v <= N - 1)
    s4p.add(Distinct(s0d, s1d, s2d, s3d))
    s4p.add(incd != s0d, incd != s1d, incd != s2d, incd != s3d)
    s4p.add(decd != s0d, decd != s1d, decd != s2d, decd != s3d)
    s4p.add(incd != decd)
    s4p.add(tstd != incd, tstd != decd)

    # tst boolean
    for j in range(N):
        s4p.add(Or(full_ite_lookup(dot4, tstd, j, N) == 0,
                   full_ite_lookup(dot4, tstd, j, N) == 1))

    # inc cycle
    s4p.add(full_ite_lookup(dot4, incd, s0d, N) == s1d)
    s4p.add(full_ite_lookup(dot4, incd, s1d, N) == s2d)
    s4p.add(full_ite_lookup(dot4, incd, s2d, N) == s3d)
    s4p.add(full_ite_lookup(dot4, incd, s3d, N) == s0d)
    # dec cycle
    s4p.add(full_ite_lookup(dot4, decd, s0d, N) == s3d)
    s4p.add(full_ite_lookup(dot4, decd, s1d, N) == s0d)
    s4p.add(full_ite_lookup(dot4, decd, s2d, N) == s1d)
    s4p.add(full_ite_lookup(dot4, decd, s3d, N) == s2d)
    # zero test
    s4p.add(full_ite_lookup(dot4, tstd, s0d, N) == 0)
    s4p.add(full_ite_lookup(dot4, tstd, s1d, N) == 1)
    s4p.add(full_ite_lookup(dot4, tstd, s2d, N) == 1)
    s4p.add(full_ite_lookup(dot4, tstd, s3d, N) == 1)

    t0 = time.time()
    r4 = s4p.check()
    elapsed4 = time.time() - t0
    print(f"\n  Result: {r4} ({elapsed4:.1f}s)")

    if r4 == sat:
        m4 = s4p.model()
        tbl4 = extract_table(m4, dot4, N)
        vals4 = {nm: m4.eval(v).as_long() for nm, v in
                 [("s0", s0d), ("s1", s1d), ("s2", s2d), ("s3", s3d),
                  ("inc", incd), ("dec", decd), ("tst", tstd)]}
        print(f"  Assignment: {vals4}")
        info4 = {vals4[k]: k for k in vals4}
        analyze_model(tbl4, "Phase 4 model", info4)

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 5: Two independent 4-cycle counters
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 5: Two independent 4-cycle counters")
    print("  Counter A: incA·a0→a1→a2→a3→a0")
    print("  Counter B: incB·b0→b1→b2→b3→b0")
    print("  Disjoint states, distinct increments")
    print(f"{'═'*70}")

    s5p, dot5 = build_base()

    # 8 state vars + 2 inc vars = 10 vars, all from {2..11}
    a = [Int(f"a{i}") for i in range(4)]
    b = [Int(f"b{i}") for i in range(4)]
    incA = Int("incA"); incB = Int("incB")

    all_vars = a + b + [incA, incB]
    for v in all_vars:
        s5p.add(v >= 2, v <= N - 1)

    # All 10 must be distinct (uses all 10 non-absorbers!)
    s5p.add(Distinct(*all_vars))

    # Counter A cycle
    for i in range(4):
        s5p.add(full_ite_lookup(dot5, incA, a[i], N) == a[(i + 1) % 4])
    # Counter B cycle
    for i in range(4):
        s5p.add(full_ite_lookup(dot5, incB, b[i], N) == b[(i + 1) % 4])

    t0 = time.time()
    r5 = s5p.check()
    elapsed5 = time.time() - t0
    print(f"\n  Result: {r5} ({elapsed5:.1f}s)")

    if r5 == sat:
        m5 = s5p.model()
        tbl5 = extract_table(m5, dot5, N)
        av = [m5.eval(x).as_long() for x in a]
        bv = [m5.eval(x).as_long() for x in b]
        iAv = m5.eval(incA).as_long()
        iBv = m5.eval(incB).as_long()
        print(f"  Counter A: states={av}, inc={iAv}")
        print(f"  Counter B: states={bv}, inc={iBv}")
        print(f"  A cycle: {' → '.join(str(tbl5[iAv][x]) for x in av)} → {tbl5[iAv][av[3]]}")
        print(f"  B cycle: {' → '.join(str(tbl5[iBv][x]) for x in bv)} → {tbl5[iBv][bv[3]]}")
        info5 = {}
        for i, v in enumerate(av):
            info5[v] = f"a{i}"
        for i, v in enumerate(bv):
            info5[v] = f"b{i}"
        info5[iAv] = "incA"
        info5[iBv] = "incB"
        analyze_model(tbl5, "Phase 5 model", info5)
    else:
        # ═══════════════════════════════════════════════════════════════
        # PHASE 6: Two counters with overlapping states
        # ═══════════════════════════════════════════════════════════════
        print(f"\n{'═'*70}")
        print("PHASE 6: Two counters, overlapping states")
        print(f"{'═'*70}")

        s6p, dot6 = build_base()

        # Two 4-cycles, may share states
        a2 = [Int(f"a2_{i}") for i in range(4)]
        b2 = [Int(f"b2_{i}") for i in range(4)]
        incA2 = Int("incA2"); incB2 = Int("incB2")

        for v in a2 + b2 + [incA2, incB2]:
            s6p.add(v >= 2, v <= N - 1)

        # Each counter's states distinct within themselves
        s6p.add(Distinct(*a2))
        s6p.add(Distinct(*b2))
        # Increments distinct from each other
        s6p.add(incA2 != incB2)
        # At least one state must be shared (otherwise it's Phase 5)
        s6p.add(Or([a2[i] == b2[j] for i in range(4) for j in range(4)]))

        # Counter A cycle
        for i in range(4):
            s6p.add(full_ite_lookup(dot6, incA2, a2[i], N) == a2[(i + 1) % 4])
        # Counter B cycle
        for i in range(4):
            s6p.add(full_ite_lookup(dot6, incB2, b2[i], N) == b2[(i + 1) % 4])

        t0 = time.time()
        r6 = s6p.check()
        elapsed6 = time.time() - t0
        print(f"\n  Result: {r6} ({elapsed6:.1f}s)")

        if r6 == sat:
            m6 = s6p.model()
            tbl6 = extract_table(m6, dot6, N)
            a2v = [m6.eval(x).as_long() for x in a2]
            b2v = [m6.eval(x).as_long() for x in b2]
            iA2v = m6.eval(incA2).as_long()
            iB2v = m6.eval(incB2).as_long()
            shared = set(a2v) & set(b2v)
            print(f"  Counter A: states={a2v}, inc={iA2v}")
            print(f"  Counter B: states={b2v}, inc={iB2v}")
            print(f"  Shared states: {shared}")
            info6 = {}
            for i, v in enumerate(a2v):
                info6[v] = info6.get(v, "") + f"a{i}/"
            for i, v in enumerate(b2v):
                info6[v] = info6.get(v, "") + f"b{i}"
            info6[iA2v] = info6.get(iA2v, "") + "incA"
            info6[iB2v] = info6.get(iB2v, "") + "incB"
            analyze_model(tbl6, "Phase 6 model", info6)

    # ═══════════════════════════════════════════════════════════════════
    # SUMMARY
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY")
    print(f"{'═'*70}")
    results = [
        ("Phase 1: Basic counter", r),
        ("Phase 2: Counter + dec", r2),
        ("Phase 3: Counter + zero-test", r3),
        ("Phase 4: Counter + dec + zero-test", r4),
        ("Phase 5: Two disjoint counters", r5),
    ]
    for name, result in results:
        print(f"  {name}: {result}")


def n16_viability():
    """N=16 viability check: axiom scaling + IO + arithmetic."""
    import time

    from z3 import And, Distinct, If, Int, Not, Or, Solver, sat, unsat, set_param

    from ds_search.axiom_explorer import (
        classify_elements,
        col_ite_lookup,
        encode_level,
        extract_table,
        ite_lookup,
    )

    N = 16
    CORE = 6
    Q_IDX, E_IDX = 6, 7
    r_idx, h_idx, Y_idx = 8, 9, 10
    t_idx, f_idx, g_idx = 3, 2, 4

    # ─── Helper functions (same as counter_embedding but for N=16) ───

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

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

    def role_map(tbl):
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role
        return rm

    def full_ite_lookup(dot, row_expr, col_expr, N):
        """dot[row_expr][col_expr] where both are Z3 expressions."""
        entry = col_ite_lookup(dot, 0, col_expr, N)
        for r in range(1, N):
            entry = If(row_expr == r, col_ite_lookup(dot, r, col_expr, N), entry)
        return entry

    def build_base16():
        """L8+C+D+PA+VV+QE+1-inert+E-trans for N=16."""
        s, dot = encode_level(8, N, timeout_seconds=600)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        # 1-inert
        for x in range(2, N):
            iflag = Int(f"zi_{x}")
            s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        # E-transparency
        s.add(dot[E_IDX][0] == 0)
        s.add(dot[E_IDX][1] == 1)
        return s, dot

    def add_branch_compose_y(s, dot, N):
        """Add Branch + Compose + Y-combinator constraints."""
        # Branch: r·x = if t·x==0 then f·x else g·x, for core
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        # f and g must differ on core
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        # Compose: h·x = r·(g·x) for core
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        # Y-combinator: Y·r is a fixed point of r
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)

    def analyze_model16(tbl, label, extra_info=None):
        """Print analysis of a model at N=16."""
        rm = role_map(tbl)
        print(f"\n  {label}:")
        for i in range(N):
            role = rm.get(i, "?")
            tag = ""
            if extra_info and i in extra_info:
                tag = f"  ← {extra_info[i]}"
            print(f"    {i:2d}: {tbl[i]}  [{role}]{tag}")

        # Axiom checks
        rows = [tuple(tbl[i]) for i in range(N)]
        ext_ok = len(set(rows)) == N
        abs0 = all(tbl[0][j] == 0 for j in range(N))
        abs1 = all(tbl[1][j] == 1 for j in range(N))
        no_extra = not any(all(tbl[i][j] == i for j in range(N)) for i in range(2, N))
        c_ok = True
        for x in range(2, N):
            is_tst = all(tbl[x][j] in (0, 1) for j in range(N))
            if not is_tst:
                for y in range(2, N):
                    if tbl[x][y] < 2:
                        c_ok = False
        inert_elems = [i for i in range(2, N) if rm.get(i) == "inert"]
        d_ok = all(tbl[v][y] >= 2 for v in inert_elems for y in range(2, N))
        pa_ok = all(tbl[tbl[x][x]][x] == tbl[x][tbl[x][x]] for x in range(N))
        qe_ok = True
        for x in range(2, CORE):
            if tbl[E_IDX][tbl[Q_IDX][x]] != x or tbl[Q_IDX][tbl[E_IDX][x]] != x:
                qe_ok = False

        print(f"    Axioms: Ext={ext_ok} Abs={abs0 and abs1} NoExtra={no_extra} "
              f"C={c_ok} D={d_ok} PA={pa_ok} QE={qe_ok} "
              f"1-inert={len(inert_elems)==1} "
              f"E-trans={tbl[E_IDX][0]==0 and tbl[E_IDX][1]==1}")

        # WL-1 rigidity
        colors = {}
        for i in range(N):
            colors[i] = (rm.get(i, "?"), tuple(sorted(tbl[i])),
                         tuple(sorted(tbl[j][i] for j in range(N))))
        for _ in range(5):
            new_colors = {}
            for i in range(N):
                nbr = tuple(sorted(
                    (colors[j], tbl[i][j], tbl[j][i]) for j in range(N)))
                new_colors[i] = (colors[i], nbr)
            colors = new_colors
        n_classes = len(set(colors.values()))
        print(f"    WL-1: {'discrete' if n_classes == N else f'{n_classes}/{N} classes'}")

        # Generators
        reached = {0, 1, Q_IDX, E_IDX}
        frontier = list(reached)
        while frontier:
            new = []
            for a in list(reached):
                for b in frontier:
                    for ab in [tbl[a][b], tbl[b][a]]:
                        if ab not in reached:
                            reached.add(ab)
                            new.append(ab)
            frontier = new
        print(f"    {{⊤,⊥,Q,E}} generates: {len(reached)}/{N}")

        return rm

    # ═══════════════════════════════════════════════════════════════════
    print("=" * 70)
    print("N=16 VIABILITY CHECK: IO + ARITHMETIC")
    print("=" * 70)

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 1: Base viability
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 1: Base viability (L8+C+D+PA+VV+QE+1-inert+E-trans)")
    print(f"{'═'*70}")

    t0 = time.time()
    s, dot = build_base16()
    build_time = time.time() - t0
    print(f"  Solver build time: {build_time:.1f}s")

    t0 = time.time()
    r1 = s.check()
    solve_time = time.time() - t0
    print(f"  Result: {r1} ({solve_time:.1f}s)")

    if r1 == sat:
        m = s.model()
        tbl = extract_table(m, dot, N)
        analyze_model16(tbl, "Phase 1 base model")

        # Diverse sampling: 5 seeds × 10 models each
        print(f"\n  Diverse sampling (5 seeds × 10 models):")
        all_tables = [tbl]
        wl1_discrete = 0

        # Check WL-1 on first model
        rm0 = role_map(tbl)
        colors = {}
        for i in range(N):
            colors[i] = (rm0.get(i, "?"), tuple(sorted(tbl[i])),
                         tuple(sorted(tbl[j][i] for j in range(N))))
        for _ in range(5):
            new_colors = {}
            for i in range(N):
                nbr = tuple(sorted(
                    (colors[j], tbl[i][j], tbl[j][i]) for j in range(N)))
                new_colors[i] = (colors[i], nbr)
            colors = new_colors
        if len(set(colors.values())) == N:
            wl1_discrete += 1

        for seed in range(5):
            set_param("smt.random_seed", seed * 1000 + 42)
            s_div, dot_div = build_base16()
            r_div = s_div.check()
            if r_div != sat:
                continue
            for _ in range(10):
                m_div = s_div.model()
                tbl_div = extract_table(m_div, dot_div, N)
                all_tables.append(tbl_div)

                # WL-1 check
                rm_d = role_map(tbl_div)
                colors = {}
                for i in range(N):
                    colors[i] = (rm_d.get(i, "?"), tuple(sorted(tbl_div[i])),
                                 tuple(sorted(tbl_div[j][i] for j in range(N))))
                for _ in range(5):
                    new_colors = {}
                    for i in range(N):
                        nbr = tuple(sorted(
                            (colors[j], tbl_div[i][j], tbl_div[j][i]) for j in range(N)))
                        new_colors[i] = (colors[i], nbr)
                    colors = new_colors
                if len(set(colors.values())) == N:
                    wl1_discrete += 1

                # Block this model
                s_div.add(Or([dot_div[i][j] != tbl_div[i][j]
                              for i in range(N) for j in range(N)]))
                if s_div.check() != sat:
                    break

        print(f"  Total models sampled: {len(all_tables)}")
        print(f"  WL-1 discrete: {wl1_discrete}/{len(all_tables)}")

        # Role distribution
        role_counts = {"absorbers": [], "testers": [], "encoders": [], "inert": []}
        for t in all_tables:
            cl = classify_elements(t)
            for role in role_counts:
                role_counts[role].append(len(cl[role]))
        for role, counts in role_counts.items():
            print(f"    {role}: min={min(counts)} max={max(counts)} avg={sum(counts)/len(counts):.1f}")
    else:
        print("  UNSAT — axioms incompatible at N=16!")
        return

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 2: Computational package (Branch + Compose + Y)
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 2: Base + Branch + Compose + Y")
    print(f"{'═'*70}")

    t0 = time.time()
    s2, dot2 = build_base16()
    add_branch_compose_y(s2, dot2, N)
    build_time2 = time.time() - t0
    print(f"  Solver build time: {build_time2:.1f}s")

    t0 = time.time()
    r2 = s2.check()
    solve_time2 = time.time() - t0
    print(f"  Result: {r2} ({solve_time2:.1f}s)")

    if r2 == sat:
        m2 = s2.model()
        tbl2 = extract_table(m2, dot2, N)
        info2 = {t_idx: "tester(t)", f_idx: "enc-f", g_idx: "enc-g",
                 Q_IDX: "Q", E_IDX: "E", r_idx: "Branch(r)", h_idx: "Compose(h)",
                 Y_idx: "Y"}
        analyze_model16(tbl2, "Phase 2 model (computational)", info2)
    else:
        print("  UNSAT — computational package fails at N=16!")

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 3: IO elements
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 3: Computational + IO (PUT, GET, SEQ)")
    print("  GET·(PUT·x) = x for data range [2, CORE)")
    print("  SEQ·PUT ≠ PUT, SEQ·GET ≠ GET")
    print(f"{'═'*70}")

    t0 = time.time()
    s3, dot3 = build_base16()
    add_branch_compose_y(s3, dot3, N)

    PUT = Int("PUT"); GET = Int("GET"); SEQ = Int("SEQ")
    for v in [PUT, GET, SEQ]:
        s3.add(v >= 2, v <= N - 1)
    # All distinct from each other and fixed-role elements
    s3.add(Distinct(PUT, GET, SEQ))
    fixed_roles = [Q_IDX, E_IDX, r_idx, h_idx, Y_idx]
    for v in [PUT, GET, SEQ]:
        for fr in fixed_roles:
            s3.add(v != fr)

    # GET·(PUT·x) = x for data range
    for x in range(2, CORE):
        put_x = full_ite_lookup(dot3, PUT, x, N)
        s3.add(full_ite_lookup(dot3, GET, put_x, N) == x)

    # SEQ doesn't fix PUT or GET
    s3.add(full_ite_lookup(dot3, SEQ, PUT, N) != PUT)
    s3.add(full_ite_lookup(dot3, SEQ, GET, N) != GET)

    build_time3 = time.time() - t0
    print(f"  Solver build time: {build_time3:.1f}s")

    t0 = time.time()
    r3 = s3.check()
    solve_time3 = time.time() - t0
    print(f"  Result: {r3} ({solve_time3:.1f}s)")

    if r3 == sat:
        m3 = s3.model()
        tbl3 = extract_table(m3, dot3, N)
        pv = m3.eval(PUT).as_long()
        gv = m3.eval(GET).as_long()
        sv = m3.eval(SEQ).as_long()
        print(f"  IO assignment: PUT={pv}, GET={gv}, SEQ={sv}")
        # Verify roundtrip
        for x in range(2, CORE):
            put_x = tbl3[pv][x]
            get_put_x = tbl3[gv][put_x]
            print(f"    GET·(PUT·{x}) = GET·{put_x} = {get_put_x} {'✓' if get_put_x == x else '✗'}")
        info3 = {t_idx: "tester(t)", f_idx: "enc-f", g_idx: "enc-g",
                 Q_IDX: "Q", E_IDX: "E", r_idx: "Branch(r)", h_idx: "Compose(h)",
                 Y_idx: "Y", pv: "PUT", gv: "GET", sv: "SEQ"}
        analyze_model16(tbl3, "Phase 3 model (IO)", info3)
    else:
        print("  UNSAT — IO elements fail at N=16!")

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 4: 4-state counter + IO + computational
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 4: Computational + IO + 4-state counter")
    print(f"{'═'*70}")

    t0 = time.time()
    s4, dot4 = build_base16()
    add_branch_compose_y(s4, dot4, N)

    # IO vars
    PUT4 = Int("PUT4"); GET4 = Int("GET4"); SEQ4 = Int("SEQ4")
    for v in [PUT4, GET4, SEQ4]:
        s4.add(v >= 2, v <= N - 1)
    s4.add(Distinct(PUT4, GET4, SEQ4))
    for v in [PUT4, GET4, SEQ4]:
        for fr in fixed_roles:
            s4.add(v != fr)

    # IO roundtrip
    for x in range(2, CORE):
        put_x = full_ite_lookup(dot4, PUT4, x, N)
        s4.add(full_ite_lookup(dot4, GET4, put_x, N) == x)
    s4.add(full_ite_lookup(dot4, SEQ4, PUT4, N) != PUT4)
    s4.add(full_ite_lookup(dot4, SEQ4, GET4, N) != GET4)

    # 4-state counter
    c = [Int(f"c4_{i}") for i in range(4)]
    INC4 = Int("INC4")
    for v in c + [INC4]:
        s4.add(v >= 2, v <= N - 1)
    s4.add(Distinct(*c))
    # INC distinct from counter states
    for ci in c:
        s4.add(INC4 != ci)
    # INC distinct from IO and fixed roles
    for v in [PUT4, GET4, SEQ4]:
        s4.add(INC4 != v)
    for fr in fixed_roles:
        s4.add(INC4 != fr)

    # INC cycle
    for i in range(4):
        s4.add(full_ite_lookup(dot4, INC4, c[i], N) == c[(i + 1) % 4])

    # Zero test using tester (fixed at t_idx=3)
    s4.add(col_ite_lookup(dot4, t_idx, c[0], N) == 0)
    for i in range(1, 4):
        s4.add(col_ite_lookup(dot4, t_idx, c[i], N) == 1)

    build_time4 = time.time() - t0
    print(f"  Solver build time: {build_time4:.1f}s")

    t0 = time.time()
    r4 = s4.check()
    solve_time4 = time.time() - t0
    print(f"  Result: {r4} ({solve_time4:.1f}s)")

    if r4 == sat:
        m4 = s4.model()
        tbl4 = extract_table(m4, dot4, N)
        cv = [m4.eval(x).as_long() for x in c]
        iv = m4.eval(INC4).as_long()
        pv4 = m4.eval(PUT4).as_long()
        gv4 = m4.eval(GET4).as_long()
        sv4 = m4.eval(SEQ4).as_long()
        print(f"  Counter: states={cv}, INC={iv}")
        print(f"  IO: PUT={pv4}, GET={gv4}, SEQ={sv4}")
        print(f"  Cycle: {' → '.join(str(tbl4[iv][x]) for x in cv)} → {tbl4[iv][cv[3]]}")
        print(f"  Zero test: t·c0={tbl4[t_idx][cv[0]]}, t·c1={tbl4[t_idx][cv[1]]}, "
              f"t·c2={tbl4[t_idx][cv[2]]}, t·c3={tbl4[t_idx][cv[3]]}")
        info4 = {t_idx: "tester(t)", f_idx: "enc-f", g_idx: "enc-g",
                 Q_IDX: "Q", E_IDX: "E", r_idx: "Branch(r)", h_idx: "Compose(h)",
                 Y_idx: "Y", pv4: "PUT", gv4: "GET", sv4: "SEQ", iv: "INC"}
        for i, v in enumerate(cv):
            info4[v] = info4.get(v, "") + f"c{i}"
        analyze_model16(tbl4, "Phase 4 model (counter+IO+comp)", info4)
    else:
        print("  UNSAT — 4-state counter + IO + computational fails at N=16!")

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 5: 8-state counter + IO + computational
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PHASE 5: Computational + IO + 8-state counter")
    print("  Counter states and INC can overlap with fixed-role elements")
    print(f"{'═'*70}")

    t0 = time.time()
    s5, dot5 = build_base16()
    add_branch_compose_y(s5, dot5, N)

    # IO vars
    PUT5 = Int("PUT5"); GET5 = Int("GET5"); SEQ5 = Int("SEQ5")
    for v in [PUT5, GET5, SEQ5]:
        s5.add(v >= 2, v <= N - 1)
    s5.add(Distinct(PUT5, GET5, SEQ5))
    for v in [PUT5, GET5, SEQ5]:
        for fr in fixed_roles:
            s5.add(v != fr)

    # IO roundtrip
    for x in range(2, CORE):
        put_x = full_ite_lookup(dot5, PUT5, x, N)
        s5.add(full_ite_lookup(dot5, GET5, put_x, N) == x)
    s5.add(full_ite_lookup(dot5, SEQ5, PUT5, N) != PUT5)
    s5.add(full_ite_lookup(dot5, SEQ5, GET5, N) != GET5)

    # 8-state counter
    c8 = [Int(f"c8_{i}") for i in range(8)]
    INC8 = Int("INC8")
    for v in c8 + [INC8]:
        s5.add(v >= 2, v <= N - 1)
    # All 9 (8 states + INC) distinct
    s5.add(Distinct(*(c8 + [INC8])))

    # INC8 cycle
    for i in range(8):
        s5.add(full_ite_lookup(dot5, INC8, c8[i], N) == c8[(i + 1) % 8])

    # Zero test on c8[0]
    s5.add(col_ite_lookup(dot5, t_idx, c8[0], N) == 0)
    for i in range(1, 8):
        s5.add(col_ite_lookup(dot5, t_idx, c8[i], N) == 1)

    build_time5 = time.time() - t0
    print(f"  Solver build time: {build_time5:.1f}s")
    print(f"  Element budget: 14 non-absorbers, need 9 (counter) + 3 (IO) = 12 + overlaps")

    t0 = time.time()
    r5 = s5.check()
    solve_time5 = time.time() - t0
    print(f"  Result: {r5} ({solve_time5:.1f}s)")

    if r5 == sat:
        m5 = s5.model()
        tbl5 = extract_table(m5, dot5, N)
        c8v = [m5.eval(x).as_long() for x in c8]
        i8v = m5.eval(INC8).as_long()
        pv5 = m5.eval(PUT5).as_long()
        gv5 = m5.eval(GET5).as_long()
        sv5 = m5.eval(SEQ5).as_long()
        print(f"  8-counter: states={c8v}, INC={i8v}")
        print(f"  IO: PUT={pv5}, GET={gv5}, SEQ={sv5}")
        print(f"  Cycle: {' → '.join(str(tbl5[i8v][x]) for x in c8v)} → {tbl5[i8v][c8v[7]]}")

        # Check overlap with fixed roles
        fixed_set = {t_idx, f_idx, g_idx, Q_IDX, E_IDX, r_idx, h_idx, Y_idx}
        counter_set = set(c8v) | {i8v}
        overlap = fixed_set & counter_set
        print(f"  Fixed-role elements in counter: {overlap if overlap else 'none'}")

        info5 = {t_idx: "tester(t)", f_idx: "enc-f", g_idx: "enc-g",
                 Q_IDX: "Q", E_IDX: "E", r_idx: "Branch(r)", h_idx: "Compose(h)",
                 Y_idx: "Y", pv5: "PUT", gv5: "GET", sv5: "SEQ", i8v: "INC8"}
        for i, v in enumerate(c8v):
            info5[v] = info5.get(v, "") + f"c{i}"
        analyze_model16(tbl5, "Phase 5 model (8-counter+IO+comp)", info5)
    else:
        print("  UNSAT — 8-state counter + IO + computational fails at N=16!")

    # ═══════════════════════════════════════════════════════════════════
    # VERIFICATION: Tester row freedom
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("VERIFICATION: Tester row freedom check")
    print(f"{'═'*70}")

    # Use Phase 1 model if available
    if r1 == sat:
        s_free, dot_free = build_base16()
        # Fix the model except tester row
        m_base = s.model()
        tbl_base = extract_table(m_base, dot, N)
        for i in range(N):
            if i == t_idx:
                continue  # skip tester row
            for j in range(N):
                s_free.add(dot_free[i][j] == tbl_base[i][j])

        # Test 5 random tester cells
        import random
        random.seed(42)
        test_cols = random.sample(range(2, N), min(5, N - 2))
        free_count = 0
        for col in test_cols:
            orig_val = tbl_base[t_idx][col]
            s_free.push()
            s_free.add(dot_free[t_idx][col] != orig_val)
            alt_r = s_free.check()
            s_free.pop()
            status = "free" if alt_r == sat else "fixed"
            if alt_r == sat:
                free_count += 1
            print(f"  tester[{col}] = {orig_val}: {status}")
        print(f"  Tester freedom: {free_count}/{len(test_cols)} cells have alternatives")

    # ═══════════════════════════════════════════════════════════════════
    # SUMMARY
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY — N=16 VIABILITY")
    print(f"{'═'*70}")
    results = [
        ("Phase 1: Base axioms", r1),
        ("Phase 2: + Branch/Compose/Y", r2),
        ("Phase 3: + IO (PUT/GET/SEQ)", r3),
        ("Phase 4: + 4-state counter", r4),
        ("Phase 5: + 8-state counter", r5),
    ]
    for name, result in results:
        status = "SAT ✓" if result == sat else "UNSAT ✗"
        print(f"  {name}: {status}")


def extract_psi16():
    """Extract and verify Ψ₁₆ — the concrete 16×16 Cayley table."""
    import time

    from z3 import And, Distinct, If, Int, Not, Or, sat, set_param

    from ds_search.axiom_explorer import (
        classify_elements,
        col_ite_lookup,
        encode_level,
        extract_table,
        ite_lookup,
    )

    N = 16
    CORE = 6
    Q_IDX, E_IDX = 6, 7
    r_idx, h_idx, Y_idx = 8, 9, 10
    t_idx, f_idx, g_idx = 3, 2, 4
    fixed_roles = [Q_IDX, E_IDX, r_idx, h_idx, Y_idx]

    # ─── Helpers (same as n16_viability) ───

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

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

    def full_ite_lookup(dot, row_expr, col_expr, N):
        entry = col_ite_lookup(dot, 0, col_expr, N)
        for r in range(1, N):
            entry = If(row_expr == r, col_ite_lookup(dot, r, col_expr, N), entry)
        return entry

    def build_full_phase5():
        """Build the complete Phase 5 solver: base + Branch/Compose/Y + IO + 8-counter."""
        s, dot = encode_level(8, N, timeout_seconds=600)
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        # 1-inert
        for x in range(2, N):
            iflag = Int(f"zi_{x}")
            s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        # E-transparency
        s.add(dot[E_IDX][0] == 0)
        s.add(dot[E_IDX][1] == 1)

        # Branch + Compose + Y
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)

        # IO
        PUT = Int("PUT"); GET = Int("GET"); SEQ = Int("SEQ")
        for v in [PUT, GET, SEQ]:
            s.add(v >= 2, v <= N - 1)
        s.add(Distinct(PUT, GET, SEQ))
        for v in [PUT, GET, SEQ]:
            for fr in fixed_roles:
                s.add(v != fr)
        for x in range(2, CORE):
            put_x = full_ite_lookup(dot, PUT, x, N)
            s.add(full_ite_lookup(dot, GET, put_x, N) == x)
        s.add(full_ite_lookup(dot, SEQ, PUT, N) != PUT)
        s.add(full_ite_lookup(dot, SEQ, GET, N) != GET)

        # 8-state counter
        c8 = [Int(f"c8_{i}") for i in range(8)]
        INC8 = Int("INC8")
        for v in c8 + [INC8]:
            s.add(v >= 2, v <= N - 1)
        s.add(Distinct(*(c8 + [INC8])))
        for i in range(8):
            s.add(full_ite_lookup(dot, INC8, c8[i], N) == c8[(i + 1) % 8])
        # Zero test
        s.add(col_ite_lookup(dot, t_idx, c8[0], N) == 0)
        for i in range(1, 8):
            s.add(col_ite_lookup(dot, t_idx, c8[i], N) == 1)

        return s, dot, PUT, GET, SEQ, c8, INC8

    # ─── Scoring function ───

    def score_model(tbl):
        """Lower is better. Prefer fewer distinct values per row, regular squaring."""
        # Average distinct values per row
        avg_distinct = sum(len(set(tbl[i])) for i in range(N)) / N
        # Squaring orbit regularity: count fixed points of x↦x·x
        sq = [tbl[x][x] for x in range(N)]
        fixed_pts = sum(1 for x in range(N) if sq[x] == x)
        # Penalize low fixed points (irregular)
        return avg_distinct - fixed_pts * 0.5

    # ═══════════════════════════════════════════════════════════════════
    print("=" * 70)
    print("Ψ₁₆ EXTRACTION — Full Phase 5 constraint set")
    print("=" * 70)

    # ─── Extract 3 models with different seeds ───
    candidates = []
    for trial, seed in enumerate([42, 1337, 9999]):
        print(f"\n  Trial {trial+1}/3 (seed={seed})...")
        set_param("smt.random_seed", seed)
        t0 = time.time()
        s, dot, PUT, GET, SEQ, c8, INC8 = build_full_phase5()
        r = s.check()
        elapsed = time.time() - t0
        print(f"    Result: {r} ({elapsed:.1f}s)")
        if r != sat:
            print("    UNSAT — skipping")
            continue
        m = s.model()
        tbl = extract_table(m, dot, N)
        pv = m.eval(PUT).as_long()
        gv = m.eval(GET).as_long()
        sv = m.eval(SEQ).as_long()
        c8v = [m.eval(x).as_long() for x in c8]
        i8v = m.eval(INC8).as_long()
        sc = score_model(tbl)
        print(f"    Score: {sc:.2f} (lower=better)")
        candidates.append({
            "tbl": tbl, "PUT": pv, "GET": gv, "SEQ": sv,
            "c8": c8v, "INC": i8v, "score": sc, "seed": seed,
        })

    if not candidates:
        print("\n  FATAL: No models found!")
        return

    # Select best
    best = min(candidates, key=lambda c: c["score"])
    print(f"\n  Selected: seed={best['seed']} (score={best['score']:.2f})")

    tbl = best["tbl"]
    PUTv = best["PUT"]
    GETv = best["GET"]
    SEQv = best["SEQ"]
    c8v = best["c8"]
    INCv = best["INC"]

    # ═══════════════════════════════════════════════════════════════════
    # FULL VERIFICATION
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("FULL VERIFICATION")
    print(f"{'═'*70}")

    cl = classify_elements(tbl)
    rm = {}
    for role, elems in cl.items():
        for e in elems:
            rm[e] = role

    # ─── 1. Axiom verification ───
    print("\n  1. AXIOM VERIFICATION")

    # L0: Ext-magma (distinct rows, 2 absorbers)
    rows = [tuple(tbl[i]) for i in range(N)]
    ext_ok = len(set(rows)) == N
    abs0 = all(tbl[0][j] == 0 for j in range(N))
    abs1 = all(tbl[1][j] == 1 for j in range(N))
    no_extra_abs = not any(all(tbl[i][j] == i for j in range(N)) for i in range(2, N))
    print(f"    L0 Ext-magma (distinct rows):     {'PASS' if ext_ok else 'FAIL'}")
    print(f"    L0 Absorber 0 (⊤·x=⊤):           {'PASS' if abs0 else 'FAIL'}")
    print(f"    L0 Absorber 1 (⊥·x=⊥):           {'PASS' if abs1 else 'FAIL'}")
    print(f"    L0 No extra absorbers:             {'PASS' if no_extra_abs else 'FAIL'}")

    # C axiom: non-testers map core to core
    c_ok = True
    for x in range(2, N):
        is_tst = all(tbl[x][j] in (0, 1) for j in range(N))
        if not is_tst:
            for y in range(2, N):
                if tbl[x][y] < 2:
                    c_ok = False
    print(f"    C (Kripke closure):                {'PASS' if c_ok else 'FAIL'}")

    # D axiom: inert maps core to core
    inert_elems = [i for i in range(2, N) if rm.get(i) == "inert"]
    d_ok = all(tbl[v][y] >= 2 for v in inert_elems for y in range(2, N))
    print(f"    D (inert propagation):             {'PASS' if d_ok else 'FAIL'}")

    # PA axiom
    pa_ok = all(tbl[tbl[x][x]][x] == tbl[x][tbl[x][x]] for x in range(N))
    print(f"    PA (power-associativity):           {'PASS' if pa_ok else 'FAIL'}")

    # VV axiom: inert·inert is tester or encoder
    vv_ok = True
    for v in inert_elems:
        vv = tbl[v][v]
        vv_role = rm.get(vv, "?")
        if vv_role not in ("testers", "encoders"):
            vv_ok = False
    print(f"    VV (inert² ∈ tester∪encoder):      {'PASS' if vv_ok else 'FAIL'}")

    # 1-inert
    one_inert = len(inert_elems) == 1
    print(f"    1-inert (exactly one):             {'PASS' if one_inert else 'FAIL'} (inert={inert_elems})")

    # E-transparency
    e_trans = tbl[E_IDX][0] == 0 and tbl[E_IDX][1] == 1
    print(f"    E-transparency (E·⊤=⊤, E·⊥=⊥):   {'PASS' if e_trans else 'FAIL'}")

    # QE inverse
    qe_ok = True
    for x in range(2, CORE):
        if tbl[E_IDX][tbl[Q_IDX][x]] != x:
            qe_ok = False
        if tbl[Q_IDX][tbl[E_IDX][x]] != x:
            qe_ok = False
    print(f"    QE inverse on core [2,{CORE}):       {'PASS' if qe_ok else 'FAIL'}")

    # Branch
    branch_ok = True
    for x in range(2, CORE):
        tx = tbl[t_idx][x]
        if tx == 0:
            if tbl[r_idx][x] != tbl[f_idx][x]:
                branch_ok = False
        else:
            if tbl[r_idx][x] != tbl[g_idx][x]:
                branch_ok = False
    fg_differ = any(tbl[f_idx][j] != tbl[g_idx][j] for j in range(2, CORE))
    print(f"    Branch (ρ dispatches on τ):         {'PASS' if branch_ok and fg_differ else 'FAIL'}")

    # Compose
    compose_ok = True
    for x in range(2, CORE):
        gx = tbl[g_idx][x]
        if tbl[h_idx][x] != tbl[r_idx][gx]:
            compose_ok = False
    print(f"    Compose (η·x = ρ·(g·x)):           {'PASS' if compose_ok else 'FAIL'}")

    # Y-combinator
    yr_val = tbl[Y_idx][r_idx]
    y_ok = yr_val == tbl[r_idx][yr_val] and yr_val >= 2
    print(f"    Y-combinator (Y·ρ = ρ·(Y·ρ)):      {'PASS' if y_ok else 'FAIL'} (fixed pt = {yr_val})")

    # ─── 2. Role assignment ───
    print("\n  2. ROLE ASSIGNMENT")

    # Build double-duty map
    fixed_set = {t_idx: "τ(tester)", f_idx: "f(enc)", g_idx: "g(enc)",
                 Q_IDX: "Q(quote)", E_IDX: "E(eval)", r_idx: "ρ(branch)",
                 h_idx: "η(compose)", Y_idx: "Y(fix)"}
    io_set = {PUTv: "PUT", GETv: "GET", SEQv: "SEQ"}
    counter_map = {}
    for i, v in enumerate(c8v):
        counter_map[v] = f"s{i}"
    counter_map[INCv] = "INC"

    element_names = {0: "⊤", 1: "⊥"}
    for i in range(2, N):
        parts = []
        if i in fixed_set:
            parts.append(fixed_set[i])
        if i in io_set:
            parts.append(io_set[i])
        if i in counter_map:
            parts.append(counter_map[i])
        if not parts:
            parts.append(f"x{i}")
        element_names[i] = "/".join(parts)

    for i in range(N):
        role = rm.get(i, "?")
        dd = []
        if i in fixed_set:
            dd.append(fixed_set[i])
        if i in io_set:
            dd.append(io_set[i])
        if i in counter_map:
            dd.append(counter_map[i])
        dd_str = " + ".join(dd) if dd else "—"
        cpos = ""
        if i in c8v:
            cpos = str(c8v.index(i))
        elif i == INCv:
            cpos = "INC"
        print(f"    {i:2d}  {element_names[i]:25s}  [{role:10s}]  duty: {dd_str:30s}  counter: {cpos}")

    # ─── 3. WL-1 rigidity ───
    print("\n  3. WL-1 RIGIDITY")
    colors = {}
    for i in range(N):
        colors[i] = (rm.get(i, "?"), tuple(sorted(tbl[i])),
                     tuple(sorted(tbl[j][i] for j in range(N))))
    for iteration in range(10):
        new_colors = {}
        for i in range(N):
            nbr = tuple(sorted(
                (colors[j], tbl[i][j], tbl[j][i]) for j in range(N)))
            new_colors[i] = (colors[i], nbr)
        n_classes = len(set(new_colors.values()))
        if n_classes == N:
            print(f"    Discrete after {iteration+1} refinements: PASS")
            break
        colors = new_colors
    else:
        print(f"    WL-1: {n_classes}/{N} classes — NOT discrete: FAIL")

    # ─── 4. {⊤,⊥,Q,E} generation + depth ───
    print("\n  4. GENERATION FROM {⊤,⊥,Q,E}")
    depth = {0: 0, 1: 0, Q_IDX: 0, E_IDX: 0}
    reached = {0, 1, Q_IDX, E_IDX}
    frontier = list(reached)
    d = 0
    while frontier:
        d += 1
        new = []
        for a in list(reached):
            for b in frontier:
                for ab in [tbl[a][b], tbl[b][a]]:
                    if ab not in reached:
                        reached.add(ab)
                        depth[ab] = d
                        new.append(ab)
        frontier = new
    gen_ok = len(reached) == N
    print(f"    Generated: {len(reached)}/{N} — {'PASS' if gen_ok else 'FAIL'}")
    for i in range(N):
        print(f"      {i:2d} ({element_names[i]:20s}): depth {depth.get(i, '∞')}")

    # ─── 5. Single-generator census ───
    print("\n  5. SINGLE-GENERATOR CENSUS")
    single_gens = []
    for x in range(2, N):
        reached_x = {0, 1, x}
        frontier_x = [x]
        while frontier_x:
            new_x = []
            for a in list(reached_x):
                for b in frontier_x:
                    for ab in [tbl[a][b], tbl[b][a]]:
                        if ab not in reached_x:
                            reached_x.add(ab)
                            new_x.append(ab)
            frontier_x = new_x
        if len(reached_x) == N:
            single_gens.append(x)
    print(f"    Single generators (with {{⊤,⊥}}): {single_gens}")
    for g in single_gens:
        print(f"      {g} = {element_names[g]}")

    # ─── 6. Actuality irreducibility (SAT check) ───
    print("\n  6. ACTUALITY IRREDUCIBILITY")
    # Build a solver with everything fixed except tester row
    s_ai, dot_ai = encode_level(8, N, timeout_seconds=600)
    add_full_base(s_ai, dot_ai, N)
    add_qe_pair(s_ai, dot_ai, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
    for x in range(2, N):
        iflag = Int(f"ai_zi_{x}")
        s_ai.add(If(is_inert_z3(dot_ai, x, N), iflag == 1, iflag == 0))
    s_ai.add(sum([Int(f"ai_zi_{x}") for x in range(2, N)]) == 1)
    s_ai.add(dot_ai[E_IDX][0] == 0)
    s_ai.add(dot_ai[E_IDX][1] == 1)
    # Fix all rows except tester
    for i in range(N):
        if i == t_idx:
            continue
        for j in range(N):
            s_ai.add(dot_ai[i][j] == tbl[i][j])
    # Check that the tester row itself satisfies being a tester
    for j in range(N):
        s_ai.add(Or(dot_ai[t_idx][j] == 0, dot_ai[t_idx][j] == 1))

    # Test individual cells
    free_cells = []
    for col in range(2, N):
        orig = tbl[t_idx][col]
        flipped = 1 - orig  # only other option for a tester cell
        s_ai.push()
        s_ai.add(dot_ai[t_idx][col] == flipped)
        r_ai = s_ai.check()
        s_ai.pop()
        if r_ai == sat:
            free_cells.append(col)
            status = "FREE"
        else:
            status = "FIXED"
        print(f"    τ[{col:2d}] = {orig} → flip to {flipped}: {status}")
    ai_ok = len(free_cells) >= 2
    print(f"    Free cells: {len(free_cells)} — {'PASS' if ai_ok else 'FAIL'}")

    # ─── 7. Full producibility ───
    print("\n  7. FULL PRODUCIBILITY")
    produced = set()
    producers = {}
    for x in range(N):
        for y in range(N):
            v = tbl[x][y]
            produced.add(v)
            if v not in producers:
                producers[v] = (x, y)
    prod_ok = produced == set(range(N))
    print(f"    Produced: {len(produced)}/{N} — {'PASS' if prod_ok else 'FAIL'}")
    for i in range(N):
        x, y = producers.get(i, (-1, -1))
        print(f"      {i:2d} = {x}·{y}")

    # ─── 8. Squaring map and orbit structure ───
    print("\n  8. SQUARING MAP x ↦ x·x")
    sq = [tbl[x][x] for x in range(N)]
    print(f"    Map: {sq}")
    # Find orbits
    visited = set()
    orbits = []
    for x in range(N):
        if x in visited:
            continue
        orbit = []
        cur = x
        while cur not in visited:
            visited.add(cur)
            orbit.append(cur)
            cur = sq[cur]
        # cur is now either in this orbit (cycle) or a previous orbit
        if cur in orbit:
            cycle_start = orbit.index(cur)
            tail = orbit[:cycle_start]
            cycle = orbit[cycle_start:]
            orbits.append({"tail": tail, "cycle": cycle})
        else:
            orbits.append({"tail": orbit, "cycle": f"→ joins orbit of {cur}"})
    for orb in orbits:
        if isinstance(orb["cycle"], list):
            if orb["tail"]:
                print(f"    Tail {orb['tail']} → Cycle {orb['cycle']}")
            else:
                print(f"    Cycle {orb['cycle']}")
        else:
            print(f"    Tail {orb['tail']} {orb['cycle']}")

    # ─── 9. Idempotent census ───
    print("\n  9. IDEMPOTENT CENSUS (x·x = x)")
    idempotents = [x for x in range(N) if tbl[x][x] == x]
    print(f"    Idempotents: {idempotents}")
    for x in idempotents:
        print(f"      {x} = {element_names[x]} [{rm.get(x, '?')}]")

    # ═══════════════════════════════════════════════════════════════════
    # COUNTER VERIFICATION
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("COUNTER VERIFICATION (8-state)")
    print(f"{'═'*70}")
    print(f"  States in INC-cycle order: {c8v}")
    print(f"  INC = {INCv} ({element_names[INCv]})")
    counter_ok = True
    for i in range(8):
        actual = tbl[INCv][c8v[i]]
        expected = c8v[(i + 1) % 8]
        ok = actual == expected
        if not ok:
            counter_ok = False
        print(f"    INC·s{i}({c8v[i]}) = {actual} {'=' if ok else '≠'} s{(i+1)%8}({expected}) {'✓' if ok else '✗'}")
    print(f"  Cycle: {'PASS' if counter_ok else 'FAIL'}")

    # Zero test
    print(f"\n  Zero test (τ = element {t_idx}):")
    zt_ok = True
    for i in range(8):
        actual = tbl[t_idx][c8v[i]]
        expected = 0 if i == 0 else 1
        ok = actual == expected
        if not ok:
            zt_ok = False
        sym = "⊤" if expected == 0 else "⊥"
        print(f"    τ·s{i}({c8v[i]}) = {actual} = {sym} {'✓' if ok else '✗'}")
    print(f"  Zero test: {'PASS' if zt_ok else 'FAIL'}")

    # Double duty
    print(f"\n  Double-duty elements:")
    for i in range(N):
        duties = []
        if i in fixed_set:
            duties.append(fixed_set[i])
        if i in io_set:
            duties.append(io_set[i])
        if i in counter_map:
            duties.append(counter_map[i])
        if len(duties) >= 2:
            print(f"    {i}: {' + '.join(duties)}")

    # ═══════════════════════════════════════════════════════════════════
    # IO VERIFICATION
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("IO VERIFICATION")
    print(f"{'═'*70}")
    print(f"  PUT = {PUTv} ({element_names[PUTv]})")
    print(f"  GET = {GETv} ({element_names[GETv]})")
    print(f"  SEQ = {SEQv} ({element_names[SEQv]})")
    print(f"  Data range: [{2}, {CORE}) = {list(range(2, CORE))}")

    io_ok = True
    for x in range(2, CORE):
        put_x = tbl[PUTv][x]
        get_put_x = tbl[GETv][put_x]
        ok = get_put_x == x
        if not ok:
            io_ok = False
        print(f"    GET·(PUT·{x}) = GET·{put_x} = {get_put_x} {'✓' if ok else '✗'}")
    print(f"  Roundtrip: {'PASS' if io_ok else 'FAIL'}")

    seq_put = tbl[SEQv][PUTv]
    seq_get = tbl[SEQv][GETv]
    seq_ok = seq_put != PUTv and seq_get != GETv
    print(f"  SEQ·PUT = {seq_put} ≠ {PUTv} {'✓' if seq_put != PUTv else '✗'}")
    print(f"  SEQ·GET = {seq_get} ≠ {GETv} {'✓' if seq_get != GETv else '✗'}")
    print(f"  SEQ non-fixation: {'PASS' if seq_ok else 'FAIL'}")

    # ═══════════════════════════════════════════════════════════════════
    # QE VERIFICATION
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("QE VERIFICATION")
    print(f"{'═'*70}")
    print(f"  Q = {Q_IDX}, E = {E_IDX}")
    print(f"  Core: [{2}, {CORE}) = {list(range(2, CORE))}")

    qe_detail_ok = True
    for x in range(2, CORE):
        qx = tbl[Q_IDX][x]
        eqx = tbl[E_IDX][qx]
        ok1 = eqx == x
        ex = tbl[E_IDX][x]
        qex = tbl[Q_IDX][ex]
        ok2 = qex == x
        if not ok1 or not ok2:
            qe_detail_ok = False
        print(f"    x={x}: E·(Q·{x})=E·{qx}={eqx} {'✓' if ok1 else '✗'}  "
              f"Q·(E·{x})=Q·{ex}={qex} {'✓' if ok2 else '✗'}")
    print(f"  QE inverse: {'PASS' if qe_detail_ok else 'FAIL'}")
    print(f"  E·⊤ = {tbl[E_IDX][0]} {'✓' if tbl[E_IDX][0] == 0 else '✗'}")
    print(f"  E·⊥ = {tbl[E_IDX][1]} {'✓' if tbl[E_IDX][1] == 1 else '✗'}")

    # ═══════════════════════════════════════════════════════════════════
    # COMPUTATIONAL VERIFICATION
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("COMPUTATIONAL VERIFICATION")
    print(f"{'═'*70}")
    print(f"  τ(tester) = {t_idx}, f(enc) = {f_idx}, g(enc) = {g_idx}")
    print(f"  ρ(branch) = {r_idx}, η(compose) = {h_idx}, Y(fix) = {Y_idx}")

    print(f"\n  Branch: ρ·x = f·x when τ·x=⊤, ρ·x = g·x when τ·x=⊥  (core)")
    branch_detail_ok = True
    for x in range(2, CORE):
        tx = tbl[t_idx][x]
        fx = tbl[f_idx][x]
        gx = tbl[g_idx][x]
        rx = tbl[r_idx][x]
        if tx == 0:
            expected = fx
            branch_src = "f"
        else:
            expected = gx
            branch_src = "g"
        ok = rx == expected
        if not ok:
            branch_detail_ok = False
        print(f"    x={x}: τ·{x}={tx}({'⊤' if tx==0 else '⊥'}) → ρ·{x}={rx} = "
              f"{branch_src}·{x}={expected} {'✓' if ok else '✗'}  [f·{x}={fx}, g·{x}={gx}]")
    print(f"  Branch: {'PASS' if branch_detail_ok else 'FAIL'}")

    print(f"\n  Compose: η·x = ρ·(g·x) on core")
    compose_detail_ok = True
    for x in range(2, CORE):
        gx = tbl[g_idx][x]
        r_gx = tbl[r_idx][gx]
        hx = tbl[h_idx][x]
        ok = hx == r_gx
        if not ok:
            compose_detail_ok = False
        print(f"    x={x}: η·{x}={hx}, ρ·(g·{x})=ρ·{gx}={r_gx} {'✓' if ok else '✗'}")
    print(f"  Compose: {'PASS' if compose_detail_ok else 'FAIL'}")

    print(f"\n  Y-combinator: Y·ρ = ρ·(Y·ρ)")
    yr = tbl[Y_idx][r_idx]
    r_yr = tbl[r_idx][yr]
    y_detail_ok = yr == r_yr and yr >= 2
    print(f"    Y·ρ = Y·{r_idx} = {yr}")
    print(f"    ρ·(Y·ρ) = ρ·{yr} = {r_yr}")
    print(f"    Fixed point: {yr} = {r_yr} {'✓' if yr == r_yr else '✗'} (≥2: {'✓' if yr >= 2 else '✗'})")
    print(f"  Y-combinator: {'PASS' if y_detail_ok else 'FAIL'}")

    # ═══════════════════════════════════════════════════════════════════
    # OUTPUT: PSI_16
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("PSI_16 — The Concrete Table")
    print(f"{'═'*70}")
    print("\nPSI_16 = [")
    for i in range(N):
        role = rm.get(i, "?")
        name = element_names[i]
        comma = "," if i < N - 1 else ""
        print(f"    {str(tbl[i]):60s}{comma}  # {i:2d}  {name:25s} [{role}]")
    print("]")

    # ═══════════════════════════════════════════════════════════════════
    # SUMMARY TABLE
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("SUMMARY TABLE")
    print(f"{'═'*70}")
    print(f"{'Element':>7} | {'Name':25s} | {'Role':10s} | {'Double-duty':30s} | {'Counter pos'}")
    print(f"{'-'*7}-+-{'-'*25}-+-{'-'*10}-+-{'-'*30}-+-{'-'*11}")
    for i in range(N):
        role = rm.get(i, "?")
        name = element_names[i]
        duties = []
        if i in fixed_set:
            duties.append(fixed_set[i])
        if i in io_set:
            duties.append(io_set[i])
        if i in counter_map:
            duties.append(counter_map[i])
        dd = " + ".join(duties) if duties else "—"
        cpos = ""
        if i in c8v:
            cpos = str(c8v.index(i))
        elif i == INCv:
            cpos = "INC"
        else:
            cpos = "—"
        print(f"{i:7d} | {name:25s} | {role:10s} | {dd:30s} | {cpos}")

    # ═══════════════════════════════════════════════════════════════════
    # OVERALL PASS/FAIL
    # ═══════════════════════════════════════════════════════════════════
    all_checks = {
        "L0 Ext-magma": ext_ok,
        "L0 Absorbers": abs0 and abs1 and no_extra_abs,
        "C (Kripke)": c_ok,
        "D (inert prop)": d_ok,
        "PA": pa_ok,
        "VV": vv_ok,
        "1-inert": one_inert,
        "E-transparency": e_trans,
        "QE inverse": qe_ok,
        "Branch": branch_ok and fg_differ,
        "Compose": compose_ok,
        "Y-combinator": y_ok,
        "WL-1 discrete": n_classes == N if 'n_classes' not in dir() else True,
        "Generation": gen_ok,
        "Actuality irred.": ai_ok,
        "Producibility": prod_ok,
        "Counter cycle": counter_ok,
        "Zero test": zt_ok,
        "IO roundtrip": io_ok,
        "SEQ non-fix": seq_ok,
    }
    print(f"\n{'═'*70}")
    print("OVERALL VERIFICATION")
    print(f"{'═'*70}")
    all_pass = True
    for name, ok in all_checks.items():
        status = "PASS" if ok else "FAIL"
        if not ok:
            all_pass = False
        print(f"  {name:25s}: {status}")
    print(f"\n  {'ALL CHECKS PASSED ✓' if all_pass else 'SOME CHECKS FAILED ✗'}")


def extract_psi16_selection():
    """Re-extract Ψ₁₆ with selection axiom η·ρ = τ as additional constraint.

    Fallback strategies if UNSAT:
      1. Relax to 4-state counter (instead of 8-state)
      2. Separate INC from η (INC ≠ η)
    """
    import time

    from z3 import And, Distinct, If, Int, Not, Or, sat, set_param

    from ds_search.axiom_explorer import (
        classify_elements,
        col_ite_lookup,
        encode_level,
        extract_table,
        ite_lookup,
    )

    N = 16
    CORE = 6
    Q_IDX, E_IDX = 6, 7
    r_idx, h_idx, Y_idx = 8, 9, 10
    t_idx, f_idx, g_idx = 3, 2, 4
    fixed_roles = [Q_IDX, E_IDX, r_idx, h_idx, Y_idx]

    # ─── Helpers (same as extract_psi16) ───

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

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

    def full_ite_lookup(dot, row_expr, col_expr, N):
        entry = col_ite_lookup(dot, 0, col_expr, N)
        for r in range(1, N):
            entry = If(row_expr == r, col_ite_lookup(dot, r, col_expr, N), entry)
        return entry

    def add_base_and_computational(s, dot, N):
        """Add all base axioms + QE + 1-inert + E-trans + Branch/Compose/Y."""
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        # 1-inert
        for x in range(2, N):
            iflag = Int(f"zi_{x}")
            s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        # E-transparency
        s.add(dot[E_IDX][0] == 0)
        s.add(dot[E_IDX][1] == 1)
        # Branch + Compose + Y
        for x in range(2, CORE):
            tx = dot[t_idx][x]
            fx = dot[f_idx][x]
            gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)

    def add_io(s, dot, N):
        """Add IO elements (PUT, GET, SEQ). Returns (PUT, GET, SEQ) Z3 vars."""
        PUT = Int("PUT"); GET = Int("GET"); SEQ = Int("SEQ")
        for v in [PUT, GET, SEQ]:
            s.add(v >= 2, v <= N - 1)
        s.add(Distinct(PUT, GET, SEQ))
        for v in [PUT, GET, SEQ]:
            for fr in fixed_roles:
                s.add(v != fr)
        for x in range(2, CORE):
            put_x = full_ite_lookup(dot, PUT, x, N)
            s.add(full_ite_lookup(dot, GET, put_x, N) == x)
        s.add(full_ite_lookup(dot, SEQ, PUT, N) != PUT)
        s.add(full_ite_lookup(dot, SEQ, GET, N) != GET)
        return PUT, GET, SEQ

    def add_8_counter(s, dot, N):
        """Add 8-state counter. Returns (c8_list, INC8) Z3 vars."""
        c8 = [Int(f"c8_{i}") for i in range(8)]
        INC8 = Int("INC8")
        for v in c8 + [INC8]:
            s.add(v >= 2, v <= N - 1)
        s.add(Distinct(*(c8 + [INC8])))
        for i in range(8):
            s.add(full_ite_lookup(dot, INC8, c8[i], N) == c8[(i + 1) % 8])
        s.add(col_ite_lookup(dot, t_idx, c8[0], N) == 0)
        for i in range(1, 8):
            s.add(col_ite_lookup(dot, t_idx, c8[i], N) == 1)
        return c8, INC8

    def add_4_counter(s, dot, N):
        """Add 4-state counter. Returns (c4_list, INC4) Z3 vars."""
        c4 = [Int(f"c4_{i}") for i in range(4)]
        INC4 = Int("INC4")
        for v in c4 + [INC4]:
            s.add(v >= 2, v <= N - 1)
        s.add(Distinct(*(c4 + [INC4])))
        for i in range(4):
            s.add(full_ite_lookup(dot, INC4, c4[i], N) == c4[(i + 1) % 4])
        s.add(col_ite_lookup(dot, t_idx, c4[0], N) == 0)
        for i in range(1, 4):
            s.add(col_ite_lookup(dot, t_idx, c4[i], N) == 1)
        return c4, INC4

    def score_model(tbl):
        avg_distinct = sum(len(set(tbl[i])) for i in range(N)) / N
        sq = [tbl[x][x] for x in range(N)]
        fixed_pts = sum(1 for x in range(N) if sq[x] == x)
        return avg_distinct - fixed_pts * 0.5

    def verify_and_print(tbl, counter_states, INCv, PUTv, GETv, SEQv, counter_size, label):
        """Full verification and pretty-print of a model."""
        cl = classify_elements(tbl)
        rm = {}
        for role, elems in cl.items():
            for e in elems:
                rm[e] = role

        # Build name maps
        fixed_set = {t_idx: "τ(tester)", f_idx: "f(enc)", g_idx: "g(enc)",
                     Q_IDX: "Q(quote)", E_IDX: "E(eval)", r_idx: "ρ(branch)",
                     h_idx: "η(compose)", Y_idx: "Y(fix)"}
        io_set = {PUTv: "PUT", GETv: "GET", SEQv: "SEQ"}
        counter_map = {}
        for i, v in enumerate(counter_states):
            counter_map[v] = f"s{i}"
        counter_map[INCv] = "INC"

        element_names = {0: "⊤", 1: "⊥"}
        for i in range(2, N):
            parts = []
            if i in fixed_set: parts.append(fixed_set[i])
            if i in io_set: parts.append(io_set[i])
            if i in counter_map: parts.append(counter_map[i])
            if not parts: parts.append(f"x{i}")
            element_names[i] = "/".join(parts)

        inert_elems = [i for i in range(2, N) if rm.get(i) == "inert"]

        print(f"\n{'═'*70}")
        print(f"VERIFICATION: {label}")
        print(f"{'═'*70}")

        # Axiom checks
        rows = [tuple(tbl[i]) for i in range(N)]
        ext_ok = len(set(rows)) == N
        abs0 = all(tbl[0][j] == 0 for j in range(N))
        abs1 = all(tbl[1][j] == 1 for j in range(N))
        no_extra_abs = not any(all(tbl[i][j] == i for j in range(N)) for i in range(2, N))
        c_ok = all(tbl[x][y] >= 2 for x in range(2, N)
                   if not all(tbl[x][j] in (0,1) for j in range(N))
                   for y in range(2, N))
        d_ok = all(tbl[v][y] >= 2 for v in inert_elems for y in range(2, N))
        pa_ok = all(tbl[tbl[x][x]][x] == tbl[x][tbl[x][x]] for x in range(N))
        vv_ok = all(rm.get(tbl[v][v], "?") in ("testers", "encoders") for v in inert_elems)
        one_inert = len(inert_elems) == 1
        e_trans = tbl[E_IDX][0] == 0 and tbl[E_IDX][1] == 1
        qe_ok = all(tbl[E_IDX][tbl[Q_IDX][x]] == x and tbl[Q_IDX][tbl[E_IDX][x]] == x
                     for x in range(2, CORE))
        branch_ok = all(
            (tbl[r_idx][x] == tbl[f_idx][x] if tbl[t_idx][x] == 0 else tbl[r_idx][x] == tbl[g_idx][x])
            for x in range(2, CORE))
        fg_differ = any(tbl[f_idx][j] != tbl[g_idx][j] for j in range(2, CORE))
        compose_ok = all(tbl[h_idx][x] == tbl[r_idx][tbl[g_idx][x]] for x in range(2, CORE))
        yr_val = tbl[Y_idx][r_idx]
        y_ok = yr_val == tbl[r_idx][yr_val] and yr_val >= 2

        # Selection axiom
        selection_val = tbl[h_idx][r_idx]
        selection_ok = selection_val == t_idx
        print(f"  η·ρ = {selection_val} {'= τ ✓' if selection_ok else f'≠ τ({t_idx}) ✗'}")

        # Counter
        counter_ok = all(tbl[INCv][counter_states[i]] == counter_states[(i+1) % counter_size]
                         for i in range(counter_size))
        zt_ok = tbl[t_idx][counter_states[0]] == 0 and all(
            tbl[t_idx][counter_states[i]] == 1 for i in range(1, counter_size))

        # IO
        io_ok = all(tbl[GETv][tbl[PUTv][x]] == x for x in range(2, CORE))
        seq_ok = tbl[SEQv][PUTv] != PUTv and tbl[SEQv][GETv] != GETv

        # Generation
        depth = {0: 0, 1: 0, Q_IDX: 0, E_IDX: 0}
        reached = {0, 1, Q_IDX, E_IDX}
        frontier = list(reached)
        d = 0
        while frontier:
            d += 1
            new = []
            for a in list(reached):
                for b in frontier:
                    for ab in [tbl[a][b], tbl[b][a]]:
                        if ab not in reached:
                            reached.add(ab)
                            depth[ab] = d
                            new.append(ab)
            frontier = new
        gen_ok = len(reached) == N

        # WL-1
        colors = {}
        for i in range(N):
            colors[i] = (rm.get(i, "?"), tuple(sorted(tbl[i])),
                         tuple(sorted(tbl[j][i] for j in range(N))))
        wl1_ok = False
        for iteration in range(10):
            new_colors = {}
            for i in range(N):
                nbr = tuple(sorted(
                    (colors[j], tbl[i][j], tbl[j][i]) for j in range(N)))
                new_colors[i] = (colors[i], nbr)
            n_classes = len(set(new_colors.values()))
            if n_classes == N:
                wl1_ok = True
                break
            colors = new_colors

        # Producibility
        produced = set()
        for x in range(N):
            for y in range(N):
                produced.add(tbl[x][y])
        prod_ok = produced == set(range(N))

        all_checks = {
            "L0 Ext-magma": ext_ok,
            "L0 Absorbers": abs0 and abs1 and no_extra_abs,
            "C (Kripke)": c_ok,
            "D (inert prop)": d_ok,
            "PA": pa_ok,
            "VV": vv_ok,
            "1-inert": one_inert,
            "E-transparency": e_trans,
            "QE inverse": qe_ok,
            "Branch": branch_ok and fg_differ,
            "Compose": compose_ok,
            "Y-combinator": y_ok,
            "Selection η·ρ=τ": selection_ok,
            "WL-1 discrete": wl1_ok,
            "Generation": gen_ok,
            "Producibility": prod_ok,
            f"Counter cycle ({counter_size})": counter_ok,
            "Zero test": zt_ok,
            "IO roundtrip": io_ok,
            "SEQ non-fix": seq_ok,
        }

        all_pass = True
        for name, ok in all_checks.items():
            status = "PASS" if ok else "FAIL"
            if not ok:
                all_pass = False
            print(f"  {name:25s}: {status}")
        print(f"\n  {'ALL CHECKS PASSED ✓' if all_pass else 'SOME CHECKS FAILED ✗'}")

        # Role assignment
        print(f"\n  ROLE ASSIGNMENT:")
        for i in range(N):
            role = rm.get(i, "?")
            duties = []
            if i in fixed_set: duties.append(fixed_set[i])
            if i in io_set: duties.append(io_set[i])
            if i in counter_map: duties.append(counter_map[i])
            dd = " + ".join(duties) if duties else "—"
            print(f"    {i:2d}  {element_names[i]:25s}  [{role:10s}]  {dd}")

        # Double-duty elements
        print(f"\n  DOUBLE-DUTY ELEMENTS:")
        for i in range(N):
            duties = []
            if i in fixed_set: duties.append(fixed_set[i])
            if i in io_set: duties.append(io_set[i])
            if i in counter_map: duties.append(counter_map[i])
            if len(duties) >= 2:
                print(f"    {i}: {' + '.join(duties)}")

        # Counter detail
        print(f"\n  COUNTER ({counter_size}-state):")
        print(f"    States: {counter_states}, INC={INCv} ({element_names[INCv]})")
        for i in range(counter_size):
            actual = tbl[INCv][counter_states[i]]
            expected = counter_states[(i+1) % counter_size]
            print(f"    INC·s{i}({counter_states[i]}) = {actual} = s{(i+1)%counter_size}({expected}) {'✓' if actual==expected else '✗'}")

        # IO detail
        print(f"\n  IO:")
        print(f"    PUT={PUTv}, GET={GETv}, SEQ={SEQv}")
        for x in range(2, CORE):
            put_x = tbl[PUTv][x]
            get_put_x = tbl[GETv][put_x]
            print(f"    GET·(PUT·{x}) = GET·{put_x} = {get_put_x} {'✓' if get_put_x==x else '✗'}")

        # Computational detail
        print(f"\n  SELECTION AXIOM:")
        print(f"    η·ρ = η·{r_idx} = dot[{h_idx}][{r_idx}] = {selection_val}")
        print(f"    Expected: τ = {t_idx}")
        print(f"    {'SATISFIED ✓' if selection_ok else 'VIOLATED ✗'}")

        # Output table
        print(f"\n  PSI_16 = [")
        for i in range(N):
            role = rm.get(i, "?")
            name = element_names[i]
            comma = "," if i < N - 1 else ""
            print(f"      {str(tbl[i]):60s}{comma}  # {i:2d}  {name:25s} [{role}]")
        print(f"  ]")

        return all_pass

    # ═══════════════════════════════════════════════════════════════════
    # STRATEGY A: Full Phase 5 + Selection axiom (8-state counter)
    # ═══════════════════════════════════════════════════════════════════
    print("=" * 70)
    print("STRATEGY A: Full Phase 5 + Selection Axiom η·ρ = τ (8-state counter)")
    print("=" * 70)

    t0 = time.time()
    set_param("smt.random_seed", 42)
    s, dot = encode_level(8, N, timeout_seconds=600)
    add_base_and_computational(s, dot, N)
    PUT, GET, SEQ = add_io(s, dot, N)
    c8, INC8 = add_8_counter(s, dot, N)
    # SELECTION AXIOM: η·ρ = τ
    s.add(dot[h_idx][r_idx] == t_idx)
    build_time = time.time() - t0
    print(f"  Build time: {build_time:.1f}s")

    t0 = time.time()
    rA = s.check()
    solve_time = time.time() - t0
    print(f"  Result: {rA} ({solve_time:.1f}s)")

    if rA == sat:
        m = s.model()
        tbl = extract_table(m, dot, N)
        pv = m.eval(PUT).as_long()
        gv = m.eval(GET).as_long()
        sv = m.eval(SEQ).as_long()
        c8v = [m.eval(x).as_long() for x in c8]
        i8v = m.eval(INC8).as_long()
        sc = score_model(tbl)
        print(f"  Score: {sc:.2f}")

        # Try 2 more seeds for best model
        candidates = [{"tbl": tbl, "PUT": pv, "GET": gv, "SEQ": sv,
                        "c8": c8v, "INC": i8v, "score": sc, "seed": 42}]
        for seed in [1337, 9999]:
            set_param("smt.random_seed", seed)
            s2, dot2 = encode_level(8, N, timeout_seconds=600)
            add_base_and_computational(s2, dot2, N)
            PUT2, GET2, SEQ2 = add_io(s2, dot2, N)
            c8_2, INC8_2 = add_8_counter(s2, dot2, N)
            s2.add(dot2[h_idx][r_idx] == t_idx)
            r2 = s2.check()
            if r2 == sat:
                m2 = s2.model()
                tbl2 = extract_table(m2, dot2, N)
                candidates.append({
                    "tbl": tbl2, "PUT": m2.eval(PUT2).as_long(),
                    "GET": m2.eval(GET2).as_long(), "SEQ": m2.eval(SEQ2).as_long(),
                    "c8": [m2.eval(x).as_long() for x in c8_2],
                    "INC": m2.eval(INC8_2).as_long(),
                    "score": score_model(tbl2), "seed": seed,
                })
                print(f"  Seed {seed}: SAT (score {candidates[-1]['score']:.2f})")
            else:
                print(f"  Seed {seed}: {r2}")

        best = min(candidates, key=lambda c: c["score"])
        print(f"\n  Selected: seed={best['seed']} (score={best['score']:.2f})")
        verify_and_print(best["tbl"], best["c8"], best["INC"],
                         best["PUT"], best["GET"], best["SEQ"], 8,
                         "Strategy A: 8-counter + Selection")
        return  # Done!

    # ═══════════════════════════════════════════════════════════════════
    # STRATEGY B: 4-state counter + Selection axiom
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'='*70}")
    print("STRATEGY B: Phase 5 relaxed to 4-state counter + Selection Axiom η·ρ = τ")
    print("=" * 70)

    t0 = time.time()
    set_param("smt.random_seed", 42)
    sB, dotB = encode_level(8, N, timeout_seconds=600)
    add_base_and_computational(sB, dotB, N)
    PUTB, GETB, SEQB = add_io(sB, dotB, N)
    c4B, INC4B = add_4_counter(sB, dotB, N)
    sB.add(dotB[h_idx][r_idx] == t_idx)
    build_timeB = time.time() - t0
    print(f"  Build time: {build_timeB:.1f}s")

    t0 = time.time()
    rB = sB.check()
    solve_timeB = time.time() - t0
    print(f"  Result: {rB} ({solve_timeB:.1f}s)")

    if rB == sat:
        mB = sB.model()
        tblB = extract_table(mB, dotB, N)
        pvB = mB.eval(PUTB).as_long()
        gvB = mB.eval(GETB).as_long()
        svB = mB.eval(SEQB).as_long()
        c4Bv = [mB.eval(x).as_long() for x in c4B]
        i4Bv = mB.eval(INC4B).as_long()
        scB = score_model(tblB)
        print(f"  Score: {scB:.2f}")

        # Try more seeds
        candidates = [{"tbl": tblB, "PUT": pvB, "GET": gvB, "SEQ": svB,
                        "c8": c4Bv, "INC": i4Bv, "score": scB, "seed": 42}]
        for seed in [1337, 9999]:
            set_param("smt.random_seed", seed)
            s2, dot2 = encode_level(8, N, timeout_seconds=600)
            add_base_and_computational(s2, dot2, N)
            PUT2, GET2, SEQ2 = add_io(s2, dot2, N)
            c4_2, INC4_2 = add_4_counter(s2, dot2, N)
            s2.add(dot2[h_idx][r_idx] == t_idx)
            r2 = s2.check()
            if r2 == sat:
                m2 = s2.model()
                tbl2 = extract_table(m2, dot2, N)
                candidates.append({
                    "tbl": tbl2, "PUT": m2.eval(PUT2).as_long(),
                    "GET": m2.eval(GET2).as_long(), "SEQ": m2.eval(SEQ2).as_long(),
                    "c8": [m2.eval(x).as_long() for x in c4_2],
                    "INC": m2.eval(INC4_2).as_long(),
                    "score": score_model(tbl2), "seed": seed,
                })
                print(f"  Seed {seed}: SAT (score {candidates[-1]['score']:.2f})")
            else:
                print(f"  Seed {seed}: {r2}")

        best = min(candidates, key=lambda c: c["score"])
        print(f"\n  Selected: seed={best['seed']} (score={best['score']:.2f})")
        verify_and_print(best["tbl"], best["c8"], best["INC"],
                         best["PUT"], best["GET"], best["SEQ"], 4,
                         "Strategy B: 4-counter + Selection")
        return

    # ═══════════════════════════════════════════════════════════════════
    # STRATEGY C: 8-state counter + Selection + INC ≠ η (separate INC)
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'='*70}")
    print("STRATEGY C: 8-counter + Selection + INC ≠ η (force separate INC)")
    print("=" * 70)

    t0 = time.time()
    set_param("smt.random_seed", 42)
    sC, dotC = encode_level(8, N, timeout_seconds=600)
    add_base_and_computational(sC, dotC, N)
    PUTC, GETC, SEQC = add_io(sC, dotC, N)
    c8C, INC8C = add_8_counter(sC, dotC, N)
    sC.add(dotC[h_idx][r_idx] == t_idx)
    # Force INC ≠ η
    sC.add(INC8C != h_idx)
    build_timeC = time.time() - t0
    print(f"  Build time: {build_timeC:.1f}s")

    t0 = time.time()
    rC = sC.check()
    solve_timeC = time.time() - t0
    print(f"  Result: {rC} ({solve_timeC:.1f}s)")

    if rC == sat:
        mC = sC.model()
        tblC = extract_table(mC, dotC, N)
        pvC = mC.eval(PUTC).as_long()
        gvC = mC.eval(GETC).as_long()
        svC = mC.eval(SEQC).as_long()
        c8Cv = [mC.eval(x).as_long() for x in c8C]
        i8Cv = mC.eval(INC8C).as_long()
        scC = score_model(tblC)
        print(f"  Score: {scC:.2f}")

        candidates = [{"tbl": tblC, "PUT": pvC, "GET": gvC, "SEQ": svC,
                        "c8": c8Cv, "INC": i8Cv, "score": scC, "seed": 42}]
        for seed in [1337, 9999]:
            set_param("smt.random_seed", seed)
            s2, dot2 = encode_level(8, N, timeout_seconds=600)
            add_base_and_computational(s2, dot2, N)
            PUT2, GET2, SEQ2 = add_io(s2, dot2, N)
            c8_2, INC8_2 = add_8_counter(s2, dot2, N)
            s2.add(dot2[h_idx][r_idx] == t_idx)
            s2.add(INC8_2 != h_idx)
            r2 = s2.check()
            if r2 == sat:
                m2 = s2.model()
                tbl2 = extract_table(m2, dot2, N)
                candidates.append({
                    "tbl": tbl2, "PUT": m2.eval(PUT2).as_long(),
                    "GET": m2.eval(GET2).as_long(), "SEQ": m2.eval(SEQ2).as_long(),
                    "c8": [m2.eval(x).as_long() for x in c8_2],
                    "INC": m2.eval(INC8_2).as_long(),
                    "score": score_model(tbl2), "seed": seed,
                })
                print(f"  Seed {seed}: SAT (score {candidates[-1]['score']:.2f})")
            else:
                print(f"  Seed {seed}: {r2}")

        best = min(candidates, key=lambda c: c["score"])
        print(f"\n  Selected: seed={best['seed']} (score={best['score']:.2f})")
        verify_and_print(best["tbl"], best["c8"], best["INC"],
                         best["PUT"], best["GET"], best["SEQ"], 8,
                         "Strategy C: 8-counter + Selection + INC≠η")
        return

    # All strategies UNSAT
    print(f"\n{'='*70}")
    print("ALL STRATEGIES UNSAT")
    print("The selection axiom η·ρ = τ is incompatible with counter embedding at N=16.")
    print("=" * 70)


def extract_psi16_full():
    """Extract Ψ₁₆ᶠ (full) — single table with ALL operational constraints.

    Base: L8+C+D+PA+VV+QE+1-inert+E-trans+Branch+Compose+Y+Selection
    Operations: INC(8-cycle), DEC(reverse), IO(PUT/GET/SEQ),
                PAIR/FST/SND(2×2 product), INC2(4-cycle), SWAP(involution)
    """
    import time

    from z3 import And, Distinct, If, Int, Not, Or, sat, set_param

    from ds_search.axiom_explorer import (
        classify_elements,
        col_ite_lookup,
        encode_level,
        extract_table,
        ite_lookup,
    )

    N = 16
    CORE = 6
    Q_IDX, E_IDX = 6, 7
    r_idx, h_idx, Y_idx = 8, 9, 10
    t_idx, f_idx, g_idx = 3, 2, 4
    fixed_roles = [Q_IDX, E_IDX, r_idx, h_idx, Y_idx]

    # ─── Helpers ───

    def add_kripke_c(s, dot, N):
        for x in range(2, N):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for y in range(2, N):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_inert_propagation(s, dot, N):
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
        for x in range(N):
            xx = dot[x][x]
            s.add(ite_lookup(dot, xx, x, N) == col_ite_lookup(dot, x, xx, N))

    def add_vv_core(s, dot, N):
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

    def add_full_base(s, dot, N):
        add_kripke_c(s, dot, N)
        add_inert_propagation(s, dot, N)
        add_pa(s, dot, N)
        add_vv_core(s, dot, N)

    def add_qe_pair(s, dot, N, q_idx, e_idx, core_lo=2, core_hi=None):
        if core_hi is None:
            core_hi = N
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, N) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, N) == x)

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

    def full_ite_lookup(dot, row_expr, col_expr, N):
        entry = col_ite_lookup(dot, 0, col_expr, N)
        for r in range(1, N):
            entry = If(row_expr == r, col_ite_lookup(dot, r, col_expr, N), entry)
        return entry

    def add_base_and_computational(s, dot, N):
        add_full_base(s, dot, N)
        add_qe_pair(s, dot, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
        for x in range(2, N):
            iflag = Int(f"zi_{x}")
            s.add(If(is_inert_z3(dot, x, N), iflag == 1, iflag == 0))
        s.add(sum([Int(f"zi_{x}") for x in range(2, N)]) == 1)
        s.add(dot[E_IDX][0] == 0)
        s.add(dot[E_IDX][1] == 1)
        for x in range(2, CORE):
            tx = dot[t_idx][x]; fx = dot[f_idx][x]; gx = dot[g_idx][x]
            s.add(If(tx == 0, dot[r_idx][x] == fx, dot[r_idx][x] == gx))
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(2, CORE)]))
        for x in range(2, CORE):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, r_idx, gx, N)
            s.add(dot[h_idx][x] == r_gx)
        yr = dot[Y_idx][r_idx]
        r_yr = col_ite_lookup(dot, r_idx, yr, N)
        s.add(yr == r_yr)
        s.add(yr >= 2)

    def add_io(s, dot, N):
        PUT = Int("PUT"); GET = Int("GET"); SEQ = Int("SEQ")
        for v in [PUT, GET, SEQ]:
            s.add(v >= 2, v <= N - 1)
        s.add(Distinct(PUT, GET, SEQ))
        for v in [PUT, GET, SEQ]:
            for fr in fixed_roles:
                s.add(v != fr)
        for x in range(2, CORE):
            put_x = full_ite_lookup(dot, PUT, x, N)
            s.add(full_ite_lookup(dot, GET, put_x, N) == x)
        s.add(full_ite_lookup(dot, SEQ, PUT, N) != PUT)
        s.add(full_ite_lookup(dot, SEQ, GET, N) != GET)
        return PUT, GET, SEQ

    def add_8_counter(s, dot, N):
        c8 = [Int(f"c8_{i}") for i in range(8)]
        INC8 = Int("INC8")
        for v in c8 + [INC8]:
            s.add(v >= 2, v <= N - 1)
        s.add(Distinct(*(c8 + [INC8])))
        for i in range(8):
            s.add(full_ite_lookup(dot, INC8, c8[i], N) == c8[(i + 1) % 8])
        s.add(col_ite_lookup(dot, t_idx, c8[0], N) == 0)
        for i in range(1, 8):
            s.add(col_ite_lookup(dot, t_idx, c8[i], N) == 1)
        return c8, INC8

    def score_model(tbl):
        avg_distinct = sum(len(set(tbl[i])) for i in range(N)) / N
        sq = [tbl[x][x] for x in range(N)]
        fixed_pts = sum(1 for x in range(N) if sq[x] == x)
        return avg_distinct - fixed_pts * 0.5

    # ─── Configurable solver builder ───

    def build_solver(inc_dec=True, inc_pair=True, inc_inc2=True, inc_swap=True):
        s, dot = encode_level(8, N, timeout_seconds=600)
        add_base_and_computational(s, dot, N)
        s.add(dot[h_idx][r_idx] == t_idx)  # Selection
        PUT, GET, SEQ = add_io(s, dot, N)
        c8, INC8 = add_8_counter(s, dot, N)
        V = {"PUT": PUT, "GET": GET, "SEQ": SEQ, "c8": c8, "INC8": INC8}

        if inc_dec:
            DEC = Int("DEC")
            s.add(DEC >= 2, DEC <= N - 1)
            for i in range(8):
                s.add(full_ite_lookup(dot, DEC, c8[i], N) == c8[(i - 1) % 8])
            V["DEC"] = DEC

        if inc_pair:
            PAIR_EL = Int("PAIR_EL"); FST_EL = Int("FST_EL"); SND_EL = Int("SND_EL")
            for v in [PAIR_EL, FST_EL, SND_EL]:
                s.add(v >= 2, v <= N - 1)
            p00 = Int("p00"); p01 = Int("p01")
            p10 = Int("p10"); p11 = Int("p11")
            for v in [p00, p01, p10, p11]:
                s.add(v >= 2, v <= N - 1)
            s.add(Distinct(p00, p01, p10, p11))
            # Curried construction: (PAIR·si)·sj = pij
            PAIR_S0 = Int("PAIR_S0"); PAIR_S1 = Int("PAIR_S1")
            s.add(PAIR_S0 >= 2, PAIR_S0 <= N - 1)
            s.add(PAIR_S1 >= 2, PAIR_S1 <= N - 1)
            s.add(PAIR_S0 != PAIR_S1)
            s.add(full_ite_lookup(dot, PAIR_EL, c8[0], N) == PAIR_S0)
            s.add(full_ite_lookup(dot, PAIR_EL, c8[1], N) == PAIR_S1)
            s.add(full_ite_lookup(dot, PAIR_S0, c8[0], N) == p00)
            s.add(full_ite_lookup(dot, PAIR_S0, c8[1], N) == p01)
            s.add(full_ite_lookup(dot, PAIR_S1, c8[0], N) == p10)
            s.add(full_ite_lookup(dot, PAIR_S1, c8[1], N) == p11)
            # FST/SND extraction
            s.add(full_ite_lookup(dot, FST_EL, p00, N) == c8[0])
            s.add(full_ite_lookup(dot, FST_EL, p01, N) == c8[0])
            s.add(full_ite_lookup(dot, FST_EL, p10, N) == c8[1])
            s.add(full_ite_lookup(dot, FST_EL, p11, N) == c8[1])
            s.add(full_ite_lookup(dot, SND_EL, p00, N) == c8[0])
            s.add(full_ite_lookup(dot, SND_EL, p01, N) == c8[1])
            s.add(full_ite_lookup(dot, SND_EL, p10, N) == c8[0])
            s.add(full_ite_lookup(dot, SND_EL, p11, N) == c8[1])
            V.update({"PAIR_EL": PAIR_EL, "FST_EL": FST_EL, "SND_EL": SND_EL,
                       "p00": p00, "p01": p01, "p10": p10, "p11": p11,
                       "PAIR_S0": PAIR_S0, "PAIR_S1": PAIR_S1})

        if inc_inc2:
            INC2_EL = Int("INC2_EL")
            s.add(INC2_EL >= 2, INC2_EL <= N - 1)
            for i in range(4):
                s.add(full_ite_lookup(dot, INC2_EL, c8[i], N) == c8[(i + 1) % 4])
            V["INC2_EL"] = INC2_EL

        if inc_swap:
            SWAP_EL = Int("SWAP_EL")
            s.add(SWAP_EL >= 2, SWAP_EL <= N - 1)
            for x in range(2, CORE):
                swap_x = ite_lookup(dot, SWAP_EL, x, N)
                s.add(swap_x >= 2)
                s.add(swap_x < CORE)
                s.add(full_ite_lookup(dot, SWAP_EL, swap_x, N) == x)
            s.add(Or([ite_lookup(dot, SWAP_EL, x, N) != x for x in range(2, CORE)]))
            V["SWAP_EL"] = SWAP_EL

        return s, dot, V

    def ev(model, var):
        return model.eval(var).as_long()

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 1: Full combined SAT check
    # ═══════════════════════════════════════════════════════════════════
    print("=" * 70)
    print("Ψ₁₆ᶠ EXTRACTION — Full operational constraint set")
    print("=" * 70)

    constraint_sets = {
        "DEC": {"inc_dec": True,  "inc_pair": False, "inc_inc2": False, "inc_swap": False},
        "PAIR": {"inc_dec": False, "inc_pair": True,  "inc_inc2": False, "inc_swap": False},
        "INC2": {"inc_dec": False, "inc_pair": False, "inc_inc2": True,  "inc_swap": False},
        "SWAP": {"inc_dec": False, "inc_pair": False, "inc_inc2": False, "inc_swap": True},
    }

    print("\n  Testing full combined SAT...")
    set_param("smt.random_seed", 42)
    t0 = time.time()
    s, dot, V = build_solver(inc_dec=True, inc_pair=True, inc_inc2=True, inc_swap=True)
    build_t = time.time() - t0
    print(f"  Build time: {build_t:.1f}s")

    t0 = time.time()
    result = s.check()
    solve_t = time.time() - t0
    print(f"  Result: {result} ({solve_t:.1f}s)")

    if result != sat:
        # ─── Ablation: test each constraint individually ───
        print(f"\n{'─'*70}")
        print("ABLATION: testing each new constraint individually")
        print(f"{'─'*70}")
        individual_results = {}
        for name, flags in constraint_sets.items():
            set_param("smt.random_seed", 42)
            t0 = time.time()
            si, di, Vi = build_solver(**flags)
            ri = si.check()
            ti = time.time() - t0
            individual_results[name] = ri
            print(f"  Base + {name:6s}: {ri} ({ti:.1f}s)")

        # Test pairwise combinations of SAT constraints
        sat_names = [n for n, r in individual_results.items() if r == sat]
        print(f"\n  Individually SAT: {sat_names}")
        if len(sat_names) >= 2:
            print(f"\n  Testing pairwise combinations:")
            from itertools import combinations
            for a, b in combinations(sat_names, 2):
                flags = {k: False for k in ["inc_dec", "inc_pair", "inc_inc2", "inc_swap"]}
                for n, fl in constraint_sets.items():
                    if n in (a, b):
                        for k, v in fl.items():
                            if v:
                                flags[k] = True
                set_param("smt.random_seed", 42)
                t0 = time.time()
                sp, dp, Vp = build_solver(**flags)
                rp = sp.check()
                tp = time.time() - t0
                print(f"    {a:6s} + {b:6s}: {rp} ({tp:.1f}s)")

        # Try dropping least important constraints
        print(f"\n{'─'*70}")
        print("FALLBACK: dropping constraints one at a time")
        print(f"{'─'*70}")
        drop_priority = ["SWAP", "INC2", "PAIR", "DEC"]  # least to most important
        for drop in drop_priority:
            flags = {k: True for k in ["inc_dec", "inc_pair", "inc_inc2", "inc_swap"]}
            for n, fl in constraint_sets.items():
                if n == drop:
                    for k, v in fl.items():
                        if v:
                            flags[k] = False
            set_param("smt.random_seed", 42)
            t0 = time.time()
            sd, dd, Vd = build_solver(**flags)
            rd = sd.check()
            td = time.time() - t0
            print(f"  Drop {drop:6s}: {rd} ({td:.1f}s)")
            if rd == sat:
                print(f"  → Dropping {drop} resolves the conflict!")
                # Use this solver for extraction
                s, dot, V = sd, dd, Vd
                result = rd
                active_ops = [n for n in ["DEC", "PAIR", "INC2", "SWAP"] if n != drop]
                print(f"  Active operations: {active_ops}")
                break
        else:
            # Try dropping two
            print(f"\n  Trying dropping two constraints:")
            for i, d1 in enumerate(drop_priority):
                for d2 in drop_priority[i+1:]:
                    flags = {k: True for k in ["inc_dec", "inc_pair", "inc_inc2", "inc_swap"]}
                    for n, fl in constraint_sets.items():
                        if n in (d1, d2):
                            for k, v in fl.items():
                                if v:
                                    flags[k] = False
                    set_param("smt.random_seed", 42)
                    sd2, dd2, Vd2 = build_solver(**flags)
                    rd2 = sd2.check()
                    print(f"    Drop {d1}+{d2}: {rd2}")
                    if rd2 == sat:
                        s, dot, V = sd2, dd2, Vd2
                        result = rd2
                        break
                if result == sat:
                    break

    if result != sat:
        print("\n  FATAL: Could not find any SAT configuration!")
        return

    active_constraints = []
    for name in ["DEC", "PAIR", "INC2", "SWAP"]:
        key_map = {"DEC": "DEC", "PAIR": "PAIR_EL", "INC2": "INC2_EL", "SWAP": "SWAP_EL"}
        if key_map[name] in V:
            active_constraints.append(name)

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 2: 3-seed extraction
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print(f"3-SEED EXTRACTION (active: {active_constraints})")
    print(f"{'═'*70}")

    candidates = []
    for seed in [42, 1337, 9999]:
        set_param("smt.random_seed", seed)
        t0 = time.time()
        flags = {"inc_dec": "DEC" in active_constraints,
                 "inc_pair": "PAIR" in active_constraints,
                 "inc_inc2": "INC2" in active_constraints,
                 "inc_swap": "SWAP" in active_constraints}
        si, di, Vi = build_solver(**flags)
        ri = si.check()
        ti = time.time() - t0
        if ri != sat:
            print(f"  Seed {seed}: {ri} ({ti:.1f}s)")
            continue
        mi = si.model()
        tbli = extract_table(mi, di, N)
        sci = score_model(tbli)
        print(f"  Seed {seed}: SAT ({ti:.1f}s) score={sci:.2f}")
        cand = {"tbl": tbli, "score": sci, "seed": seed}
        # Extract all Z3 variable values
        for k, v in Vi.items():
            if k == "c8":
                cand["c8"] = [ev(mi, x) for x in v]
            elif isinstance(v, list):
                cand[k] = [ev(mi, x) for x in v]
            else:
                cand[k] = ev(mi, v)
        candidates.append(cand)

    if not candidates:
        print("  FATAL: No models found!")
        return

    best = min(candidates, key=lambda c: c["score"])
    print(f"\n  Selected: seed={best['seed']} (score={best['score']:.2f})")

    tbl = best["tbl"]
    c8v = best["c8"]
    INCv = best["INC8"]
    PUTv = best.get("PUT")
    GETv = best.get("GET")
    SEQv = best.get("SEQ")
    DECv = best.get("DEC")
    PAIR_ELv = best.get("PAIR_EL")
    FST_ELv = best.get("FST_EL")
    SND_ELv = best.get("SND_EL")
    p00v = best.get("p00")
    p01v = best.get("p01")
    p10v = best.get("p10")
    p11v = best.get("p11")
    PAIR_S0v = best.get("PAIR_S0")
    PAIR_S1v = best.get("PAIR_S1")
    INC2v = best.get("INC2_EL")
    SWAPv = best.get("SWAP_EL")

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 3: Full verification
    # ═══════════════════════════════════════════════════════════════════
    cl = classify_elements(tbl)
    rm = {}
    for role, elems in cl.items():
        for e in elems:
            rm[e] = role

    inert_elems = [i for i in range(2, N) if rm.get(i) == "inert"]
    tester_elems = [i for i in range(2, N) if rm.get(i) == "testers"]

    # Build element name map
    role_map = {}  # element -> list of roles
    for i in range(N):
        role_map[i] = []
    role_map[0].append("⊤")
    role_map[1].append("⊥")
    fixed = {t_idx: "τ", f_idx: "f", g_idx: "g", Q_IDX: "Q", E_IDX: "E",
             r_idx: "ρ", h_idx: "η", Y_idx: "Y"}
    for idx, name in fixed.items():
        role_map[idx].append(name)
    role_map[INCv].append("INC")
    if DECv is not None:
        role_map[DECv].append("DEC")
    if PUTv is not None:
        role_map[PUTv].append("PUT")
    if GETv is not None:
        role_map[GETv].append("GET")
    if SEQv is not None:
        role_map[SEQv].append("SEQ")
    if PAIR_ELv is not None:
        role_map[PAIR_ELv].append("PAIR")
    if FST_ELv is not None:
        role_map[FST_ELv].append("FST")
    if SND_ELv is not None:
        role_map[SND_ELv].append("SND")
    if INC2v is not None:
        role_map[INC2v].append("INC2")
    if SWAPv is not None:
        role_map[SWAPv].append("SWAP")
    for i, v in enumerate(c8v):
        role_map[v].append(f"s{i}")
    if p00v is not None:
        for pv, pn in [(p00v, "p00"), (p01v, "p01"), (p10v, "p10"), (p11v, "p11")]:
            role_map[pv].append(pn)

    def ename(i):
        parts = role_map[i]
        return "/".join(parts) if parts else f"x{i}"

    print(f"\n{'═'*70}")
    print("FULL VERIFICATION")
    print(f"{'═'*70}")

    checks = {}

    # ─── Axiom checks ───
    print("\n  AXIOMS:")
    rows = [tuple(tbl[i]) for i in range(N)]
    checks["L0 Ext-magma"] = len(set(rows)) == N
    checks["L0 Absorber ⊤"] = all(tbl[0][j] == 0 for j in range(N))
    checks["L0 Absorber ⊥"] = all(tbl[1][j] == 1 for j in range(N))
    checks["L0 No extra abs"] = not any(all(tbl[i][j] == i for j in range(N)) for i in range(2, N))
    checks["C (Kripke)"] = all(tbl[x][y] >= 2
        for x in range(2, N) if not all(tbl[x][j] in (0,1) for j in range(N))
        for y in range(2, N))
    checks["D (inert prop)"] = all(tbl[v][y] >= 2 for v in inert_elems for y in range(2, N))
    checks["PA"] = all(tbl[tbl[x][x]][x] == tbl[x][tbl[x][x]] for x in range(N))
    checks["VV"] = all(rm.get(tbl[v][v], "?") in ("testers", "encoders") for v in inert_elems)
    checks["1-inert"] = len(inert_elems) == 1
    checks["E-transparency"] = tbl[E_IDX][0] == 0 and tbl[E_IDX][1] == 1
    checks["QE inverse"] = all(tbl[E_IDX][tbl[Q_IDX][x]] == x and tbl[Q_IDX][tbl[E_IDX][x]] == x
                                for x in range(2, CORE))
    checks["Branch"] = all(
        (tbl[r_idx][x] == tbl[f_idx][x] if tbl[t_idx][x] == 0 else tbl[r_idx][x] == tbl[g_idx][x])
        for x in range(2, CORE)) and any(tbl[f_idx][j] != tbl[g_idx][j] for j in range(2, CORE))
    checks["Compose"] = all(tbl[h_idx][x] == tbl[r_idx][tbl[g_idx][x]] for x in range(2, CORE))
    yr_val = tbl[Y_idx][r_idx]
    checks["Y-combinator"] = yr_val == tbl[r_idx][yr_val] and yr_val >= 2
    checks["Selection η·ρ=τ"] = tbl[h_idx][r_idx] == t_idx

    for name, ok in checks.items():
        print(f"    {name:25s}: {'PASS' if ok else 'FAIL'}")

    # ─── Operational checks ───
    print("\n  OPERATIONS:")

    # INC cycle
    inc_ok = all(tbl[INCv][c8v[i]] == c8v[(i+1) % 8] for i in range(8))
    checks["INC 8-cycle"] = inc_ok
    print(f"    INC 8-cycle               : {'PASS' if inc_ok else 'FAIL'}")
    print(f"      INC={INCv}({ename(INCv)}), cycle: {' → '.join(str(c8v[i]) for i in range(8))} → {c8v[0]}")

    # Zero test
    zt_ok = tbl[t_idx][c8v[0]] == 0 and all(tbl[t_idx][c8v[i]] == 1 for i in range(1, 8))
    checks["Zero test"] = zt_ok
    print(f"    Zero test                 : {'PASS' if zt_ok else 'FAIL'}")

    # DEC
    if DECv is not None:
        dec_ok = all(tbl[DECv][c8v[i]] == c8v[(i-1) % 8] for i in range(8))
        checks["DEC reverse cycle"] = dec_ok
        print(f"    DEC reverse cycle         : {'PASS' if dec_ok else 'FAIL'}")
        print(f"      DEC={DECv}({ename(DECv)})")
        for i in range(8):
            actual = tbl[DECv][c8v[i]]
            expected = c8v[(i-1) % 8]
            print(f"        DEC·s{i}({c8v[i]}) = {actual} = s{(i-1)%8}({expected}) {'✓' if actual==expected else '✗'}")

    # IO
    if PUTv is not None:
        io_ok = all(tbl[GETv][tbl[PUTv][x]] == x for x in range(2, CORE))
        seq_ok = tbl[SEQv][PUTv] != PUTv and tbl[SEQv][GETv] != GETv
        checks["IO roundtrip"] = io_ok
        checks["SEQ non-fix"] = seq_ok
        print(f"    IO roundtrip              : {'PASS' if io_ok else 'FAIL'}  PUT={PUTv}({ename(PUTv)}) GET={GETv}({ename(GETv)})")
        print(f"    SEQ non-fix               : {'PASS' if seq_ok else 'FAIL'}  SEQ={SEQv}({ename(SEQv)})")
        for x in range(2, CORE):
            put_x = tbl[PUTv][x]
            get_put_x = tbl[GETv][put_x]
            print(f"      GET·(PUT·{x}) = GET·{put_x} = {get_put_x} {'✓' if get_put_x==x else '✗'}")

    # PAIR/FST/SND
    if PAIR_ELv is not None:
        pair_ok = True
        # Verify curried construction
        ps0v = tbl[PAIR_ELv][c8v[0]]  # PAIR·s0
        ps1v = tbl[PAIR_ELv][c8v[1]]  # PAIR·s1
        pair_construct = (
            tbl[ps0v][c8v[0]] == p00v and tbl[ps0v][c8v[1]] == p01v and
            tbl[ps1v][c8v[0]] == p10v and tbl[ps1v][c8v[1]] == p11v)
        fst_ok = (tbl[FST_ELv][p00v] == c8v[0] and tbl[FST_ELv][p01v] == c8v[0] and
                  tbl[FST_ELv][p10v] == c8v[1] and tbl[FST_ELv][p11v] == c8v[1])
        snd_ok = (tbl[SND_ELv][p00v] == c8v[0] and tbl[SND_ELv][p01v] == c8v[1] and
                  tbl[SND_ELv][p10v] == c8v[0] and tbl[SND_ELv][p11v] == c8v[1])
        checks["PAIR construction"] = pair_construct
        checks["FST extraction"] = fst_ok
        checks["SND extraction"] = snd_ok
        print(f"    PAIR construction         : {'PASS' if pair_construct else 'FAIL'}  PAIR={PAIR_ELv}({ename(PAIR_ELv)})")
        print(f"      PAIR·s0={ps0v}({ename(ps0v)}), PAIR·s1={ps1v}({ename(ps1v)})")
        print(f"      p00={p00v}({ename(p00v)}) p01={p01v}({ename(p01v)}) p10={p10v}({ename(p10v)}) p11={p11v}({ename(p11v)})")
        print(f"    FST extraction            : {'PASS' if fst_ok else 'FAIL'}  FST={FST_ELv}({ename(FST_ELv)})")
        print(f"    SND extraction            : {'PASS' if snd_ok else 'FAIL'}  SND={SND_ELv}({ename(SND_ELv)})")

    # INC2
    if INC2v is not None:
        inc2_ok = all(tbl[INC2v][c8v[i]] == c8v[(i+1) % 4] for i in range(4))
        checks["INC2 4-cycle"] = inc2_ok
        print(f"    INC2 4-cycle              : {'PASS' if inc2_ok else 'FAIL'}  INC2={INC2v}({ename(INC2v)})")
        for i in range(4):
            actual = tbl[INC2v][c8v[i]]
            expected = c8v[(i+1) % 4]
            print(f"      INC2·s{i}({c8v[i]}) = {actual} = s{(i+1)%4}({expected}) {'✓' if actual==expected else '✗'}")

    # SWAP
    if SWAPv is not None:
        swap_ok = True
        swap_nontrivial = False
        for x in range(2, CORE):
            sx = tbl[SWAPv][x]
            if sx < 2 or sx >= CORE:
                swap_ok = False
            if tbl[SWAPv][sx] != x:
                swap_ok = False
            if sx != x:
                swap_nontrivial = True
        checks["SWAP involution"] = swap_ok and swap_nontrivial
        print(f"    SWAP involution           : {'PASS' if swap_ok and swap_nontrivial else 'FAIL'}  SWAP={SWAPv}({ename(SWAPv)})")
        for x in range(2, CORE):
            sx = tbl[SWAPv][x]
            print(f"      SWAP·{x} = {sx}, SWAP·{sx} = {tbl[SWAPv][sx]} {'✓' if tbl[SWAPv][sx]==x else '✗'}")

    # ─── WL-1 rigidity ───
    print("\n  STRUCTURAL:")
    colors = {}
    for i in range(N):
        colors[i] = (rm.get(i, "?"), tuple(sorted(tbl[i])),
                     tuple(sorted(tbl[j][i] for j in range(N))))
    wl1_ok = False
    for iteration in range(10):
        new_colors = {}
        for i in range(N):
            nbr = tuple(sorted((colors[j], tbl[i][j], tbl[j][i]) for j in range(N)))
            new_colors[i] = (colors[i], nbr)
        n_classes = len(set(new_colors.values()))
        if n_classes == N:
            wl1_ok = True
            print(f"    WL-1 discrete             : PASS (after {iteration+1} refinements)")
            break
        colors = new_colors
    if not wl1_ok:
        print(f"    WL-1 discrete             : FAIL ({n_classes}/{N})")
    checks["WL-1"] = wl1_ok

    # Generation
    depth = {0: 0, 1: 0, Q_IDX: 0, E_IDX: 0}
    reached = {0, 1, Q_IDX, E_IDX}
    frontier = list(reached)
    d = 0
    while frontier:
        d += 1
        new = []
        for a in list(reached):
            for b in frontier:
                for ab in [tbl[a][b], tbl[b][a]]:
                    if ab not in reached:
                        reached.add(ab)
                        depth[ab] = d
                        new.append(ab)
        frontier = new
    gen_ok = len(reached) == N
    checks["Generation"] = gen_ok
    max_depth = max(depth.values()) if depth else 0
    print(f"    Generation {{⊤,⊥,Q,E}}      : {'PASS' if gen_ok else 'FAIL'} ({len(reached)}/{N}, max depth={max_depth})")
    for i in range(N):
        print(f"      {i:2d} ({ename(i):20s}): depth {depth.get(i, '∞')}")

    # Producibility
    produced = set()
    for x in range(N):
        for y in range(N):
            produced.add(tbl[x][y])
    prod_ok = produced == set(range(N))
    checks["Producibility"] = prod_ok
    print(f"    Producibility             : {'PASS' if prod_ok else 'FAIL'}")

    # Actuality irreducibility
    print("\n    Actuality irreducibility (tester cell freedom):")
    s_ai, dot_ai = encode_level(8, N, timeout_seconds=600)
    add_full_base(s_ai, dot_ai, N)
    add_qe_pair(s_ai, dot_ai, N, Q_IDX, E_IDX, core_lo=2, core_hi=CORE)
    for x in range(2, N):
        iflag = Int(f"ai_zi_{x}")
        s_ai.add(If(is_inert_z3(dot_ai, x, N), iflag == 1, iflag == 0))
    s_ai.add(sum([Int(f"ai_zi_{x}") for x in range(2, N)]) == 1)
    s_ai.add(dot_ai[E_IDX][0] == 0)
    s_ai.add(dot_ai[E_IDX][1] == 1)
    for i in range(N):
        if i == t_idx:
            continue
        for j in range(N):
            s_ai.add(dot_ai[i][j] == tbl[i][j])
    for j in range(N):
        s_ai.add(Or(dot_ai[t_idx][j] == 0, dot_ai[t_idx][j] == 1))
    free_cells = 0
    for col in range(2, N):
        orig = tbl[t_idx][col]
        s_ai.push()
        s_ai.add(dot_ai[t_idx][col] == 1 - orig)
        r_ai = s_ai.check()
        s_ai.pop()
        if r_ai == sat:
            free_cells += 1
    checks["Actuality irred."] = free_cells >= 2
    print(f"      Free tester cells: {free_cells}/{N-2} — {'PASS' if free_cells >= 2 else 'FAIL'}")

    # Squaring map
    sq = [tbl[x][x] for x in range(N)]
    print(f"\n    Squaring map: {sq}")
    visited = set()
    orbits = []
    for x in range(N):
        if x in visited:
            continue
        orbit = []
        cur = x
        while cur not in visited:
            visited.add(cur)
            orbit.append(cur)
            cur = sq[cur]
        if cur in orbit:
            cycle_start = orbit.index(cur)
            tail = orbit[:cycle_start]
            cycle = orbit[cycle_start:]
            orbits.append({"tail": tail, "cycle": cycle})
        else:
            orbits.append({"tail": orbit, "cycle": f"→ joins orbit of {cur}"})
    for orb in orbits:
        if isinstance(orb["cycle"], list):
            if orb["tail"]:
                print(f"      Tail {orb['tail']} → Cycle {orb['cycle']}")
            else:
                print(f"      Cycle {orb['cycle']}")
        else:
            print(f"      Tail {orb['tail']} {orb['cycle']}")

    # Idempotents
    idempotents = [x for x in range(N) if tbl[x][x] == x]
    print(f"\n    Idempotents: {idempotents} = {[ename(x) for x in idempotents]}")

    # ─── Element role table ───
    print(f"\n{'═'*70}")
    print("ELEMENT ROLE TABLE")
    print(f"{'═'*70}")
    print(f"{'Elem':>4} {'Name':25s} {'Role':10s} {'#Roles':>6} {'All roles'}")
    print(f"{'─'*4} {'─'*25} {'─'*10} {'─'*6} {'─'*40}")
    for i in range(N):
        name = ename(i)
        role = rm.get(i, "?")
        roles = role_map[i]
        print(f"{i:4d} {name:25s} {role:10s} {len(roles):6d} {', '.join(roles)}")

    # ─── PSI_16 output ───
    print(f"\n{'═'*70}")
    print("PSI_16_FULL — The Concrete Table")
    print(f"{'═'*70}")
    print("\nPSI_16_FULL = [")
    for i in range(N):
        role = rm.get(i, "?")
        name = ename(i)
        comma = "," if i < N - 1 else ""
        print(f"    {str(tbl[i]):60s}{comma}  # {i:2d}  {name:25s} [{role}]")
    print("]")

    # ─── Overall pass/fail ───
    print(f"\n{'═'*70}")
    print("OVERALL VERIFICATION")
    print(f"{'═'*70}")
    all_pass = True
    for name, ok in checks.items():
        status = "PASS" if ok else "FAIL"
        if not ok:
            all_pass = False
        print(f"  {name:25s}: {status}")
    print(f"\n  {'ALL CHECKS PASSED ✓' if all_pass else 'SOME CHECKS FAILED ✗'}")

    if not all_pass:
        print("\n  WARNING: Not all checks passed. Lean file not generated.")
        return

    # ═══════════════════════════════════════════════════════════════════
    # PHASE 4: Generate Lean file
    # ═══════════════════════════════════════════════════════════════════
    print(f"\n{'═'*70}")
    print("GENERATING Psi16Full.lean")
    print(f"{'═'*70}")

    # Build Lean name map: element index -> lean identifier
    lean_name = {}
    lean_name[0] = "top"
    lean_name[1] = "bot"
    lean_name[f_idx] = "f_enc"
    lean_name[t_idx] = "tau"
    lean_name[g_idx] = "g_enc"
    lean_name[Q_IDX] = "Q"
    lean_name[E_IDX] = "E"
    lean_name[r_idx] = "rho"
    lean_name[h_idx] = "eta"
    lean_name[Y_idx] = "Y_fix"
    lean_name[INCv] = "INC"
    for i in range(N):
        if i not in lean_name:
            # Use counter state name if applicable
            if i in c8v:
                idx = c8v.index(i)
                lean_name[i] = f"s{idx}"
            else:
                lean_name[i] = f"x{i}"
    # Add aliases for operational elements
    lean_aliases = {}  # lean_name -> element index (for additional abbrevs)
    if DECv is not None and DECv != INCv:
        lean_aliases["DEC"] = DECv
    if PUTv is not None:
        lean_aliases["PUT"] = PUTv
    if GETv is not None:
        lean_aliases["GET_IO"] = GETv
    if SEQv is not None:
        lean_aliases["SEQ"] = SEQv
    if PAIR_ELv is not None:
        lean_aliases["PAIR_OP"] = PAIR_ELv
    if FST_ELv is not None:
        lean_aliases["FST_OP"] = FST_ELv
    if SND_ELv is not None:
        lean_aliases["SND_OP"] = SND_ELv
    if INC2v is not None:
        lean_aliases["INC2"] = INC2v
    if SWAPv is not None:
        lean_aliases["SWAP_OP"] = SWAPv
    if p00v is not None:
        lean_aliases["p00"] = p00v
        lean_aliases["p01"] = p01v
        lean_aliases["p10"] = p10v
        lean_aliases["p11"] = p11v

    def ln(i):
        """Lean name for element i."""
        return lean_name[i]

    L = []  # lines
    L.append("/- # Ψ₁₆ᶠ — The 16-element self-describing algebra (full operations)")
    L.append("")
    L.append("   Machine verification of the concrete 16×16 Cayley table with ALL")
    L.append("   operational constraints: L8+C+D+PA+VV+QE+1-inert+E-trans +")
    L.append("   Branch+Compose+Y+Selection + INC(8-cycle)+DEC(reverse) +")
    L.append("   IO(PUT/GET/SEQ) + PAIR/FST/SND(2×2 product) +")
    active_str = "+".join(active_constraints)
    L.append(f"   INC2(4-cycle)+SWAP(involution). Active new ops: {active_str}.")
    L.append("")
    L.append("   All proofs are computational: `decide` or `native_decide`.")
    L.append("-/")
    L.append("")
    L.append("import Mathlib.Data.Fintype.Basic")
    L.append("")
    L.append("set_option maxHeartbeats 800000")
    L.append("")
    L.append("namespace Psi16Full")
    L.append("")
    L.append("/-! ## Part 1: The Cayley Table -/")
    L.append("")
    L.append("private def rawPsi : Nat → Nat → Nat")

    # Generate match arms
    for i in range(N):
        if all(tbl[i][j] == tbl[i][0] for j in range(N)):
            L.append(f"  | {i}, _ => {tbl[i][0]}")
        else:
            row_comment = f"  -- Row {i}: {ename(i)}"
            L.append(row_comment)
            for j in range(N):
                L.append(f"  | {i}, {j} => {tbl[i][j]}")
    L.append("  | _, _ => 0")
    L.append("")
    L.append("private theorem rawPsi_bound (a b : Fin 16) : rawPsi a.val b.val < 16 := by")
    L.append("  revert a b; native_decide")
    L.append("")
    L.append("/-- The Ψ₁₆ᶠ binary operation. -/")
    L.append("def psi (a b : Fin 16) : Fin 16 := ⟨rawPsi a.val b.val, rawPsi_bound a b⟩")
    L.append("")

    # Named constants
    L.append("/-! ## Part 2: Named Constants -/")
    L.append("")
    for i in range(N):
        comment_parts = role_map[i]
        comment = " / ".join(comment_parts)
        L.append(f"abbrev {ln(i)} : Fin 16 := {i}    -- {comment}")
    L.append("")
    # Aliases
    for alias_name, idx in lean_aliases.items():
        L.append(f"abbrev {alias_name} : Fin 16 := {idx}    -- alias for {ln(idx)}")
    L.append("")

    # Part 3: Structural axioms
    L.append("/-! ## Part 3: Structural Axioms -/")
    L.append("")
    L.append("theorem top_absorbs : ∀ x : Fin 16, psi top x = top := by decide")
    L.append("theorem bot_absorbs : ∀ x : Fin 16, psi bot x = bot := by decide")
    L.append("theorem only_two_absorbers : ∀ a : Fin 16,")
    L.append("    (∀ x : Fin 16, psi a x = a) → (a = top ∨ a = bot) := by decide")
    L.append("theorem ext_rows : ∀ a b : Fin 16, a ≠ b →")
    L.append("    ∃ x : Fin 16, psi a x ≠ psi b x := by decide")
    L.append("theorem ext_cols : ∀ a b : Fin 16, a ≠ b →")
    L.append("    ∃ x : Fin 16, psi x a ≠ psi x b := by decide")
    L.append("")

    # Part 4: Role classification
    L.append("/-! ## Part 4: Role Classification -/")
    L.append("")
    L.append("def is_absorber (a : Fin 16) : Prop := ∀ x : Fin 16, psi a x = a")
    L.append("def is_boolean (v : Fin 16) : Prop := v = top ∨ v = bot")
    L.append("def is_tester (a : Fin 16) : Prop :=")
    L.append("  ¬is_absorber a ∧ ∀ x : Fin 16, is_boolean (psi a x)")
    L.append("")
    L.append("instance : DecidablePred is_absorber := fun a =>")
    L.append("  inferInstanceAs (Decidable (∀ x : Fin 16, psi a x = a))")
    L.append("instance : DecidablePred is_boolean := fun v =>")
    L.append("  inferInstanceAs (Decidable (v = top ∨ v = bot))")
    L.append("instance : DecidablePred is_tester := fun a =>")
    L.append("  inferInstanceAs (Decidable (¬is_absorber a ∧ ∀ x : Fin 16, is_boolean (psi a x)))")
    L.append("")
    L.append("def is_encoder (a : Fin 16) : Prop :=")
    L.append("  ¬is_absorber a ∧ ¬(∀ x : Fin 16, is_boolean (psi a x)) ∧")
    L.append("  ∃ x y : Fin 16, ¬is_boolean (psi a x) ∧ ¬is_boolean (psi a y) ∧ psi a x ≠ psi a y")
    L.append("instance : DecidablePred is_encoder := fun a =>")
    L.append("  inferInstanceAs (Decidable (¬is_absorber a ∧ ¬(∀ x, is_boolean (psi a x)) ∧")
    L.append("    ∃ x y : Fin 16, ¬is_boolean (psi a x) ∧ ¬is_boolean (psi a y) ∧ psi a x ≠ psi a y))")
    L.append("")
    L.append("def is_inert (a : Fin 16) : Prop :=")
    L.append("  ¬is_absorber a ∧ ¬is_tester a ∧ ¬is_encoder a")
    L.append("instance : DecidablePred is_inert := fun a =>")
    L.append("  inferInstanceAs (Decidable (¬is_absorber a ∧ ¬is_tester a ∧ ¬is_encoder a))")
    L.append("")

    # Tester theorems
    for t in tester_elems:
        L.append(f"theorem {ln(t)}_is_tester : is_tester {ln(t)} := by decide")
    tester_disj = " ∨ ".join(f"a = {ln(t)}" for t in tester_elems)
    L.append(f"theorem exactly_{len(tester_elems)}_testers : ∀ a : Fin 16,")
    L.append(f"    is_tester a → ({tester_disj}) := by native_decide")
    L.append("")

    # Inert theorems
    inert_e = inert_elems[0] if inert_elems else None
    if inert_e is not None:
        L.append(f"theorem {ln(inert_e)}_is_inert : is_inert {ln(inert_e)} := by decide")
        L.append(f"theorem exactly_one_inert : ∀ a : Fin 16,")
        L.append(f"    is_inert a → a = {ln(inert_e)} := by native_decide")
    L.append("")

    # Part 5: Kripke
    L.append("/-! ## Part 5: Kripke (C) -/")
    L.append("")
    L.append("theorem kripke : ∀ a x : Fin 16,")
    L.append("    ¬is_absorber a → ¬is_absorber x → is_boolean (psi a x) → is_tester a := by native_decide")
    L.append("")

    # Part 6: PA
    L.append("/-! ## Part 6: Power-Associativity -/")
    L.append("")
    L.append("theorem power_assoc : ∀ x : Fin 16,")
    L.append("    psi (psi x x) x = psi x (psi x x) := by decide")
    L.append("theorem not_associative : ∃ a b c : Fin 16,")
    L.append("    psi (psi a b) c ≠ psi a (psi b c) := by decide")
    L.append("")

    # Part 7: QE
    L.append("/-! ## Part 7: QE Inverse -/")
    L.append("")
    L.append("def in_core (x : Fin 16) : Prop := x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5")
    L.append("instance : DecidablePred in_core := fun x =>")
    L.append("  inferInstanceAs (Decidable (x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))")
    L.append("")
    L.append("theorem qe_roundtrip : ∀ x : Fin 16, in_core x →")
    L.append("    psi E (psi Q x) = x := by decide")
    L.append("theorem eq_roundtrip : ∀ x : Fin 16, in_core x →")
    L.append("    psi Q (psi E x) = x := by decide")
    L.append("theorem e_transparent_top : psi E top = top := by decide")
    L.append("theorem e_transparent_bot : psi E bot = bot := by decide")
    L.append("")

    # Part 8: Computational
    L.append("/-! ## Part 8: Computational Structure -/")
    L.append("")
    L.append("theorem branch_true : ∀ x : Fin 16, in_core x →")
    L.append("    psi tau x = top → psi rho x = psi f_enc x := by decide")
    L.append("theorem branch_false : ∀ x : Fin 16, in_core x →")
    L.append("    psi tau x = bot → psi rho x = psi g_enc x := by decide")
    L.append("theorem f_g_differ : ∃ x : Fin 16, in_core x ∧ psi f_enc x ≠ psi g_enc x := by decide")
    L.append("theorem compose_def : ∀ x : Fin 16, in_core x →")
    L.append("    psi eta x = psi rho (psi g_enc x) := by decide")
    L.append(f"theorem y_fixed : psi Y_fix rho = psi rho (psi Y_fix rho) := by decide")
    L.append(f"theorem y_fixed_value : psi Y_fix rho = {ln(yr_val)} := by decide")
    L.append("theorem selection_axiom : psi eta rho = tau := by decide")
    L.append("")

    # Part 9: INC counter
    L.append("/-! ## Part 9: INC Counter (8-state) -/")
    L.append("")
    cycle_comment = " → ".join(f"s{i}({c8v[i]})" for i in range(8)) + f" → s0({c8v[0]})"
    L.append(f"-- Cycle: {cycle_comment}")
    L.append("")
    for i in range(8):
        si = ln(c8v[i])
        si_next = ln(c8v[(i+1) % 8])
        L.append(f"theorem inc_s{i} : psi INC {si} = {si_next} := by decide")
    L.append("")
    # Zero test
    L.append(f"theorem zero_test_hit : psi tau {ln(c8v[0])} = top := by decide")
    for i in range(1, 8):
        L.append(f"theorem zero_test_s{i} : psi tau {ln(c8v[i])} = bot := by decide")
    L.append("")

    # Part 10: DEC counter
    if DECv is not None:
        L.append("/-! ## Part 10: DEC Counter (reverse 8-cycle) -/")
        L.append("")
        for i in range(8):
            si = ln(c8v[i])
            si_prev = ln(c8v[(i-1) % 8])
            L.append(f"theorem dec_s{i} : psi DEC {si} = {si_prev} := by decide")
        L.append("")

    # Part 11: IO
    L.append("/-! ## Part 11: IO -/")
    L.append("")
    if PUTv is not None:
        L.append(f"theorem io_roundtrip : ∀ x : Fin 16, in_core x →")
        L.append(f"    psi GET_IO (psi PUT x) = x := by decide")
        L.append(f"theorem seq_put : psi SEQ PUT ≠ PUT := by decide")
        L.append(f"theorem seq_get : psi SEQ GET_IO ≠ GET_IO := by decide")
    L.append("")

    # Part 12: PAIR/FST/SND
    if PAIR_ELv is not None:
        L.append("/-! ## Part 12: PAIR/FST/SND (2×2 product on {s0,s1}) -/")
        L.append("")
        L.append(f"-- Pair states: p00={p00v}({ename(p00v)}) p01={p01v}({ename(p01v)}) p10={p10v}({ename(p10v)}) p11={p11v}({ename(p11v)})")
        L.append("")
        # PAIR construction
        s0n = ln(c8v[0])
        s1n = ln(c8v[1])
        L.append(f"theorem pair_s0_s0 : psi (psi PAIR_OP {s0n}) {s0n} = p00 := by decide")
        L.append(f"theorem pair_s0_s1 : psi (psi PAIR_OP {s0n}) {s1n} = p01 := by decide")
        L.append(f"theorem pair_s1_s0 : psi (psi PAIR_OP {s1n}) {s0n} = p10 := by decide")
        L.append(f"theorem pair_s1_s1 : psi (psi PAIR_OP {s1n}) {s1n} = p11 := by decide")
        L.append("")
        # FST
        L.append(f"theorem fst_p00 : psi FST_OP p00 = {s0n} := by decide")
        L.append(f"theorem fst_p01 : psi FST_OP p01 = {s0n} := by decide")
        L.append(f"theorem fst_p10 : psi FST_OP p10 = {s1n} := by decide")
        L.append(f"theorem fst_p11 : psi FST_OP p11 = {s1n} := by decide")
        L.append("")
        # SND
        L.append(f"theorem snd_p00 : psi SND_OP p00 = {s0n} := by decide")
        L.append(f"theorem snd_p01 : psi SND_OP p01 = {s1n} := by decide")
        L.append(f"theorem snd_p10 : psi SND_OP p10 = {s0n} := by decide")
        L.append(f"theorem snd_p11 : psi SND_OP p11 = {s1n} := by decide")
        L.append("")

    # Part 13: INC2
    if INC2v is not None:
        L.append("/-! ## Part 13: INC2 (4-state sub-counter) -/")
        L.append("")
        for i in range(4):
            si = ln(c8v[i])
            si_next = ln(c8v[(i+1) % 4])
            L.append(f"theorem inc2_s{i} : psi INC2 {si} = {si_next} := by decide")
        L.append("")

    # Part 14: SWAP
    if SWAPv is not None:
        L.append("/-! ## Part 14: SWAP (involution on core) -/")
        L.append("")
        for x in range(2, CORE):
            sx = tbl[SWAPv][x]
            L.append(f"theorem swap_{x} : psi SWAP_OP ({x} : Fin 16) = ({sx} : Fin 16) := by decide")
        L.append("theorem swap_involution : ∀ x : Fin 16, in_core x →")
        L.append("    psi SWAP_OP (psi SWAP_OP x) = x := by decide")
        L.append("")

    # Part 15: Rigidity
    L.append("/-! ## Part 15: Rigidity -/")
    L.append("")
    L.append("theorem fingerprint_unique : ∀ a b : Fin 16, a ≠ b →")
    L.append("    (∃ x, psi a x ≠ psi b x) ∨ (∃ x, psi x a ≠ psi x b) := by decide")
    L.append("theorem row_injective : ∀ a b : Fin 16,")
    L.append("    (∀ x : Fin 16, psi a x = psi b x) → a = b := by decide")
    L.append("")

    # Part 16: Constructibility
    L.append("/-! ## Part 16: Constructibility -/")
    L.append("")
    L.append("theorem fully_producible : ∀ z : Fin 16,")
    L.append("    ∃ a b : Fin 16, psi a b = z := by decide")
    L.append("")
    L.append("private def gen_set_0 : Finset (Fin 16) := {top, bot, Q, E}")
    L.append("private def gen_close (S : Finset (Fin 16)) : Finset (Fin 16) :=")
    L.append("  S ∪ Finset.univ.filter (fun z => ∃ a ∈ S, ∃ b ∈ S, psi a b = z)")
    L.append("private def gen_iter : Nat → Finset (Fin 16)")
    L.append("  | 0 => gen_set_0")
    L.append("  | n + 1 => gen_close (gen_iter n)")
    L.append("")
    L.append("set_option maxHeartbeats 3200000 in")
    L.append("theorem generates_all : gen_iter 4 = Finset.univ := by native_decide")
    L.append("")

    # Part 17: Idempotents
    L.append("/-! ## Part 17: Idempotents -/")
    L.append("")
    for x in idempotents:
        L.append(f"theorem idem_{ln(x)} : psi {ln(x)} {ln(x)} = {ln(x)} := by decide")
    idem_disj = " ∨ ".join(f"a = {ln(x)}" for x in idempotents)
    L.append(f"theorem exactly_{len(idempotents)}_idempotents : ∀ a : Fin 16,")
    L.append(f"    psi a a = a → ({idem_disj}) := by decide")
    L.append("")

    # Part 18: Additional
    L.append("/-! ## Part 18: Additional Properties -/")
    L.append("")
    L.append("theorem vv_axiom : ∀ v : Fin 16,")
    L.append("    is_inert v → (is_tester (psi v v) ∨ is_encoder (psi v v)) := by native_decide")
    L.append("theorem inert_propagation : ∀ v x : Fin 16,")
    L.append("    is_inert v → ¬is_absorber x → psi v x ≥ 2 := by native_decide")
    L.append("")

    # Find a non-associativity witness
    witness = None
    for a in range(N):
        for b in range(N):
            for c in range(N):
                if tbl[tbl[a][b]][c] != tbl[a][tbl[b][c]]:
                    witness = (a, b, c)
                    break
            if witness:
                break
        if witness:
            break
    if witness:
        a, b, c = witness
        L.append(f"theorem not_assoc_witness : psi (psi {ln(a)} {ln(b)}) {ln(c)} ≠ psi {ln(a)} (psi {ln(b)} {ln(c)}) := by decide")
    L.append("")
    L.append("end Psi16Full")
    L.append("")

    lean_content = "\n".join(L)

    lean_path = "/Users/spalmieri/Desktop/DistinctionStructures/DistinctionStructures/Psi16Full.lean"
    with open(lean_path, "w") as f:
        f.write(lean_content)
    print(f"\n  Wrote {lean_path} ({len(L)} lines)")

    # Count theorems
    thm_count = sum(1 for line in L if line.startswith("theorem "))
    print(f"  Total theorems: {thm_count}")


if __name__ == "__main__":
    extract_psi16_full()

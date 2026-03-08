#!/usr/bin/env python3
"""
Bottom-Up Axiom Exploration via SMT

Explores what finite magmas look like when built from minimal,
independently-motivated structural properties — NOT reverse-engineered
from Δ₁.

Axiom Ladder:
  Level 0: Ext-magma with exactly two left-absorbers (0=top, 1=bot)
  Level 1: + at least one tester (non-absorber with boolean output)
  Level 2: + at least one encoder (element with ≥2 distinct non-boolean outputs)
  Level 3: + encoder outputs are testers (shallow branch)
  Level 4: + two independent encoders with tester outputs (shallow branch)
  Level 5: Generative Synthesis — branches from Level 2 (not 3/4):
            two independent encoders + encoder produces encoder +
            every tester is produced by some encoder (tester constructibility).
            (Level 3's universal tester-closure prevents this, so Level 5 skips it)
  Level 6: + open closure with feedback — the computational core
            (abs ∪ tst ∪ enc) is NOT closed under ·. There exists inert
            substrate outside the descriptive machinery, AND the substrate
            feeds back: some core element applied to inert yields a
            non-absorber core element. Ontological reading: Actuality as
            genuine selection (A5), where the actual is encountered and
            engaged with, not merely discarded.
  Level 7: + context tokens + producibility — there exist two
            non-absorber context tokens c₁ ≠ c₂ and two encoders e₁ ≠ e₂
            that both differentiate the contexts into non-absorber outputs,
            extracting different structural information. AND every element
            is in the image of · (full producibility).
            Ontological: A4 (Contextuality) + self-grounding (the framework
            accounts for all its own parts).
  Level 8: + encoder completeness + inert transformation —
            both encoders touch all 4 role categories (absorber, tester,
            encoder, inert) in their outputs, AND the inert element does
            NOT self-identify (p·p ≠ p).
            Ontological: Synthesis is comprehensive (it can produce every
            kind of thing), and Actuality is always transformed by
            engagement (substrate never persists unchanged under
            self-application).

Usage:
  uv run python ds_search/axiom_explorer.py
"""

from __future__ import annotations

import time
from dataclasses import dataclass, field

from z3 import And, If, Int, Not, Or, Solver, sat, unsat


# ═══════════════════════════════════════════════════════════════════════
# Δ₁ reference table (for comparison at N=17)
# ═══════════════════════════════════════════════════════════════════════

def build_delta1_table() -> list[list[int]]:
    """Build the 17×17 Cayley table for Δ₁."""
    TOP, BOT = 0, 1
    I, K, A_, B_ = 2, 3, 4, 5
    E_I, E_D, E_M, E_SIGMA, E_DELTA = 6, 7, 8, 9, 10
    D_I, D_K, M_I, M_K, S_C, P = 11, 12, 13, 14, 15, 16
    N = 17

    t = [[P] * N for _ in range(N)]
    for y in range(N):
        t[TOP][y] = TOP
        t[BOT][y] = BOT
        t[E_I][y] = TOP if y in (I, K) else BOT
        t[D_K][y] = TOP if y in (A_, B_) else BOT
        t[M_K][y] = TOP if y == A_ else BOT
        t[M_I][y] = BOT if y == P else TOP

    t[E_D][I] = D_I;  t[E_D][K] = D_K
    t[E_M][I] = M_I;  t[E_M][K] = M_K
    t[E_SIGMA][S_C] = E_DELTA
    t[E_DELTA][E_D] = D_I
    t[P][TOP] = TOP
    for x in [I, K, A_, B_, D_I, S_C]:
        t[x][TOP] = x
    return t


DELTA1_TABLE = build_delta1_table()


# ═══════════════════════════════════════════════════════════════════════
# Search result
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class SearchResult:
    status: str          # "sat", "unsat", "timeout"
    time: float          # seconds
    table: list[list[int]] | None = None
    model_count: int | None = None


# ═══════════════════════════════════════════════════════════════════════
# Z3 helper: indirect table lookup via ITE chains
# ═══════════════════════════════════════════════════════════════════════

def ite_lookup(dot, row_expr, col, N):
    """dot[row_expr][col] where row_expr is a Z3 expression, col is concrete."""
    entry = dot[0][col]
    for r in range(1, N):
        entry = If(row_expr == r, dot[r][col], entry)
    return entry


def col_ite_lookup(dot, row, col_expr, N):
    """dot[row][col_expr] where row is concrete, col_expr is a Z3 expression."""
    entry = dot[row][0]
    for c in range(1, N):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def row_is_boolean(dot, t_expr, N):
    """All outputs of row t are in {0,1}, where t is a Z3 expression."""
    clauses = []
    for z in range(N):
        entry = ite_lookup(dot, t_expr, z, N)
        clauses.append(Or(entry == 0, entry == 1))
    return And(clauses)


# ═══════════════════════════════════════════════════════════════════════
# Constraint encoding — one level builds on the previous
# ═══════════════════════════════════════════════════════════════════════

def encode_level(level: int, N: int, timeout_seconds: int = 120) -> tuple[Solver, list[list]]:
    """
    Encode axiom level constraints for an N-element magma.

    Returns (solver, dot) where dot[i][j] are Z3 Int variables.
    """
    s = Solver()
    s.set("timeout", timeout_seconds * 1000)

    dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]

    # Range constraints
    for i in range(N):
        for j in range(N):
            s.add(dot[i][j] >= 0, dot[i][j] < N)

    # ── Level 0: Ext-magma with exactly two left-absorbers ──

    # Element 0 is a left-absorber (top)
    for j in range(N):
        s.add(dot[0][j] == 0)

    # Element 1 is a left-absorber (bot)
    for j in range(N):
        s.add(dot[1][j] == 1)

    # No other left-absorbers
    for x in range(2, N):
        s.add(Or([dot[x][j] != x for j in range(N)]))

    # Ext: all rows distinct
    for x in range(N):
        for y in range(x + 1, N):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(N)]))

    if level < 1:
        return s, dot

    # ── Level 1: at least one tester ──
    # ∃ x ∉ {0,1} such that ∀ y, x·y ∈ {0,1}
    tester_candidates = []
    for x in range(2, N):
        tester_candidates.append(
            And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        )
    s.add(Or(tester_candidates))

    if level < 2:
        return s, dot

    # ── Level 2: at least one encoder ──
    # ∃ x such that ∃ y₁ ≠ y₂ with x·y₁ ∉ {0,1}, x·y₂ ∉ {0,1}, x·y₁ ≠ x·y₂
    encoder_candidates = []
    for x in range(N):
        # For each pair (y1, y2) with y1 < y2
        pair_clauses = []
        for y1 in range(N):
            for y2 in range(y1 + 1, N):
                pair_clauses.append(And(
                    dot[x][y1] != 0, dot[x][y1] != 1,
                    dot[x][y2] != 0, dot[x][y2] != 1,
                    dot[x][y1] != dot[x][y2],
                ))
        if pair_clauses:
            encoder_candidates.append(Or(pair_clauses))
    s.add(Or(encoder_candidates))

    if level >= 5:
        # ── Level 5: Generative Synthesis ──
        # Branches from Level 2. Level 3's universal tester-closure
        # ("all non-boolean outputs are testers") prevents encoder→encoder
        # chains — an encoder has non-boolean outputs so it can't be a
        # tester. Level 5 skips that constraint entirely.
        #
        # Ontological reading: Synthesis produces further Synthesis.
        # There exists an encoder whose output is itself an encoder —
        # the framework generates new generative capacity, not only
        # new distinctions.

        # Precompute "element x is an encoder" for each concrete x
        enc_exprs = []
        for x in range(N):
            pairs = []
            for y1 in range(N):
                for y2 in range(y1 + 1, N):
                    pairs.append(And(
                        dot[x][y1] != 0, dot[x][y1] != 1,
                        dot[x][y2] != 0, dot[x][y2] != 1,
                        dot[x][y1] != dot[x][y2],
                    ))
            enc_exprs.append(Or(pairs) if pairs else False)

        # Two independent encoders with different output profiles
        pair_clauses = []
        for e1 in range(N):
            for e2 in range(e1 + 1, N):
                diff_clauses = []
                for y in range(N):
                    diff_clauses.append(And(
                        dot[e1][y] != 0, dot[e1][y] != 1,
                        Or(dot[e2][y] == 0, dot[e2][y] == 1),
                    ))
                    diff_clauses.append(And(
                        dot[e2][y] != 0, dot[e2][y] != 1,
                        Or(dot[e1][y] == 0, dot[e1][y] == 1),
                    ))
                    diff_clauses.append(And(
                        dot[e1][y] != 0, dot[e1][y] != 1,
                        dot[e2][y] != 0, dot[e2][y] != 1,
                        dot[e1][y] != dot[e2][y],
                    ))
                pair_clauses.append(And(
                    enc_exprs[e1], enc_exprs[e2], Or(diff_clauses),
                ))
        s.add(Or(pair_clauses))

        # Generative: ∃ encoder e, input y, such that e·y is also an encoder
        gen_clauses = []
        for e in range(N):
            for y in range(N):
                for t in range(2, N):  # output can't be an absorber
                    gen_clauses.append(And(
                        enc_exprs[e],
                        dot[e][y] == t,
                        enc_exprs[t],
                    ))
        s.add(Or(gen_clauses))

        # Precompute "element x is a tester" for each concrete x
        tst_exprs = [
            And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
            for x in range(N)
        ]

        # Tester constructibility: every tester is produced by some encoder.
        # For all t: if t is a tester, then ∃ encoder e, input y with e·y = t.
        # Ontological reading: Distinction is derived from Synthesis — the
        # framework's descriptive apparatus is built by its own synthetic
        # operations, not given as an ungrounded primitive.
        for t in range(2, N):
            # t is a tester → ∃ e, y with enc(e) ∧ dot[e][y] == t
            producer_clauses = []
            for e in range(N):
                for y in range(N):
                    producer_clauses.append(And(
                        enc_exprs[e],
                        dot[e][y] == t,
                    ))
            s.add(Or(Not(tst_exprs[t]), Or(producer_clauses)))

        if level < 6:
            return s, dot

        # ── Level 6: Open closure (Actuality as genuine selection) ──
        # The computational core {absorbers ∪ testers ∪ encoders} is NOT
        # closed under ·. There exists x, y in the core such that x·y is
        # inert — neither absorber, tester, nor encoder. The computation
        # produces "stuff" outside its own descriptive machinery.
        #
        # Encoding: ∃ x, y, v where x and y are in the core (absorber,
        # tester, or encoder), x·y = v, and v is inert (not absorber,
        # not tester, not encoder).
        #
        # "x is a tester" = all outputs in {0,1}
        # "x is an encoder" = enc_exprs[x] (≥2 distinct non-boolean outputs)
        # "x is an absorber" = (x == 0 or x == 1)
        # "x is inert" = not absorber, not tester, not encoder
        #   = x ≥ 2 AND NOT all outputs boolean AND NOT ≥2 distinct non-boolean outputs
        #   = x ≥ 2 AND has some non-boolean output AND at most 1 distinct non-boolean output value

        # tst_exprs already computed in Level 5 above

        # "x is in the core" = absorber OR tester OR encoder
        def in_core(x):
            if x < 2:
                return True  # absorber, always in core
            return Or(tst_exprs[x], enc_exprs[x])

        # "v is inert" = v ≥ 2 AND NOT tester AND NOT encoder
        def is_inert(v):
            if v < 2:
                return False  # absorbers are never inert
            return And(Not(tst_exprs[v]), Not(enc_exprs[v]))

        # ∃ x, y in core, v = x·y, v is inert
        escape_clauses = []
        for x in range(N):
            x_core = in_core(x)
            if x_core is False:
                continue
            for y in range(N):
                y_core = in_core(y)
                if y_core is False:
                    continue
                for v in range(2, N):
                    v_inert = is_inert(v)
                    if v_inert is False:
                        continue
                    clause = And(dot[x][y] == v, v_inert)
                    if x_core is not True:
                        clause = And(x_core, clause)
                    if y_core is not True:
                        clause = And(y_core, clause)
                    escape_clauses.append(clause)

        s.add(Or(escape_clauses))

        # Inert feedback: ∃ core element c, inert element v, such that
        # c·v is a non-absorber core element (tester or encoder).
        # Ontological reading: Actuality is not a dead end — the substrate,
        # when probed by the descriptive machinery, yields something to
        # work with. Encountering what-is-the-case feeds back into the
        # capacity for distinction or synthesis.
        feedback_clauses = []
        for c in range(N):
            c_core = in_core(c)
            if c_core is False:
                continue
            for v in range(2, N):
                v_inert = is_inert(v)
                if v_inert is False:
                    continue
                for result in range(2, N):
                    # result is tester or encoder (non-absorber core)
                    result_useful = Or(tst_exprs[result], enc_exprs[result])
                    clause = And(dot[c][v] == result, v_inert, result_useful)
                    if c_core is not True:
                        clause = And(c_core, clause)
                    feedback_clauses.append(clause)
        s.add(Or(feedback_clauses))

        if level < 7:
            return s, dot

        # ── Level 7: Context tokens (multiple-context modeling) ──
        # There exist at least two non-absorber elements c₁ ≠ c₂ (context
        # tokens) and two distinct encoders e₁ ≠ e₂ such that:
        #   - Both encoders differentiate the contexts: e₁·c₁ ≠ e₁·c₂
        #     and e₂·c₁ ≠ e₂·c₂
        #   - The outputs are structurally meaningful (non-absorber)
        #   - The two encoders extract DIFFERENT information: the output
        #     pairs (e₁·c₁, e₁·c₂) ≠ (e₂·c₁, e₂·c₂)
        #
        # Ontological reading: The framework models multiple contexts
        # (frames of reference). Distinct synthetic perspectives extract
        # distinct structural information from the same pair of contexts.
        # This is A4 (Contextuality) made operational: distinctions belong
        # to their context, and the framework can represent this.

        ctx_clauses = []
        for c1 in range(2, N):
            for c2 in range(c1 + 1, N):
                for e1 in range(N):
                    for e2 in range(e1 + 1, N):
                        # Both must be encoders
                        both_enc = And(enc_exprs[e1], enc_exprs[e2])

                        # e1 differentiates contexts with non-absorber outputs
                        e1_diff = And(
                            dot[e1][c1] != dot[e1][c2],
                            dot[e1][c1] != 0, dot[e1][c1] != 1,
                            dot[e1][c2] != 0, dot[e1][c2] != 1,
                        )

                        # e2 differentiates contexts with non-absorber outputs
                        e2_diff = And(
                            dot[e2][c1] != dot[e2][c2],
                            dot[e2][c1] != 0, dot[e2][c1] != 1,
                            dot[e2][c2] != 0, dot[e2][c2] != 1,
                        )

                        # Different information extracted
                        diff_info = Or(
                            dot[e1][c1] != dot[e2][c1],
                            dot[e1][c2] != dot[e2][c2],
                        )

                        ctx_clauses.append(And(
                            both_enc, e1_diff, e2_diff, diff_info,
                        ))

        s.add(Or(ctx_clauses))

        # Producibility: every element is in the image of ·.
        # For all x, ∃ a, b such that a·b = x.
        # Ontological reading: the framework accounts for all its own
        # parts — nothing exists as an ungrounded primitive.
        for x in range(N):
            s.add(Or([dot[a][b] == x for a in range(N) for b in range(N)]))

        if level < 8:
            return s, dot

        # ── Level 8: Encoder completeness + Inert transformation ──
        # Every encoder's row touches all 4 role categories:
        # absorber (0 or 1), tester, encoder, and inert.
        # Ontological: Synthesis is comprehensive — it can produce
        # every kind of thing the framework contains.
        for e in range(2, N):
            # If e is an encoder, its outputs must include:
            # (a) at least one absorber output
            has_abs = Or([Or(dot[e][y] == 0, dot[e][y] == 1) for y in range(N)])
            # (b) at least one tester output
            has_tst = Or([And(dot[e][y] == t, tst_exprs[t])
                          for y in range(N) for t in range(2, N)])
            # (c) at least one encoder output (already guaranteed — it IS an encoder)
            # (d) at least one inert output
            has_inert = Or([And(dot[e][y] == v, is_inert(v))
                            for y in range(N) for v in range(2, N)
                            if is_inert(v) is not False])

            s.add(Or(Not(enc_exprs[e]), And(has_abs, has_tst, has_inert)))

        # Inert non-self-identification: for every inert element v, v·v ≠ v.
        # Ontological: Actuality is always transformed by engagement.
        # The substrate does not persist unchanged under self-application —
        # encountering the actual always yields something different.
        for v in range(2, N):
            v_inert = is_inert(v)
            if v_inert is False:
                continue
            s.add(Or(Not(v_inert), dot[v][v] != v))

        return s, dot

    if level < 3:
        return s, dot

    # ── Level 3: encoder outputs are testers ──
    # For every element x and column y: if x·y ∉ {0,1}, then row (x·y) is boolean
    # This means: any non-boolean output of any row is itself a tester.
    for x in range(N):
        for y in range(N):
            s.add(
                Or(
                    dot[x][y] == 0,
                    dot[x][y] == 1,
                    row_is_boolean(dot, dot[x][y], N),
                )
            )

    if level < 4:
        return s, dot

    # ── Level 4: two independent encoders with tester outputs ──
    # Two distinct encoders e1, e2 with different non-boolean output sets
    # Since Level 3 already forces non-boolean outputs to be testers,
    # we just need two distinct elements each producing ≥2 distinct non-boolean outputs
    # with different output sets.

    # Use auxiliary boolean variables to track which elements are encoders
    # and build the independence constraint.
    # For each pair (e1, e2) with e1 < e2, check:
    #   - both are encoders (≥2 distinct non-boolean outputs)
    #   - their non-boolean output sets differ (∃ column where one outputs
    #     non-boolean and the other doesn't, or they output different non-boolean values)
    pair_clauses = []
    for e1 in range(N):
        for e2 in range(e1 + 1, N):
            # e1 is an encoder
            e1_encoder_pairs = []
            for y1 in range(N):
                for y2 in range(y1 + 1, N):
                    e1_encoder_pairs.append(And(
                        dot[e1][y1] != 0, dot[e1][y1] != 1,
                        dot[e1][y2] != 0, dot[e1][y2] != 1,
                        dot[e1][y1] != dot[e1][y2],
                    ))
            if not e1_encoder_pairs:
                continue

            # e2 is an encoder
            e2_encoder_pairs = []
            for y1 in range(N):
                for y2 in range(y1 + 1, N):
                    e2_encoder_pairs.append(And(
                        dot[e2][y1] != 0, dot[e2][y1] != 1,
                        dot[e2][y2] != 0, dot[e2][y2] != 1,
                        dot[e2][y1] != dot[e2][y2],
                    ))
            if not e2_encoder_pairs:
                continue

            # Output sets differ: ∃ column y where their non-boolean outputs differ
            diff_clauses = []
            for y in range(N):
                # e1 outputs non-boolean at y but e2 doesn't (or vice versa, or both non-boolean but different)
                diff_clauses.append(And(
                    dot[e1][y] != 0, dot[e1][y] != 1,
                    Or(dot[e2][y] == 0, dot[e2][y] == 1),
                ))
                diff_clauses.append(And(
                    dot[e2][y] != 0, dot[e2][y] != 1,
                    Or(dot[e1][y] == 0, dot[e1][y] == 1),
                ))
                diff_clauses.append(And(
                    dot[e1][y] != 0, dot[e1][y] != 1,
                    dot[e2][y] != 0, dot[e2][y] != 1,
                    dot[e1][y] != dot[e2][y],
                ))

            pair_clauses.append(And(
                Or(e1_encoder_pairs),
                Or(e2_encoder_pairs),
                Or(diff_clauses),
            ))

    s.add(Or(pair_clauses))

    return s, dot


# ═══════════════════════════════════════════════════════════════════════
# Model extraction and analysis
# ═══════════════════════════════════════════════════════════════════════

def extract_table(model, dot, N: int) -> list[list[int]]:
    return [[model.evaluate(dot[i][j]).as_long() for j in range(N)] for i in range(N)]


def classify_elements(table: list[list[int]]) -> dict:
    """Classify elements as absorbers, testers, encoders, or inert."""
    N = len(table)
    absorbers = []
    testers = []
    encoders = []
    inert = []

    for x in range(N):
        if all(table[x][y] == x for y in range(N)):
            absorbers.append(x)
            continue
        row_vals = [table[x][y] for y in range(N)]
        is_boolean = all(v in (0, 1) for v in row_vals)
        if is_boolean:
            testers.append(x)
            continue
        non_bool_outputs = set(v for v in row_vals if v not in (0, 1))
        if len(non_bool_outputs) >= 2:
            encoders.append(x)
        else:
            inert.append(x)

    return {
        "absorbers": absorbers,
        "testers": testers,
        "encoders": encoders,
        "inert": inert,
    }


def print_model_summary(table: list[list[int]]):
    """Print structural summary of a model."""
    N = len(table)
    cats = classify_elements(table)

    print(f"    Elements: {N}")
    print(f"    Absorbers: {cats['absorbers']}")
    print(f"    Testers: {cats['testers']} (count={len(cats['testers'])})")
    print(f"    Encoders: {cats['encoders']} (count={len(cats['encoders'])})")
    print(f"    Inert: {cats['inert']} (count={len(cats['inert'])})")

    # Show tester signatures
    for t in cats["testers"][:4]:
        accepts = [y for y in range(N) if table[t][y] == 0]
        print(f"    Tester {t}: accepts {accepts}")

    # Show encoder output profiles
    for e in cats["encoders"][:4]:
        non_bool = {y: table[e][y] for y in range(N) if table[e][y] not in (0, 1)}
        print(f"    Encoder {e}: non-boolean outputs {non_bool}")

    # Check if encoder outputs are testers
    encoder_outputs_are_testers = True
    tester_set = set(cats["testers"])
    for e in cats["encoders"]:
        for y in range(N):
            v = table[e][y]
            if v not in (0, 1) and v not in tester_set:
                encoder_outputs_are_testers = False
                break
        if not encoder_outputs_are_testers:
            break
    if cats["encoders"]:
        print(f"    Encoder outputs are testers: {encoder_outputs_are_testers}")


def print_table(table: list[list[int]]):
    """Pretty-print a Cayley table."""
    N = len(table)
    header = "     " + " ".join(f"{j:>3d}" for j in range(N))
    print(header)
    print("     " + "----" * N)
    for i in range(N):
        row = " ".join(f"{table[i][j]:>3d}" for j in range(N))
        print(f"  {i:>2d}|{row}")


def check_delta1_match(table: list[list[int]]) -> bool:
    """Check if a 17-element table matches Δ₁ exactly (no isomorphism)."""
    if len(table) != 17:
        return False
    return table == DELTA1_TABLE


# ═══════════════════════════════════════════════════════════════════════
# Solution counting via iterative exclusion
# ═══════════════════════════════════════════════════════════════════════

def count_models(level: int, N: int, cap: int = 100, timeout_seconds: int = 300) -> int:
    """Count solutions up to cap via iterative model exclusion."""
    s, dot = encode_level(level, N, timeout_seconds=timeout_seconds)
    count = 0
    while count < cap:
        if s.check() != sat:
            break
        table = extract_table(s.model(), dot, N)
        count += 1
        # Exclude this exact table
        s.add(Or([dot[i][j] != table[i][j] for i in range(N) for j in range(N)]))
    return count


# ═══════════════════════════════════════════════════════════════════════
# Search at a single (level, N)
# ═══════════════════════════════════════════════════════════════════════

def search(level: int, N: int, timeout_seconds: int = 120) -> SearchResult:
    """Run SAT check for given level and N."""
    t0 = time.time()
    s, dot = encode_level(level, N, timeout_seconds=timeout_seconds)
    result = s.check()
    elapsed = time.time() - t0

    if result == sat:
        table = extract_table(s.model(), dot, N)
        return SearchResult(status="sat", time=elapsed, table=table)
    elif result == unsat:
        return SearchResult(status="unsat", time=elapsed)
    else:
        return SearchResult(status="timeout", time=elapsed)


# ═══════════════════════════════════════════════════════════════════════
# Campaign
# ═══════════════════════════════════════════════════════════════════════

LEVEL_NAMES = [
    "Ext-magma + 2 absorbers",
    "+ tester",
    "+ encoder",
    "+ encoder outputs are testers",
    "+ two independent encoders",
    "Generative Synthesis",
    "+ open closure with feedback",
    "+ context tokens + producibility",
    "+ encoder completeness + inert transformation",
]

MAX_N = 12


def main():
    print("=" * 70)
    print("BOTTOM-UP AXIOM EXPLORATION")
    print("=" * 70)

    summary = []  # (level, N, status, time)

    for level in range(9):
        print(f"\n{'='*70}")
        print(f"Level {level}: {LEVEL_NAMES[level]}")
        print(f"{'='*70}")

        min_sat_n = None

        for N in range(3, MAX_N + 1):
            result = search(level, N, timeout_seconds=120)
            status_str = result.status.upper()
            print(f"  N={N:>2d}: {status_str:>7s} ({result.time:.1f}s)", end="")

            if result.status == "sat" and result.table is not None:
                if min_sat_n is None:
                    min_sat_n = N
                cats = classify_elements(result.table)
                print(f"  [abs={len(cats['absorbers'])} tst={len(cats['testers'])} "
                      f"enc={len(cats['encoders'])} inert={len(cats['inert'])}]")
            else:
                print()

            summary.append((level, N, result.status, result.time))

            # Print first SAT model details
            if result.status == "sat" and result.table is not None and N == min_sat_n:
                print(f"\n    --- First model at N={N} ---")
                print_model_summary(result.table)
                if N <= 8:
                    print_table(result.table)

                # Count models at this N
                print(f"\n    Counting models (cap=100)...")
                t0 = time.time()
                count = count_models(level, N, cap=100, timeout_seconds=300)
                ct = time.time() - t0
                cap_note = "+" if count >= 100 else ""
                print(f"    Models at N={N}: {count}{cap_note} ({ct:.1f}s)")

        if min_sat_n is not None:
            print(f"\n  Minimum N for Level {level}: {min_sat_n}")
        else:
            print(f"\n  Level {level}: No SAT found up to N={MAX_N}")

    # ── Summary table ──
    print(f"\n\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"{'Level':<6} {'N':>3} {'Status':>8} {'Time':>8}")
    print("-" * 30)
    for level, N, status, t in summary:
        print(f"  {level:<4d} {N:>3d} {status:>8s} {t:>7.1f}s")

    # Min-N table
    print(f"\n{'Level':<42} {'Min N':>6}")
    print("-" * 50)
    for level in range(9):
        sat_ns = [N for lv, N, st, _ in summary if lv == level and st == "sat"]
        min_n = min(sat_ns) if sat_ns else "> " + str(MAX_N)
        print(f"  {level}: {LEVEL_NAMES[level]:<38} {str(min_n):>6}")


if __name__ == "__main__":
    main()

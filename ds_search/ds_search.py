#!/usr/bin/env python3
"""
Distinction Structure Search via Z3 SMT Solver

Searches for finite magmas (D, dot) satisfying the Distinction Structure
axioms extracted from the Lean formalization (Basic.lean, Delta1.lean,
Discoverable.lean).

Key insight: A DS requires 17 distinct role elements. We fix their indices
(0–16) via symmetry breaking and search only over the Cayley table.
For N=17, the roles exhaust the carrier. For N>17, extra elements exist.
For N<17, full DS is impossible (not enough distinct roles).

Usage:
  uv run python -m ds_search.ds_search
"""

from __future__ import annotations

import json
import time
from itertools import permutations
from pathlib import Path

from z3 import And, Distinct, If, Int, Not, Or, Solver, Sum, sat, unsat

# ═══════════════════════════════════════════════════════════════════════
# Fixed role indices (symmetry breaking — no generality lost)
# ═══════════════════════════════════════════════════════════════════════

# Matching D1ι inductive order from Delta1.lean
TOP = 0
BOT = 1
I = 2    # context token ι
K = 3    # context token κ
A_ = 4   # κ-element encoding a
B_ = 5   # κ-element encoding b
E_I = 6  # context tester
E_D = 7  # domain encoder
E_M = 8  # actuality encoder
E_SIGMA = 9   # synthesis source
E_DELTA = 10  # synthesis target (whole-structure encoder)
D_I = 11  # domain code for ι
D_K = 12  # domain code for κ (also a tester)
M_I = 13  # actuality code for ι (also a tester)
M_K = 14  # actuality code for κ (also a tester)
S_C = 15  # component-set token
P = 16    # non-actual element

ROLE_NAMES = [
    "top", "bot", "i", "k", "a", "b", "e_I",
    "e_D", "e_M", "e_Sigma", "e_Delta",
    "d_I", "d_K", "m_I", "m_K", "s_C", "p",
]

TESTERS = [E_I, D_K, M_K, M_I]
SELF_ID_ELEMS = [I, K, A_, B_, D_I, S_C]  # x · top = x
CORE_SIZE = 17


def build_delta1_table() -> list[list[int]]:
    """Build the 17×17 Cayley table for Δ₁ from Delta1.lean rules."""
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
    for x in SELF_ID_ELEMS:
        t[x][TOP] = x
    return t


DELTA1_TABLE = build_delta1_table()


def core_default_constrained_pairs(relax: set[str] | None = None) -> set[tuple[int, int]]:
    """
    Return the 17×17 core entries that are fixed by non-default constraints.

    This corresponds to the positions explicitly governed by Blocks A–E + H/A7'
    in the fixed-role encoding.
    """
    relax = relax or set()
    constrained: set[tuple[int, int]] = set()

    # Rows TOP, BOT fully constrained.
    for j in range(CORE_SIZE):
        constrained.add((TOP, j))
        constrained.add((BOT, j))

    # Tester rows fully constrained.
    for tester in TESTERS:
        for j in range(CORE_SIZE):
            constrained.add((tester, j))

    # H conditions.
    if "h_conditions" not in relax:
        constrained.update({(E_D, I), (E_D, K), (E_M, I), (E_M, K)})

    # H3 + A7'.
    if "synthesis" not in relax:
        constrained.update({(E_SIGMA, S_C), (E_DELTA, E_D)})

    # Block D.
    constrained.add((P, TOP))

    # Self-identification.
    if "self_id" not in relax:
        for x in SELF_ID_ELEMS:
            constrained.add((x, TOP))

    return constrained


def core_default_unconstrained_pairs(relax: set[str] | None = None) -> list[tuple[int, int]]:
    """Return 17×17 core positions that Block F sends to `p` when active."""
    constrained = core_default_constrained_pairs(relax)
    return [
        (i, j)
        for i in range(CORE_SIZE)
        for j in range(CORE_SIZE)
        if (i, j) not in constrained
    ]


# ═══════════════════════════════════════════════════════════════════════
# Z3 Encoding
# ═══════════════════════════════════════════════════════════════════════


def encode_ds(
    N: int,
    *,
    exclude_delta1: bool = False,
    exclude_delta1_core: bool = False,
    relax: set[str] | None = None,
    force_nondefault_unconstrained_core: bool = False,
    timeout_seconds: int = 3600,
) -> tuple[Solver, list[list]]:
    """
    Encode Distinction Structure axioms as Z3 constraints.

    All 17 role elements are fixed to indices 0–16. The Cayley table
    entries are the only Z3 variables.

    relax options: "tester_cards", "discovery_unique", "synthesis",
                   "context", "actuality", "h_conditions", "self_id",
                   "ext", "default_p"

    exclude_delta1:
      For N=17, force at least one core entry to differ from Δ₁.

    exclude_delta1_core:
      For N>=17, force at least one entry in the 17×17 core to differ from Δ₁.

    force_nondefault_unconstrained_core:
      Requires `default_p` to be relaxed and forces at least one otherwise
      Block-F slot in the 17×17 core to take a non-`p` value. Useful for
      proving Block F is not derivable from the other encoded constraints.
    """
    if N < 17:
        # Can't have 17 distinct roles with < 17 elements
        s = Solver()
        s.add(False)  # trivially UNSAT
        return s, [[]]

    relax = relax or set()
    s = Solver()
    s.set("timeout", timeout_seconds * 1000)

    # Cayley table: dot[i][j] is a Z3 Int variable
    dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]
    for i in range(N):
        for j in range(N):
            s.add(dot[i][j] >= 0, dot[i][j] < N)

    # ═══════════════════════════════════════════════════════════════
    # AXIOM GROUP A: Boolean absorption
    # ═══════════════════════════════════════════════════════════════

    # A.1-2: top and bot are left-absorbers
    for j in range(N):
        s.add(dot[TOP][j] == TOP)
        s.add(dot[BOT][j] == BOT)

    # A.4: Exactly two left-absorbers (no third element absorbs)
    for x in range(2, N):
        s.add(Not(And([dot[x][j] == x for j in range(N)])))

    # ═══════════════════════════════════════════════════════════════
    # AXIOM GROUP A: Testers
    # ═══════════════════════════════════════════════════════════════

    # Testers: left-image ⊆ {top, bot}
    for tester in TESTERS:
        for j in range(N):
            s.add(Or(dot[tester][j] == TOP, dot[tester][j] == BOT))

    # Exactly 4 testers: no other non-boolean element is a tester
    for x in range(2, N):
        if x in TESTERS:
            continue
        # x must have at least one non-boolean output
        s.add(Or([And(dot[x][j] != TOP, dot[x][j] != BOT) for j in range(N)]))

    # ═══════════════════════════════════════════════════════════════
    # Tester partition properties
    # ═══════════════════════════════════════════════════════════════

    # e_I: accepts exactly {i, k}
    s.add(dot[E_I][I] == TOP)
    s.add(dot[E_I][K] == TOP)
    for j in range(N):
        if j not in (I, K):
            s.add(dot[E_I][j] == BOT)

    # d_K: accepts exactly {a, b}
    s.add(dot[D_K][A_] == TOP)
    s.add(dot[D_K][B_] == TOP)
    for j in range(N):
        if j not in (A_, B_):
            s.add(dot[D_K][j] == BOT)

    # m_K: accepts exactly {a}
    s.add(dot[M_K][A_] == TOP)
    for j in range(N):
        if j != A_:
            s.add(dot[M_K][j] == BOT)

    # m_I: rejects exactly {p}, accepts everything else
    if "actuality" not in relax:
        s.add(dot[M_I][P] == BOT)
        for j in range(N):
            if j != P:
                s.add(dot[M_I][j] == TOP)

    # ═══════════════════════════════════════════════════════════════
    # Tester cardinality signatures (Discoverable.lean Lemma 3)
    # ═══════════════════════════════════════════════════════════════

    if "tester_cards" not in relax:
        # These are already implied by the exact partition constraints above
        # for the fixed-index case, but let's be explicit for N > 17
        if N > 17:
            s.add(Sum([If(dot[M_I][j] == TOP, 1, 0) for j in range(N)]) == N - 1)

    # ═══════════════════════════════════════════════════════════════
    # Ext: Behavioral separability
    # ═══════════════════════════════════════════════════════════════

    if "ext" not in relax:
        for x in range(N):
            for y in range(x + 1, N):
                s.add(Or([dot[x][j] != dot[y][j] for j in range(N)]))

    # ═══════════════════════════════════════════════════════════════
    # H: Homomorphism conditions (self-model)
    # ═══════════════════════════════════════════════════════════════

    if "h_conditions" not in relax:
        # H1: dot(e_D, i) = d_I, dot(e_D, k) = d_K
        s.add(dot[E_D][I] == D_I)
        s.add(dot[E_D][K] == D_K)
        # H2: dot(e_M, i) = m_I, dot(e_M, k) = m_K
        s.add(dot[E_M][I] == M_I)
        s.add(dot[E_M][K] == M_K)

    if "synthesis" not in relax:
        # H3: dot(e_Sigma, s_C) = e_Delta
        s.add(dot[E_SIGMA][S_C] == E_DELTA)

    # ═══════════════════════════════════════════════════════════════
    # IR: Intrinsic reflexivity (mostly handled by fixed indices)
    # ═══════════════════════════════════════════════════════════════

    # IR conditions are satisfied by construction since all role
    # indices are distinct and p=16 is distinct from all encoders.

    # ═══════════════════════════════════════════════════════════════
    # Block D: p · top = top (absorption breaker for Ext)
    # ═══════════════════════════════════════════════════════════════

    s.add(dot[P][TOP] == TOP)

    # ═══════════════════════════════════════════════════════════════
    # Block E: Passive self-identification (x · top = x)
    # ═══════════════════════════════════════════════════════════════

    if "self_id" not in relax:
        for x in SELF_ID_ELEMS:
            s.add(dot[x][TOP] == x)

    # ═══════════════════════════════════════════════════════════════
    # A7': Structural novelty
    # ═══════════════════════════════════════════════════════════════

    if "synthesis" not in relax:
        s.add(dot[E_DELTA][E_D] == D_I)
        s.add(dot[E_DELTA][E_D] != dot[E_I][E_D])
        s.add(dot[E_DELTA][E_D] != dot[E_D][E_D])
        s.add(dot[E_DELTA][E_D] != dot[E_M][E_D])
        s.add(dot[E_DELTA][E_D] != dot[E_SIGMA][E_D])

    # ═══════════════════════════════════════════════════════════════
    # Discoverability uniqueness
    # ═══════════════════════════════════════════════════════════════

    if "discovery_unique" not in relax:
        # D.4: Rich vs inert — d_I produces non-boolean output (not a tester)
        s.add(Or([And(dot[D_I][j] != TOP, dot[D_I][j] != BOT) for j in range(N)]))

        # D.5: Only e_D and e_M produce non-trivial output on BOTH i and k
        for x in range(N):
            if x in (E_D, E_M):
                continue
            nontrivial_on_both = And(
                And(dot[x][I] != TOP, dot[x][I] != BOT, dot[x][I] != P),
                And(dot[x][K] != TOP, dot[x][K] != BOT, dot[x][K] != P),
            )
            s.add(Not(nontrivial_on_both))

        # D.4 inert: for all non-tester non-boolean x,
        # dot(x, a) and dot(x, b) are in {top, bot, p}
        for x in range(2, N):
            if x in TESTERS:
                continue
            for y in [A_, B_]:
                s.add(Or(dot[x][y] == TOP, dot[x][y] == BOT, dot[x][y] == P))

    # ═══════════════════════════════════════════════════════════════
    # Block F: Default behavior (unconstrained entries → p)
    # ═══════════════════════════════════════════════════════════════
    #
    # In Δ₁, all entries not explicitly specified by Blocks A–E + H/A7'
    # default to p. In this encoding this is an explicit assumption (Block F),
    # not a theorem of the remaining constraints.

    core_unconstrained = core_default_unconstrained_pairs(relax)

    if "default_p" not in relax:
        # All unconstrained entries in the 17×17 core → p
        for i, j in core_unconstrained:
            s.add(dot[i][j] == P)

        # For N > 17: do NOT constrain extra rows/cols (they're genuinely new)

    if force_nondefault_unconstrained_core:
        if "default_p" not in relax:
            raise ValueError(
                "force_nondefault_unconstrained_core requires relax to include 'default_p'"
            )
        if not core_unconstrained:
            raise ValueError("No unconstrained core entries available for witness forcing")
        s.add(Or([dot[i][j] != P for i, j in core_unconstrained]))

    # ═══════════════════════════════════════════════════════════════
    # Exclude Δ₁ / Δ₁ core
    # ═══════════════════════════════════════════════════════════════

    if exclude_delta1_core:
        s.add(Or([
            dot[i][j] != DELTA1_TABLE[i][j]
            for i in range(17) for j in range(17)
        ]))

    if exclude_delta1:
        if N == 17:
            # With all roles fixed, just require at least one table entry differs
            s.add(Or([
                dot[i][j] != DELTA1_TABLE[i][j]
                for i in range(17) for j in range(17)
            ]))
        # For N > 17, the table is automatically different (different size)

    return s, dot


# ═══════════════════════════════════════════════════════════════════════
# Model extraction
# ═══════════════════════════════════════════════════════════════════════


def extract_table(model, dot, N: int) -> list[list[int]]:
    """Extract Cayley table from a Z3 model."""
    return [
        [model.evaluate(dot[i][j]).as_long() for j in range(N)]
        for i in range(N)
    ]


def get_role_map(N: int = 17) -> dict[str, int]:
    """Return the fixed role map."""
    return {name: idx for idx, name in enumerate(ROLE_NAMES[:min(N, 17)])}


# ═══════════════════════════════════════════════════════════════════════
# Independent Verifier (no Z3)
# ═══════════════════════════════════════════════════════════════════════


def verify_ds(table: list[list[int]], role_map: dict[str, int] | None = None) -> dict[str, bool]:
    """Independently verify all DS axioms on a given Cayley table."""
    N = len(table)
    if role_map is None:
        role_map = get_role_map(N)

    results = {}

    def dot(x, y):
        return table[x][y]

    # Absorbers
    results["top_absorber"] = all(dot(TOP, y) == TOP for y in range(N))
    results["bot_absorber"] = all(dot(BOT, y) == BOT for y in range(N))
    absorbers = [x for x in range(N) if all(dot(x, y) == x for y in range(N))]
    results["exactly_2_absorbers"] = set(absorbers) == {TOP, BOT}

    # Testers
    for name, idx in [("e_I", E_I), ("d_K", D_K), ("m_K", M_K), ("m_I", M_I)]:
        results[f"{name}_is_tester"] = all(dot(idx, y) in (TOP, BOT) for y in range(N))

    actual_testers = {
        x for x in range(N) if x not in (TOP, BOT)
        and all(dot(x, y) in (TOP, BOT) for y in range(N))
    }
    results["exactly_4_testers"] = actual_testers == set(TESTERS)

    # Tester partitions
    results["eI_accepts_ik"] = (
        dot(E_I, I) == TOP and dot(E_I, K) == TOP
        and sum(1 for y in range(N) if dot(E_I, y) == TOP) == 2
    )
    results["dK_accepts_ab"] = (
        dot(D_K, A_) == TOP and dot(D_K, B_) == TOP
        and sum(1 for y in range(N) if dot(D_K, y) == TOP) == 2
    )
    results["mK_accepts_a"] = (
        dot(M_K, A_) == TOP
        and sum(1 for y in range(N) if dot(M_K, y) == TOP) == 1
    )
    results["mI_rejects_p_only"] = (
        dot(M_I, P) == BOT
        and sum(1 for y in range(N) if dot(M_I, y) == TOP) == N - 1
    )

    # Ext
    ext_ok = True
    for x in range(N):
        for y in range(x + 1, N):
            if not any(dot(x, z) != dot(y, z) for z in range(N)):
                ext_ok = False
                break
        if not ext_ok:
            break
    results["ext"] = ext_ok

    # H conditions
    results["H1_eD_i"] = dot(E_D, I) == D_I
    results["H1_eD_k"] = dot(E_D, K) == D_K
    results["H2_eM_i"] = dot(E_M, I) == M_I
    results["H2_eM_k"] = dot(E_M, K) == M_K
    results["H3"] = dot(E_SIGMA, S_C) == E_DELTA

    # A7'
    results["A7_prime"] = all(
        dot(E_DELTA, E_D) != dot(x, E_D)
        for x in [E_I, E_D, E_M, E_SIGMA]
    )
    results["eDelta_eD_eq_dI"] = dot(E_DELTA, E_D) == D_I

    # Self-identification
    for name, idx in zip(["i", "k", "a", "b", "d_I", "s_C"], SELF_ID_ELEMS):
        results[f"{name}_self_id"] = dot(idx, TOP) == idx

    results["p_top_eq_top"] = dot(P, TOP) == TOP

    # d_I is not a tester (needed for encoder asymmetry)
    results["dI_not_tester"] = any(
        dot(D_I, y) not in (TOP, BOT) for y in range(N)
    )

    # Inert kappa tokens
    results["inert_kappa"] = all(
        dot(x, A_) in (TOP, BOT, P) and dot(x, B_) in (TOP, BOT, P)
        for x in range(2, N) if x not in TESTERS
    )

    # Encoder pair uniqueness
    others_nontrivial = False
    for x in range(N):
        if x in (E_D, E_M):
            continue
        if (dot(x, I) not in (TOP, BOT, P) and dot(x, K) not in (TOP, BOT, P)):
            others_nontrivial = True
            break
    results["encoder_pair_unique"] = not others_nontrivial

    return results


# ═══════════════════════════════════════════════════════════════════════
# Isomorphism checker
# ═══════════════════════════════════════════════════════════════════════


def check_isomorphism_z3(
    table1: list[list[int]], table2: list[list[int]], timeout_ms: int = 60000
) -> list[int] | None:
    """Check isomorphism via Z3. Returns permutation or None."""
    N = len(table1)
    if len(table2) != N:
        return None

    # Quick check: are they literally the same table?
    if table1 == table2:
        return list(range(N))

    s = Solver()
    s.set("timeout", timeout_ms)

    perm = [Int(f"p_{i}") for i in range(N)]
    for i in range(N):
        s.add(perm[i] >= 0, perm[i] < N)
    s.add(Distinct(perm))

    # perm[table1[i][j]] == table2[perm[i]][perm[j]]
    # Use nested ITE chains instead of Sum (which has the wrong semantics)
    def table2_lookup(r, c):
        """Build ITE chain for table2[r][c] where r, c are Z3 exprs."""
        expr = table2[0][0]
        for ri in range(N):
            for ci in range(N):
                expr = If(And(r == ri, c == ci), table2[ri][ci], expr)
        return expr

    for i in range(N):
        for j in range(N):
            v = table1[i][j]
            s.add(perm[v] == table2_lookup(perm[i], perm[j]))

    if s.check() == sat:
        m = s.model()
        return [m.evaluate(perm[i]).as_long() for i in range(N)]
    return None


# ═══════════════════════════════════════════════════════════════════════
# Category Analysis
# ═══════════════════════════════════════════════════════════════════════


def analyze_categories(table: list[list[int]]) -> dict:
    """Analyze ontological categories in a model."""
    N = len(table)

    def dot(x, y):
        return table[x][y]

    analysis = {}

    # DISTINCTION
    testers = []
    for x in range(N):
        if x in (TOP, BOT):
            continue
        if all(dot(x, y) in (TOP, BOT) for y in range(N)):
            testers.append(x)
    analysis["distinction"] = len(testers) >= 1
    analysis["num_testers"] = len(testers)
    analysis["tester_indices"] = testers

    # CONTEXT
    context_tokens = []
    for y in range(N):
        productive = sum(
            1 for x in range(N)
            if x not in (TOP, BOT) and x not in testers
            and dot(x, y) not in (TOP, BOT, P)
        )
        if productive >= 2:
            context_tokens.append(y)
    analysis["context"] = len(context_tokens) >= 2
    analysis["context_tokens"] = context_tokens

    # ACTUALITY
    actuality_tester = None
    for tst in testers:
        rejects = [y for y in range(N) if dot(tst, y) == BOT]
        if len(rejects) == 1:
            actuality_tester = tst
            break
    analysis["actuality"] = actuality_tester is not None

    # SYNTHESIS
    has_synthesis = False
    for f in range(N):
        if f in (TOP, BOT) or f in testers:
            continue
        for g in range(N):
            if g in (TOP, BOT):
                continue
            h = dot(f, g)
            if h in (TOP, BOT, P) or h == f or h == g:
                continue
            if any(dot(h, z) not in (TOP, BOT, P) for z in range(N)):
                has_synthesis = True
                break
        if has_synthesis:
            break
    analysis["synthesis"] = has_synthesis

    analysis["all_four"] = all([
        analysis["distinction"], analysis["context"],
        analysis["actuality"], analysis["synthesis"],
    ])
    return analysis


# ═══════════════════════════════════════════════════════════════════════
# Search Runner
# ═══════════════════════════════════════════════════════════════════════


def run_search(
    N: int,
    label: str,
    *,
    exclude_delta1: bool = False,
    exclude_delta1_core: bool = False,
    relax: set[str] | None = None,
    force_nondefault_unconstrained_core: bool = False,
    timeout_seconds: int = 3600,
) -> dict:
    """Run a single search."""
    print(f"\n{'='*60}")
    print(f"Search: {label} (N={N}, timeout={timeout_seconds}s)")
    if relax:
        print(f"  Relaxed: {relax}")
    if force_nondefault_unconstrained_core:
        print("  Witness: force at least one unconstrained core entry != p")
    print(f"{'='*60}")

    t0 = time.time()
    solver, dot = encode_ds(
        N,
        exclude_delta1=exclude_delta1,
        exclude_delta1_core=exclude_delta1_core,
        relax=relax,
        force_nondefault_unconstrained_core=force_nondefault_unconstrained_core,
        timeout_seconds=timeout_seconds,
    )
    result_status = solver.check()
    elapsed = time.time() - t0

    result = {
        "label": label, "N": N, "status": str(result_status),
        "time_seconds": round(elapsed, 2),
        "exclude_delta1": exclude_delta1,
        "exclude_delta1_core": exclude_delta1_core,
        "relax": list(relax) if relax else [],
        "force_nondefault_unconstrained_core": force_nondefault_unconstrained_core,
    }

    if result_status == sat:
        table = extract_table(solver.model(), dot, N)
        result["role_map"] = get_role_map(N)

        # Independent verification
        verification = verify_ds(table)
        passed = sum(1 for v in verification.values() if v)
        total = len(verification)
        result["verification"] = f"{passed}/{total}"
        result["all_verified"] = all(verification.values())

        if not all(verification.values()):
            failed = [k for k, v in verification.items() if not v]
            result["failed_checks"] = failed
            print(f"  WARNING: {len(failed)} checks failed: {failed}")

        # Isomorphism check with Δ₁
        if N == 17:
            iso = check_isomorphism_z3(table, DELTA1_TABLE, timeout_ms=30000)
            result["isomorphic_to_delta1"] = iso is not None
            if iso:
                print(f"  Isomorphic to Δ₁ (perm found)")
            else:
                print(f"  NOT isomorphic to Δ₁!")

        # Category analysis
        cats = analyze_categories(table)
        result["categories"] = {
            k: v for k, v in cats.items()
            if k in ("distinction", "context", "actuality", "synthesis",
                     "all_four", "num_testers")
        }

        if N >= CORE_SIZE and relax and "default_p" in relax:
            varied = [
                (i, j, table[i][j])
                for i, j in core_default_unconstrained_pairs(relax)
                if table[i][j] != P
            ]
            result["nondefault_unconstrained_core_count"] = len(varied)
            result["nondefault_unconstrained_core_examples"] = [
                {"row": i, "col": j, "value": v} for i, j, v in varied[:12]
            ]
            print(f"  Non-default values in Block-F slots: {len(varied)}")

        result["table"] = table

        print(f"  SAT in {elapsed:.1f}s")
        print(f"  Verification: {result['verification']}")
        print(f"  Categories: D={cats['distinction']} C={cats['context']} "
              f"A={cats['actuality']} S={cats['synthesis']}")

    elif result_status == unsat:
        print(f"  UNSAT in {elapsed:.1f}s")
    else:
        print(f"  TIMEOUT after {elapsed:.1f}s")

    return result


def print_table(table: list[list[int]]):
    """Pretty-print a Cayley table."""
    N = len(table)
    names = ROLE_NAMES + [str(i) for i in range(17, N)]
    header = "      " + " ".join(f"{names[j]:>5s}" for j in range(N))
    print(header)
    print("      " + "------" * N)
    for i in range(N):
        row = " ".join(f"{names[table[i][j]]:>5s}" for j in range(N))
        print(f"{names[i]:>5s}|{row}")


def main():
    results = []

    # ───────────────────────────────────────────────────────
    # 3.1: Verify encoding by finding Δ₁
    # ───────────────────────────────────────────────────────
    r = run_search(17, "3.1: Find Δ₁ (verify encoding)", timeout_seconds=600)
    results.append(r)

    if r["status"] == "sat" and r.get("all_verified"):
        print("\n  Encoding verified — found valid DS at N=17")
        if r.get("isomorphic_to_delta1"):
            print("  Confirmed isomorphic to Δ₁")

    # ───────────────────────────────────────────────────────
    # 3.2: Uniqueness at N=17
    # ───────────────────────────────────────────────────────
    r = run_search(
        17, "3.2: Uniqueness at N=17 (exclude Δ₁)",
        exclude_delta1=True, timeout_seconds=600,
    )
    results.append(r)

    # 3.2b: Block F independence witness (base axioms do not force default_p)
    r = run_search(
        17,
        "3.2b: Block F independence witness",
        relax={"default_p"},
        force_nondefault_unconstrained_core=True,
        timeout_seconds=600,
    )
    results.append(r)

    # ───────────────────────────────────────────────────────
    # 3.3: Smaller models (trivially UNSAT for N<17)
    # ───────────────────────────────────────────────────────
    for n in [14, 16]:
        r = run_search(n, f"3.3: Smaller model N={n}", timeout_seconds=60)
        results.append(r)

    # ───────────────────────────────────────────────────────
    # 3.4: Larger model
    # ───────────────────────────────────────────────────────
    r = run_search(18, "3.4: Larger model N=18", timeout_seconds=600)
    results.append(r)

    # 3.4b: Force core mismatch at N=18
    r = run_search(
        18, "3.4b: N=18 with core mismatch forced",
        exclude_delta1_core=True, timeout_seconds=600,
    )
    results.append(r)

    # ───────────────────────────────────────────────────────
    # 3.5: Relaxed searches at N=17 (excluding Δ₁)
    # ───────────────────────────────────────────────────────
    for relax_set, label in [
        ({"default_p"}, "No default-to-p"),
        ({"discovery_unique"}, "No discovery uniqueness"),
        ({"synthesis"}, "No synthesis"),
        ({"h_conditions"}, "No H conditions"),
        ({"self_id"}, "No self-identification"),
    ]:
        r = run_search(
            17, f"3.5: Relaxed ({label})",
            exclude_delta1=True, relax=relax_set, timeout_seconds=300,
        )
        results.append(r)
        if r["status"] == "sat" and r.get("table"):
            cats = r.get("categories", {})
            if not cats.get("all_four"):
                missing = [c for c in ["distinction", "context", "actuality", "synthesis"]
                           if not cats.get(c)]
                print(f"  Missing categories: {missing}")

    # ───────────────────────────────────────────────────────
    # Summary
    # ───────────────────────────────────────────────────────
    print("\n" + "=" * 80)
    print("SEARCH CAMPAIGN SUMMARY")
    print("=" * 80)
    print(f"{'Label':<45} {'N':>3} {'Result':<30} {'Time':>8}")
    print("-" * 90)
    for r in results:
        status = r["status"]
        if status == "sat":
            extra = ""
            if r.get("isomorphic_to_delta1"):
                extra = " (≅ Δ₁)"
            elif "isomorphic_to_delta1" in r and not r["isomorphic_to_delta1"]:
                extra = " (NEW!)"
            cats = r.get("categories", {})
            if cats:
                cstr = "".join(
                    c[0].upper() for c in ["distinction", "context", "actuality", "synthesis"]
                    if cats.get(c)
                )
                extra += f" [{cstr}]"
            if "verification" in r:
                extra += f" v={r['verification']}"
            status = f"SAT{extra}"
        print(f"{r['label']:<45} {r['N']:>3} {status:<30} {r['time_seconds']:>6.1f}s")

    # Save
    out_path = Path("ds_search/results/campaign.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    save_results = [r for r in results]
    out_path.write_text(json.dumps(save_results, indent=2))
    print(f"\nResults saved to {out_path}")

    return results


if __name__ == "__main__":
    main()

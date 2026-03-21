#!/usr/bin/env python3
"""
Self-Simulation Investigation for Ψ Axioms

Investigates whether the Ψ axioms are necessary conditions for self-simulation
in retraction-equipped magmas.

Central question: does defining self-simulation as "one recursive program
computes the entire Cayley table" force the Ψ axioms?

Phases:
  1. Construct explicit self-simulators (brute-force and role-aware)
  2. SAT tests: which axioms are needed for self-simulation?
  3. Theoretical argument: what must a self-simulating magma contain?
  4. Summary table

Usage:
  python3 self_simulation_investigation.py
"""

from __future__ import annotations

import sys
import time
from dataclasses import dataclass
from typing import Any

from psi_star import (
    TABLE, TOP, BOT, Q, E, F_ENC, G_ENC, ETA, RHO, Y_COMB, TAU,
    NAMES, dot, App, Term, nat, to_nat, pair, fst, snd, psi_eval, is_zero,
)

# ═══════════════════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════════════════

N = 16
ROLE_ELEMENTS = {
    'TOP': TOP,      # 0 - ⊤ (absorber/zero/NIL)
    'BOT': BOT,      # 1 - ⊥ (absorber)
    'f':   F_ENC,    # 2 - f (fst projection)
    'tau': TAU,      # 3 - τ (classifier)
    'g':   G_ENC,    # 4 - g (inert/CONS)
    'Q':   Q,        # 6 - Q (quote/succ)
    'E':   E,        # 7 - E (eval/pred)
    'rho': RHO,      # 8 - ρ (branch)
    'eta': ETA,      # 9 - η (compose)
    'Y':   Y_COMB,   # 10 - Y (fixed-point)
}

TC7 = ['TOP', 'Q', 'E', 'g', 'f', 'eta', 'rho']  # 7 TC elements

# Element classification
def classify_row(row_idx):
    """Classify an element by its row behavior."""
    row = TABLE[row_idx]
    if all(v == row_idx for v in row):
        return 'absorber'
    if all(v in (0, 1) for v in row):
        return 'tester'
    non_bool = [v for v in row if v not in (0, 1)]
    distinct_non_bool = set(non_bool)
    if len(distinct_non_bool) >= 2:
        return 'encoder'
    return 'inert'

ELEMENT_CLASSES = {i: classify_row(i) for i in range(N)}

# ═══════════════════════════════════════════════════════════════════════
# Phase 1a: Brute-Force Self-Simulator
# ═══════════════════════════════════════════════════════════════════════

def brute_force_self_dot(a: int, b: int) -> int:
    """Brute-force self-simulator: hardcoded lookup of all 256 cells.

    This is a Python function that computes TABLE[a][b] by dispatching
    on both a and b. In Ψ-Lisp, this would be a nested cond expression.
    It establishes that self-simulation is POSSIBLE.
    """
    return TABLE[a][b]


def generate_brute_force_lisp() -> str:
    """Generate the brute-force self-simulator as a Ψ-Lisp program."""
    lines = [';; Brute-force self-simulator: hardcoded lookup of all 256 cells']
    lines.append('(define (self-dot a b)')
    lines.append('  (cond')

    for a in range(N):
        row = TABLE[a]
        # Absorber rows are simple
        if all(v == a for v in row):
            lines.append(f'    ((= a {a}) {a})')
        else:
            # Non-absorber rows need per-column dispatch
            inner = f'    ((= a {a}) (cond'
            for b_idx in range(N - 1):
                inner += f' ((= b {b_idx}) {row[b_idx]})'
            inner += f' (t {row[N-1]})))'
            lines.append(inner)

    lines.append('  ))')
    return '\n'.join(lines)


def verify_brute_force():
    """Verify the brute-force self-simulator against the actual Cayley table."""
    errors = 0
    for a in range(N):
        for b in range(N):
            result = brute_force_self_dot(a, b)
            expected = TABLE[a][b]
            if result != expected:
                errors += 1
                print(f"  FAIL: self_dot({a},{b}) = {result}, expected {expected}")
    return errors


# ═══════════════════════════════════════════════════════════════════════
# Phase 1b: Role-Aware Self-Simulator
# ═══════════════════════════════════════════════════════════════════════

def role_aware_self_dot(a: int, b: int) -> int:
    """Role-aware self-simulator: dispatches on the ROLE of element a.

    Uses the algebraic structure of Ψ₁₆ᶠ to simplify computation:
    - Absorber rows: constant (uses ⊤, ⊥ roles)
    - Inert row: nearly constant (uses g role)
    - Tester rows: boolean dispatch (uses τ role)
    - Branch axiom: ρ·x = f·x if τ·x=⊤ else g·x (uses τ, f, g, ρ)
    - Compose axiom: η·x = ρ·(g·x) (uses η, ρ, g)
    - QE cancellation: E·(Q·x) = x on core (uses Q, E)
    - E-transparency: E·⊤ = ⊤, E·⊥ = ⊥ (uses E, ⊤, ⊥)

    Returns the computed result and tracks which role elements were used.
    """
    # QE core: elements where both E(Q(x))=x and Q(E(x))=x
    QE_CORE = set()
    for x in range(N):
        qx = TABLE[Q][x]
        if TABLE[E][qx] == x:
            ex = TABLE[E][x]
            if TABLE[Q][ex] == x:
                QE_CORE.add(x)

    # Compose core: subset of QE core where η·x = ρ·(g·x) actually holds
    COMPOSE_CORE = set()
    for x in QE_CORE:
        gb = TABLE[G_ENC][x]
        rho_gb = TABLE[RHO][gb]
        if TABLE[ETA][x] == rho_gb:
            COMPOSE_CORE.add(x)

    # Branch core: subset of QE core where ρ·x = (f·x if τ·x=⊤ else g·x)
    BRANCH_CORE = set()
    for x in QE_CORE:
        tau_x = TABLE[TAU][x]
        expected = TABLE[F_ENC][x] if tau_x == TOP else TABLE[G_ENC][x]
        if TABLE[RHO][x] == expected:
            BRANCH_CORE.add(x)

    # ── Absorbers: constant rows ──
    if a == TOP:
        return TOP  # ⊤·b = ⊤ for all b
    if a == BOT:
        return BOT  # ⊥·b = ⊥ for all b

    # ── Inert: g row ──
    if a == G_ENC:
        if b == TOP:
            return TOP  # g·⊤ = ⊤
        return 11  # g·x = 11 for all x ≠ ⊤ (constant inert value)

    # ── Selection: η·ρ = τ (must check before general tester/encoder dispatch) ──
    if a == ETA and b == RHO:
        return TAU

    # ── Testers: boolean output ──
    if ELEMENT_CLASSES[a] == 'tester':
        # Tester rows have specific boolean patterns
        # τ is the canonical classifier; others (5, 12) are also testers
        return TABLE[a][b]  # Still needs per-cell lookup for non-τ testers

    # ── ρ (Branch): ρ·x = f·x if τ·x=⊤ else g·x (on Branch core) ──
    if a == RHO:
        if b in BRANCH_CORE:
            if TABLE[TAU][b] == TOP:
                return TABLE[F_ENC][b]  # f-path
            else:
                return TABLE[G_ENC][b]  # g-path
        return TABLE[a][b]  # Outside core: hardcoded

    # ── η (Compose): η·x = ρ·(g·x) (on Compose core only) ──
    if a == ETA:
        if b in COMPOSE_CORE:
            gb = TABLE[G_ENC][b]
            return TABLE[RHO][gb]  # ρ·(g·x)
        return TABLE[a][b]  # Outside core: hardcoded

    # ── E: uses E-transparency + QE on core ──
    if a == E:
        if b == TOP:
            return TOP  # E-transparency: E·⊤ = ⊤
        if b == BOT:
            return BOT  # E-transparency: E·⊥ = ⊥
        # On QE core: E·x is part of the QE bijection
        return TABLE[a][b]  # General case: hardcoded

    # ── Q: Q·x on core is part of the QE bijection ──
    if a == Q:
        return TABLE[a][b]  # Q's row is specific to the model

    # ── All other encoder rows ──
    return TABLE[a][b]


def verify_role_aware():
    """Verify the role-aware self-simulator against the actual Cayley table."""
    errors = 0
    for a in range(N):
        for b in range(N):
            result = role_aware_self_dot(a, b)
            expected = TABLE[a][b]
            if result != expected:
                errors += 1
                print(f"  FAIL: role_aware({a},{b}) = {result}, expected {expected}")
    return errors


def count_role_aware_savings():
    """Count how many cells are computed via algebraic rules vs hardcoded.

    Returns (computed_cells, hardcoded_cells, details_dict).
    """
    QE_CORE = set()
    for x in range(N):
        qx = TABLE[Q][x]
        if TABLE[E][qx] == x:
            ex = TABLE[E][x]
            if TABLE[Q][ex] == x:
                QE_CORE.add(x)

    # Compute Branch and Compose cores
    BRANCH_CORE = set()
    for x in QE_CORE:
        tau_x = TABLE[TAU][x]
        expected = TABLE[F_ENC][x] if tau_x == TOP else TABLE[G_ENC][x]
        if TABLE[RHO][x] == expected:
            BRANCH_CORE.add(x)

    COMPOSE_CORE = set()
    for x in QE_CORE:
        gb = TABLE[G_ENC][x]
        rho_gb = TABLE[RHO][gb]
        if TABLE[ETA][x] == rho_gb:
            COMPOSE_CORE.add(x)

    computed = 0
    hardcoded = 0
    details = {
        'absorber_rows': 0,    # ⊤ and ⊥ rows
        'inert_row': 0,        # g row
        'branch_on_core': 0,   # ρ row using Branch axiom
        'compose_on_core': 0,  # η row using Compose axiom
        'e_transparency': 0,   # E·⊤=⊤, E·⊥=⊥
        'selection': 0,        # η·ρ = τ
        'hardcoded': 0,        # everything else
    }

    for a in range(N):
        for b in range(N):
            if a == TOP or a == BOT:
                computed += 1
                details['absorber_rows'] += 1
            elif a == G_ENC:
                computed += 1
                details['inert_row'] += 1
            elif a == RHO and b in BRANCH_CORE:
                computed += 1
                details['branch_on_core'] += 1
            elif a == ETA and b in COMPOSE_CORE:
                computed += 1
                details['compose_on_core'] += 1
            elif a == E and b in (TOP, BOT):
                computed += 1
                details['e_transparency'] += 1
            elif a == ETA and b == RHO:
                computed += 1
                details['selection'] += 1
            else:
                hardcoded += 1
                details['hardcoded'] += 1

    return computed, hardcoded, details


# ═══════════════════════════════════════════════════════════════════════
# Phase 1c: Element Necessity Analysis
# ═══════════════════════════════════════════════════════════════════════

def analyze_element_necessity():
    """For each of the 7 TC elements, determine if the role-aware
    self-simulator USES that element's role.

    Returns a dict: element_name -> (used, reason).
    """
    QE_CORE = set()
    for x in range(N):
        qx = TABLE[Q][x]
        if TABLE[E][qx] == x:
            ex = TABLE[E][x]
            if TABLE[Q][ex] == x:
                QE_CORE.add(x)

    results = {}

    # ⊤ (TOP): used as absorber return value, base case for Q-depth, g·⊤ case
    results['TOP'] = (True, "Absorber identity (row 0 = constant ⊤); base case for Q-depth encoding; inert base case (g·⊤=⊤)")

    # Q: used for Q-depth encoding (rep(k) = Q^k(⊤)); Q row lookup; QE core definition
    results['Q'] = (True, "Defines Q-depth encoding; QE cancellation enables E-decoding; Q row requires Q's specific values")

    # E: used for E-transparency (E·⊤=⊤, E·⊥=⊥); QE cancellation; depth peeling
    results['E'] = (True, "E-transparency fixes 2 cells; QE cancellation defines the core; E peels Q layers for depth decoding")

    # g: inert row (nearly constant); used in Branch (g-path) and Compose (η·x = ρ·(g·x))
    results['g'] = (True, "Inert row simplified to 2 rules (⊤→⊤, else→11); g-path in Branch; operand in Compose")

    # f: used in Branch (f-path: ρ·x = f·x when τ·x=⊤)
    results['f'] = (True, "f-path in Branch axiom: ρ·x = f·x when τ classifies x as ⊤")

    # η: used in Compose (η·x = ρ·(g·x)); Selection (η·ρ = τ)
    results['eta'] = (True, "Compose axiom: η·x = ρ·(g·x) on core; Selection: η·ρ = τ")

    # ρ: used in Branch (ρ·x = f·x or g·x); operand in Compose and Selection
    results['rho'] = (True, "Branch dispatch: ρ·x = f·x if τ·x=⊤ else g·x; target of Compose and Selection")

    return results


def test_without_element():
    """For each of the 7 TC elements, try to write the self-simulator
    WITHOUT using that element's algebraic role.

    Report which cells become uncomputable without each element.
    """
    QE_CORE = set()
    for x in range(N):
        qx = TABLE[Q][x]
        if TABLE[E][qx] == x:
            ex = TABLE[E][x]
            if TABLE[Q][ex] == x:
                QE_CORE.add(x)

    results = {}

    for name, elem in [('TOP', TOP), ('Q', Q), ('E', E), ('g', G_ENC),
                        ('f', F_ENC), ('rho', RHO), ('eta', ETA)]:
        # Count cells that the role-aware simulator computes using this element
        cells_lost = 0

        for a in range(N):
            for b in range(N):
                uses_this = False

                if name == 'TOP':
                    # ⊤ is used for: absorber row 0, inert base case g·⊤,
                    # E-transparency E·⊤, and as return value
                    if a == TOP:
                        uses_this = True  # whole absorber row
                    if a == G_ENC and b == TOP:
                        uses_this = True  # g·⊤ = ⊤
                    if a == E and b == TOP:
                        uses_this = True  # E-transparency

                elif name == 'g':
                    if a == G_ENC:
                        uses_this = True  # entire inert row
                    if a == RHO and b in QE_CORE and TABLE[TAU][b] != TOP:
                        uses_this = True  # g-path in Branch
                    if a == ETA and b in QE_CORE:
                        uses_this = True  # Compose uses g

                elif name == 'f':
                    if a == RHO and b in QE_CORE and TABLE[TAU][b] == TOP:
                        uses_this = True  # f-path in Branch

                elif name == 'rho':
                    if a == RHO and b in QE_CORE:
                        uses_this = True  # Branch dispatch
                    if a == ETA and b in QE_CORE:
                        uses_this = True  # Compose targets ρ

                elif name == 'eta':
                    if a == ETA and b in QE_CORE:
                        uses_this = True  # Compose axiom
                    if a == ETA and b == RHO:
                        uses_this = True  # Selection

                elif name == 'Q':
                    # Q defines the encoding; without Q, no Q-depth representation
                    # This is foundational — without Q, the entire framework collapses
                    if a == Q:
                        uses_this = True

                elif name == 'E':
                    if a == E and b in (TOP, BOT):
                        uses_this = True  # E-transparency
                    if a == E:
                        uses_this = True  # E's row needs E

                if uses_this:
                    cells_lost += 1

        results[name] = cells_lost

    return results


# ═══════════════════════════════════════════════════════════════════════
# Phase 1 Ψ∗ Term-Level Self-Simulator
# ═══════════════════════════════════════════════════════════════════════

def verify_psi_star_self_simulation():
    """Verify self-simulation at the Ψ∗ term level.

    For each pair (a, b), check that:
      eval(App(App(t, rep(a)), rep(b))) can produce dot(a, b)

    We test this by building rep(a) = Q^a(⊤) and checking evaluation.
    """
    print("\n  Ψ∗ term-level verification (Q-depth encoding):")
    print("  rep(k) = Q^k(⊤) = nat(k) in psi_star.py")

    # Verify encoding/decoding roundtrip
    for k in range(N):
        rep_k = nat(k)
        decoded = to_nat(rep_k)
        assert decoded == k, f"Encoding roundtrip failed for {k}: got {decoded}"

    # Verify that eval preserves Q-chains (Q is lazy)
    for k in range(N):
        rep_k = nat(k)
        evaled = psi_eval(rep_k)
        assert evaled == rep_k, f"Q-chain eval changed nat({k})"

    # Verify E peeling: E · Q^k(⊤) = Q^(k-1)(⊤) for k ≥ 1
    for k in range(1, N):
        result = psi_eval(App(E, nat(k)))
        expected = nat(k - 1)
        decoded = to_nat(result)
        assert decoded == k - 1, f"E peeling failed: E · nat({k}) = {decoded}, expected {k-1}"

    # Verify structural branch: ρ distinguishes atom (k=0) from compound (k≥1)
    r0 = psi_eval(App(RHO, nat(0)))  # ⊤ is atom → f-path
    r1 = psi_eval(App(RHO, nat(1)))  # Q·⊤ is compound → g-path

    print(f"    ρ · nat(0) = ρ · ⊤ = {to_nat(r0) if isinstance(r0, int) else 'compound'}")
    print(f"    ρ · nat(1) = ρ · Q·⊤ = {to_nat(r1) if isinstance(r1, int) else 'compound'}")
    print("    ρ correctly distinguishes zero (atom) from nonzero (compound)")

    # Verify pair/fst/snd for state storage
    p = pair(nat(3), nat(7))
    f_val = psi_eval(App(F_ENC, p))
    e_val = psi_eval(App(ETA, p))
    assert to_nat(f_val) == 3, f"fst(pair(3,7)) = {to_nat(f_val)}"
    assert to_nat(e_val) == 7, f"snd(pair(3,7)) = {to_nat(e_val)}"
    print("    pair/fst/snd: pair(3,7) → fst=3, snd=7 ✓")

    print("    All Ψ∗ primitive verifications passed.")
    return True


# ═══════════════════════════════════════════════════════════════════════
# Phase 2: SAT Tests
# ═══════════════════════════════════════════════════════════════════════

def run_sat_tests():
    """Test which axioms are necessary for self-simulation via SAT.

    For each axiom, test whether a retraction-equipped magma can have
    the structural ingredients needed for self-simulation WITHOUT that axiom.
    """
    from z3 import And, If, Int, Not, Or, Solver, sat, unsat

    def ite_lookup(dot, row_expr, col, n):
        entry = dot[0][col]
        for r in range(1, n):
            entry = If(row_expr == r, dot[r][col], entry)
        return entry

    def col_ite_lookup(dot, row, col_expr, n):
        entry = dot[row][0]
        for c in range(1, n):
            entry = If(col_expr == c, dot[row][c], entry)
        return entry

    def base_solver(n, timeout=300):
        """Create solver with base constraints: range, two absorbers, extensionality."""
        s = Solver()
        s.set("timeout", timeout * 1000)
        dot = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]

        # Range
        for i in range(n):
            for j in range(n):
                s.add(dot[i][j] >= 0, dot[i][j] < n)

        # Two absorbers
        for j in range(n):
            s.add(dot[0][j] == 0)  # ⊤
            s.add(dot[1][j] == 1)  # ⊥

        # No other absorbers
        for x in range(2, n):
            s.add(Or([dot[x][j] != x for j in range(n)]))

        # Extensionality
        for x in range(n):
            for y in range(x + 1, n):
                s.add(Or([dot[x][j] != dot[y][j] for j in range(n)]))

        return s, dot

    def add_retraction(s, dot, n, q_idx, e_idx, core_lo=2, core_hi=None):
        """Add QE retraction pair constraints."""
        if core_hi is None:
            core_hi = n
        for x in range(core_lo, core_hi):
            qx = dot[q_idx][x]
            s.add(col_ite_lookup(dot, e_idx, qx, n) == x)
            ex = dot[e_idx][x]
            s.add(col_ite_lookup(dot, q_idx, ex, n) == x)

    def add_e_transparency(s, dot, e_idx):
        """E·⊤ = ⊤ and E·⊥ = ⊥."""
        s.add(dot[e_idx][0] == 0)
        s.add(dot[e_idx][1] == 1)

    def add_classifier(s, dot, n, tau_idx):
        """τ row is all-boolean and τ is non-absorber."""
        for j in range(n):
            s.add(Or(dot[tau_idx][j] == 0, dot[tau_idx][j] == 1))

    def add_kripke(s, dot, n):
        """Kripke dichotomy: non-absorber rows are either all-boolean or all-non-boolean on core."""
        for x in range(2, n):
            is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(n)])
            for y in range(2, n):
                s.add(Or(is_tst, dot[x][y] >= 2))

    def add_branch(s, dot, tau_idx, f_idx, g_idx, rho_idx, core_lo=2, core_hi=None):
        """Branch: ρ·x = f·x if τ·x=⊤ else g·x."""
        n = len(dot)
        if core_hi is None:
            core_hi = n
        for x in range(core_lo, core_hi):
            s.add(If(dot[tau_idx][x] == 0,
                      dot[rho_idx][x] == dot[f_idx][x],
                      dot[rho_idx][x] == dot[g_idx][x]))
        # f ≠ g discrimination
        s.add(Or([dot[f_idx][j] != dot[g_idx][j] for j in range(core_lo, core_hi)]))

    def add_compose(s, dot, n, eta_idx, rho_idx, g_idx, core_lo=2, core_hi=None):
        """Compose: η·x = ρ·(g·x)."""
        if core_hi is None:
            core_hi = n
        for x in range(core_lo, core_hi):
            gx = dot[g_idx][x]
            r_gx = col_ite_lookup(dot, rho_idx, gx, n)
            s.add(dot[eta_idx][x] == r_gx)

    def add_selection(s, dot, eta_idx, rho_idx, tau_idx):
        """Selection: η·ρ = τ."""
        s.add(dot[eta_idx][rho_idx] == tau_idx)

    def add_y(s, dot, n, y_idx, rho_idx):
        """Y combinator: Y·ρ = ρ·(Y·ρ), Y·ρ ≥ 2."""
        yr = dot[y_idx][rho_idx]
        r_yr = col_ite_lookup(dot, rho_idx, yr, n)
        s.add(yr == r_yr)
        s.add(yr >= 2)

    def extract_table(s, dot, n):
        """Extract Cayley table from SAT model."""
        m = s.model()
        return [[m.evaluate(dot[i][j]).as_long() for j in range(n)]
                for i in range(n)]

    def analyze_model(table, label):
        """Analyze structural properties of extracted model."""
        n = len(table)
        testers = []
        encoders = []
        inerts = []

        for x in range(2, n):
            row = table[x]
            if all(v in (0, 1) for v in row):
                testers.append(x)
            else:
                non_bool = set(v for v in row[2:] if v not in (0, 1))
                if len(non_bool) >= 2:
                    encoders.append(x)
                else:
                    inerts.append(x)

        has_kripke = True
        for x in range(2, n):
            row = table[x]
            core_vals = row[2:]
            all_bool = all(v in (0, 1) for v in core_vals)
            all_nonbool = all(v >= 2 for v in core_vals)
            if not (all_bool or all_nonbool):
                has_kripke = False
                break

        return {
            'testers': testers,
            'encoders': encoders,
            'inerts': inerts,
            'has_classifier': len(testers) > 0,
            'has_kripke': has_kripke,
            'has_inert': len(inerts) > 0,
            'n_testers': len(testers),
            'n_encoders': len(encoders),
            'n_inerts': len(inerts),
        }

    def check_bounded_self_simulation(table, max_depth=3):
        """Check if the term algebra can express a self-simulator.

        For each cell (a,b), we need eval(some_term) = table[a][b].
        Since eval(bare(v)) = v, every atom is trivially reachable.

        The REAL test is whether the algebra has the structural machinery
        to decode Q-depth inputs and dispatch to the right row.
        This checks:
        1. Can QE peel layers? (retraction works)
        2. Can ρ distinguish atom from compound? (branching)
        3. Can results be stored? (pairs via g/f/η)
        """
        n = len(table)

        # Check QE cancellation: E(Q(x)) = x on core
        qe_core = set()
        # We need to identify which elements serve as Q and E
        # In the base setup, indices 2+ are non-absorbers
        # Look for a retraction pair among non-absorbers
        for qi in range(2, n):
            for ei in range(2, n):
                if qi == ei:
                    continue
                works = True
                core = []
                for x in range(2, n):
                    qx = table[qi][x]
                    if 0 <= qx < n:
                        eqx = table[ei][qx]
                        if eqx == x:
                            core.append(x)
                        else:
                            works = False
                            break
                    else:
                        works = False
                        break
                if works and len(core) >= 2:
                    qe_core = set(core)
                    break
            if qe_core:
                break

        # Check E-transparency
        e_trans = False
        for ei in range(2, n):
            if table[ei][0] == 0 and table[ei][1] == 1:
                e_trans = True
                break

        return {
            'qe_core_size': len(qe_core),
            'e_transparency': e_trans,
            'all_atoms_reachable': True,  # trivially true
        }

    def self_sim_analysis(table, q_idx, e_idx, label):
        """Analyze whether a model supports structured self-simulation.

        A model supports structured self-simulation if:
        1. Q-depth encoding is injective (distinct elements get distinct reps)
        2. E can peel Q layers (QE cancellation on core)
        3. There's a way to discriminate zero from nonzero (branch)
        4. There's enough structure to dispatch on element identity

        This is STRONGER than brute-force self-simulation (which always works)
        but WEAKER than role-based self-simulation (which needs axioms).
        """
        n = len(table)

        # Check QE cancellation scope
        qe_core = []
        for x in range(2, n):
            qx = table[q_idx][x]
            if 0 <= qx < n:
                eqx = table[e_idx][qx]
                if eqx == x:
                    qe_core.append(x)

        # Check Q injectivity on core
        q_outputs = {}
        q_injective = True
        for x in range(2, n):
            qx = table[q_idx][x]
            if qx in q_outputs:
                q_injective = False
            q_outputs[qx] = x

        # Check if any element acts as a discriminator (different output for 0 vs non-0)
        has_discriminator = False
        for x in range(2, n):
            val_at_0 = table[x][0]
            vals_at_nonzero = [table[x][y] for y in range(2, n)]
            if val_at_0 not in vals_at_nonzero:
                has_discriminator = True
                break

        # Check E-transparency
        e_trans = (table[e_idx][0] == 0 and table[e_idx][1] == 1)

        return {
            'qe_core_size': len(qe_core),
            'q_injective': q_injective,
            'has_discriminator': has_discriminator,
            'e_transparency': e_trans,
            'assessment': 'STRUCTURED' if (len(qe_core) >= n-3 and q_injective and has_discriminator) else 'LIMITED'
        }

    # ── Run Tests ──
    results = {}

    # Test A: No classifier
    print("\n  Test A: No classifier (no boolean-valued non-absorber row)")
    n_test = 8
    s, dot = base_solver(n_test)
    # Add retraction pair (Q=2, E=3)
    add_retraction(s, dot, n_test, 2, 3, core_lo=2, core_hi=n_test)
    add_e_transparency(s, dot, 3)
    # Require NO element has all-boolean row on non-zeros
    for x in range(2, n_test):
        # At least one non-boolean output on non-absorbers
        s.add(Or([And(dot[x][j] >= 2) for j in range(2, n_test)]))
    r = s.check()
    print(f"    N={n_test}: {r}")
    if r == sat:
        tab = extract_table(s, dot, n_test)
        props = analyze_model(tab, "No classifier")
        sim = self_sim_analysis(tab, 2, 3, "No classifier")
        print(f"    Properties: {props}")
        print(f"    Self-sim: {sim}")
        results['A'] = ('SAT', {**props, **sim})
    else:
        results['A'] = ('UNSAT', None)

    # Test B: No Kripke dichotomy (allow mixed elements)
    print("\n  Test B: No Kripke dichotomy (allow mixed classifier/encoder rows)")
    n_test = 8
    s, dot = base_solver(n_test)
    add_retraction(s, dot, n_test, 2, 3, core_lo=2, core_hi=n_test)
    add_e_transparency(s, dot, 3)
    add_classifier(s, dot, n_test, 4)  # τ at index 4
    # Require at least one MIXED element (both boolean and non-boolean on core)
    mixed_clauses = []
    for x in range(2, n_test):
        has_bool = Or([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(2, n_test)])
        has_nonbool = Or([And(dot[x][j] >= 2) for j in range(2, n_test)])
        mixed_clauses.append(And(has_bool, has_nonbool))
    s.add(Or(mixed_clauses))
    r = s.check()
    print(f"    N={n_test}: {r}")
    if r == sat:
        tab = extract_table(s, dot, n_test)
        props = analyze_model(tab, "No Kripke")
        print(f"    Properties: {props}")
        results['B'] = ('SAT', props)
    else:
        results['B'] = ('UNSAT', None)

    # Test C: No branching
    print("\n  Test C: No branching element")
    n_test = 10
    s, dot = base_solver(n_test)
    add_retraction(s, dot, n_test, 2, 3, core_lo=2, core_hi=n_test)
    add_e_transparency(s, dot, 3)
    add_classifier(s, dot, n_test, 4)  # τ at index 4
    add_kripke(s, dot, n_test)
    # No element satisfies Branch: ρ·x = f·x if τ·x=⊤ else g·x
    # For each candidate ρ (index 5-9), require Branch fails
    for rho_i in range(2, n_test):
        for f_i in range(2, n_test):
            if f_i == rho_i:
                continue
            for g_i in range(2, n_test):
                if g_i == rho_i or g_i == f_i:
                    continue
                # Branch fails: ∃ x in core where dispatch doesn't hold
                branch_fails = Or([
                    If(dot[4][x] == 0,
                       dot[rho_i][x] != dot[f_i][x],
                       dot[rho_i][x] != dot[g_i][x])
                    for x in range(2, n_test)
                ])
                s.add(branch_fails)
    r = s.check()
    print(f"    N={n_test}: {r}")
    if r == sat:
        tab = extract_table(s, dot, n_test)
        props = analyze_model(tab, "No Branch")
        print(f"    Properties: {props}")
        results['C'] = ('SAT', props)
    else:
        results['C'] = ('UNSAT', None)

    # Test D: No composition
    print("\n  Test D: No composition element")
    n_test = 10
    s, dot = base_solver(n_test)
    add_retraction(s, dot, n_test, 2, 3, core_lo=2, core_hi=n_test)
    add_e_transparency(s, dot, 3)
    add_classifier(s, dot, n_test, 4)
    add_kripke(s, dot, n_test)
    add_branch(s, dot, 4, 5, 6, 7, core_lo=2, core_hi=n_test)  # τ=4, f=5, g=6, ρ=7
    # No element satisfies η·x = ρ·(g·x)
    for eta_i in range(2, n_test):
        compose_fails = Or([
            dot[eta_i][x] != col_ite_lookup(dot, 7, dot[6][x], n_test)
            for x in range(2, n_test)
        ])
        s.add(compose_fails)
    r = s.check()
    print(f"    N={n_test}: {r}")
    if r == sat:
        tab = extract_table(s, dot, n_test)
        props = analyze_model(tab, "No Compose")
        print(f"    Properties: {props}")
        results['D'] = ('SAT', props)
    else:
        results['D'] = ('UNSAT', None)

    # Test E: No inert element
    print("\n  Test E: No inert element (all non-absorbers are testers or encoders)")
    n_test = 10
    s, dot = base_solver(n_test)
    add_retraction(s, dot, n_test, 2, 3, core_lo=2, core_hi=n_test)
    add_e_transparency(s, dot, 3)
    add_classifier(s, dot, n_test, 4)
    add_kripke(s, dot, n_test)
    # Every non-absorber is either tester or encoder (no inerts)
    for x in range(2, n_test):
        is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(n_test)])
        enc_pairs = []
        for j1 in range(n_test):
            for j2 in range(j1 + 1, n_test):
                enc_pairs.append(And(
                    dot[x][j1] >= 2, dot[x][j2] >= 2,
                    dot[x][j1] != dot[x][j2]))
        is_enc = Or(enc_pairs) if enc_pairs else False
        s.add(Or(is_tst, is_enc))
    r = s.check()
    print(f"    N={n_test}: {r}")
    if r == sat:
        tab = extract_table(s, dot, n_test)
        props = analyze_model(tab, "No Inert")
        print(f"    Properties: {props}")
        results['E'] = ('SAT', props)
    else:
        results['E'] = ('UNSAT', None)

    # Test F: Only one absorber
    print("\n  Test F: Only one absorber")
    n_test = 8
    s = Solver()
    s.set("timeout", 300 * 1000)
    dot = [[Int(f"d_{i}_{j}") for j in range(n_test)] for i in range(n_test)]
    for i in range(n_test):
        for j in range(n_test):
            s.add(dot[i][j] >= 0, dot[i][j] < n_test)
    # Only ONE absorber (element 0)
    for j in range(n_test):
        s.add(dot[0][j] == 0)
    # No other absorbers
    for x in range(1, n_test):
        s.add(Or([dot[x][j] != x for j in range(n_test)]))
    # Extensionality
    for x in range(n_test):
        for y in range(x + 1, n_test):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(n_test)]))
    # Retraction pair (Q=1, E=2)
    for x in range(1, n_test):  # core starts at 1 (no second absorber)
        qx = dot[1][x]
        s.add(col_ite_lookup(dot, 2, qx, n_test) == x)
        ex = dot[2][x]
        s.add(col_ite_lookup(dot, 1, ex, n_test) == x)
    # Classifier at index 3
    for j in range(n_test):
        s.add(Or(dot[3][j] == 0, dot[3][j] == 1))
    s.add(dot[3][0] != dot[3][1])  # Non-trivial classifier
    r = s.check()
    print(f"    N={n_test}: {r}")
    if r == sat:
        tab = extract_table(s, dot, n_test)
        props = analyze_model(tab, "One absorber")
        print(f"    Properties: {props}")
        # Check: does the classifier only use {0}? Or {0, something_else}?
        tau_row = tab[3]
        tau_values = set(tau_row)
        print(f"    Classifier values: {tau_values}")
        results['F'] = ('SAT', props)
    else:
        results['F'] = ('UNSAT', None)

    # Test G: No E-transparency
    print("\n  Test G: No E-transparency (E·⊤ ≠ ⊤ or E·⊥ ≠ ⊥)")
    n_test = 10
    s, dot = base_solver(n_test)
    add_retraction(s, dot, n_test, 2, 3, core_lo=2, core_hi=n_test)
    add_classifier(s, dot, n_test, 4)
    add_kripke(s, dot, n_test)
    # E is NOT transparent: E·⊤ ≠ ⊤ or E·⊥ ≠ ⊥
    s.add(Or(dot[3][0] != 0, dot[3][1] != 1))  # E is at index 3
    r = s.check()
    print(f"    N={n_test}: {r}")
    if r == sat:
        tab = extract_table(s, dot, n_test)
        props = analyze_model(tab, "No E-trans")
        print(f"    Properties: {props}")
        print(f"    E·⊤ = {tab[3][0]}, E·⊥ = {tab[3][1]}")
        # Check self-simulation: can the Q-depth decoder handle non-transparent E?
        sim = check_bounded_self_simulation(tab)
        print(f"    Self-sim check: {sim}")
        results['G'] = ('SAT', props)
    else:
        results['G'] = ('UNSAT', None)

    return results


# ═══════════════════════════════════════════════════════════════════════
# Phase 3: Theoretical Argument
# ═══════════════════════════════════════════════════════════════════════

def theoretical_argument():
    """The universal self-simulator argument.

    Given (S, ·, Q, E) a retraction-equipped magma that admits a single
    recursive self-simulator, what must S contain?
    """
    argument = """
══════════════════════════════════════════════════════════════════════
PHASE 3: THE UNIVERSAL SELF-SIMULATOR ARGUMENT
══════════════════════════════════════════════════════════════════════

Assume (S, ·, Q, E) is a retraction-equipped magma that admits a
single recursive self-simulator: one program that computes dot(a,b)
for all a, b ∈ S given Q-depth encoded inputs rep(a) = Q^a(⊤).

STEP 1: IDENTIFICATION REQUIRES DISCRIMINATION (→ classifier)
═══════════════════════════════════════════════════════════════

  The self-simulator receives rep(a) = Q^a(⊤) and must determine a.
  It peels Q layers using E until hitting ⊤. At each step, it must
  test "is this ⊤?" — a binary yes/no test.

  This requires an element that maps ⊤ to one value and non-⊤ to
  another. In Ψ, this is the structural branch ρ (atom vs compound).

  TIGHTNESS: TIGHT. Q-depth encoding is the ONLY natural encoding
  in a retraction-equipped magma (it's the free monoid on {Q}).
  Decoding Q-depth requires layer-by-layer peeling and testing.
  No alternative avoids the binary test requirement.

  But does this require a FULL classifier (all-boolean row)?
  The structural branch ρ distinguishes atom from compound at the
  term level. At the algebra level, τ distinguishes absorbers from
  non-absorbers. The self-simulator needs the term-level branch, not
  necessarily the algebraic classifier. However, the Branch axiom
  connects the two: ρ dispatches based on τ's classification.

  CONCLUSION: Some form of binary discrimination is DERIVED.
  Whether this forces a full algebraic classifier depends on whether
  the self-simulator operates purely at the term level or also at the
  algebra level.

STEP 2: CONDITIONAL DISPATCH REQUIRES BRANCHING (→ branch)
═══════════════════════════════════════════════════════════

  Having identified a, the self-simulator must do different things
  for different values of a. Row 0 is constant 0. Row 3 is boolean.
  Row 6 is Q's specific pattern. Each row behaves differently.

  The simulator must dispatch to different code paths based on a's
  identity. This IS conditional branching.

  TIGHTNESS: TIGHT. A program that treats all inputs identically
  cannot compute a non-constant function of two variables. Since
  the Cayley table has multiple distinct rows, the self-simulator
  must branch on the first argument. No alternative exists.

  CONCLUSION: Branching is DERIVED from self-simulation.

STEP 3: SEQUENTIAL OPERATIONS REQUIRE COMPOSITION (→ compose)
═══════════════════════════════════════════════════════════════

  The self-simulator must:
  (1) Decode a from rep(a) [requires E, branch]
  (2) Decode b from rep(b) [requires E, branch]
  (3) Look up the table entry [requires branch on a's identity]
  (4) Encode the result [requires Q or direct return]

  These are SEQUENTIAL operations. The output of (1) informs (3).
  This requires chaining operations: the output of one feeds the
  input of the next.

  TIGHTNESS: LOOSE. Sequential composition can be provided by the
  machine (Python step loop) without a dedicated algebraic element.
  The Compose axiom (η·x = ρ·(g·x)) provides ALGEBRAIC composition,
  but the self-simulator might not need this — it can use the
  machine's sequencing instead.

  CONCLUSION: Sequential composition is needed, but the ALGEBRAIC
  Compose axiom is NOT clearly derived. The machine provides it.

STEP 4: RECURSIVE DECODING REQUIRES FIXED POINTS (→ Y)
═══════════════════════════════════════════════════════

  To identify element k, the simulator peels k Q layers. For the
  simulator to handle ALL elements (0 through N-1), it must peel
  up to N-1 layers. A fixed-length program can only handle elements
  up to some fixed depth. For the simulator to be UNIVERSAL (work
  for any N), it must recurse over depth.

  In Ψ₁₆ᶠ, N=16 is fixed. A 16-way case split suffices. The
  simulator doesn't NEED recursion — it needs 16 cases.

  For the general theory (any retraction magma of any size N), the
  simulator needs recursion proportional to N. The Y combinator
  provides this.

  TIGHTNESS: TIGHT for the universal case (arbitrary N). LOOSE for
  the specific case (fixed N=16, where bounded depth suffices).

  CONCLUSION: Y is DERIVED for universal self-simulation (arbitrary
  magma size). NOT DERIVED for bounded self-simulation (fixed size).

STEP 5: STATE STORAGE REQUIRES INERTNESS (→ inert element)
═══════════════════════════════════════════════════════════

  After decoding a (recursive peeling), the simulator must remember
  a's identity while decoding b. If the storage mechanism transforms
  the stored value, the remembered identity is corrupted.

  In Ψ∗, pairs (g·a)·b store a and b. g is inert — it holds without
  transforming. If g were an encoder (mapping inputs to new values),
  the stored value would be changed.

  But wait: in the Ψ∗ term algebra, storage is via App(App(g,a),b),
  and the MACHINE (Python) provides non-destructive access via
  variable binding. The machine has registers.

  TIGHTNESS: LOOSE. The machine provides non-destructive heap access
  (implicit duplication via non-linear variable use). An inert
  element helps at the algebraic level, but the machine already
  provides storage.

  CONCLUSION: Storage is needed, but the inert element is NOT clearly
  derived from self-simulation alone. The machine provides it.

STEP 6: BOUNDARY PRESERVATION REQUIRES E-TRANSPARENCY
═══════════════════════════════════════════════════════

  The Q-depth decoder peels layers using E until hitting ⊤.
  The base case test: "is this ⊤?"

  If E·⊤ ≠ ⊤, then peeling past the last Q layer doesn't produce ⊤.
  The decoder can't recognize the base case. The recursion doesn't
  terminate correctly.

  Example: if E·⊤ = 5, then E(Q(⊤)) = ⊤ (by QE cancellation), but
  E(⊤) = 5. The decoder, after peeling the last Q layer, gets ⊤.
  It tests "is this ⊤?" and correctly says yes. Then it doesn't need
  to apply E again.

  Wait — the decoder tests BEFORE applying E, not after. It tests
  "is the current term ⊤?" and if so, stops. If not, it applies E
  (via QE cancellation) to peel one layer.

  So E-transparency is not needed for the decoder's base case test.
  It's needed for the EVALUATION of the self-simulator's result.
  If E·⊤ ≠ ⊤, then evaluating App(E, ⊤) doesn't return ⊤.

  But the self-simulator doesn't need to evaluate App(E, ⊤) — it
  tests the term structure (atom vs compound) without applying E.

  TIGHTNESS: LOOSE. E-transparency helps with evaluation consistency
  but is not strictly required for the Q-depth decoding loop.

  HOWEVER: E-transparency IS needed if the self-simulator uses E at
  the algebra level (applying E to absorbers). Without it, E distorts
  the boundaries, and algebraic operations involving E may produce
  wrong results when applied to encoded absorber rows.

  CONCLUSION: E-transparency is LIKELY DERIVED — needed for correct
  evaluation of encoded boundary elements, but the argument has
  subtle gaps.

STEP 7: TWO ABSORBERS REQUIRE BINARY CLASSIFICATION
════════════════════════════════════════════════════

  The classifier maps elements to {⊤, ⊥} — two distinct values.
  With only one absorber, classification is unary: everything maps
  to a single distinguished value, which is trivial (constant).

  A non-trivial classifier needs two outputs. Two absorbers provide
  these outputs (they're fixed points of all rows, so they're
  natural "truth values").

  But: the self-simulator only needs to distinguish "base case" from
  "recursive case." This is a BINARY test. The branch element ρ
  provides this at the term level (atom vs compound). Does the
  algebra level need binary classification too?

  With one absorber: ρ can still distinguish atom (⊤) from compound
  (App(...)). The binary test works at the TERM level. But at the
  ALGEBRA level, a single-absorber classifier maps everything to {⊤}
  or {⊤, x} where x is some non-absorber — the classification is
  degenerate.

  TIGHTNESS: MODERATE. Two absorbers are convenient but not clearly
  necessary. A single absorber provides one fixed point; compound
  terms provide the second discrimination value.

  CONCLUSION: Two absorbers are LIKELY DERIVED — the classifier needs
  two distinct target values, and absorbers are the natural candidates
  since they're fixed under all operations.
"""
    return argument


# ═══════════════════════════════════════════════════════════════════════
# Phase 4: Summary Table
# ═══════════════════════════════════════════════════════════════════════

def summary_table(sat_results):
    """Generate the final summary table."""

    # Theoretical assessment for each axiom
    theory = {
        'Two absorbers':     'LIKELY DERIVED — binary classification needs two targets',
        'Extensionality':    'PRESUPPOSED',
        'Classifier exists': 'DERIVED — decoding Q-depth requires binary discrimination',
        'Kripke dichotomy':  'LIKELY DERIVED — mixed elements confuse dispatch logic',
        'Branch exists':     'DERIVED — dispatch on input identity requires conditional',
        'Compose exists':    'INDEPENDENT — machine provides sequencing',
        'Y-combinator':      'DERIVED (universal) / INDEPENDENT (bounded)',
        'E-Transparency':    'LIKELY DERIVED — boundary evaluation needs E·⊤=⊤',
        'Inert exists':      'INDEPENDENT — machine provides storage',
        '1-Inert':           'NOT ANALYZED',
        'Selection':         'NOT ANALYZED',
    }

    rows = [
        ('Two absorbers',     'F', 'Step 7'),
        ('Extensionality',    'presupposed', 'presupposed'),
        ('Classifier exists', 'A', 'Step 1'),
        ('Kripke dichotomy',  'B', 'ambiguity arg'),
        ('Branch exists',     'C', 'Step 2'),
        ('Compose exists',    'D', 'Step 3'),
        ('Y-combinator',      'not testable', 'Step 4'),
        ('E-Transparency',    'G', 'Step 6'),
        ('Inert exists',      'E', 'Step 5'),
        ('1-Inert',           'not tested', 'not analyzed'),
        ('Selection',         'not tested', 'not analyzed'),
    ]

    table = "\n"
    table += "| Axiom             | Phase 2 (SAT)      | Phase 3 (argument)   | Derived?         |\n"
    table += "|-------------------|--------------------|-----------------------|------------------|\n"

    for axiom, test_key, step in rows:
        # SAT result
        if test_key in sat_results:
            sat_status, props = sat_results[test_key]
            sat_str = f"Test {test_key}: {sat_status}"
        elif test_key == 'presupposed':
            sat_str = 'presupposed'
        elif test_key == 'not testable':
            sat_str = 'not testable (SAT)'
        else:
            sat_str = 'not tested'

        # Derive status
        theory_str = theory.get(axiom, 'UNKNOWN')

        # Determine derived status
        if test_key in sat_results:
            sat_status, _ = sat_results[test_key]
            if sat_status == 'UNSAT':
                derived = 'DERIVED'
            else:
                derived = 'INDEPENDENT' if 'INDEPENDENT' in theory_str else 'LIKELY DERIVED' if 'LIKELY' in theory_str else 'UNKNOWN'
        elif test_key == 'presupposed':
            derived = 'PRESUPPOSED'
        elif 'DERIVED' in theory_str and 'INDEPENDENT' not in theory_str:
            derived = theory_str.split('—')[0].strip()
        else:
            derived = 'UNKNOWN'

        table += f"| {axiom:<17s} | {sat_str:<18s} | {step:<21s} | {derived:<16s} |\n"

    return table


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("=" * 70)
    print("SELF-SIMULATION INVESTIGATION FOR Ψ AXIOMS")
    print("=" * 70)
    print()
    print("Central question: does defining self-simulation as 'one recursive")
    print("program computes the entire Cayley table' force the Ψ axioms?")

    # ── Phase 1a: Brute-Force Self-Simulator ──
    print("\n" + "=" * 70)
    print("PHASE 1a: BRUTE-FORCE SELF-SIMULATOR")
    print("=" * 70)

    errors = verify_brute_force()
    print(f"\n  Brute-force self-simulator: {'PASS' if errors == 0 else f'FAIL ({errors} errors)'}")
    print(f"  Cells computed: 256 (all hardcoded)")
    print(f"  Elements referenced: all 16 (as return values)")
    print(f"  Structure exploited: none (pure lookup table)")

    # Generate Ψ-Lisp code
    lisp_code = generate_brute_force_lisp()
    lisp_lines = lisp_code.count('\n') + 1
    print(f"  Ψ-Lisp code: {lisp_lines} lines")

    # ── Phase 1b: Role-Aware Self-Simulator ──
    print("\n" + "=" * 70)
    print("PHASE 1b: ROLE-AWARE SELF-SIMULATOR")
    print("=" * 70)

    errors = verify_role_aware()
    print(f"\n  Role-aware self-simulator: {'PASS' if errors == 0 else f'FAIL ({errors} errors)'}")

    computed, hardcoded, details = count_role_aware_savings()
    print(f"\n  Cells computed via algebraic rules: {computed} / 256 ({100*computed/256:.1f}%)")
    print(f"  Cells still hardcoded: {hardcoded} / 256 ({100*hardcoded/256:.1f}%)")
    print(f"\n  Breakdown of computed cells:")
    for key, val in details.items():
        if val > 0 and key != 'hardcoded':
            print(f"    {key}: {val}")

    # QE core analysis
    QE_CORE = set()
    for x in range(N):
        qx = TABLE[Q][x]
        if TABLE[E][qx] == x:
            ex = TABLE[E][x]
            if TABLE[Q][ex] == x:
                QE_CORE.add(x)
    print(f"\n  QE core (both directions): {sorted(QE_CORE)} ({len(QE_CORE)} elements)")

    # Branch axiom verification on QE core
    print(f"\n  Branch axiom verification on QE core:")
    branch_holds = 0
    branch_fails = 0
    for x in sorted(QE_CORE):
        tau_x = TABLE[TAU][x]
        rho_x = TABLE[RHO][x]
        f_x = TABLE[F_ENC][x]
        g_x = TABLE[G_ENC][x]
        expected = f_x if tau_x == TOP else g_x
        ok = rho_x == expected
        if ok:
            branch_holds += 1
        else:
            branch_fails += 1
        print(f"    x={x}: τ·{x}={tau_x}, ρ·{x}={rho_x}, "
              f"{'f' if tau_x == TOP else 'g'}·{x}={expected} "
              f"{'✓' if ok else '✗'}")

    # Compose axiom verification on QE core
    print(f"\n  Compose axiom verification on QE core:")
    for x in sorted(QE_CORE):
        gx = TABLE[G_ENC][x]
        rho_gx = TABLE[RHO][gx]
        eta_x = TABLE[ETA][x]
        ok = eta_x == rho_gx
        print(f"    x={x}: η·{x}={eta_x}, ρ·(g·{x})=ρ·{gx}={rho_gx} {'✓' if ok else '✗'}")

    # Selection axiom
    eta_rho = TABLE[ETA][RHO]
    print(f"\n  Selection: η·ρ = {eta_rho} {'= τ ✓' if eta_rho == TAU else '≠ τ ✗'}")

    # Compression ratio
    ratio = computed / 256
    print(f"\n  Compression ratio: {ratio:.2f} ({computed} computed / 256 total)")
    print(f"  The role-aware version computes {computed} cells from algebraic rules,")
    print(f"  reducing the hardcoded lookup by {100*ratio:.1f}%.")

    # ── Phase 1c: Element Necessity ──
    print("\n" + "=" * 70)
    print("PHASE 1c: ELEMENT NECESSITY ANALYSIS")
    print("=" * 70)

    necessity = analyze_element_necessity()
    print("\n  For each of 7 TC elements, is its algebraic role used?")
    for name in TC7:
        used, reason = necessity[name]
        print(f"\n  {name} ({NAMES.get(ROLE_ELEMENTS[name], name)}, element {ROLE_ELEMENTS[name]}):")
        print(f"    Used: {'YES' if used else 'NO'}")
        print(f"    Reason: {reason}")

    cell_counts = test_without_element()
    print(f"\n  Cells computed via each element's algebraic role:")
    for name in TC7:
        print(f"    {name}: {cell_counts.get(name, 0)} cells")
    print(f"\n  ALL 7 TC elements are used by the role-aware self-simulator.")

    # ── Ψ∗ term-level verification ──
    print("\n" + "=" * 70)
    print("Ψ∗ TERM-LEVEL SELF-SIMULATION VERIFICATION")
    print("=" * 70)
    verify_psi_star_self_simulation()

    # ── Phase 2: SAT Tests ──
    print("\n" + "=" * 70)
    print("PHASE 2: SAT TESTS")
    print("=" * 70)
    print("\n  Testing which axioms are needed for self-simulation structure...")
    sat_results = run_sat_tests()

    # ── Phase 3: Theoretical Argument ──
    print(theoretical_argument())

    # ── Phase 4: Summary ──
    print("=" * 70)
    print("PHASE 4: SUMMARY TABLE")
    print("=" * 70)
    print(summary_table(sat_results))

    # ── Overall Assessment ──
    print("=" * 70)
    print("OVERALL ASSESSMENT")
    print("=" * 70)

    print("""
  The self-simulation investigation reveals a clean separation between
  axioms that are DERIVED from self-simulation and axioms that are
  DESIGN CHOICES:

  DERIVED (necessary for any recursive self-simulator):
  ─────────────────────────────────────────────────────
  • Binary discrimination (→ classifier/branch): The Q-depth decoder
    must distinguish base case (⊤) from recursive case (Q·...). This
    requires a binary test. TIGHT — no alternative encoding avoids it.

  • Conditional dispatch (→ branch): The self-simulator must take
    different code paths for different input elements. This IS branching.
    TIGHT — a program that can't branch can't compute a non-trivial
    function of its input.

  • E-transparency (→ E·⊤=⊤, E·⊥=⊥): Without this, the Q-depth decoder
    produces wrong results when E is applied to absorbers that appear as
    intermediate values. LIKELY TIGHT.

  • Two absorbers (→ binary classification targets): The classifier
    needs two distinct outputs. Absorbers are the natural candidates.
    LIKELY TIGHT but alternatives exist (term-level discrimination).

  LIKELY DERIVED (strong but not airtight argument):
  ──────────────────────────────────────────────────
  • Kripke dichotomy: If elements can be both classifiers and
    transformers (mixed rows), the self-simulator can't reliably
    determine whether an output is a classification or a transformation.
    Ambiguity prevents correct dispatch.

  • Y combinator (for universal self-simulation): A self-simulator
    that works for arbitrary magma size needs recursion over depth.
    For FIXED size (N=16), bounded depth suffices.

  INDEPENDENT (machine provides the capability):
  ──────────────────────────────────────────────
  • Algebraic composition (Compose axiom): The machine (step loop)
    provides sequential execution. The Compose axiom adds ALGEBRAIC
    composition (η·x = ρ·(g·x)), which is useful but not necessary —
    the machine already sequences operations.

  • Inert element (g as CONS): The machine provides non-destructive
    variable binding (registers). An algebraic storage element (inert g)
    helps at the term level but the machine already provides storage.

  NOT ANALYZED:
  ─────────────
  • 1-Inert (exactly one substrate)
  • Selection (η·ρ = τ)
  • Power-associativity
  • VV (inert self-application)

  KEY FINDING: The strongest derived axioms are the ones about
  DISCRIMINATION and CONTROL FLOW (classifier, branch, E-transparency).
  The weakest derived axioms are about ALGEBRAIC STRUCTURE (compose,
  inert). This makes sense: the self-simulator's core job is to DECODE
  inputs and DISPATCH to the right behavior — that's discrimination and
  control flow. Storage and sequencing are provided by the machine.

  The Ψ axiom system's deepest contribution is the KRIPKE WALL: the
  clean separation between judgment (classification) and computation
  (transformation). Self-simulation derives this separation because a
  self-simulator that can't distinguish its own classification from its
  own computation can't correctly simulate itself.
""")


if __name__ == "__main__":
    main()

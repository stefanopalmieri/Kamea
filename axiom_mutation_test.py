#!/usr/bin/env python3
"""
Axiom Mutation: Can the capability axioms be replaced with alternatives?

For each axiom in H, test whether alternative formulations are satisfiable
over S+D. If only the original is SAT, the specific axiom form is forced.
If alternatives are SAT, they represent equivalent choices.

Focus: Compose mutations (the axiom most connected to Lisp structure).

Original:  η·x = ρ·(g·x)    "substrate then branch"

Mutations:
  C1: η·x = g·(ρ·x)         "branch then substrate" (reversed)
  C2: η·x = f·(g·x)         "substrate then projection"
  C3: η·x = ρ·(f·x)         "projection then branch"
  C4: η·x = f·(ρ·x)         "branch then projection"
  C5: η·x = g·(f·x)         "projection then substrate"

Also test Y and Branch mutations.
"""

from __future__ import annotations
import time
from z3 import And, If, Int, Or, Solver, sat


def col_ite(dot, row, col_expr, n):
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def build_base(n, timeout=300):
    """S+D base + Branch + Inert (everything except Compose and Y)."""
    s = Solver()
    s.set("timeout", timeout * 1000)
    dot = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]

    for i in range(n):
        for j in range(n):
            s.add(dot[i][j] >= 0, dot[i][j] < n)
    for j in range(n):
        s.add(dot[0][j] == 0)
        s.add(dot[1][j] == 1)
    for x in range(2, n):
        s.add(Or([dot[x][j] != x for j in range(n)]))
    for x in range(n):
        for y in range(x + 1, n):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(n)]))

    Q, E, TAU, F, G, RHO, ETA, Y = 2, 3, 4, 5, 6, 7, 8, 9

    # S
    for x in range(2, n):
        s.add(col_ite(dot, E, dot[Q][x], n) == x)
        s.add(col_ite(dot, Q, dot[E][x], n) == x)
    s.add(dot[E][0] == 0)
    s.add(dot[E][1] == 1)

    # D
    for j in range(n):
        s.add(Or(dot[TAU][j] == 0, dot[TAU][j] == 1))
    for x in range(2, n):
        is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(n)])
        for y in range(2, n):
            s.add(Or(is_tst, dot[x][y] >= 2))

    return s, dot


def add_branch(s, dot, n):
    TAU, F, G, RHO = 4, 5, 6, 7
    for x in range(2, n):
        s.add(If(dot[TAU][x] == 0, dot[RHO][x] == dot[F][x], dot[RHO][x] == dot[G][x]))
    s.add(Or([dot[F][j] != dot[G][j] for j in range(2, n)]))


def add_inert(s, dot, n):
    G = 6
    for x in range(2, n):
        s.add(dot[G][x] >= 2)


def add_y_original(s, dot, n):
    RHO, Y = 7, 9
    yr = dot[Y][RHO]
    s.add(yr == col_ite(dot, RHO, yr, n))
    s.add(yr >= 2)


def test_mutation(name, compose_fn, n=10, timeout=300, include_y=True):
    """Test a Compose mutation with full S+D+Branch+Inert+Y context."""
    s, dot = build_base(n, timeout)
    add_branch(s, dot, n)
    add_inert(s, dot, n)
    compose_fn(s, dot, n)
    if include_y:
        add_y_original(s, dot, n)

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0

    status = str(result).upper()
    print(f"  {name:45s}  {status:7s}  ({elapsed:.1f}s)")
    return status


def main():
    print("=" * 70)
    print("  AXIOM MUTATION: COMPOSE ALTERNATIVES")
    print("=" * 70)
    print()
    print("  Testing whether alternative Compose formulations are satisfiable")
    print("  over S+D+Branch+Inert+Y. Each mutation replaces η·x = ρ·(g·x).")
    print()

    n = 10
    F, G, RHO, ETA = 5, 6, 7, 8

    # ── Compose mutations ──
    print("── Compose mutations (with Y) ──")

    def compose_original(s, dot, n):
        for x in range(2, n):
            s.add(dot[ETA][x] == col_ite(dot, RHO, dot[G][x], n))

    def compose_reversed(s, dot, n):  # g(ρ(x))
        for x in range(2, n):
            s.add(dot[ETA][x] == col_ite(dot, G, dot[RHO][x], n))

    def compose_f_of_g(s, dot, n):  # f(g(x))
        for x in range(2, n):
            s.add(dot[ETA][x] == col_ite(dot, F, dot[G][x], n))

    def compose_rho_of_f(s, dot, n):  # ρ(f(x))
        for x in range(2, n):
            s.add(dot[ETA][x] == col_ite(dot, RHO, dot[F][x], n))

    def compose_f_of_rho(s, dot, n):  # f(ρ(x))
        for x in range(2, n):
            s.add(dot[ETA][x] == col_ite(dot, F, dot[RHO][x], n))

    def compose_g_of_f(s, dot, n):  # g(f(x))
        for x in range(2, n):
            s.add(dot[ETA][x] == col_ite(dot, G, dot[F][x], n))

    results_compose = {}
    for name, fn in [
        ("η·x = ρ·(g·x)  [ORIGINAL]", compose_original),
        ("η·x = g·(ρ·x)  [reversed]", compose_reversed),
        ("η·x = f·(g·x)  [substrate→proj]", compose_f_of_g),
        ("η·x = ρ·(f·x)  [proj→branch]", compose_rho_of_f),
        ("η·x = f·(ρ·x)  [branch→proj]", compose_f_of_rho),
        ("η·x = g·(f·x)  [proj→substrate]", compose_g_of_f),
    ]:
        results_compose[name] = test_mutation(name, fn, n)

    # ── Y mutations ──
    print("\n── Y mutations (with original Compose) ──")

    def test_y_mutation(name, y_fn, n=10):
        s, dot = build_base(n)
        add_branch(s, dot, n)
        add_inert(s, dot, n)
        # Original Compose
        for x in range(2, n):
            s.add(dot[ETA][x] == col_ite(dot, RHO, dot[G][x], n))
        y_fn(s, dot, n)
        t0 = time.time()
        result = s.check()
        elapsed = time.time() - t0
        status = str(result).upper()
        print(f"  {name:45s}  {status:7s}  ({elapsed:.1f}s)")
        return status

    Y_IDX, RHO_IDX, G_IDX = 9, 7, 6

    def y_original(s, dot, n):  # Y·ρ = ρ·(Y·ρ), Y·ρ ≥ 2
        yr = dot[Y_IDX][RHO_IDX]
        s.add(yr == col_ite(dot, RHO_IDX, yr, n))
        s.add(yr >= 2)

    def y_general(s, dot, n):  # Y·x = x·(Y·x) for x=ρ, Y·ρ ≥ 2
        yr = dot[Y_IDX][RHO_IDX]
        s.add(yr == col_ite(dot, RHO_IDX, yr, n))
        s.add(yr >= 2)
        # Also require Y·g = g·(Y·g) (fixed point under g too)
        yg = dot[Y_IDX][G_IDX]
        s.add(yg == col_ite(dot, G_IDX, yg, n))
        s.add(yg >= 2)

    def y_under_g(s, dot, n):  # Y·g = g·(Y·g), Y·g ≥ 2 (fixed point under substrate instead)
        yg = dot[Y_IDX][G_IDX]
        s.add(yg == col_ite(dot, G_IDX, yg, n))
        s.add(yg >= 2)

    def y_self(s, dot, n):  # Y·Y = Y (idempotent)
        s.add(dot[Y_IDX][Y_IDX] == Y_IDX)

    results_y = {}
    for name, fn in [
        ("Y·ρ = ρ·(Y·ρ)  [ORIGINAL]", y_original),
        ("Y·ρ = ρ·(Y·ρ) + Y·g = g·(Y·g)  [general]", y_general),
        ("Y·g = g·(Y·g)  [substrate fixpt]", y_under_g),
        ("Y·Y = Y  [idempotent]", y_self),
    ]:
        results_y[name] = test_y_mutation(name, fn, n)

    # ── Branch mutations ──
    print("\n── Branch mutations (with original Compose + Y) ──")

    def test_branch_mutation(name, branch_fn, n=10):
        s, dot = build_base(n)
        add_inert(s, dot, n)
        branch_fn(s, dot, n)
        # Original Compose + Y
        for x in range(2, n):
            s.add(dot[ETA][x] == col_ite(dot, RHO, dot[G][x], n))
        add_y_original(s, dot, n)
        t0 = time.time()
        result = s.check()
        elapsed = time.time() - t0
        status = str(result).upper()
        print(f"  {name:45s}  {status:7s}  ({elapsed:.1f}s)")
        return status

    TAU, F_IDX, G_IDX, RHO_IDX = 4, 5, 6, 7

    def branch_original(s, dot, n):
        for x in range(2, n):
            s.add(If(dot[TAU][x] == 0, dot[RHO_IDX][x] == dot[F_IDX][x], dot[RHO_IDX][x] == dot[G_IDX][x]))
        s.add(Or([dot[F_IDX][j] != dot[G_IDX][j] for j in range(2, n)]))

    def branch_swapped(s, dot, n):  # Swapped: true→g, false→f
        for x in range(2, n):
            s.add(If(dot[TAU][x] == 0, dot[RHO_IDX][x] == dot[G_IDX][x], dot[RHO_IDX][x] == dot[F_IDX][x]))
        s.add(Or([dot[F_IDX][j] != dot[G_IDX][j] for j in range(2, n)]))

    def branch_three_way(s, dot, n):  # Three-way: τ·x=0→f, τ·x=1→g, else→η
        for x in range(2, n):
            s.add(If(dot[TAU][x] == 0, dot[RHO_IDX][x] == dot[F_IDX][x],
                      If(dot[TAU][x] == 1, dot[RHO_IDX][x] == dot[G_IDX][x],
                         dot[RHO_IDX][x] == dot[8][x])))
        s.add(Or([dot[F_IDX][j] != dot[G_IDX][j] for j in range(2, n)]))

    results_branch = {}
    for name, fn in [
        ("τ→0: f, else: g  [ORIGINAL]", branch_original),
        ("τ→0: g, else: f  [swapped]", branch_swapped),
        ("τ→0: f, τ→1: g, else: η  [three-way]", branch_three_way),
    ]:
        results_branch[name] = test_branch_mutation(name, fn, n)

    # ── Summary ──
    print(f"\n{'='*70}")
    print(f"  MUTATION SUMMARY")
    print(f"{'='*70}")

    print(f"\n  Compose ({sum(1 for v in results_compose.values() if v=='SAT')}/{len(results_compose)} SAT):")
    for name, status in results_compose.items():
        tag = " ←" if "ORIGINAL" in name else ""
        print(f"    {'✓' if status=='SAT' else '✗'} {name}{tag}")

    print(f"\n  Y ({sum(1 for v in results_y.values() if v=='SAT')}/{len(results_y)} SAT):")
    for name, status in results_y.items():
        tag = " ←" if "ORIGINAL" in name else ""
        print(f"    {'✓' if status=='SAT' else '✗'} {name}{tag}")

    print(f"\n  Branch ({sum(1 for v in results_branch.values() if v=='SAT')}/{len(results_branch)} SAT):")
    for name, status in results_branch.items():
        tag = " ←" if "ORIGINAL" in name else ""
        print(f"    {'✓' if status=='SAT' else '✗'} {name}{tag}")

    # Interpretation
    compose_unique = sum(1 for v in results_compose.values() if v == 'SAT') == 1
    print(f"\n  Compose is {'CANONICAL (only form that works)' if compose_unique else 'one of several viable forms'}")


if __name__ == "__main__":
    main()

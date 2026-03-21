#!/usr/bin/env python3
"""
Axiom irredundancy within each capability.

For each axiom in each capability, test whether removing it (while
keeping all other axioms) produces a model where that axiom fails.
If SAT: the axiom is irredundant (not derivable from the others).
If UNSAT: the axiom is redundant (implied by the others).

Capability S: {retraction pair, E-transparency}
  - Is E-transparency irredundant over the retraction pair?

Capability D: {Kripke dichotomy}
  - D is a single axiom, so irredundancy is trivial.

Capability H: {Branch, Compose, Inert, Y}
  - Is Branch irredundant over {Compose, Inert, Y} + S + D?
  - Is Compose irredundant over {Branch, Inert, Y} + S + D?
  - Is Inert irredundant over {Branch, Compose, Y} + S + D?
  - Is Y irredundant over {Branch, Compose, Inert} + S + D?
"""

from __future__ import annotations
import time
from z3 import And, If, Int, Not, Or, Solver, sat, unsat


def col_ite_lookup(dot, row, col_expr, n):
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def build_sdh_base(n, timeout=300):
    """Build solver with S+D base (absorbers, extensionality, retraction, E-trans, Kripke)."""
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

    Q, E, TAU = 2, 3, 4
    # S: retraction pair
    for x in range(2, n):
        s.add(col_ite_lookup(dot, E, dot[Q][x], n) == x)
        s.add(col_ite_lookup(dot, Q, dot[E][x], n) == x)
    # S: E-transparency
    s.add(dot[E][0] == 0)
    s.add(dot[E][1] == 1)
    # D: classifier
    for j in range(n):
        s.add(Or(dot[TAU][j] == 0, dot[TAU][j] == 1))
    # D: Kripke dichotomy
    for x in range(2, n):
        is_tst = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(n)])
        for y in range(2, n):
            s.add(Or(is_tst, dot[x][y] >= 2))

    return s, dot


def add_branch(s, dot, n, tau=4, f=5, g=6, rho=7):
    for x in range(2, n):
        s.add(If(dot[tau][x] == 0, dot[rho][x] == dot[f][x], dot[rho][x] == dot[g][x]))
    s.add(Or([dot[f][j] != dot[g][j] for j in range(2, n)]))


def add_inert(s, dot, n, g=6):
    for x in range(2, n):
        s.add(dot[g][x] >= 2)


def add_compose(s, dot, n, rho=7, g=6, eta=8):
    for x in range(2, n):
        s.add(dot[eta][x] == col_ite_lookup(dot, rho, dot[g][x], n))


def add_y(s, dot, n, rho=7, y=9):
    yr = dot[y][rho]
    s.add(yr == col_ite_lookup(dot, rho, yr, n))
    s.add(yr >= 2)


def negate_branch(s, dot, n, tau=4, f=5, g=6, rho=7):
    """Require Branch to FAIL for all candidate (f, g, rho) triples at the assigned indices."""
    s.add(Or([
        If(dot[tau][x] == 0, dot[rho][x] != dot[f][x], dot[rho][x] != dot[g][x])
        for x in range(2, n)
    ]))


def negate_compose(s, dot, n, rho=7, g=6, eta=8):
    """Require Compose to fail for η=8."""
    s.add(Or([dot[eta][x] != col_ite_lookup(dot, rho, dot[g][x], n) for x in range(2, n)]))


def negate_inert(s, dot, n, g=6):
    """Require g to map some core element to an absorber."""
    s.add(Or([dot[g][x] < 2 for x in range(2, n)]))


def negate_y(s, dot, n, rho=7, y=9):
    """Require Y fixed-point to fail."""
    yr = dot[y][rho]
    s.add(Or(yr != col_ite_lookup(dot, rho, yr, n), yr < 2))


def test_irredundancy(name, n, add_others, negate_target, timeout=300):
    """Test if target axiom is irredundant: others hold, target fails."""
    s, dot = build_sdh_base(n, timeout)
    add_others(s, dot, n)
    negate_target(s, dot, n)

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0

    status = str(result).upper()
    verdict = "IRREDUNDANT" if status == "SAT" else ("REDUNDANT" if status == "UNSAT" else "TIMEOUT")
    print(f"  {name:30s}  {status:7s}  ({elapsed:.1f}s)  → {verdict}")
    return verdict


def main():
    print("=" * 70)
    print("  AXIOM IRREDUNDANCY WITHIN EACH CAPABILITY")
    print("=" * 70)
    print()
    print("  SAT = axiom is irredundant (not derivable from the others)")
    print("  UNSAT = axiom is redundant (implied by the others)")
    print()

    n = 10
    results = {}

    # ── S: E-transparency irredundant? ──
    print("── Capability S ──")

    def add_nothing(s, dot, n): pass
    def negate_e_trans(s, dot, n):
        s.add(Or(dot[3][0] != 0, dot[3][1] != 1))

    # Build solver without E-transparency, require its negation
    s = Solver()
    s.set("timeout", 300000)
    dot_vars = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            s.add(dot_vars[i][j] >= 0, dot_vars[i][j] < n)
    for j in range(n):
        s.add(dot_vars[0][j] == 0)
        s.add(dot_vars[1][j] == 1)
    for x in range(2, n):
        s.add(Or([dot_vars[x][j] != x for j in range(n)]))
    for x in range(n):
        for y in range(x + 1, n):
            s.add(Or([dot_vars[x][j] != dot_vars[y][j] for j in range(n)]))
    # Retraction pair only (no E-transparency)
    for x in range(2, n):
        s.add(col_ite_lookup(dot_vars, 3, dot_vars[2][x], n) == x)
        s.add(col_ite_lookup(dot_vars, 2, dot_vars[3][x], n) == x)
    # Negate E-transparency
    s.add(Or(dot_vars[3][0] != 0, dot_vars[3][1] != 1))

    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    status = str(r).upper()
    verdict = "IRREDUNDANT" if status == "SAT" else "REDUNDANT"
    print(f"  {'E-transparency over retraction':30s}  {status:7s}  ({elapsed:.1f}s)  → {verdict}")
    results['E-trans'] = verdict

    # ── H: each axiom irredundant over the other three + S + D ──
    print("\n── Capability H (over S+D base) ──")

    # Branch irredundant?
    def add_CIY(s, dot, n):
        add_inert(s, dot, n)
        add_compose(s, dot, n)
        add_y(s, dot, n)
    results['Branch'] = test_irredundancy("Branch over {Compose,Inert,Y}", n, add_CIY, negate_branch)

    # Compose irredundant?
    def add_BIY(s, dot, n):
        add_branch(s, dot, n)
        add_inert(s, dot, n)
        add_y(s, dot, n)
    results['Compose'] = test_irredundancy("Compose over {Branch,Inert,Y}", n, add_BIY, negate_compose)

    # Inert irredundant?
    def add_BCY(s, dot, n):
        add_branch(s, dot, n)
        add_compose(s, dot, n)
        add_y(s, dot, n)
    results['Inert'] = test_irredundancy("Inert over {Branch,Compose,Y}", n, add_BCY, negate_inert)

    # Y irredundant?
    def add_BCI(s, dot, n):
        add_branch(s, dot, n)
        add_compose(s, dot, n)
        add_inert(s, dot, n)
    results['Y'] = test_irredundancy("Y over {Branch,Compose,Inert}", n, add_BCI, negate_y)

    # ── Summary ──
    print(f"\n{'='*70}")
    print(f"  IRREDUNDANCY RESULTS")
    print(f"{'='*70}")
    for name, verdict in results.items():
        symbol = "✓" if verdict == "IRREDUNDANT" else "✗"
        print(f"    {symbol} {name}: {verdict}")

    all_irredundant = all(v == "IRREDUNDANT" for v in results.values())
    if all_irredundant:
        print(f"\n  All axioms irredundant. The capability axiom sets have no redundancies.")
        print(f"  S = {{retraction pair, E-transparency}} — minimal")
        print(f"  D = {{Kripke dichotomy}} — minimal (single axiom)")
        print(f"  H = {{Branch, Compose, Inert, Y}} — minimal")
    else:
        redundant = [k for k, v in results.items() if v != "IRREDUNDANT"]
        print(f"\n  Redundant axioms found: {redundant}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
What is the minimum N where all three capabilities (S+D+H) coexist?

S = self-simulating: retraction pair (Q/E)
D = self-describing: Kripke dichotomy
H = self-hosting: Branch + Compose + Inert + Y

We need 10 distinguished elements (⊤,⊥,Q,E,τ,f,g,ρ,η,Y), so N≥10.
Test N=10, 11, 12 to find the minimum.

Also test subsets to map the full capability space:
  S alone:   min N?
  D alone:   min N?  (known: N=4 from CatKripkeWallMinimal.lean)
  H alone:   min N?  (known: SAT at N=10 from diagonal test)
  S+D:       min N?
  S+H:       min N?
  D+H:       min N?
  S+D+H:     min N?
"""

from __future__ import annotations
import time
from z3 import And, If, Int, Not, Or, Solver, sat, unsat


def col_ite_lookup(dot, row, col_expr, n):
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def build_base(n, timeout=300):
    """Base: range, two absorbers, no extra absorbers, extensionality."""
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

    return s, dot


def add_S(s, dot, n, q=2, e=3):
    """Self-simulation: retraction pair Q/E + E-transparency."""
    for x in range(2, n):
        qx = dot[q][x]
        s.add(col_ite_lookup(dot, e, qx, n) == x)
        ex = dot[e][x]
        s.add(col_ite_lookup(dot, q, ex, n) == x)
    s.add(dot[e][0] == 0)
    s.add(dot[e][1] == 1)


def add_D(s, dot, n, tau=4):
    """Self-description: classifier + Kripke dichotomy."""
    # Classifier: all-boolean outputs
    for j in range(n):
        s.add(Or(dot[tau][j] == 0, dot[tau][j] == 1))

    # Kripke dichotomy: every non-absorber is all-boolean or all-non-boolean on core
    for x in range(2, n):
        is_tester = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(n)])
        for y in range(2, n):
            # If x is not a tester, then dot[x][y] must be ≥ 2
            s.add(Or(is_tester, dot[x][y] >= 2))


def add_H(s, dot, n, tau=4, f=5, g=6, rho=7, eta=8, y=9):
    """Self-hosting: Branch + Inert + Compose + Y."""
    # Branch: ρ·x = f·x if τ·x=⊤, else ρ·x = g·x
    for x in range(2, n):
        s.add(If(dot[tau][x] == 0,
                  dot[rho][x] == dot[f][x],
                  dot[rho][x] == dot[g][x]))
    s.add(Or([dot[f][j] != dot[g][j] for j in range(2, n)]))

    # Inert: g maps core away from absorbers
    for x in range(2, n):
        s.add(dot[g][x] >= 2)

    # Compose: η·x = ρ·(g·x) on core
    for x in range(2, n):
        gx = dot[g][x]
        rho_gx = col_ite_lookup(dot, rho, gx, n)
        s.add(dot[eta][x] == rho_gx)

    # Y fixed-point: Y·ρ = ρ·(Y·ρ), Y·ρ ∈ core
    y_rho = dot[y][rho]
    rho_y_rho = col_ite_lookup(dot, rho, y_rho, n)
    s.add(y_rho == rho_y_rho)
    s.add(y_rho >= 2)


def test_combo(name, caps, n, timeout=300):
    """Test a capability combination at size n."""
    s, dot = build_base(n, timeout)

    if 'S' in caps:
        add_S(s, dot, n)
    if 'D' in caps:
        add_D(s, dot, n)
    if 'H' in caps:
        add_H(s, dot, n)

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0

    tag = '+'.join(caps) if caps else '(base)'
    status = str(result).upper()
    print(f"  N={n:2d}  {tag:8s}  {status:7s}  ({elapsed:.1f}s)")
    return status


def find_minimum(name, caps, lo, hi, timeout=300):
    """Binary-ish search for minimum N where caps are SAT."""
    print(f"\n  Finding min N for {'+'.join(caps)}...")
    for n in range(lo, hi + 1):
        status = test_combo(name, caps, n, timeout)
        if status == 'SAT':
            return n
    return None


def main():
    print("=" * 60)
    print("  MINIMUM N FOR EACH CAPABILITY COMBINATION")
    print("=" * 60)

    results = {}

    # Known results
    print("  Known: D alone has min N=4 (Lean witness in CatKripkeWallMinimal.lean)")
    print("  Known: Full axiom set (S+D+H + ladder) has min N=12")
    print()

    # H needs indices 0-9 (⊤,⊥,Q,E,τ,f,g,ρ,η,Y), so min N=10 for any combo with H
    # S needs indices 0-3 (⊤,⊥,Q,E), so min N=4 for S alone
    # D needs indices 0-2 (⊤,⊥,τ) at minimum, but tau=4 in our encoding needs N≥5

    # S alone (retraction pair + extensionality)
    print("── S (self-simulating) alone ──")
    for n in [4, 5, 6, 7, 8]:
        status = test_combo('S', ['S'], n)
        if status == 'SAT' and 'S' not in results:
            results['S'] = n

    # H alone
    print("\n── H (self-hosting) alone — no Kripke, no retraction pair ──")
    for n in [10, 11, 12]:
        status = test_combo('H', ['H'], n)
        if status == 'SAT' and 'H' not in results:
            results['H'] = n

    # S+H (self-simulating + self-hosting, no Kripke)
    print("\n── S+H (simulating + hosting, no Kripke) ──")
    for n in [10, 11, 12]:
        status = test_combo('S+H', ['S', 'H'], n)
        if status == 'SAT' and 'S+H' not in results:
            results['S+H'] = n

    # D+H (self-describing + self-hosting)
    print("\n── D+H (describing + hosting) ──")
    for n in [10, 11, 12]:
        status = test_combo('D+H', ['D', 'H'], n)
        if status == 'SAT' and 'D+H' not in results:
            results['D+H'] = n

    # S+D (simulating + describing)
    print("\n── S+D (simulating + describing) ──")
    for n in [5, 6, 7, 8]:
        status = test_combo('S+D', ['S', 'D'], n)
        if status == 'SAT' and 'S+D' not in results:
            results['S+D'] = n

    # S+D+H (all three)
    print("\n── S+D+H (all three capabilities) ──")
    for n in [10, 11, 12, 13, 14]:
        status = test_combo('S+D+H', ['S', 'D', 'H'], n, timeout=600)
        if status == 'SAT' and 'S+D+H' not in results:
            results['S+D+H'] = n
            break

    # Summary
    print(f"\n{'='*60}")
    print(f"  MINIMUM N FOR EACH CAPABILITY COMBINATION")
    print(f"{'='*60}")
    print(f"    D alone:  N=4 (Lean witness)")
    for combo in ['S', 'S+D', 'H', 'S+H', 'D+H', 'S+D+H']:
        n = results.get(combo, '?')
        print(f"    {combo:8s}  min N = {n}")


if __name__ == "__main__":
    main()

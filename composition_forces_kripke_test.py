#!/usr/bin/env python3
"""
Does internal composition force the Kripke dichotomy?

The three-level hierarchy claims:
  Level 1 (FRM)  ⊬  Level 2 (Kripke dichotomy)   [proved: N=8 counterexample]
  Level 2 (DRM)  ⊬  Level 3 (Compose + Inert)     [proved: N=10 counterexamples]

But the DIAGONAL question is untested:
  Does Level 3 machinery FORCE Level 2?
  Can you have Branch + Compose + Y WITHOUT the Kripke dichotomy?

Test: Find a finite extensional magma with:
  - Two absorbers + extensionality (base)
  - Retraction pair Q/E
  - A classifier τ (boolean outputs)
  - Branch: ρ dispatches based on τ
  - Compose: η·x = ρ·(g·x) on core
  - Y fixed-point: Y·ρ = ρ·(Y·ρ), Y·ρ ≥ 2
  - AT LEAST ONE mixed element (violates Kripke dichotomy)

If SAT:  Composition does NOT force Kripke. The levels are genuinely independent.
If UNSAT: Composition FORCES Kripke. Level 3 implies Level 2. Major result.
"""

from __future__ import annotations
import time
from z3 import And, If, Int, Not, Or, Solver, sat, unsat


def ite_lookup(dot, row_expr, col, n):
    """Lookup dot[row_expr][col] where row_expr is a Z3 expression."""
    entry = dot[0][col]
    for r in range(1, n):
        entry = If(row_expr == r, dot[r][col], entry)
    return entry


def col_ite_lookup(dot, row, col_expr, n):
    """Lookup dot[row][col_expr] where col_expr is a Z3 expression."""
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def run_test(n, timeout=600):
    """Run the composition-forces-Kripke test at size n."""
    print(f"\n{'='*60}")
    print(f"  Composition → Kripke test at N={n}")
    print(f"{'='*60}")

    s = Solver()
    s.set("timeout", timeout * 1000)
    dot = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]

    # ── Base constraints ──

    # Range
    for i in range(n):
        for j in range(n):
            s.add(dot[i][j] >= 0, dot[i][j] < n)

    # Two absorbers at 0, 1
    for j in range(n):
        s.add(dot[0][j] == 0)
        s.add(dot[1][j] == 1)

    # No other absorbers
    for x in range(2, n):
        s.add(Or([dot[x][j] != x for j in range(n)]))

    # Extensionality (all rows distinct)
    for x in range(n):
        for y in range(x + 1, n):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(n)]))

    # ── Distinguished elements ──
    # Indices: 0=⊤, 1=⊥, 2=Q, 3=E, 4=τ, 5=f, 6=g, 7=ρ, 8=η, 9=Y
    Q_IDX = 2
    E_IDX = 3
    TAU_IDX = 4
    F_IDX = 5
    G_IDX = 6
    RHO_IDX = 7
    ETA_IDX = 8
    Y_IDX = 9

    assert n > Y_IDX, f"Need N > {Y_IDX}, got N={n}"

    # All distinguished elements are distinct
    distinguished = [0, 1, Q_IDX, E_IDX, TAU_IDX, F_IDX, G_IDX, RHO_IDX, ETA_IDX, Y_IDX]
    for i in range(len(distinguished)):
        for j in range(i + 1, len(distinguished)):
            assert distinguished[i] != distinguished[j]

    # ── Retraction pair (Q/E on core) ──
    for x in range(2, n):
        qx = dot[Q_IDX][x]
        s.add(col_ite_lookup(dot, E_IDX, qx, n) == x)
        ex = dot[E_IDX][x]
        s.add(col_ite_lookup(dot, Q_IDX, ex, n) == x)

    # E-transparency: E·⊤ = ⊤, E·⊥ = ⊥
    s.add(dot[E_IDX][0] == 0)
    s.add(dot[E_IDX][1] == 1)

    # ── Classifier τ ──
    # τ has all-boolean outputs
    for j in range(n):
        s.add(Or(dot[TAU_IDX][j] == 0, dot[TAU_IDX][j] == 1))

    # ── Branch: ρ·x = f·x if τ·x=⊤, else ρ·x = g·x ──
    for x in range(2, n):
        s.add(If(dot[TAU_IDX][x] == 0,
                  dot[RHO_IDX][x] == dot[F_IDX][x],
                  dot[RHO_IDX][x] == dot[G_IDX][x]))

    # f and g must actually differ on core (non-trivial branching)
    s.add(Or([dot[F_IDX][j] != dot[G_IDX][j] for j in range(2, n)]))

    # ── Inert: g maps core away from absorbers ──
    for x in range(2, n):
        s.add(dot[G_IDX][x] >= 2)

    # ── Compose: η·x = ρ·(g·x) on core ──
    for x in range(2, n):
        gx = dot[G_IDX][x]
        rho_gx = col_ite_lookup(dot, RHO_IDX, gx, n)
        s.add(dot[ETA_IDX][x] == rho_gx)

    # ── Y fixed-point: Y·ρ = ρ·(Y·ρ), Y·ρ ∈ core ──
    y_rho = dot[Y_IDX][RHO_IDX]
    rho_y_rho = col_ite_lookup(dot, RHO_IDX, y_rho, n)
    s.add(y_rho == rho_y_rho)
    s.add(y_rho >= 2)

    # ── KEY: Require at least one MIXED element (violates Kripke) ──
    # A mixed element has BOTH boolean and non-boolean outputs on core
    mixed_clauses = []
    for x in range(2, n):
        has_bool_on_core = Or([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(2, n)])
        has_nonbool_on_core = Or([dot[x][j] >= 2 for j in range(2, n)])
        mixed_clauses.append(And(has_bool_on_core, has_nonbool_on_core))
    s.add(Or(mixed_clauses))

    # ── Solve ──
    print(f"  Constraints built. Solving (timeout={timeout}s)...")
    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    print(f"  Result: {result}  ({elapsed:.1f}s)")

    if result == sat:
        m = s.model()
        table = [[m.evaluate(dot[i][j]).as_long() for j in range(n)] for i in range(n)]
        print_model(table, n)
        return 'SAT', table
    elif result == unsat:
        return 'UNSAT', None
    else:
        return 'TIMEOUT', None


def print_model(table, n):
    """Print and analyze a counterexample model."""
    print(f"\n  Cayley table ({n}x{n}):")
    header = "     " + "".join(f"{j:3d}" for j in range(n))
    print(header)
    print("     " + "---" * n)
    for i in range(n):
        row_str = "".join(f"{table[i][j]:3d}" for j in range(n))
        print(f"  {i:2d} |{row_str}")

    # Analyze
    print(f"\n  Analysis:")
    mixed = []
    testers = []
    encoders = []
    for x in range(2, n):
        core_vals = table[x][2:]
        all_bool = all(v in (0, 1) for v in core_vals)
        all_nonbool = all(v >= 2 for v in core_vals)
        if all_bool:
            testers.append(x)
        elif all_nonbool:
            encoders.append(x)
        else:
            mixed.append(x)
            bool_vals = [v for v in core_vals if v in (0, 1)]
            nonbool_vals = [v for v in core_vals if v >= 2]
            print(f"    Mixed element {x}: {len(bool_vals)} boolean + {len(nonbool_vals)} non-boolean on core")
            print(f"      Row: {table[x]}")

    print(f"    Testers (all-boolean): {testers}")
    print(f"    Encoders (all-nonbool): {encoders}")
    print(f"    Mixed (violate Kripke): {mixed}")

    # Verify Branch
    tau = 4; f = 5; g = 6; rho = 7
    branch_ok = True
    for x in range(2, n):
        if table[tau][x] == 0:
            if table[rho][x] != table[f][x]:
                branch_ok = False
        else:
            if table[rho][x] != table[g][x]:
                branch_ok = False
    print(f"    Branch holds: {branch_ok}")

    # Verify Compose
    eta = 8
    compose_ok = True
    for x in range(2, n):
        gx = table[g][x]
        rho_gx = table[rho][gx]
        if table[eta][x] != rho_gx:
            compose_ok = False
    print(f"    Compose holds: {compose_ok}")

    # Verify Y
    y = 9
    yr = table[y][rho]
    ryr = table[rho][yr]
    print(f"    Y·ρ = {yr}, ρ·(Y·ρ) = {ryr}, fixed-point: {yr == ryr}, in core: {yr >= 2}")

    # Verify QE
    q = 2; e = 3
    qe_ok = True
    for x in range(2, n):
        qx = table[q][x]
        eqx = table[e][qx] if 0 <= qx < n else -1
        if eqx != x:
            qe_ok = False
    print(f"    QE round-trip on core: {qe_ok}")


def main():
    print("=" * 60)
    print("  DOES INTERNAL COMPOSITION FORCE THE KRIPKE DICHOTOMY?")
    print("=" * 60)
    print()
    print("  If SAT:  Composition does NOT force Kripke.")
    print("           Three levels are genuinely independent.")
    print("  If UNSAT: Composition FORCES Kripke.")
    print("           Level 3 implies Level 2. Major result.")
    print()

    # Try increasing sizes
    # N=10 is the minimum (need 10 distinguished elements: 0,1,Q,E,τ,f,g,ρ,η,Y)
    results = {}
    for n in [10, 11, 12]:
        status, table = run_test(n, timeout=600)
        results[n] = status
        if status == 'SAT':
            print(f"\n  *** FOUND COUNTEREXAMPLE AT N={n} ***")
            print(f"  Composition does NOT force Kripke dichotomy.")
            print(f"  The three levels are genuinely independent.")
            break
        elif status == 'UNSAT':
            print(f"\n  N={n}: UNSAT — no model exists at this size.")
        else:
            print(f"\n  N={n}: TIMEOUT — inconclusive at this size.")

    # Summary
    print(f"\n{'='*60}")
    print(f"  SUMMARY")
    print(f"{'='*60}")
    for n, status in results.items():
        print(f"    N={n}: {status}")

    if all(v == 'UNSAT' for v in results.values()):
        print(f"\n  UNSAT at all tested sizes.")
        print(f"  Strong evidence that composition FORCES Kripke dichotomy.")
        print(f"  If true: Level 3 ⇒ Level 2 (the architecture is partially necessary).")
    elif any(v == 'SAT' for v in results.values()):
        print(f"\n  SAT — counterexample found.")
        print(f"  Composition does NOT force Kripke.")
        print(f"  The three levels are fully independent in both directions.")


if __name__ == "__main__":
    main()

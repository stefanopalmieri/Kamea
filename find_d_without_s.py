#!/usr/bin/env python3
"""
Search for D ⇏ S and H ⇏ S witnesses.

An extensional 2-pointed magma (E2PM) is:
  - Binary operation dot on {0..n-1}
  - Two absorbers: dot(0,x)=0, dot(1,x)=1 for all x
  - No other absorbers
  - Extensional: all rows distinct

Capability S = E2PM + retraction pair (sec,ret mutual inverses on core, ret(0)=0)
Capability D = E2PM + classifier dichotomy
Capability H = E2PM + ICP

We search for:
  1. D without S: E2PM with dichotomy but NO retraction pair
  2. H without S: E2PM with ICP but NO retraction pair

If both exist, all six independence directions are proved.
"""

from z3 import And, If, Int, Not, Or, Solver, sat, unsat


def col_ite_lookup(dot, row, col_expr, n):
    """Lookup dot[row][col_expr] using ITE chain."""
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def e2pm_solver(n, timeout=300):
    """Create a solver with E2PM constraints (no retraction pair)."""
    s = Solver()
    s.set("timeout", timeout * 1000)
    dot = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]

    # Range constraints
    for i in range(n):
        for j in range(n):
            s.add(dot[i][j] >= 0, dot[i][j] < n)

    # Absorbers: 0 and 1
    for j in range(n):
        s.add(dot[0][j] == 0)
        s.add(dot[1][j] == 1)

    # No extra absorbers
    for x in range(2, n):
        s.add(Or([dot[x][j] != x for j in range(n)]))

    # Extensionality: all rows distinct
    for x in range(n):
        for y in range(x + 1, n):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(n)]))

    return s, dot


def add_no_retraction_pair(s, dot, n):
    """Assert that NO retraction pair exists.

    A retraction pair (sec, ret) requires:
      - sec, ret both in core (not 0 or 1)
      - ret(sec(x)) = x for all x in core
      - sec(ret(x)) = x for all x in core
      - ret(0) = 0

    We assert: for ALL pairs (q, e) of core elements, the retraction fails.
    """
    for q in range(2, n):
        for e in range(2, n):
            # For this (q, e) pair to be a valid retraction pair, ALL of
            # these must hold:
            #   ret(0) = 0  (i.e., dot[e][0] = 0)
            #   for all x in core: dot[e][dot[q][x]] = x AND dot[q][dot[e][x]] = x
            #
            # We assert that at least one fails.
            failures = []

            # ret_zero₁ failure
            failures.append(dot[e][0] != 0)

            # ret_sec failure: exists x in core where dot[e][dot[q][x]] != x
            for x in range(2, n):
                qx = dot[q][x]
                e_of_qx = col_ite_lookup(dot, e, qx, n)
                failures.append(e_of_qx != x)

            # sec_ret failure: exists x in core where dot[q][dot[e][x]] != x
            for x in range(2, n):
                ex = dot[e][x]
                q_of_ex = col_ite_lookup(dot, q, ex, n)
                failures.append(q_of_ex != x)

            s.add(Or(failures))


def add_dichotomy(s, dot, n, tau_val):
    """Add classifier dichotomy constraints for a specific tau value."""
    # Classifier: tau is all-boolean
    for j in range(n):
        s.add(Or(dot[tau_val][j] == 0, dot[tau_val][j] == 1))

    # Kripke dichotomy: every non-absorber is all-boolean or all-non-boolean on core
    for y in range(2, n):
        is_classifier = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in range(2, n)])
        is_non_classifier = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in range(2, n)])
        s.add(Or(is_classifier, is_non_classifier))

    # Non-degeneracy: at least one non-classifier exists
    s.add(Or([
        Not(And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in range(2, n)]))
        for y in range(2, n)
    ]))


def add_icp(s, dot, n):
    """Add ICP constraints (existential over all triples)."""
    icp_clauses = []
    for a in range(2, n):
        for b in range(2, n):
            if b == a:
                continue
            for c in range(2, n):
                if c == a or c == b:
                    continue
                # b preserves core
                b_pres = And([dot[b][x] >= 2 for x in range(2, n)])
                # Factorization: a·x = c·(b·x) on core
                fact_conjs = []
                for x in range(2, n):
                    bx = dot[b][x]
                    c_bx = col_ite_lookup(dot, c, bx, n)
                    fact_conjs.append(dot[a][x] == c_bx)
                factorization = And(fact_conjs)
                # Non-triviality: a takes >=2 distinct values on core
                nontriv_clauses = []
                for x in range(2, n):
                    for y in range(x + 1, n):
                        nontriv_clauses.append(dot[a][x] != dot[a][y])
                nontrivial = Or(nontriv_clauses)

                icp_clauses.append(And(b_pres, factorization, nontrivial))

    s.add(Or(icp_clauses))


def extract_table(s, dot, n):
    m = s.model()
    return [[m.evaluate(dot[i][j]).as_long() for j in range(n)] for i in range(n)]


def verify_e2pm(table, n):
    """Verify E2PM properties on a plain table."""
    # Absorbers
    for j in range(n):
        assert table[0][j] == 0, f"row 0 not absorber at col {j}"
        assert table[1][j] == 1, f"row 1 not absorber at col {j}"
    # No extra absorbers
    for x in range(2, n):
        assert not all(table[x][j] == x for j in range(n)), f"row {x} is extra absorber"
    # Extensionality
    for x in range(n):
        for y in range(x + 1, n):
            assert table[x] != table[y], f"rows {x} and {y} are identical"
    return True


def verify_no_retraction(table, n):
    """Verify that NO retraction pair exists."""
    for q in range(2, n):
        for e in range(2, n):
            # Check if (q, e) is a valid retraction pair
            if table[e][0] != 0:
                continue  # ret_zero₁ fails
            ok = True
            for x in range(2, n):
                qx = table[q][x]
                if table[e][qx] != x:
                    ok = False
                    break
            if not ok:
                continue
            for x in range(2, n):
                ex = table[e][x]
                if table[q][ex] != x:
                    ok = False
                    break
            if ok:
                return False, q, e  # Found a retraction pair!
    return True, None, None


def verify_dichotomy(table, n):
    """Verify classifier dichotomy."""
    # Check every non-absorber is all-boolean or all-non-boolean on core
    has_classifier = False
    has_non_classifier = False
    for y in range(2, n):
        core_vals = [table[y][x] for x in range(2, n)]
        all_bool = all(v in (0, 1) for v in core_vals)
        all_non_bool = all(v >= 2 for v in core_vals)
        if not (all_bool or all_non_bool):
            return False, f"element {y} is mixed: {core_vals}"
        if all_bool:
            has_classifier = True
        if all_non_bool:
            has_non_classifier = True
    if not has_classifier:
        return False, "no classifier"
    if not has_non_classifier:
        return False, "no non-classifier"
    return True, "ok"


def verify_icp(table, n):
    """Verify ICP and find witness."""
    for a in range(2, n):
        for b in range(2, n):
            if b == a:
                continue
            for c in range(2, n):
                if c == a or c == b:
                    continue
                # b preserves core
                if not all(table[b][x] >= 2 for x in range(2, n)):
                    continue
                # Factorization
                if not all(table[a][x] == table[c][table[b][x]] for x in range(2, n)):
                    continue
                # Non-triviality
                vals = set(table[a][x] for x in range(2, n))
                if len(vals) >= 2:
                    return True, (a, b, c)
    return False, None


def print_lean_table(table, n, func_name):
    """Print table in Lean-ready format."""
    print(f"\nprivate def {func_name} : Nat → Nat → Nat")
    for i in range(n):
        parts = [f"| {i}, {j} => {table[i][j]}" for j in range(n)]
        prefix = "  " if i > 0 else "  "
        print(f"{prefix}{' '.join(parts)}")
    print(f"  | _, _ => 0")


def search_d_without_s():
    """Search for D without S: E2PM with dichotomy but no retraction pair."""
    print("=" * 60)
    print("SEARCH: D without S (dichotomy, no retraction pair)")
    print("=" * 60)

    for n in range(5, 11):
        print(f"\n--- N={n} ---")
        for tau_val in range(2, n):
            s, dot = e2pm_solver(n)
            add_no_retraction_pair(s, dot, n)
            add_dichotomy(s, dot, n, tau_val)

            result = s.check()
            if result == sat:
                table = extract_table(s, dot, n)
                print(f"\n*** SAT at N={n}, tau={tau_val} ***")
                for i in range(n):
                    print(f"  row {i}: {table[i]}")

                # Verify
                verify_e2pm(table, n)
                no_ret, q, e = verify_no_retraction(table, n)
                if not no_ret:
                    print(f"  VERIFICATION FAILED: retraction pair found at q={q}, e={e}")
                    continue
                dich_ok, msg = verify_dichotomy(table, n)
                if not dich_ok:
                    print(f"  VERIFICATION FAILED: dichotomy: {msg}")
                    continue

                print("  Verified: E2PM ✓, no retraction pair ✓, dichotomy ✓")
                print_lean_table(table, n, f"rawDnoS{n}")
                return table, n
            else:
                print(f"  tau={tau_val}: {result}")

    print("\nNo D-without-S witness found up to N=10")
    return None, None


def search_h_without_s():
    """Search for H without S: E2PM with ICP but no retraction pair."""
    print("\n" + "=" * 60)
    print("SEARCH: H without S (ICP, no retraction pair)")
    print("=" * 60)

    for n in range(6, 11):
        print(f"\n--- N={n} ---")
        s, dot = e2pm_solver(n)
        add_no_retraction_pair(s, dot, n)
        add_icp(s, dot, n)

        result = s.check()
        if result == sat:
            table = extract_table(s, dot, n)
            print(f"\n*** SAT at N={n} ***")
            for i in range(n):
                print(f"  row {i}: {table[i]}")

            # Verify
            verify_e2pm(table, n)
            no_ret, q, e = verify_no_retraction(table, n)
            if not no_ret:
                print(f"  VERIFICATION FAILED: retraction pair found at q={q}, e={e}")
                continue
            icp_ok, witness = verify_icp(table, n)
            if not icp_ok:
                print(f"  VERIFICATION FAILED: ICP not satisfied")
                continue

            print(f"  Verified: E2PM ✓, no retraction pair ✓, ICP ✓ (witness: a={witness[0]}, b={witness[1]}, c={witness[2]})")
            print_lean_table(table, n, f"rawHnoS{n}")
            return table, n
        else:
            print(f"  {result}")

    print("\nNo H-without-S witness found up to N=10")
    return None, None


if __name__ == "__main__":
    d_table, d_n = search_d_without_s()
    h_table, h_n = search_h_without_s()

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    if d_table:
        print(f"  D ⇏ S witness found at N={d_n}")
    else:
        print(f"  D ⇏ S: NO WITNESS FOUND")
    if h_table:
        print(f"  H ⇏ S witness found at N={h_n}")
    else:
        print(f"  H ⇏ S: NO WITNESS FOUND")

    if d_table and h_table:
        print("\n  *** FULL 6-WAY INDEPENDENCE IS ACHIEVABLE ***")
    else:
        print("\n  Full independence may require larger N or different approach.")

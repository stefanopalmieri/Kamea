#!/usr/bin/env python3
"""
Find an N=6 S+D+ICP witness with existential role assignment.
Roles may overlap (ICP witnesses can coincide with retraction pair/classifier).
"""

from z3 import *

def col_ite_lookup(dot, row, col_expr, n):
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry

def find_n6_sdh():
    n = 6
    s = Solver()
    s.set("timeout", 60000)
    dot = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]

    # Range
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

    # Extensionality
    for x in range(n):
        for y in range(x + 1, n):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(n)]))

    # S: retraction pair Q=2, E=3 with E-transparency
    q, e = 2, 3
    for x in range(2, n):
        qx = dot[q][x]
        s.add(col_ite_lookup(dot, e, qx, n) == x)
        ex = dot[e][x]
        s.add(col_ite_lookup(dot, q, ex, n) == x)
    s.add(dot[e][0] == 0)
    s.add(dot[e][1] == 1)

    # D: try each tau value explicitly

    for tau_val in range(2, n):
        print(f"Trying tau={tau_val}...")
        s2 = Solver()
        s2.set("timeout", 60000)
        # Copy all assertions
        for a in s.assertions():
            s2.add(a)

        # Classifier: tau_val is all-boolean
        for j in range(n):
            s2.add(Or(dot[tau_val][j] == 0, dot[tau_val][j] == 1))

        # tau ≠ absorbers (already guaranteed since tau_val >= 2)

        # Kripke dichotomy: every non-absorber is all-boolean or all-non-boolean on core
        for x in range(2, n):
            is_tester = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(n)])
            for y in range(2, n):
                s2.add(Or(is_tester, dot[x][y] >= 2))

        # has_non_classifier: at least one non-absorber is not all-boolean
        s2.add(Or([Not(And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(n)])) for x in range(2, n)]))

        # ICP: existential a, b, c (pairwise distinct non-absorbers)
        # b preserves core, a·x = c·(b·x) on core, a non-trivial
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

        s2.add(Or(icp_clauses))

        result = s2.check()
        if result == sat:
            m = s2.model()
            print(f"\nSAT at N={n} with tau={tau_val}!")
            print(f"\nCayley table:")
            table = []
            for i in range(n):
                row = []
                for j in range(n):
                    v = m.eval(dot[i][j]).as_long()
                    row.append(v)
                table.append(row)
                print(f"  row {i}: {row}")

            # Find ICP witness
            for a in range(2, n):
                for b in range(2, n):
                    if b == a: continue
                    for c in range(2, n):
                        if c == a or c == b: continue
                        # Check b preserves core
                        if not all(table[b][x] >= 2 for x in range(2, n)):
                            continue
                        # Check factorization
                        if not all(table[a][x] == table[c][table[b][x]] for x in range(2, n)):
                            continue
                        # Check non-triviality
                        vals = set(table[a][x] for x in range(2, n))
                        if len(vals) >= 2:
                            print(f"  ICP witness: a={a}, b={b}, c={c}")

            # Print Lean format
            print(f"\nLean rawW6:")
            for i in range(n):
                parts = []
                for j in range(n):
                    parts.append(f"| {i}, {j} => {table[i][j]}")
                print(f"  {' '.join(parts)}")

            return table

    print("UNSAT at all tau values")
    return None

if __name__ == "__main__":
    find_n6_sdh()

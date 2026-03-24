#!/usr/bin/env python3
"""
Find an FRM where ICP-without-non-triviality holds but full ICP fails.
Need: a,b,c pairwise distinct non-absorbers, b preserves core, a·x = c·(b·x) on core,
but a is constant on core (trivial). AND no non-trivial ICP witness exists.
"""

from z3 import *

def col_ite_lookup(dot, row, col_expr, n):
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry

for n in range(5, 8):
    print(f"\n=== Trying N={n} ===")
    s = Solver()
    s.set("timeout", 60000)
    dot = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]

    # Range
    for i in range(n):
        for j in range(n):
            s.add(dot[i][j] >= 0, dot[i][j] < n)

    # Absorbers
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

    # FRM: retraction pair Q=2, E=3
    q_idx, e_idx = 2, 3
    for x in range(2, n):
        qx = dot[q_idx][x]
        s.add(col_ite_lookup(dot, e_idx, qx, n) == x)
        ex = dot[e_idx][x]
        s.add(col_ite_lookup(dot, q_idx, ex, n) == x)
    s.add(dot[e_idx][0] == 0)
    s.add(dot[e_idx][1] == 1)

    # ICP-without-non-triviality holds: ∃ a,b,c pairwise distinct non-absorbers,
    # b preserves core, a·x = c·(b·x) on core (but a may be constant on core)
    weak_icp_clauses = []
    for a in range(2, n):
        for b in range(2, n):
            if b == a: continue
            for c in range(2, n):
                if c == a or c == b: continue
                b_pres = And([dot[b][x] >= 2 for x in range(2, n)])
                fact = And([dot[a][x] == col_ite_lookup(dot, c, dot[b][x], n) for x in range(2, n)])
                weak_icp_clauses.append(And(b_pres, fact))
    s.add(Or(weak_icp_clauses))

    # Full ICP fails: no triple satisfies factorization + non-triviality
    for a in range(2, n):
        for b in range(2, n):
            if b == a: continue
            for c in range(2, n):
                if c == a or c == b: continue
                b_pres = And([dot[b][x] >= 2 for x in range(2, n)])
                fact = And([dot[a][x] == col_ite_lookup(dot, c, dot[b][x], n) for x in range(2, n)])
                nontriv = Or([dot[a][x] != dot[a][y] for x in range(2, n) for y in range(x+1, n)])
                # Block this triple from satisfying full ICP
                s.add(Not(And(b_pres, fact, nontriv)))

    result = s.check()
    if result == sat:
        m = s.model()
        print(f"SAT!")
        table = []
        for i in range(n):
            row = [m.eval(dot[i][j]).as_long() for j in range(n)]
            table.append(row)
            print(f"  row {i}: {row}")

        # Find the weak ICP witness
        for a in range(2, n):
            for b in range(2, n):
                if b == a: continue
                for c in range(2, n):
                    if c == a or c == b: continue
                    if not all(table[b][x] >= 2 for x in range(2, n)):
                        continue
                    if not all(table[a][x] == table[c][table[b][x]] for x in range(2, n)):
                        continue
                    vals = set(table[a][x] for x in range(2, n))
                    print(f"  Weak ICP: a={a}, b={b}, c={c}, a-values={vals}, trivial={len(vals)==1}")

        # Lean format
        print(f"\nLean format:")
        for i in range(n):
            parts = [f"| {i}, {j} => {table[i][j]}" for j in range(n)]
            print(f"  {' '.join(parts)}")
        break
    else:
        print(f"  {result}")

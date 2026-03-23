#!/usr/bin/env python3
"""
Search for a structural S ⇏ H counterexample.

An extensional 2-pointed magma with a retraction pair (capability S)
but no ICP (capability H), at a size where ICP is non-vacuous
(≥ 3 core elements, so the failure is structural, not cardinality).
"""

from z3 import And, If, Int, Not, Or, Solver, sat


def lookup(table, row, col_expr, n):
    """Encode table[row][col_expr] where col_expr is a Z3 expression."""
    result = table[row][0]
    for v in range(1, n):
        result = If(col_expr == v, table[row][v], result)
    return result


def search_s_not_h(N, timeout=300):
    print(f"--- N={N} (core size {N-2}) ---")
    s = Solver()
    s.set("timeout", timeout * 1000)

    T = [[Int(f"t_{i}_{j}") for j in range(N)] for i in range(N)]
    core = list(range(2, N))

    # Range
    for i in range(N):
        for j in range(N):
            s.add(T[i][j] >= 0, T[i][j] < N)

    # 1. Left-absorbers
    for j in range(N):
        s.add(T[0][j] == 0)
        s.add(T[1][j] == 1)

    # 2. No other left-absorbers
    for a in core:
        s.add(Or([T[a][x] != a for x in range(N)]))

    # 3. Extensionality
    for a in range(N):
        for b in range(a + 1, N):
            s.add(Or([T[a][x] != T[b][x] for x in range(N)]))

    # 4. Retraction pair (existential over all s_val, r_val in core)
    retract_clauses = []
    for s_val in core:
        for r_val in core:
            conditions = []
            # r · (s · x) = x for all core x
            for x in core:
                sx = T[s_val][x]
                r_of_sx = lookup(T, r_val, sx, N)
                conditions.append(r_of_sx == x)
            # r · 0 = 0 (anchoring)
            conditions.append(T[r_val][0] == 0)
            retract_clauses.append(And(conditions))
    s.add(Or(retract_clauses))

    # 5. No ICP: for all (a,b,c) pairwise distinct in core, ICP fails
    for a in core:
        for b in core:
            if b == a:
                continue
            for c in core:
                if c == a or c == b:
                    continue
                # Core-preservation of b
                core_pres = And([And(T[b][x] != 0, T[b][x] != 1) for x in core])
                # Factorization: a·x = c·(b·x) for all core x
                fact_conjs = []
                for x in core:
                    bx = T[b][x]
                    c_of_bx = lookup(T, c, bx, N)
                    fact_conjs.append(T[a][x] == c_of_bx)
                factor = And(fact_conjs)
                # Non-triviality: not all a·x equal
                all_equal = And([T[a][x] == T[a][core[0]] for x in core[1:]])
                nontriv = Not(all_equal)
                # ICP holds iff all three; we forbid it
                s.add(Not(And(core_pres, factor, nontriv)))

    result = s.check()
    if result == sat:
        m = s.model()
        table = [[m.evaluate(T[i][j]).as_long() for j in range(N)] for i in range(N)]

        print(f"\n*** SAT — structural S-without-H witness at N={N} ***\n")
        print(f"{'·':>3}", end="")
        for j in range(N):
            print(f"{j:>3}", end="")
        print()
        print("   " + "---" * N)
        for i in range(N):
            print(f"{i:>3}", end="")
            for j in range(N):
                print(f"{table[i][j]:>3}", end="")
            print()

        # Find retraction pair
        for s_val in core:
            for r_val in core:
                ok = all(table[r_val][table[s_val][x]] == x for x in core)
                if ok and table[r_val][0] == 0:
                    print(f"\nRetraction pair: s={s_val}, r={r_val}")
                    # Check if mutual inverse too
                    mutual = all(table[s_val][table[r_val][x]] == x for x in core)
                    print(f"  Mutual inverse (s·(r·x)=x on core): {mutual}")

        # Verify no ICP
        print("\nICP check:")
        found_icp = False
        for a in core:
            for b in core:
                if b == a:
                    continue
                for c in core:
                    if c == a or c == b:
                        continue
                    cp = all(table[b][x] not in {0, 1} for x in core)
                    fc = all(
                        table[a][x] == table[c][table[b][x]] for x in core
                    )
                    vals = set(table[a][x] for x in core)
                    nt = len(vals) >= 2
                    if cp and fc and nt:
                        print(f"  BUG: ICP satisfied by a={a}, b={b}, c={c}")
                        found_icp = True
        if not found_icp:
            print("  Confirmed: no ICP triple exists.")

        # Print Lean format
        print(f"\nLean format:")
        for i in range(N):
            parts = [f"| {i}, {j} => {table[i][j]}" for j in range(N)]
            print(f"  {' '.join(parts)}")
        print(f"  | _, _ => 0")

        return True
    else:
        print(f"  {result}")
        return False


if __name__ == "__main__":
    for N in [6, 7, 8, 10]:
        if search_s_not_h(N):
            break
        print()

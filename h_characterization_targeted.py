#!/usr/bin/env python3
"""
Targeted SAT validation: generate models WITH and WITHOUT H axioms,
test ICP equivalence on both.
"""

from z3 import *
import random
import sys

N = 10
CORE = list(range(2, N))
ABS_SET = {0, 1}


def ite_lookup(dot, row, col_expr, n):
    """Indirect Z3 table lookup."""
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def build_frm_solver(n=10):
    """Base FRM solver."""
    s = Solver()
    s.set("timeout", 15000)

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

    # Retraction pair Q=2, E=3
    for x in range(2, n):
        qx = dot[2][x]
        s.add(ite_lookup(dot, 3, qx, n) == x)
        ex = dot[3][x]
        s.add(ite_lookup(dot, 2, ex, n) == x)

    s.add(dot[3][0] == 0)
    s.add(dot[3][1] == 1)

    return s, dot


def add_H_axioms(s, dot, n=10, g=6, rho=7, eta=8):
    """Add Compose + Inert axioms."""
    core = list(range(2, n))

    # Inert: g maps core away from absorbers
    for x in core:
        s.add(dot[g][x] != 0)
        s.add(dot[g][x] != 1)

    # Compose: η·x = ρ·(g·x) on core
    for x in core:
        gx = dot[g][x]
        s.add(dot[eta][x] == ite_lookup(dot, rho, gx, n))


def add_no_compose(s, dot, n=10, g=6, rho=7):
    """Forbid Compose: for every η candidate, some core x violates η·x = ρ·(g·x)."""
    core = list(range(2, n))
    for eta in range(n):
        # η must fail Compose for at least one core element
        s.add(Or([dot[eta][x] != ite_lookup(dot, rho, dot[g][x], n) for x in core]))


def add_no_ICP(s, dot, n=10):
    """Forbid ICP: for all triples (a, b, c), a != c∘b on core OR b doesn't preserve core."""
    core = list(range(2, n))
    # For every pair (b, c) where b preserves core and c in range:
    # either b doesn't preserve core, or no a matches c∘b
    for b in core:
        for c in range(n):
            # Either b maps some core element to absorber:
            b_not_inert = Or([Or(dot[b][x] == 0, dot[b][x] == 1) for x in core])
            # Or no element (except absorbers, b, c) matches c∘b on core
            no_match_clauses = []
            for a in range(n):
                if a in {0, 1}:
                    continue
                # a fails to match c∘b on at least one core element, OR a==b OR a==c
                a_matches = And([dot[a][x] == ite_lookup(dot, c, dot[b][x], n) for x in core])
                a_is_bc = Or(a == b, a == c)
                no_match_clauses.append(Or(Not(a_matches), a_is_bc))

            s.add(Or(b_not_inert, And(no_match_clauses)))


def extract_table(model, dot, n):
    table = []
    for i in range(n):
        row = [model.evaluate(dot[i][j]).as_long() for j in range(n)]
        table.append(row)
    return table


def has_current_H(table, n=10):
    """Test Compose + Inert with any element assignments."""
    core = list(range(2, n))
    for g in core:
        if not all(table[g][x] not in {0, 1} for x in core):
            continue
        for rho in core:
            if rho == g:
                continue
            comp = tuple(table[rho][table[g][x]] for x in core)
            for eta in range(n):
                if eta == g or eta == rho or eta in {0, 1}:
                    continue
                eta_row = tuple(table[eta][x] for x in core)
                if eta_row == comp:
                    return True, (g, rho, eta)
    return False, None


def has_ICP(table, n=10):
    """Internal Composition Property."""
    core = list(range(2, n))
    for b in core:
        if not all(table[b][x] not in {0, 1} for x in core):
            continue
        for c in range(n):
            comp = tuple(table[c][table[b][x]] for x in core)
            for a in range(n):
                if a in {0, 1} or a == b or a == c:
                    continue
                a_row = tuple(table[a][x] for x in core)
                if a_row == comp:
                    return True, (a, b, c)
    return False, None


def sample_with_constraint(constraint_fn, n_models=50, label="", seed=42):
    """Generate models with a specific constraint."""
    random.seed(seed)
    models = []

    for trial in range(n_models * 20):
        if len(models) >= n_models:
            break

        s, dot = build_frm_solver()
        constraint_fn(s, dot)

        # Random diversity
        s.push()
        for _ in range(2):
            i = random.randint(2, N - 1)
            j = random.randint(0, N - 1)
            v = random.randint(0, N - 1)
            s.add(dot[i][j] == v)

        result = s.check()
        if result == sat:
            table = extract_table(s.model(), dot, N)
            table_key = tuple(tuple(row) for row in table)
            if table_key not in {tuple(tuple(r) for r in m) for m in models}:
                models.append(table)

        s.pop()

    print(f"  [{label}] Generated {len(models)}/{n_models} models", file=sys.stderr)
    return models


def main():
    print("=" * 60)
    print("TARGETED H-CHARACTERIZATION VALIDATION")
    print("=" * 60)

    # Group 1: Models WITH H (Compose + Inert forced)
    print("\nGenerating models WITH H axioms (Compose + Inert)...")
    h_models = sample_with_constraint(
        lambda s, dot: add_H_axioms(s, dot),
        n_models=50, label="WITH H", seed=42
    )

    # Group 2: Models WITHOUT Compose (forced to fail)
    print("Generating models WITHOUT Compose...")
    no_compose_models = sample_with_constraint(
        lambda s, dot: add_no_compose(s, dot),
        n_models=50, label="NO Compose", seed=123
    )

    # Group 3: Models without any ICP (forced)
    print("Generating models WITHOUT ICP (no representable composition)...")
    no_icp_models = sample_with_constraint(
        lambda s, dot: add_no_ICP(s, dot),
        n_models=50, label="NO ICP", seed=456
    )

    # Test all properties on all groups
    groups = [
        ("WITH H", h_models),
        ("NO Compose (g=6,ρ=7)", no_compose_models),
        ("NO ICP", no_icp_models),
    ]

    print("\n" + "=" * 60)
    print("RESULTS")
    print("=" * 60)

    for group_name, models in groups:
        if not models:
            print(f"\n  [{group_name}] No models generated")
            continue

        h_count = 0
        icp_count = 0
        agree = 0
        h_not_icp = 0
        icp_not_h = 0

        for table in models:
            h_result, _ = has_current_H(table)
            icp_result, _ = has_ICP(table)

            if h_result:
                h_count += 1
            if icp_result:
                icp_count += 1
            if h_result == icp_result:
                agree += 1
            if h_result and not icp_result:
                h_not_icp += 1
            if icp_result and not h_result:
                icp_not_h += 1

        n = len(models)
        print(f"\n  [{group_name}] ({n} models)")
        print(f"    H (Compose+Inert): {h_count}/{n} ({h_count/n:.0%})")
        print(f"    ICP:               {icp_count}/{n} ({icp_count/n:.0%})")
        print(f"    H ↔ ICP agreement: {agree}/{n} ({agree/n:.0%})")
        if h_not_icp > 0:
            print(f"    H ∧ ¬ICP: {h_not_icp} *** DISCREPANCY ***")
        if icp_not_h > 0:
            print(f"    ICP ∧ ¬H: {icp_not_h} *** DISCREPANCY ***")

        # Show any discrepancies in detail
        if h_not_icp > 0 or icp_not_h > 0:
            for idx, table in enumerate(models):
                h_r, h_w = has_current_H(table)
                i_r, i_w = has_ICP(table)
                if h_r != i_r:
                    print(f"\n    Discrepancy model {idx}:")
                    print(f"      H={h_r} (witness: {h_w})")
                    print(f"      ICP={i_r} (witness: {i_w})")
                    for row in table:
                        print(f"        {row}")

    # Final verdict
    print("\n" + "=" * 60)
    print("EQUIVALENCE VERDICT")
    print("=" * 60)

    total_models = sum(len(m) for _, m in groups)
    total_agree = 0
    total_h = 0
    total_icp = 0
    for _, models in groups:
        for table in models:
            h_r, _ = has_current_H(table)
            i_r, _ = has_ICP(table)
            if h_r == i_r:
                total_agree += 1
            if h_r:
                total_h += 1
            if i_r:
                total_icp += 1

    print(f"  Total models tested: {total_models}")
    print(f"  H holds: {total_h}")
    print(f"  ICP holds: {total_icp}")
    print(f"  Perfect agreement: {total_agree}/{total_models} ({total_agree/total_models:.0%})")

    if total_agree == total_models:
        print("\n  ✓ H ↔ ICP: EMPIRICALLY EQUIVALENT across all tested models")
        print("    The Internal Composition Property is a valid single-concept")
        print("    characterization of evaluator internalization (Compose + Inert).")
    else:
        print("\n  ✗ H and ICP are NOT equivalent. See discrepancies above.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
SAT-based validation: test candidate H-characterizations across many random
retraction magmas at N=10.

For each model, test:
  1. Current H axioms: Compose (η·x = ρ·(g·x)) + Inert (g maps core to core)
  2. ICP (Internal Composition Property): ∃ a,b,c distinct in core:
     b·x ∉ ABS for x in core, and a·x = c·(b·x) for all x in core
  3. Compositional Absorption (CA): ICP + fixed-point requirement
  4. Whether any non-trivial composition is representable at all

Goal: check whether ICP perfectly tracks H across diverse models.
"""

from z3 import *
import random
import sys

N = 10
CORE = list(range(2, N))
ABS = {0, 1}


def build_frm_solver(n=10):
    """Build Z3 solver for Faithful Retract Magma (FRM) at size n."""
    s = Solver()
    s.set("timeout", 10000)  # 10s per model

    dot = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]

    # Range constraints
    for i in range(n):
        for j in range(n):
            s.add(dot[i][j] >= 0, dot[i][j] < n)

    # Two absorbers
    for j in range(n):
        s.add(dot[0][j] == 0)  # ⊤
        s.add(dot[1][j] == 1)  # ⊥

    # No extra absorbers
    for x in range(2, n):
        s.add(Or([dot[x][j] != x for j in range(n)]))

    # Extensionality: distinct rows
    for x in range(n):
        for y in range(x + 1, n):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(n)]))

    # Retraction pair: Q=2, E=3
    # E·(Q·x) = x and Q·(E·x) = x for x in core
    def ite_lookup(row, col_expr):
        """Indirect table lookup: dot[row][col_expr]."""
        entry = dot[row][0]
        for c in range(1, n):
            entry = If(col_expr == c, dot[row][c], entry)
        return entry

    for x in range(2, n):
        qx = dot[2][x]
        s.add(ite_lookup(3, qx) == x)  # E·(Q·x) = x
        ex = dot[3][x]
        s.add(ite_lookup(2, ex) == x)  # Q·(E·x) = x

    # E-transparency
    s.add(dot[3][0] == 0)
    s.add(dot[3][1] == 1)

    return s, dot


def extract_table(model, dot, n):
    """Extract Cayley table from Z3 model."""
    table = []
    for i in range(n):
        row = []
        for j in range(n):
            row.append(model.evaluate(dot[i][j]).as_long())
        table.append(row)
    return table


def has_current_H(table, n=10):
    """
    Test current H axioms (Compose + Inert) with ANY element assignments.
    Search for g, ρ, η (all in core) such that:
    - g maps core away from absorbers (Inert)
    - η·x = ρ·(g·x) for all x in core (Compose)
    """
    core = list(range(2, n))
    abs_set = {0, 1}

    for g in core:
        # Check Inert
        if not all(table[g][x] not in abs_set for x in core):
            continue
        for rho in core:
            if rho == g:
                continue
            # Compute ρ∘g on core
            comp = tuple(table[rho][table[g][x]] for x in core)
            # Check if any element has this row on core
            for eta in range(n):
                if eta == g or eta == rho:
                    continue
                eta_row = tuple(table[eta][x] for x in core)
                if eta_row == comp:
                    return True, (g, rho, eta)
    return False, None


def has_ICP(table, n=10):
    """
    Internal Composition Property:
    ∃ a, b, c ∈ S, pairwise distinct, with b ∈ core, such that:
    - b·x ∉ {0,1} for all x in core (b preserves core)
    - a·x = c·(b·x) for all x in core (a = c ∘ b on core)
    - a ∉ {0,1} (non-trivial)
    """
    core = list(range(2, n))
    abs_set = {0, 1}

    for b in core:
        if not all(table[b][x] not in abs_set for x in core):
            continue
        for c in range(n):
            comp = tuple(table[c][table[b][x]] for x in core)
            for a in range(n):
                if a in abs_set:
                    continue
                if a == b or a == c:
                    continue
                a_row = tuple(table[a][x] for x in core)
                if a_row == comp:
                    return True, (a, b, c)
    return False, None


def has_CA(table, n=10):
    """
    Compositional Absorption: ICP + fixed-point requirement.
    In addition to ICP(a,b,c), require:
    ∃ y: c has a non-absorber fixed point reachable via y
    i.e., ∃ y: c·(y·c) = y·c and y·c ∉ {0,1}
    """
    core = list(range(2, n))
    abs_set = {0, 1}

    for b in core:
        if not all(table[b][x] not in abs_set for x in core):
            continue
        for c in core:
            comp = tuple(table[c][table[b][x]] for x in core)
            a_found = None
            for a in range(n):
                if a in abs_set or a == b or a == c:
                    continue
                a_row = tuple(table[a][x] for x in core)
                if a_row == comp:
                    a_found = a
                    break

            if a_found is None:
                continue

            # Check: c has non-absorber fixed point via some y
            for y in range(n):
                yc = table[y][c]
                if yc not in abs_set and table[c][yc] == yc:
                    return True, (a_found, b, c, y, yc)

    return False, None


def has_any_representable_composition(table, n=10):
    """
    Does ANY non-trivial two-element composition factor through a single element?
    ∃ a, b, c ∈ core: a·x = c·(b·x) for all x in core
    (no inertness requirement on b)
    """
    core = list(range(2, n))

    # Build row lookup
    row_to_elem = {}
    for a in range(n):
        r = tuple(table[a][x] for x in core)
        if r not in row_to_elem:
            row_to_elem[r] = a

    for c in core:
        for b in core:
            if c == b:
                continue
            comp = tuple(table[c][table[b][x]] for x in core)
            if comp in row_to_elem:
                a = row_to_elem[comp]
                if a not in {0, 1} and a != b and a != c:
                    return True, (a, b, c)
    return False, None


def sample_models(n_models=100, seed=42):
    """Generate diverse FRM models using SAT with random diversity constraints."""
    random.seed(seed)
    models = []

    s, dot = build_frm_solver()

    for trial in range(n_models * 10):  # Try more times than needed
        if len(models) >= n_models:
            break

        # Add random preference to get diverse models
        s.push()

        # Randomly fix a few cells to diversify
        for _ in range(3):
            i = random.randint(2, N - 1)
            j = random.randint(0, N - 1)
            v = random.randint(0, N - 1)
            s.add(dot[i][j] == v)

        result = s.check()
        if result == sat:
            table = extract_table(s.model(), dot, N)
            # Check it's not a duplicate
            table_key = tuple(tuple(row) for row in table)
            if table_key not in {tuple(tuple(r) for r in m) for m in models}:
                models.append(table)
                if len(models) % 10 == 0:
                    print(f"  Generated {len(models)}/{n_models} models...",
                          file=sys.stderr)

        s.pop()

    return models


def main():
    print("Generating diverse FRM models at N=10...")
    models = sample_models(100)
    print(f"Generated {len(models)} unique models.\n")

    # Test each property on each model
    results = {
        'H': [],       # Current H (Compose + Inert)
        'ICP': [],     # Internal Composition Property
        'CA': [],      # Compositional Absorption
        'AnyComp': [], # Any representable composition
    }

    for i, table in enumerate(models):
        h_result, _ = has_current_H(table)
        icp_result, _ = has_ICP(table)
        ca_result, _ = has_CA(table)
        any_result, _ = has_any_representable_composition(table)

        results['H'].append(h_result)
        results['ICP'].append(icp_result)
        results['CA'].append(ca_result)
        results['AnyComp'].append(any_result)

    # Summary
    print("=" * 60)
    print("PROPERTY FREQUENCIES")
    print("=" * 60)
    for prop, vals in results.items():
        count = sum(vals)
        print(f"  {prop:<12}: {count}/{len(vals)} ({count/len(vals):.1%})")

    # Correlation matrix
    print("\n" + "=" * 60)
    print("CORRELATION MATRIX (agreement rate)")
    print("=" * 60)
    props = list(results.keys())
    print(f"{'':>12}", end="")
    for p in props:
        print(f"  {p:>8}", end="")
    print()

    for p1 in props:
        print(f"  {p1:<10}", end="")
        for p2 in props:
            agree = sum(1 for a, b in zip(results[p1], results[p2]) if a == b)
            print(f"  {agree/len(models):>7.1%}", end="")
        print()

    # Detailed discrepancies
    print("\n" + "=" * 60)
    print("DISCREPANCY ANALYSIS")
    print("=" * 60)

    # H vs ICP
    h_not_icp = sum(1 for h, i in zip(results['H'], results['ICP']) if h and not i)
    icp_not_h = sum(1 for h, i in zip(results['H'], results['ICP']) if not h and i)
    print(f"\n  H ∧ ¬ICP: {h_not_icp} (H holds but ICP fails)")
    print(f"  ICP ∧ ¬H: {icp_not_h} (ICP holds but H fails)")

    if h_not_icp > 0 or icp_not_h > 0:
        print("  WARNING: H and ICP are NOT equivalent!")
        for idx in range(len(models)):
            if results['H'][idx] != results['ICP'][idx]:
                print(f"    Model {idx}: H={results['H'][idx]}, ICP={results['ICP'][idx]}")
                # Print the table
                for row in models[idx]:
                    print(f"      {row}")
                h_det, h_wit = has_current_H(models[idx])
                icp_det, icp_wit = has_ICP(models[idx])
                print(f"    H witness: {h_wit}")
                print(f"    ICP witness: {icp_wit}")
                if idx > 5:
                    print("    (truncated)")
                    break
    else:
        print("  H ↔ ICP: PERFECT EQUIVALENCE across all models")

    # H vs CA
    h_not_ca = sum(1 for h, c in zip(results['H'], results['CA']) if h and not c)
    ca_not_h = sum(1 for h, c in zip(results['H'], results['CA']) if not h and c)
    print(f"\n  H ∧ ¬CA: {h_not_ca} (H holds but CA fails)")
    print(f"  CA ∧ ¬H: {ca_not_h} (CA holds but H fails)")

    # AnyComp vs H
    h_not_any = sum(1 for h, a in zip(results['H'], results['AnyComp']) if h and not a)
    any_not_h = sum(1 for h, a in zip(results['H'], results['AnyComp']) if not h and a)
    print(f"\n  H ∧ ¬AnyComp: {h_not_any}")
    print(f"  AnyComp ∧ ¬H: {any_not_h}")

    if any_not_h > 0:
        print("  Models with representable composition but no H:")
        count = 0
        for idx in range(len(models)):
            if results['AnyComp'][idx] and not results['H'][idx]:
                count += 1
                if count <= 3:
                    _, wit = has_any_representable_composition(models[idx])
                    print(f"    Model {idx}: witness {wit}")

    # Implication summary
    print("\n" + "=" * 60)
    print("IMPLICATION SUMMARY")
    print("=" * 60)
    pairs = [
        ('H', 'ICP', 'H ⇒ ICP'),
        ('ICP', 'H', 'ICP ⇒ H'),
        ('H', 'CA', 'H ⇒ CA'),
        ('CA', 'H', 'CA ⇒ H'),
        ('H', 'AnyComp', 'H ⇒ AnyComp'),
        ('AnyComp', 'H', 'AnyComp ⇒ H'),
        ('ICP', 'CA', 'ICP ⇒ CA'),
        ('CA', 'ICP', 'CA ⇒ ICP'),
    ]

    for p1, p2, label in pairs:
        violations = sum(1 for a, b in zip(results[p1], results[p2]) if a and not b)
        holds = violations == 0
        print(f"  {label:<20}: {'YES' if holds else 'NO'} "
              f"({violations} violations)")


if __name__ == "__main__":
    main()

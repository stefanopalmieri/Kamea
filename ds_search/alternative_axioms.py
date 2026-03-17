#!/usr/bin/env python3
"""
Alternative Axiom Systems — Direction 2 from AXIOM_PROMPT.md

Design DIFFERENT axiom systems for self-describing finite algebras,
starting from different intuitions entirely. Check if the same
5 categories and 3 walls emerge.

Approach A — Information-theoretic:
  Axiomatize in terms of information flow (constant/injective/surjective
  rows), not roles. See if the same role structure emerges.

Approach B — Category-theoretic:
  Require retraction pair, product with projections, initial/terminal
  object. See if the same role structure emerges.

Usage:
  uv run python -m ds_search.alternative_axioms
"""

import time
from z3 import Solver, Int, If, And, Or, Not, Distinct, sat, unsat

from ds_search.axiom_explorer import (
    ite_lookup, col_ite_lookup, classify_elements, extract_table,
    print_table, print_model_summary,
)


N = 12


def make_dot(s, N):
    """Create dot table with range constraints."""
    dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]
    for i in range(N):
        for j in range(N):
            s.add(dot[i][j] >= 0, dot[i][j] < N)
    return dot


def add_extensionality(s, dot, N):
    """All rows distinct."""
    for x in range(N):
        for y in range(x + 1, N):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(N)]))


# ═══════════════════════════════════════════════════════════════════════
# Approach A: Information-Theoretic
# ═══════════════════════════════════════════════════════════════════════

def approach_a():
    """
    Axiomatize via information flow properties of rows:
    - Constant rows (information-destroying) = absorbers
    - Boolean rows (binary classifiers) = testers
    - Injective rows (information-preserving) = encoders?
    - Non-injective, non-constant, non-boolean = inert?

    Key axioms:
    A1: Exactly 2 constant rows (left-absorbers)
    A2: At least 1 binary-classifier row (outputs only in {0,1})
    A3: At least 1 information-preserving row (injective on non-absorbers)
    A4: At least 1 information-destroying-but-not-constant row
        (non-injective, non-boolean, non-absorber)
    A5: Extensionality (all rows distinct)
    A6: Inverse pair — ∃ two elements a,b such that a·(b·x)=x and b·(a·x)=x
        on some subset (quote/eval analog via information theory)
    A7: Discoverability — for every element x, there exists some element d
        such that d·x is unique (distinguishes x from all others)
    """
    print("=" * 70)
    print("APPROACH A: Information-Theoretic Axioms")
    print("=" * 70)

    s = Solver()
    s.set("timeout", 300 * 1000)
    dot = make_dot(s, N)

    # A1: Exactly 2 constant (absorber) rows: elements 0 and 1
    for j in range(N):
        s.add(dot[0][j] == 0)
        s.add(dot[1][j] == 1)
    # No other absorbers
    for x in range(2, N):
        s.add(Or([dot[x][j] != x for j in range(N)]))

    # A5: Extensionality
    add_extensionality(s, dot, N)

    # A2: At least 1 binary classifier (tester)
    tester_exprs = []
    for x in range(2, N):
        tester_exprs.append(
            And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        )
    s.add(Or(tester_exprs))

    # A3: At least 1 injective row on non-absorbers (information-preserving)
    # Injective on {2..N-1}: all outputs distinct
    inj_exprs = []
    for x in range(2, N):
        # x's outputs on non-absorber inputs are all distinct
        non_abs_outputs = [dot[x][j] for j in range(2, N)]
        # All pairs distinct
        pairs = []
        for j1 in range(2, N):
            for j2 in range(j1 + 1, N):
                pairs.append(dot[x][j1] != dot[x][j2])
        if pairs:
            inj_exprs.append(And(pairs))
    s.add(Or(inj_exprs))

    # A4: At least 1 "lossy" row — not constant, not boolean, not injective on non-abs
    # i.e., has a collision on non-absorber inputs and has non-boolean outputs
    lossy_exprs = []
    for x in range(2, N):
        # Not boolean
        not_bool = Or([And(dot[x][j] != 0, dot[x][j] != 1) for j in range(N)])
        # Has a collision on non-absorber inputs
        collision = Or([dot[x][j1] == dot[x][j2]
                        for j1 in range(2, N) for j2 in range(j1 + 1, N)])
        lossy_exprs.append(And(not_bool, collision))
    s.add(Or(lossy_exprs))

    # A6: Inverse pair on core {2,3,4,5}
    CORE_LO, CORE_HI = 2, 6
    # ∃ a, b (both ≥ 2, a ≠ b) such that a·(b·x) = x and b·(a·x) = x for x in core
    inv_exprs = []
    for a in range(2, N):
        for b in range(a + 1, N):
            roundtrip = []
            for x in range(CORE_LO, CORE_HI):
                bx = dot[b][x]
                a_bx = col_ite_lookup(dot, a, bx, N)
                ax = dot[a][x]
                b_ax = col_ite_lookup(dot, b, ax, N)
                roundtrip.append(a_bx == x)
                roundtrip.append(b_ax == x)
            inv_exprs.append(And(roundtrip))
    s.add(Or(inv_exprs))

    # A7: Discoverability — every non-absorber element is uniquely identified
    # For all x ≥ 2, ∃ d such that d·x ≠ d·y for all y ≠ x (y ≥ 2)
    for x in range(2, N):
        disc_exprs = []
        for d in range(N):
            # d distinguishes x from all other non-absorbers
            diffs = [dot[d][x] != dot[d][y] for y in range(2, N) if y != x]
            if diffs:
                disc_exprs.append(And(diffs))
        s.add(Or(disc_exprs))

    print("\nChecking SAT...")
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  Status: {str(r).upper()} ({elapsed:.1f}s)")

    if str(r) == "sat":
        table = extract_table(s.model(), dot, N)
        cats = classify_elements(table)
        print(f"\n  Categories (standard classification):")
        print(f"    Absorbers: {cats['absorbers']} (count={len(cats['absorbers'])})")
        print(f"    Testers:   {cats['testers']} (count={len(cats['testers'])})")
        print(f"    Encoders:  {cats['encoders']} (count={len(cats['encoders'])})")
        print(f"    Inert:     {cats['inert']} (count={len(cats['inert'])})")
        print(f"\n  Five categories present: {len(cats['absorbers']) >= 2 and len(cats['testers']) >= 1 and len(cats['encoders']) >= 1 and len(cats['inert']) >= 1}")

        # Check information-theoretic properties
        print(f"\n  Information-theoretic analysis:")
        for x in range(2, N):
            row = [table[x][j] for j in range(N)]
            non_abs_outputs = [table[x][j] for j in range(2, N)]
            is_bool = all(v in (0, 1) for v in row)
            is_injective = len(set(non_abs_outputs)) == len(non_abs_outputs)
            has_collision = len(set(non_abs_outputs)) < len(non_abs_outputs)
            has_nonbool = any(v not in (0, 1) for v in row)
            label = "tester" if is_bool else "injective" if is_injective else "lossy" if (has_nonbool and has_collision) else "other"
            if x < 8 or label != "other":  # only show interesting elements
                print(f"    Element {x}: {label} (unique outputs on non-abs: {len(set(non_abs_outputs))}/{len(non_abs_outputs)})")

        print_table(table)
        return table
    return None


# ═══════════════════════════════════════════════════════════════════════
# Approach B: Category-Theoretic
# ═══════════════════════════════════════════════════════════════════════

def approach_b():
    """
    Think of the Cayley table as defining a single-object category
    where elements are endomorphisms. Require:
    B1: Absorbers (initial + terminal object analogs)
    B2: Extensionality
    B3: Retraction pair: ∃ r, s with r·s·x = x on core (section/retraction)
    B4: Product structure: ∃ p, π₁, π₂ with π₁·(p·x) and π₂·(p·x) projections
    B5: Discriminator: ∃ d with d·x = π₁·x if test(x) else π₂·x
    """
    print("\n" + "=" * 70)
    print("APPROACH B: Category-Theoretic Axioms")
    print("=" * 70)

    s = Solver()
    s.set("timeout", 300 * 1000)
    dot = make_dot(s, N)

    CORE_LO, CORE_HI = 2, 6

    # B1: Two absorbers
    for j in range(N):
        s.add(dot[0][j] == 0)
        s.add(dot[1][j] == 1)
    for x in range(2, N):
        s.add(Or([dot[x][j] != x for j in range(N)]))

    # B2: Extensionality
    add_extensionality(s, dot, N)

    # B3: Retraction pair — ∃ r, s with r·(s·x) = x on core AND s·(r·x) = x
    # This is the same as QE (quote/eval), just category-theoretically motivated
    ret_exprs = []
    for r in range(2, N):
        for sec in range(2, N):
            if r == sec:
                continue
            roundtrip = []
            for x in range(CORE_LO, CORE_HI):
                sx = dot[sec][x]
                r_sx = col_ite_lookup(dot, r, sx, N)
                rx = dot[r][x]
                s_rx = col_ite_lookup(dot, sec, rx, N)
                roundtrip.append(r_sx == x)
                roundtrip.append(s_rx == x)
            ret_exprs.append(And(roundtrip))
    s.add(Or(ret_exprs))

    # B4: There exists a "classifier" — element whose row is all-boolean
    # (morphism to the terminal/initial subobject)
    classifier_exprs = []
    for x in range(2, N):
        classifier_exprs.append(
            And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        )
    s.add(Or(classifier_exprs))

    # B5: There exists a "constant morphism" that is not an absorber
    # but has limited range (inert — maps to at most one non-boolean value)
    # This is the categorical "ground" — a morphism that factors through
    # the terminal object on most inputs
    from ds_search.forced_roles_test import is_inert_z3
    inert_exprs = []
    for x in range(2, N):
        inert_exprs.append(is_inert_z3(dot, x, N))
    s.add(Or(inert_exprs))

    # B6: Conditional morphism — ∃ d that dispatches based on classifier
    # d·x = f·x if τ·x = 0, else g·x, for some f, g, τ
    cond_exprs = []
    for d in range(2, N):
        for tau in range(2, N):
            for f in range(2, N):
                for g in range(2, N):
                    if len({d, tau, f, g}) < 3:  # need at least 3 distinct
                        continue
                    dispatch = []
                    for x in range(CORE_LO, CORE_HI):
                        dispatch.append(
                            If(dot[tau][x] == 0,
                               dot[d][x] == dot[f][x],
                               dot[d][x] == dot[g][x])
                        )
                    # f and g must differ on core
                    dispatch.append(
                        Or([dot[f][x] != dot[g][x] for x in range(CORE_LO, CORE_HI)])
                    )
                    cond_exprs.append(And(dispatch))
    s.add(Or(cond_exprs))

    print("\nChecking SAT...")
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  Status: {str(r).upper()} ({elapsed:.1f}s)")

    if str(r) == "sat":
        table = extract_table(s.model(), dot, N)
        cats = classify_elements(table)
        print(f"\n  Categories (standard classification):")
        print(f"    Absorbers: {cats['absorbers']} (count={len(cats['absorbers'])})")
        print(f"    Testers:   {cats['testers']} (count={len(cats['testers'])})")
        print(f"    Encoders:  {cats['encoders']} (count={len(cats['encoders'])})")
        print(f"    Inert:     {cats['inert']} (count={len(cats['inert'])})")
        print(f"\n  Five categories present: {len(cats['absorbers']) >= 2 and len(cats['testers']) >= 1 and len(cats['encoders']) >= 1 and len(cats['inert']) >= 1}")
        print_table(table)
        return table
    return None


# ═══════════════════════════════════════════════════════════════════════
# Approach C: Game-Theoretic (Discoverability-First)
# ═══════════════════════════════════════════════════════════════════════

def approach_c():
    """
    Start from discoverability as the PRIMARY axiom, not a consequence.

    C1: Two absorbers (dominant strategies)
    C2: Extensionality (strategies are distinguishable by opponents)
    C3: Full discoverability — every element can be uniquely identified
        by probing with some element
    C4: Classification strategy — ∃ element that partitions opponents
        into exactly 2 groups ({0,1} outputs = tester)
    C5: Transformation strategies — ∃ elements that remap opponents
        into non-trivial images (encoders)
    C6: Inert strategy — ∃ element that is "neutral" (neither classifies
        nor transforms significantly)
    C7: Strategic diversity — the classification and transformation
        strategies are independent (not derivable from each other)
    """
    print("\n" + "=" * 70)
    print("APPROACH C: Game-Theoretic (Discoverability-First)")
    print("=" * 70)

    s = Solver()
    s.set("timeout", 300 * 1000)
    dot = make_dot(s, N)

    # C1: Two absorbers (dominant strategies)
    for j in range(N):
        s.add(dot[0][j] == 0)
        s.add(dot[1][j] == 1)
    for x in range(2, N):
        s.add(Or([dot[x][j] != x for j in range(N)]))

    # C2: Extensionality
    add_extensionality(s, dot, N)

    # C3: Full discoverability — for every x ≥ 2, ∃ d that uniquely identifies x
    for x in range(2, N):
        disc_exprs = []
        for d in range(N):
            diffs = [dot[d][x] != dot[d][y] for y in range(2, N) if y != x]
            if diffs:
                disc_exprs.append(And(diffs))
        s.add(Or(disc_exprs))

    # C4: At least 1 classifier (tester)
    for_tester = []
    for x in range(2, N):
        for_tester.append(
            And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        )
    s.add(Or(for_tester))

    # C5: At least 2 distinct transformers (encoders) with different profiles
    enc_exprs = {}  # indexed by element index
    for x in range(2, N):
        pairs = []
        for j1 in range(N):
            for j2 in range(j1 + 1, N):
                pairs.append(And(
                    dot[x][j1] != 0, dot[x][j1] != 1,
                    dot[x][j2] != 0, dot[x][j2] != 1,
                    dot[x][j1] != dot[x][j2]))
        enc_exprs[x] = Or(pairs) if pairs else False

    # At least 2 encoders
    enc_pair_exprs = []
    for e1 in range(2, N):
        for e2 in range(e1 + 1, N):
            enc_pair_exprs.append(And(enc_exprs[e1], enc_exprs[e2]))
    s.add(Or(enc_pair_exprs))

    # C6: At least 1 inert element
    from ds_search.forced_roles_test import is_inert_z3
    inert_exprs = []
    for x in range(2, N):
        inert_exprs.append(is_inert_z3(dot, x, N))
    s.add(Or(inert_exprs))

    # C7: Strategic diversity — ∃ inverse pair on some core
    CORE_LO, CORE_HI = 2, 6
    inv_exprs = []
    for a in range(2, N):
        for b in range(a + 1, N):
            roundtrip = []
            for x in range(CORE_LO, CORE_HI):
                bx = dot[b][x]
                a_bx = col_ite_lookup(dot, a, bx, N)
                ax = dot[a][x]
                b_ax = col_ite_lookup(dot, b, ax, N)
                roundtrip.append(a_bx == x)
                roundtrip.append(b_ax == x)
            inv_exprs.append(And(roundtrip))
    s.add(Or(inv_exprs))

    print("\nChecking SAT...")
    t0 = time.time()
    r = s.check()
    elapsed = time.time() - t0
    print(f"  Status: {str(r).upper()} ({elapsed:.1f}s)")

    if str(r) == "sat":
        table = extract_table(s.model(), dot, N)
        cats = classify_elements(table)
        print(f"\n  Categories (standard classification):")
        print(f"    Absorbers: {cats['absorbers']} (count={len(cats['absorbers'])})")
        print(f"    Testers:   {cats['testers']} (count={len(cats['testers'])})")
        print(f"    Encoders:  {cats['encoders']} (count={len(cats['encoders'])})")
        print(f"    Inert:     {cats['inert']} (count={len(cats['inert'])})")
        print(f"\n  Five categories present: {len(cats['absorbers']) >= 2 and len(cats['testers']) >= 1 and len(cats['encoders']) >= 1 and len(cats['inert']) >= 1}")

        # Check discoverability
        print(f"\n  Discoverability verification:")
        all_disc = True
        for x in range(2, N):
            found_disc = False
            for d in range(N):
                outputs = [table[d][y] for y in range(2, N)]
                if outputs[x - 2] not in [outputs[y - 2] for y in range(2, N) if y != x]:
                    # d·x is unique among d's outputs on non-absorbers
                    found_disc = True
                    break
            if not found_disc:
                all_disc = False
                print(f"    Element {x}: NOT discoverable!")
        if all_disc:
            print(f"    All {N-2} non-absorber elements are discoverable ✓")

        print_table(table)
        return table
    return None


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("=" * 70)
    print("ALTERNATIVE AXIOM SYSTEMS — Direction 2 from AXIOM_PROMPT.md")
    print(f"N={N}")
    print("=" * 70)

    table_a = approach_a()
    table_b = approach_b()
    table_c = approach_c()

    # Summary
    print("\n" + "=" * 70)
    print("COMPARISON SUMMARY")
    print("=" * 70)

    for name, table in [("A (Info-theoretic)", table_a),
                         ("B (Category-theoretic)", table_b),
                         ("C (Game-theoretic)", table_c)]:
        if table is not None:
            cats = classify_elements(table)
            has_5 = (len(cats['absorbers']) >= 2 and len(cats['testers']) >= 1
                     and len(cats['encoders']) >= 1 and len(cats['inert']) >= 1)
            print(f"\n  Approach {name}:")
            print(f"    SAT: YES")
            print(f"    Categories: abs={len(cats['absorbers'])} tst={len(cats['testers'])} "
                  f"enc={len(cats['encoders'])} inr={len(cats['inert'])}")
            print(f"    5 categories: {'YES' if has_5 else 'NO'}")
        else:
            print(f"\n  Approach {name}: UNSAT or timeout")


if __name__ == "__main__":
    main()

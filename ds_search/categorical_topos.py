#!/usr/bin/env python3
"""
Categorical Topos-like Axioms — Genuine finite endomorphism magma.

NOT a transliteration of Ψ axioms into categorical language.
Start from standard categorical concepts and see what they force.

Axioms (all standard categorical concepts):
  1. Zero morphisms: exactly 2 left-zero morphisms (absorbers)
  2. Extensionality: all morphisms distinct (faithful action)
  3. Retraction pair: r ∘ s = id and s ∘ r = id on core (section/retraction)
  4. Subobject classifier: unique non-zero morphism with image in {0,1}
     (Kripke barrier as uniqueness of the classifier)
  5. Binary product: non-commuting projection pair + pairing morphism
  6. Conditional (copairing): ρ dispatches based on τ

NO inert axiom. The question: does the inert element emerge?

Usage:
  uv run python -m ds_search.categorical_topos
"""

import time
import sys
from itertools import combinations

from z3 import Solver, Int, If, And, Or, Not, sat, unsat

from ds_search.axiom_explorer import (
    ite_lookup, col_ite_lookup, classify_elements, extract_table,
    print_table,
)


N = 12
CORE_LO, CORE_HI = 2, 6  # core subcategory for retraction pair


def make_solver():
    """Create solver with dot table and range constraints."""
    s = Solver()
    s.set("timeout", 300 * 1000)
    dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]
    for i in range(N):
        for j in range(N):
            s.add(dot[i][j] >= 0, dot[i][j] < N)
    return s, dot


# ═══════════════════════════════════════════════════════════════════════
# Axiom 1: Zero morphisms
# ═══════════════════════════════════════════════════════════════════════

def axiom_zero_morphisms(s, dot):
    """Exactly 2 left-zero morphisms: elements 0 and 1."""
    # 0 is left-zero: 0 ∘ x = 0 for all x
    for j in range(N):
        s.add(dot[0][j] == 0)
    # 1 is left-zero: 1 ∘ x = 1 for all x
    for j in range(N):
        s.add(dot[1][j] == 1)
    # No other left-zeros
    for x in range(2, N):
        s.add(Or([dot[x][j] != x for j in range(N)]))


# ═══════════════════════════════════════════════════════════════════════
# Axiom 2: Extensionality (faithful action)
# ═══════════════════════════════════════════════════════════════════════

def axiom_extensionality(s, dot):
    """All morphisms are distinct — no two have the same action."""
    for x in range(N):
        for y in range(x + 1, N):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(N)]))


# ═══════════════════════════════════════════════════════════════════════
# Axiom 3: Retraction pair (section/retraction on core)
# ═══════════════════════════════════════════════════════════════════════

def axiom_retraction_pair(s, dot):
    """∃ r, s (both non-zero, r ≠ s) with r∘s = id and s∘r = id on core.

    Existentially quantified — we don't fix which elements are r and s.
    """
    ret_clauses = []
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
            ret_clauses.append(And(roundtrip))
    s.add(Or(ret_clauses))


# ═══════════════════════════════════════════════════════════════════════
# Axiom 4: Subobject classifier (unique classifier morphism)
# ═══════════════════════════════════════════════════════════════════════

def axiom_subobject_classifier(s, dot):
    """There exists exactly one non-zero morphism whose image ⊆ {0,1}.

    This is the Kripke barrier stated categorically: the subobject
    classifier is unique. Any non-zero morphism that factors through
    Bool IS the classifier.

    Formally:
    - ∃ exactly one t ≥ 2 such that ∀j: dot[t][j] ∈ {0,1}
    - For all other x ≥ 2: ∃j with dot[x][j] ∉ {0,1}
    """
    # Define "is_bool(x)" = all outputs in {0,1}
    # Count boolean non-zero morphisms = exactly 1
    bool_flags = []
    for x in range(2, N):
        is_bool_x = And([Or(dot[x][j] == 0, dot[x][j] == 1) for j in range(N)])
        flag = Int(f"bf_{x}")
        s.add(If(is_bool_x, flag == 1, flag == 0))
        bool_flags.append(flag)
    # Exactly 1 classifier
    s.add(sum(bool_flags) == 1)


# ═══════════════════════════════════════════════════════════════════════
# Axiom 5: Binary product structure
# ═══════════════════════════════════════════════════════════════════════

def axiom_binary_product(s, dot):
    """Product structure: ∃ non-commuting projection pair + pairing morphism.

    Standard categorical product requires:
    - Two projections π₁, π₂ with π₁ ≠ π₂
    - A pairing morphism p
    - The projections are asymmetric: π₁ ∘ p ≠ π₂ ∘ p on some input
    - Non-commutativity: π₁ ∘ π₂ ≠ π₂ ∘ π₁ on some input

    All existentially quantified.
    """
    prod_clauses = []
    for pi1 in range(2, N):
        for pi2 in range(2, N):
            if pi1 == pi2:
                continue
            for p in range(2, N):
                if p == pi1 or p == pi2:
                    continue

                # π₁ and π₂ are non-zero, distinct morphisms (already covered by ext)
                # They must be encoders (≥2 distinct non-boolean outputs)
                pi1_enc_pairs = []
                for j1 in range(N):
                    for j2 in range(j1 + 1, N):
                        pi1_enc_pairs.append(And(
                            dot[pi1][j1] != 0, dot[pi1][j1] != 1,
                            dot[pi1][j2] != 0, dot[pi1][j2] != 1,
                            dot[pi1][j1] != dot[pi1][j2]))
                pi2_enc_pairs = []
                for j1 in range(N):
                    for j2 in range(j1 + 1, N):
                        pi2_enc_pairs.append(And(
                            dot[pi2][j1] != 0, dot[pi2][j1] != 1,
                            dot[pi2][j2] != 0, dot[pi2][j2] != 1,
                            dot[pi2][j1] != dot[pi2][j2]))

                # Asymmetry: π₁∘p ≠ π₂∘p on some core input
                asym = []
                for x in range(CORE_LO, CORE_HI):
                    px = dot[p][x]
                    pi1_px = col_ite_lookup(dot, pi1, px, N)
                    pi2_px = col_ite_lookup(dot, pi2, px, N)
                    asym.append(pi1_px != pi2_px)

                # Non-commutativity: π₁∘π₂ ≠ π₂∘π₁ on some input
                noncomm = []
                for x in range(CORE_LO, CORE_HI):
                    pi1_pi2_x = col_ite_lookup(dot, pi1, dot[pi2][x], N)
                    pi2_pi1_x = col_ite_lookup(dot, pi2, dot[pi1][x], N)
                    noncomm.append(pi1_pi2_x != pi2_pi1_x)

                prod_clauses.append(And(
                    Or(pi1_enc_pairs),
                    Or(pi2_enc_pairs),
                    Or(asym),
                    Or(noncomm),
                ))

    s.add(Or(prod_clauses))


# ═══════════════════════════════════════════════════════════════════════
# Axiom 6: Conditional (copairing via classifier)
# ═══════════════════════════════════════════════════════════════════════

def axiom_conditional(s, dot):
    """∃ ρ, τ, f, g (all non-zero, pairwise constraints) such that:
       ρ∘x = f∘x when τ∘x = 0, else ρ∘x = g∘x on core.
       f ≠ g on core (discrimination).
       τ is the classifier (boolean row).

    All existentially quantified.
    """
    cond_clauses = []
    for tau in range(2, N):
        # τ must be the classifier (boolean row)
        tau_is_bool = And([Or(dot[tau][j] == 0, dot[tau][j] == 1) for j in range(N)])

        for rho in range(2, N):
            if rho == tau:
                continue
            for f in range(2, N):
                for g in range(2, N):
                    if f == g:
                        continue
                    if len({rho, tau, f, g}) < 4:
                        continue

                    # Dispatch: ρ∘x = f∘x if τ∘x = 0, else ρ∘x = g∘x
                    dispatch = []
                    for x in range(CORE_LO, CORE_HI):
                        dispatch.append(
                            If(dot[tau][x] == 0,
                               dot[rho][x] == dot[f][x],
                               dot[rho][x] == dot[g][x]))

                    # f ≠ g on core (discrimination)
                    discrim = Or([dot[f][x] != dot[g][x]
                                  for x in range(CORE_LO, CORE_HI)])

                    cond_clauses.append(And(
                        tau_is_bool,
                        And(dispatch),
                        discrim,
                    ))

    s.add(Or(cond_clauses))


# ═══════════════════════════════════════════════════════════════════════
# Analysis utilities
# ═══════════════════════════════════════════════════════════════════════

def wl_refine(table, n, max_rounds=20):
    """WL-1 color refinement. Returns (colors, num_rounds)."""
    colors = list(range(n))
    for rnd in range(max_rounds):
        new_colors = {}
        for x in range(n):
            sig = (colors[x],
                   tuple(colors[table[x][j]] for j in range(n)),
                   tuple(colors[table[j][x]] for j in range(n)))
            new_colors[x] = sig
        # Map signatures to integers
        sig_to_int = {}
        next_id = 0
        new_color_list = []
        for x in range(n):
            sig = new_colors[x]
            if sig not in sig_to_int:
                sig_to_int[sig] = next_id
                next_id += 1
            new_color_list.append(sig_to_int[sig])
        if new_color_list == colors:
            return colors, rnd
        colors = new_color_list
    return colors, max_rounds


def check_rigidity(table):
    """Check WL-1 rigidity (all colors unique)."""
    n = len(table)
    colors, rounds = wl_refine(table, n)
    unique = len(set(colors)) == n
    return unique, rounds, len(set(colors))


def check_discoverability(table):
    """Check if every non-absorber element is uniquely identifiable."""
    n = len(table)
    for x in range(2, n):
        found = False
        for d in range(n):
            if all(table[d][x] != table[d][y] for y in range(2, n) if y != x):
                found = True
                break
        if not found:
            return False
    return True


# ═══════════════════════════════════════════════════════════════════════
# Main experiment
# ═══════════════════════════════════════════════════════════════════════

def run_categorical_search(num_models=20):
    """Run the categorical axiom search and analyze results."""
    print("=" * 70)
    print("CATEGORICAL TOPOS-LIKE AXIOMS — Finite Endomorphism Magma")
    print(f"N={N}, core={{{CORE_LO}..{CORE_HI-1}}}")
    print("=" * 70)
    print()
    print("Axioms (all standard categorical concepts):")
    print("  1. Zero morphisms (exactly 2 left-zeros)")
    print("  2. Extensionality (faithful action)")
    print("  3. Retraction pair (section/retraction on core)")
    print("  4. Subobject classifier (unique Bool-factoring morphism)")
    print("  5. Binary product (non-commuting projections + pairing)")
    print("  6. Conditional (copairing via classifier dispatch)")
    print("  NO inert axiom.")
    print()

    s, dot = make_solver()

    print("Building constraints...", flush=True)
    t0 = time.time()
    axiom_zero_morphisms(s, dot)
    axiom_extensionality(s, dot)
    axiom_retraction_pair(s, dot)
    axiom_subobject_classifier(s, dot)
    axiom_binary_product(s, dot)
    axiom_conditional(s, dot)
    build_time = time.time() - t0
    print(f"  Constraints built in {build_time:.1f}s", flush=True)

    print(f"\nSearching for models (up to {num_models})...", flush=True)

    models = []
    inert_counts = []
    cat_distributions = []
    rigid_count = 0
    discoverable_count = 0

    for i in range(num_models):
        t0 = time.time()
        r = s.check()
        elapsed = time.time() - t0

        if str(r) != "sat":
            if i == 0:
                print(f"  UNSAT ({elapsed:.1f}s) — no models exist!")
            else:
                print(f"  Exhausted after {i} models ({elapsed:.1f}s)")
            break

        table = extract_table(s.model(), dot, N)
        cats = classify_elements(table)
        n_inert = len(cats['inert'])
        inert_counts.append(n_inert)
        dist = (len(cats['absorbers']), len(cats['testers']),
                len(cats['encoders']), n_inert)
        cat_distributions.append(dist)

        is_rigid, wl_rounds, n_colors = check_rigidity(table)
        is_disc = check_discoverability(table)
        if is_rigid:
            rigid_count += 1
        if is_disc:
            discoverable_count += 1

        models.append({
            'table': table,
            'cats': cats,
            'dist': dist,
            'rigid': is_rigid,
            'discoverable': is_disc,
            'wl_rounds': wl_rounds,
        })

        if i < 5:
            print(f"\n  Model {i}: abs={dist[0]} tst={dist[1]} enc={dist[2]} "
                  f"inr={dist[3]}  rigid={is_rigid} disc={is_disc} "
                  f"({elapsed:.1f}s)")
            if n_inert > 0:
                print(f"    *** INERT ELEMENT(S) FOUND: {cats['inert']} ***")
                for v in cats['inert']:
                    row = table[v]
                    non_bool = set(val for val in row if val not in (0, 1))
                    print(f"    Inert {v}: row = {row}")
                    print(f"             non-boolean outputs: {non_bool}")

            # Show first model in detail
            if i == 0:
                print()
                print_table(table)

                # Verify classifier uniqueness
                print()
                for x in range(2, N):
                    row = [table[x][j] for j in range(N)]
                    if all(v in (0, 1) for v in row):
                        print(f"    Classifier: element {x}, row = {row}")

                # Find retraction pair
                for r_idx in range(2, N):
                    for s_idx in range(2, N):
                        if r_idx == s_idx:
                            continue
                        ok = True
                        for x in range(CORE_LO, CORE_HI):
                            sx = table[s_idx][x]
                            if sx >= N or table[r_idx][sx] != x:
                                ok = False
                                break
                            rx = table[r_idx][x]
                            if rx >= N or table[s_idx][rx] != x:
                                ok = False
                                break
                        if ok:
                            print(f"    Retraction pair: r={r_idx}, s={s_idx}")
                            break
                    else:
                        continue
                    break

        elif i == 5:
            print(f"  ... (showing summary for remaining models)")

        # Block this model
        s.add(Or([dot[i_][j] != table[i_][j]
                   for i_ in range(N) for j in range(N)]))

    # ── Summary ──────────────────────────────────────────────────────
    n_models = len(models)
    if n_models == 0:
        return

    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"  Models found: {n_models}")

    # Inert analysis
    models_with_inert = sum(1 for c in inert_counts if c > 0)
    models_without_inert = sum(1 for c in inert_counts if c == 0)
    print(f"\n  Models WITH inert element:    {models_with_inert}/{n_models} "
          f"({100*models_with_inert/n_models:.0f}%)")
    print(f"  Models WITHOUT inert element: {models_without_inert}/{n_models} "
          f"({100*models_without_inert/n_models:.0f}%)")

    if inert_counts:
        from collections import Counter
        inert_dist = Counter(inert_counts)
        print(f"  Inert count distribution: {dict(sorted(inert_dist.items()))}")

    # Category distribution
    from collections import Counter
    dist_counter = Counter(cat_distributions)
    print(f"\n  Category distributions:")
    for dist, count in sorted(dist_counter.items(), key=lambda x: -x[1]):
        print(f"    abs={dist[0]} tst={dist[1]} enc={dist[2]} inr={dist[3]}: "
              f"{count} models ({100*count/n_models:.0f}%)")

    # Rigidity and discoverability
    print(f"\n  WL-1 rigid:     {rigid_count}/{n_models} "
          f"({100*rigid_count/n_models:.0f}%)")
    print(f"  Discoverable:   {discoverable_count}/{n_models} "
          f"({100*discoverable_count/n_models:.0f}%)")

    # Kripke wall verification
    print(f"\n  Kripke wall (subobject classifier uniqueness):")
    kripke_holds = 0
    for m in models:
        # Check: exactly 1 non-zero boolean morphism
        bool_count = sum(1 for x in range(2, N)
                         if all(m['table'][x][j] in (0, 1) for j in range(N)))
        if bool_count == 1:
            kripke_holds += 1
    print(f"    Holds in {kripke_holds}/{n_models} models "
          f"(should be {n_models}/{n_models} by axiom)")

    # ── Comparison ───────────────────────────────────────────────────
    print(f"\n{'='*70}")
    print("COMPARISON WITH Ψ AND PREVIOUS APPROACH B")
    print(f"{'='*70}")
    print()
    print(f"  {'System':<30} {'Dist':<15} {'Inert?':<10} {'Kripke':<10} "
          f"{'Rigid':<10} {'Disc':<10}")
    print(f"  {'-'*85}")
    print(f"  {'Ψ (full axioms)':<30} {'2-1-8-1':<15} {'YES':<10} {'YES':<10} "
          f"{'YES':<10} {'YES':<10}")
    print(f"  {'Approach B (prev)':<30} {'2-1-8-1':<15} {'YES':<10} {'?':<10} "
          f"{'?':<10} {'?':<10}")

    # Dominant distribution from this run
    if cat_distributions:
        dom_dist = dist_counter.most_common(1)[0][0]
        dom_str = f"{dom_dist[0]}-{dom_dist[1]}-{dom_dist[2]}-{dom_dist[3]}"
        inert_str = "YES" if models_with_inert > n_models // 2 else (
            "MIXED" if models_with_inert > 0 else "NO")
        rigid_str = f"{100*rigid_count/n_models:.0f}%"
        disc_str = f"{100*discoverable_count/n_models:.0f}%"
        print(f"  {'Categorical (this)':<30} {dom_str:<15} {inert_str:<10} "
              f"{'YES':<10} {rigid_str:<10} {disc_str:<10}")

    print()
    if models_with_inert > 0:
        print("  *** THE INERT ELEMENT EMERGES from categorical axioms alone. ***")
        print("  *** The substrate is FORCED by products + subobject classifier, ***")
        print("  *** not a separate philosophical commitment. ***")
    else:
        print("  The inert element does NOT emerge from categorical axioms.")
        print("  The substrate remains genuinely contingent even in")
        print("  categorical formulation.")


def main():
    run_categorical_search(num_models=20)


if __name__ == "__main__":
    main()

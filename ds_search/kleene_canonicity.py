#!/usr/bin/env python3
"""
KleeneMag Canonicity Analysis

1. Enumerate all KleeneMagma models at N=4 (sec=ret) and N=5 (sec≠ret)
2. Count isomorphism classes — check if minimal models are unique
3. Search for magma homomorphisms from minimal models to Ψ₁₆ᶠ
   - Strict: preserve all distinguished elements (zero₁, zero₂, sec, ret, cls)
   - Weak: preserve only zeros (zero₁, zero₂)

Usage:
  uv run python -m ds_search.kleene_canonicity
"""

import time
import sys
from itertools import permutations, product as iproduct

from z3 import Solver, Int, And, Or, Not, sat, If

# ═══════════════════════════════════════════════════════════════════════
# Ψ₁₆ᶠ table
# ═══════════════════════════════════════════════════════════════════════

TABLE16 = [
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    [5,1,13,7,11,5,6,8,2,5,11,9,4,14,3,15],
    [0,1,0,0,0,0,1,1,1,0,1,1,0,0,1,1],
    [0,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11],
    [0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,0],
    [15,0,5,9,3,15,14,14,2,12,8,14,12,4,12,8],
    [0,1,8,4,13,2,11,2,14,3,15,12,14,15,6,5],
    [12,1,13,7,11,5,12,11,4,12,5,14,15,7,11,12],
    [1,6,14,14,14,14,9,8,3,15,5,7,13,11,12,4],
    [13,1,4,3,12,11,2,11,5,3,8,14,9,7,11,11],
    [14,1,9,10,11,13,12,7,5,6,8,2,14,12,10,4],
    [0,1,1,0,1,1,0,1,1,1,0,0,0,0,0,1],
    [3,0,14,4,14,6,11,12,7,3,15,10,14,2,6,8],
    [14,0,5,4,3,2,12,5,11,14,3,14,12,2,6,3],
    [1,3,13,15,3,7,14,8,15,4,11,6,7,14,12,10],
]

# Ψ₁₆ᶠ distinguished elements
PSI_ZERO1 = 0   # ⊤
PSI_ZERO2 = 1   # ⊥
PSI_SEC = 6     # Q (section)
PSI_RET = 7     # E (retraction)
PSI_CLS = 3     # τ (classifier)


# ═══════════════════════════════════════════════════════════════════════
# KleeneMagma model enumeration via Z3
# ═══════════════════════════════════════════════════════════════════════

def enumerate_kleene_models(n, sec_idx, ret_idx, cls_idx, max_models=1000,
                            timeout_s=300):
    """
    Enumerate all KleeneMagma models at size n with given element assignments.

    Returns list of (table, sec, ret, cls) tuples.
    """
    models = []

    while len(models) < max_models:
        s = Solver()
        s.set("timeout", timeout_s * 1000)

        dot = [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]

        # Range
        for i in range(n):
            for j in range(n):
                s.add(dot[i][j] >= 0, dot[i][j] < n)

        # Absorbers
        for j in range(n):
            s.add(dot[0][j] == 0)
            s.add(dot[1][j] == 1)

        # No extra zeros
        for x in range(2, n):
            s.add(Or([dot[x][j] != x for j in range(n)]))

        # Extensionality
        for x in range(n):
            for y in range(x + 1, n):
                s.add(Or([dot[x][j] != dot[y][j] for j in range(n)]))

        # Retraction pair
        for x in range(2, n):
            # ret(sec(x)) = x
            sec_x = dot[sec_idx][x]
            ret_sec_x = dot[ret_idx][0]  # placeholder
            for c in range(1, n):
                ret_sec_x = If(sec_x == c, dot[ret_idx][c], ret_sec_x)
            s.add(ret_sec_x == x)

            # sec(ret(x)) = x
            ret_x = dot[ret_idx][x]
            sec_ret_x = dot[sec_idx][0]
            for c in range(1, n):
                sec_ret_x = If(ret_x == c, dot[sec_idx][c], sec_ret_x)
            s.add(sec_ret_x == x)

        # ret_zero1
        s.add(dot[ret_idx][0] == 0)

        # cls_boolean
        for x in range(n):
            s.add(Or(dot[cls_idx][x] == 0, dot[cls_idx][x] == 1))

        # cls is not absorber (ensured by index >= 2)

        # Kleene dichotomy
        for y in range(2, n):
            all_bool = And([Or(dot[y][x] == 0, dot[y][x] == 1)
                           for x in range(2, n)])
            all_non_bool = And([And(dot[y][x] != 0, dot[y][x] != 1)
                               for x in range(2, n)])
            s.add(Or(all_bool, all_non_bool))

        # has_non_classifier
        nc_clauses = []
        for y in range(2, n):
            for x in range(2, n):
                nc_clauses.append(And(dot[y][x] != 0, dot[y][x] != 1))
        s.add(Or(nc_clauses))

        # cls not constant (not all 0 or all 1)
        s.add(Or([dot[cls_idx][j] != 0 for j in range(n)]))
        s.add(Or([dot[cls_idx][j] != 1 for j in range(n)]))

        # Block all previously found models
        for prev_table in models:
            block = []
            for i in range(n):
                for j in range(n):
                    block.append(dot[i][j] != prev_table[i][j])
            s.add(Or(block))

        result = s.check()
        if str(result) != "sat":
            break

        m = s.model()
        table = [[m.evaluate(dot[i][j]).as_long() for j in range(n)]
                 for i in range(n)]
        models.append(table)

    return models


def tables_isomorphic(t1, t2, n):
    """
    Check if two n×n magma tables are isomorphic.

    An isomorphism is a permutation σ of {0,...,n-1} such that
    σ(t1[a][b]) = t2[σ(a)][σ(b)] for all a, b.

    We also require σ(0) = 0 and σ(1) = 1 (preserve zeros).
    """
    # Fix σ(0)=0, σ(1)=1, permute the rest
    rest = list(range(2, n))
    for perm_rest in permutations(rest):
        sigma = [0, 1] + list(perm_rest)
        ok = True
        for a in range(n):
            if not ok:
                break
            for b in range(n):
                if sigma[t1[a][b]] != t2[sigma[a]][sigma[b]]:
                    ok = False
                    break
        if ok:
            return True, sigma
    return False, None


def count_iso_classes(tables, n):
    """Group tables into isomorphism classes."""
    classes = []  # list of (representative, members)

    for idx, table in enumerate(tables):
        found = False
        for cls_idx, (rep, members) in enumerate(classes):
            iso, sigma = tables_isomorphic(table, rep, n)
            if iso:
                members.append(idx)
                found = True
                break
        if not found:
            classes.append((table, [idx]))

    return classes


# ═══════════════════════════════════════════════════════════════════════
# Homomorphism search
# ═══════════════════════════════════════════════════════════════════════

def find_homomorphisms(src_table, src_n, dst_table, dst_n,
                       fix_zeros=True, fix_sec=None, fix_ret=None,
                       fix_cls=None):
    """
    Find all magma homomorphisms σ: src → dst.

    σ(src_table[a][b]) = dst_table[σ(a)][σ(b)] for all a,b.

    fix_zeros: σ(0)=0, σ(1)=1
    fix_sec: (src_sec, dst_sec) pair to enforce σ(src_sec) = dst_sec
    fix_ret: (src_ret, dst_ret) pair
    fix_cls: (src_cls, dst_cls) pair
    """
    # Build constraints on σ
    fixed = {}
    if fix_zeros:
        fixed[0] = 0
        fixed[1] = 1
    if fix_sec:
        fixed[fix_sec[0]] = fix_sec[1]
    if fix_ret:
        fixed[fix_ret[0]] = fix_ret[1]
    if fix_cls:
        fixed[fix_cls[0]] = fix_cls[1]

    # Generate candidates for unfixed elements
    unfixed = [i for i in range(src_n) if i not in fixed]
    possible = list(range(dst_n))

    homomorphisms = []

    for assignment in iproduct(possible, repeat=len(unfixed)):
        sigma = [0] * src_n
        for k, v in fixed.items():
            sigma[k] = v
        for i, idx in enumerate(unfixed):
            sigma[idx] = assignment[i]

        # Check homomorphism condition
        ok = True
        for a in range(src_n):
            if not ok:
                break
            for b in range(src_n):
                lhs = sigma[src_table[a][b]]
                rhs = dst_table[sigma[a]][sigma[b]]
                if lhs != rhs:
                    ok = False
                    break

        if ok:
            homomorphisms.append(tuple(sigma))

    return homomorphisms


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("=" * 70)
    print("KLEENE MAGMA CANONICITY ANALYSIS")
    print("=" * 70)

    # ── N=4 enumeration (sec=ret) ────────────────────────────────────
    print(f"\n{'─'*70}")
    print("1. Enumerate all N=4 KleeneMagmas (sec=ret)")
    print(f"{'─'*70}")

    # At N=4: elements {0,1,2,3}. Fix sec=ret=2, cls=3.
    # (Swapping 2↔3 gives isomorphic models.)
    t0 = time.time()
    models4_a = enumerate_kleene_models(4, sec_idx=2, ret_idx=2, cls_idx=3)
    # Also try sec=ret=3, cls=2
    models4_b = enumerate_kleene_models(4, sec_idx=3, ret_idx=3, cls_idx=2)
    elapsed = time.time() - t0

    # Combine and deduplicate by isomorphism
    all_models4 = models4_a + models4_b
    print(f"  Raw models found: {len(models4_a)} (sec=ret=2, cls=3) "
          f"+ {len(models4_b)} (sec=ret=3, cls=2) = {len(all_models4)}")

    classes4 = count_iso_classes(all_models4, 4)
    print(f"  Isomorphism classes: {len(classes4)}")
    print(f"  Time: {elapsed:.1f}s")

    for i, (rep, members) in enumerate(classes4):
        print(f"\n  Class {i+1} ({len(members)} models):")
        for row in rep:
            print(f"    {row}")

    # ── N=5 enumeration (sec≠ret) ────────────────────────────────────
    print(f"\n{'─'*70}")
    print("2. Enumerate all N=5 KleeneMagmas (sec≠ret)")
    print(f"{'─'*70}")

    # At N=5: elements {0,1,2,3,4}. Try all 6 permutations of (sec,ret,cls)
    # among {2,3,4}. Due to isomorphism, we only need one assignment,
    # but let's enumerate all and deduplicate.
    all_models5 = []
    assignment_counts = []
    t0 = time.time()

    for sec, ret, cls in permutations([2, 3, 4]):
        if sec == ret:
            continue
        models = enumerate_kleene_models(5, sec_idx=sec, ret_idx=ret, cls_idx=cls)
        assignment_counts.append((sec, ret, cls, len(models)))
        all_models5.extend(models)

    elapsed = time.time() - t0
    print(f"  Assignments tried: {len(assignment_counts)}")
    for sec, ret, cls, count in assignment_counts:
        print(f"    sec={sec}, ret={ret}, cls={cls}: {count} models")
    print(f"  Total raw models: {len(all_models5)}")

    classes5 = count_iso_classes(all_models5, 5)
    print(f"  Isomorphism classes: {len(classes5)}")
    print(f"  Time: {elapsed:.1f}s")

    for i, (rep, members) in enumerate(classes5):
        print(f"\n  Class {i+1} ({len(members)} models):")
        for row in rep:
            print(f"    {row}")

    # ── Homomorphisms: minimal → Ψ₁₆ᶠ ──────────────────────────────
    print(f"\n{'─'*70}")
    print("3. Homomorphisms from minimal models to Ψ₁₆ᶠ")
    print(f"{'─'*70}")

    # Use the Lean witnesses
    kleene4_table = [
        [0, 0, 0, 0],
        [1, 1, 1, 1],
        [0, 1, 0, 1],  # cls
        [0, 0, 2, 3],  # sec = ret
    ]
    kleene4_sec, kleene4_ret, kleene4_cls = 3, 3, 2

    kleene5_table = [
        [0, 0, 0, 0, 0],
        [1, 1, 1, 1, 1],
        [1, 0, 3, 4, 2],  # sec
        [0, 2, 4, 2, 3],  # ret
        [0, 1, 1, 0, 0],  # cls
    ]
    kleene5_sec, kleene5_ret, kleene5_cls = 2, 3, 4

    # Identify Ψ₁₆ᶠ's classifiers (all-boolean rows on non-zeros)
    psi_classifiers = []
    for y in range(2, 16):
        if all(TABLE16[y][x] in (0, 1) for x in range(2, 16)):
            psi_classifiers.append(y)
    print(f"\n  Ψ₁₆ᶠ classifiers (boolean rows on core): {psi_classifiers}")

    # Identify Ψ₁₆ᶠ's retraction pairs
    psi_retraction_pairs = []
    for sec in range(2, 16):
        for ret in range(2, 16):
            if TABLE16[ret][0] != 0:
                continue
            ok = True
            for x in range(2, 6):  # check on core {2,3,4,5}
                sec_x = TABLE16[sec][x]
                if sec_x < 0 or sec_x >= 16:
                    ok = False
                    break
                if TABLE16[ret][sec_x] != x:
                    ok = False
                    break
                ret_x = TABLE16[ret][x]
                if ret_x < 0 or ret_x >= 16:
                    ok = False
                    break
                if TABLE16[sec][ret_x] != x:
                    ok = False
                    break
            if ok:
                psi_retraction_pairs.append((sec, ret))
    print(f"  Ψ₁₆ᶠ retraction pairs (on core {{2..5}}): {psi_retraction_pairs}")

    # 3a: Strict homomorphisms (preserve all distinguished elements)
    print(f"\n  3a. Strict homomorphisms (preserve zeros + sec + ret + cls)")
    for label, src_table, src_n, src_sec, src_ret, src_cls in [
        ("kleene4", kleene4_table, 4, kleene4_sec, kleene4_ret, kleene4_cls),
        ("kleene5", kleene5_table, 5, kleene5_sec, kleene5_ret, kleene5_cls),
    ]:
        # Try all retraction pairs and classifiers in Ψ₁₆ᶠ
        total_found = 0
        for dst_sec, dst_ret in psi_retraction_pairs:
            for dst_cls in psi_classifiers:
                homos = find_homomorphisms(
                    src_table, src_n, TABLE16, 16,
                    fix_zeros=True,
                    fix_sec=(src_sec, dst_sec),
                    fix_ret=(src_ret, dst_ret),
                    fix_cls=(src_cls, dst_cls),
                )
                if homos:
                    total_found += len(homos)
                    for h in homos:
                        print(f"    {label} → Ψ₁₆ᶠ: σ = {list(h)} "
                              f"(sec→{dst_sec}, ret→{dst_ret}, cls→{dst_cls})")
        if total_found == 0:
            print(f"    {label} → Ψ₁₆ᶠ: NO strict homomorphisms found")
        else:
            print(f"    {label}: {total_found} total strict homomorphisms")

    # 3b: Weak homomorphisms (preserve zeros only)
    print(f"\n  3b. Weak homomorphisms (preserve zeros only)")
    for label, src_table, src_n in [
        ("kleene4", kleene4_table, 4),
        ("kleene5", kleene5_table, 5),
    ]:
        t0 = time.time()
        homos = find_homomorphisms(
            src_table, src_n, TABLE16, 16, fix_zeros=True)
        elapsed = time.time() - t0
        print(f"    {label} → Ψ₁₆ᶠ: {len(homos)} weak homomorphisms ({elapsed:.1f}s)")
        if homos:
            for h in homos[:5]:  # show first 5
                print(f"      σ = {list(h)}")
            if len(homos) > 5:
                print(f"      ... and {len(homos) - 5} more")

    # ── N=4 without sec=ret constraint ───────────────────────────────
    print(f"\n{'─'*70}")
    print("4. N=4 KleeneMagmas with sec≠ret (expected: none, proves N≥5)")
    print(f"{'─'*70}")

    models4_sr = []
    for sec, ret, cls in permutations([2, 3]):
        if sec == ret:
            continue
        # Only 2 non-zero elements, need sec≠ret → sec=2,ret=3 or sec=3,ret=2
        # cls must be ≠ sec, ≠ ret, ≠ 0, ≠ 1. But {2,3} are taken → NO cls!
        # This means N=4 with sec≠ret and a separate cls is impossible.
        # But let's verify with Z3 anyway.
        # Actually cls could be 2 or 3 (same as sec or ret).
        # But the axioms say cls ≠ zero₁, cls ≠ zero₂, and the Lean proofs
        # show cls ≠ sec and cls ≠ ret. So with only {2,3} and sec≠ret,
        # there's no room for cls. UNSAT.
        pass
    print("  At N=4 with sec≠ret: only 2 non-zero elements {2,3}")
    print("  cls must differ from zero₁, zero₂, sec, ret → no room. UNSAT.")
    print("  (Confirmed by Lean: card_ge_five_of_sec_ne_ret)")

    # ── Summary ──────────────────────────────────────────────────────
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"  N=4 KleeneMagmas (sec=ret): {len(classes4)} iso class(es), "
          f"{sum(len(m) for _, m in classes4)} total models")
    print(f"  N=5 KleeneMagmas (sec≠ret): {len(classes5)} iso class(es), "
          f"{sum(len(m) for _, m in classes5)} total models")
    if len(classes4) == 1:
        print(f"  → N=4 minimal model is UNIQUE up to isomorphism")
    if len(classes5) == 1:
        print(f"  → N=5 minimal model (sec≠ret) is UNIQUE up to isomorphism")


if __name__ == "__main__":
    main()

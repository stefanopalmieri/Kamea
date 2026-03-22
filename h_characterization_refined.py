#!/usr/bin/env python3
"""
Refined H-characterization validation: fix the b≠c degeneracy in ICP.

The original ICP allowed b=c (same element composing with itself), which
catches the trivial Q²=E case from the retraction pair. The refined ICP
requires all three elements to be pairwise distinct.
"""

from z3 import *
import random
import sys

N = 10
CORE = list(range(2, N))
ABS_SET = {0, 1}


def ite_lookup(dot, row, col_expr, n):
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def build_frm_solver(n=10):
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

    for x in range(2, n):
        qx = dot[2][x]
        s.add(ite_lookup(dot, 3, qx, n) == x)
        ex = dot[3][x]
        s.add(ite_lookup(dot, 2, ex, n) == x)

    s.add(dot[3][0] == 0)
    s.add(dot[3][1] == 1)

    return s, dot


def add_H_axioms(s, dot, n=10, g=6, rho=7, eta=8):
    core = list(range(2, n))
    for x in core:
        s.add(dot[g][x] != 0)
        s.add(dot[g][x] != 1)
    for x in core:
        gx = dot[g][x]
        s.add(dot[eta][x] == ite_lookup(dot, rho, gx, n))


def add_no_compose(s, dot, n=10, g=6, rho=7):
    core = list(range(2, n))
    for eta in range(n):
        s.add(Or([dot[eta][x] != ite_lookup(dot, rho, dot[g][x], n) for x in core]))


def extract_table(model, dot, n):
    return [[model.evaluate(dot[i][j]).as_long() for j in range(n)] for i in range(n)]


def has_current_H(table, n=10):
    """Compose + Inert with ANY element assignments (g,ρ,η pairwise distinct, non-absorber)."""
    core = list(range(2, n))
    for g in core:
        if not all(table[g][x] not in {0, 1} for x in core):
            continue
        for rho in core:
            if rho == g:
                continue
            comp = tuple(table[rho][table[g][x]] for x in core)
            for eta in range(n):
                if eta in {0, 1} or eta == g or eta == rho:
                    continue
                if tuple(table[eta][x] for x in core) == comp:
                    return True, (g, rho, eta)
    return False, None


def has_ICP_refined(table, n=10):
    """
    REFINED Internal Composition Property:
    ∃ a, b, c ∈ S, PAIRWISE DISTINCT, all ∉ {0,1}, such that:
    - b·x ∉ {0,1} for all x in core (b preserves core)
    - a·x = c·(b·x) for all x in core (a = c ∘ b on core)

    Key fix: requires b ≠ c (eliminates Q²=E degeneracy).
    """
    core = list(range(2, n))
    for b in core:
        if not all(table[b][x] not in {0, 1} for x in core):
            continue
        for c in range(n):
            if c in {0, 1} or c == b:  # c ≠ b (the key fix)
                continue
            comp = tuple(table[c][table[b][x]] for x in core)
            for a in range(n):
                if a in {0, 1} or a == b or a == c:
                    continue
                if tuple(table[a][x] for x in core) == comp:
                    return True, (a, b, c)
    return False, None


def has_ICP_original(table, n=10):
    """Original ICP (allows b=c)."""
    core = list(range(2, n))
    for b in core:
        if not all(table[b][x] not in {0, 1} for x in core):
            continue
        for c in range(n):
            comp = tuple(table[c][table[b][x]] for x in core)
            for a in range(n):
                if a in {0, 1} or a == b or a == c:
                    continue
                if tuple(table[a][x] for x in core) == comp:
                    return True, (a, b, c)
    return False, None


def sample_models(constraint_fn, n_models=50, label="", seed=42):
    random.seed(seed)
    models = []
    for trial in range(n_models * 20):
        if len(models) >= n_models:
            break
        s, dot = build_frm_solver()
        constraint_fn(s, dot)
        s.push()
        for _ in range(2):
            i = random.randint(2, N - 1)
            j = random.randint(0, N - 1)
            v = random.randint(0, N - 1)
            s.add(dot[i][j] == v)
        if s.check() == sat:
            table = extract_table(s.model(), dot, N)
            key = tuple(tuple(row) for row in table)
            if key not in {tuple(tuple(r) for r in m) for m in models}:
                models.append(table)
        s.pop()
    print(f"  [{label}] Generated {len(models)}/{n_models} models", file=sys.stderr)
    return models


# ═══════════════════════════════════════════════════════════════════
# Also test the Lean counterexamples directly
# ═══════════════════════════════════════════════════════════════════

D_NOT_H = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [3, 3, 2, 3, 4, 5, 6, 7, 9, 8],
    [0, 1, 2, 3, 4, 5, 6, 7, 9, 8],
    [0, 0, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [2, 3, 9, 9, 9, 9, 9, 9, 9, 8],
    [3, 2, 9, 9, 9, 9, 9, 9, 9, 8],
    [1, 0, 1, 0, 1, 1, 1, 1, 0, 0],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
]

H_NOT_D = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [3, 1, 3, 4, 9, 6, 8, 5, 7, 2],
    [0, 1, 9, 2, 3, 7, 5, 8, 6, 4],
    [0, 0, 1, 1, 1, 1, 1, 1, 0, 0],
    [0, 0, 2, 0, 0, 0, 0, 0, 3, 1],
    [2, 2, 2, 8, 3, 9, 4, 7, 9, 7],
    [8, 3, 2, 8, 3, 9, 4, 7, 3, 1],
    [9, 2, 2, 3, 8, 1, 3, 7, 1, 7],
    [2, 2, 2, 2, 4, 7, 6, 7, 2, 0],
]

SDH = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [3, 3, 4, 3, 7, 5, 9, 6, 8, 2],
    [0, 1, 9, 3, 2, 5, 7, 4, 8, 6],
    [0, 0, 1, 1, 1, 0, 0, 0, 1, 1],
    [2, 2, 7, 2, 8, 9, 4, 3, 4, 2],
    [0, 0, 6, 4, 8, 7, 3, 3, 4, 9],
    [2, 2, 6, 4, 8, 9, 4, 3, 4, 9],
    [2, 2, 4, 8, 4, 3, 4, 4, 8, 9],
    [3, 4, 7, 3, 9, 2, 2, 9, 2, 3],
]


def main():
    print("=" * 60)
    print("LEAN COUNTEREXAMPLE VALIDATION (refined ICP)")
    print("=" * 60)

    for table, name in [(D_NOT_H, "D⊬H"), (H_NOT_D, "H⊬D"), (SDH, "S+D+H")]:
        h, hw = has_current_H(table)
        icp_r, icp_rw = has_ICP_refined(table)
        icp_o, icp_ow = has_ICP_original(table)
        print(f"\n  {name}:")
        print(f"    H (Compose+Inert): {h} {hw or ''}")
        print(f"    ICP (original):    {icp_o} {icp_ow or ''}")
        print(f"    ICP (refined):     {icp_r} {icp_rw or ''}")

    print("\n" + "=" * 60)
    print("TARGETED SAT VALIDATION (refined ICP)")
    print("=" * 60)

    # Generate models
    print("\nGenerating models WITH H axioms...")
    h_models = sample_models(lambda s, d: add_H_axioms(s, d), 50, "WITH H", seed=42)

    print("Generating models WITHOUT Compose (g=6,ρ=7)...")
    no_compose = sample_models(lambda s, d: add_no_compose(s, d), 50, "NO Compose", seed=123)

    print("Generating plain FRM models (no extra constraints)...")
    plain = sample_models(lambda s, d: None, 100, "Plain FRM", seed=789)

    groups = [("WITH H", h_models), ("NO Compose", no_compose), ("Plain FRM", plain)]

    for group_name, models in groups:
        if not models:
            print(f"\n  [{group_name}] No models")
            continue

        n = len(models)
        h_cnt = icp_r_cnt = icp_o_cnt = 0
        h_not_icp_r = icp_r_not_h = 0
        h_not_icp_o = icp_o_not_h = 0

        for table in models:
            h, _ = has_current_H(table)
            ir, _ = has_ICP_refined(table)
            io, _ = has_ICP_original(table)

            if h: h_cnt += 1
            if ir: icp_r_cnt += 1
            if io: icp_o_cnt += 1
            if h and not ir: h_not_icp_r += 1
            if ir and not h: icp_r_not_h += 1
            if h and not io: h_not_icp_o += 1
            if io and not h: icp_o_not_h += 1

        print(f"\n  [{group_name}] ({n} models)")
        print(f"    H (Compose+Inert):  {h_cnt}/{n}")
        print(f"    ICP (original):     {icp_o_cnt}/{n}")
        print(f"    ICP (refined, b≠c): {icp_r_cnt}/{n}")
        print(f"    H ∧ ¬ICP_refined:   {h_not_icp_r}")
        print(f"    ICP_refined ∧ ¬H:   {icp_r_not_h}")

        if icp_r_not_h > 0:
            print(f"    *** ICP STILL WEAKER: {icp_r_not_h} models satisfy refined ICP but not H ***")
            shown = 0
            for idx, table in enumerate(models):
                h_r, h_w = has_current_H(table)
                i_r, i_w = has_ICP_refined(table)
                if i_r and not h_r:
                    shown += 1
                    print(f"\n    Discrepancy {shown} (model {idx}):")
                    print(f"      H witness: {h_w}")
                    print(f"      ICP witness: {i_w}")
                    # Check what the ICP composition looks like
                    a, b, c = i_w
                    print(f"      a={a} row on core: {[table[a][x] for x in CORE]}")
                    print(f"      c∘b on core: {[table[c][table[b][x]] for x in CORE]}")
                    print(f"      b={b} on core: {[table[b][x] for x in CORE]}")
                    print(f"      c={c} on core: {[table[c][x] for x in CORE]}")
                    # Is b=Q or c=E?
                    is_b_Q = (b == 2)
                    is_c_E = (c == 3)
                    print(f"      b is Q: {is_b_Q}, c is E: {is_c_E}")
                    if shown >= 3:
                        break

    # Final summary
    print("\n" + "=" * 60)
    print("EQUIVALENCE ANALYSIS")
    print("=" * 60)

    total = 0
    total_agree = 0
    total_h = 0
    total_icp_r = 0
    for _, models in groups:
        for table in models:
            total += 1
            h, _ = has_current_H(table)
            ir, _ = has_ICP_refined(table)
            if h == ir: total_agree += 1
            if h: total_h += 1
            if ir: total_icp_r += 1

    print(f"  Total models: {total}")
    print(f"  H: {total_h}, ICP_refined: {total_icp_r}")
    print(f"  Agreement: {total_agree}/{total} ({total_agree/total:.1%})")

    if total_agree == total:
        print("\n  H ↔ ICP_refined: PERFECT EQUIVALENCE")
    else:
        gap = total - total_agree
        print(f"\n  {gap} discrepancies remain. ICP_refined is not equivalent to H.")
        print("  Analyzing the gap...")

        # Check if ICP is strictly weaker (ICP ⊃ H)
        icp_implies_h = True
        h_implies_icp = True
        for _, models in groups:
            for table in models:
                h, _ = has_current_H(table)
                ir, _ = has_ICP_refined(table)
                if ir and not h:
                    icp_implies_h = False
                if h and not ir:
                    h_implies_icp = False

        if h_implies_icp and not icp_implies_h:
            print("  H ⇒ ICP_refined: YES")
            print("  ICP_refined ⇒ H: NO")
            print("  ICP_refined is STRICTLY WEAKER than H.")
        elif icp_implies_h and not h_implies_icp:
            print("  ICP_refined is STRICTLY STRONGER than H.")
        else:
            print("  H and ICP_refined are INCOMPARABLE.")


if __name__ == "__main__":
    main()

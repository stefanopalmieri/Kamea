#!/usr/bin/env python3
"""
Final H-characterization investigation.

Two degeneracies found:
1. b=c (Q²=E): fixed by requiring pairwise distinct
2. Trivial collapse (composite maps core to single absorber): need non-triviality

The refined ICP requires:
- All three elements pairwise distinct and non-absorber
- b maps core away from absorbers (core-preserving)
- a = c ∘ b on core (composition)
- The composite (a's core row) has ≥ 2 distinct values (non-trivial)

We also test even stricter conditions to find the right boundary.
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
        s.add(dot[g][x] != 0, dot[g][x] != 1)
    for x in core:
        s.add(dot[eta][x] == ite_lookup(dot, rho, dot[g][x], n))
    # Add non-triviality: η must have ≥2 distinct values on core
    # (ensures composition is not collapsing)
    s.add(Or([dot[eta][x] != dot[eta][y] for x in core for y in core if x < y]))


def add_no_compose(s, dot, n=10, g=6, rho=7):
    core = list(range(2, n))
    for eta in range(n):
        s.add(Or([dot[eta][x] != ite_lookup(dot, rho, dot[g][x], n) for x in core]))


def add_kripke(s, dot, n=10, tau=4):
    """Add Kripke dichotomy."""
    core = list(range(2, n))
    s.add(And([Or(dot[tau][x] == 0, dot[tau][x] == 1) for x in range(n)]))
    s.add(dot[tau][0] != dot[tau][1])  # τ distinguishes absorbers

    for y in range(2, n):
        all_bool = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
        all_non_bool = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
        s.add(Or(all_bool, all_non_bool))


def extract_table(model, dot, n):
    return [[model.evaluate(dot[i][j]).as_long() for j in range(n)] for i in range(n)]


# ═══════════════════════════════════════════════════════════════════
# Property testers
# ═══════════════════════════════════════════════════════════════════

def has_H_nontrivial(table, n=10):
    """
    H with non-triviality: ∃ g,ρ,η pairwise distinct, non-absorber:
    - g maps core away from absorbers
    - η·x = ρ·(g·x) on core
    - η has ≥ 2 distinct values on core (non-collapsing)
    """
    core = list(range(2, n))
    for g in core:
        if not all(table[g][x] not in {0, 1} for x in core):
            continue
        for rho in core:
            if rho == g:
                continue
            comp = tuple(table[rho][table[g][x]] for x in core)
            if len(set(comp)) < 2:
                continue  # trivial (constant) composition
            for eta in range(n):
                if eta in {0, 1} or eta == g or eta == rho:
                    continue
                if tuple(table[eta][x] for x in core) == comp:
                    return True, (g, rho, eta)
    return False, None


def has_ICP_v1(table, n=10):
    """
    ICP v1: ∃ a,b,c pairwise distinct, non-absorber:
    - b maps core to core
    - a = c∘b on core
    - a has ≥2 distinct values on core (non-trivial)
    """
    core = list(range(2, n))
    for b in core:
        if not all(table[b][x] not in {0, 1} for x in core):
            continue
        for c in range(n):
            if c in {0, 1} or c == b:
                continue
            comp = tuple(table[c][table[b][x]] for x in core)
            if len(set(comp)) < 2:
                continue
            for a in range(n):
                if a in {0, 1} or a == b or a == c:
                    continue
                if tuple(table[a][x] for x in core) == comp:
                    return True, (a, b, c)
    return False, None


def has_ICP_v2(table, n=10):
    """
    ICP v2: ICP v1 + c must have ≥2 distinct non-absorber values on core
    (c is a "genuine transformer", not a classifier)
    """
    core = list(range(2, n))
    for b in core:
        if not all(table[b][x] not in {0, 1} for x in core):
            continue
        for c in core:
            if c == b:
                continue
            c_core = [table[c][x] for x in core]
            non_abs_vals = [v for v in c_core if v not in {0, 1}]
            if len(set(non_abs_vals)) < 2:
                continue
            comp = tuple(table[c][table[b][x]] for x in core)
            if len(set(comp)) < 2:
                continue
            for a in range(n):
                if a in {0, 1} or a == b or a == c:
                    continue
                if tuple(table[a][x] for x in core) == comp:
                    return True, (a, b, c)
    return False, None


def has_ICP_v3(table, n=10):
    """
    ICP v3: ICP v1 + a maps core away from absorbers
    (the composite is a genuine core transformation)
    """
    core = list(range(2, n))
    for b in core:
        if not all(table[b][x] not in {0, 1} for x in core):
            continue
        for c in range(n):
            if c in {0, 1} or c == b:
                continue
            comp = tuple(table[c][table[b][x]] for x in core)
            # a must map core away from absorbers
            if not all(v not in {0, 1} for v in comp):
                continue
            if len(set(comp)) < 2:
                continue
            for a in range(n):
                if a in {0, 1} or a == b or a == c:
                    continue
                if tuple(table[a][x] for x in core) == comp:
                    return True, (a, b, c)
    return False, None


# ═══════════════════════════════════════════════════════════════════
# Lean counterexamples
# ═══════════════════════════════════════════════════════════════════

D_NOT_H = [
    [0,0,0,0,0,0,0,0,0,0],[1,1,1,1,1,1,1,1,1,1],
    [3,3,2,3,4,5,6,7,9,8],[0,1,2,3,4,5,6,7,9,8],
    [0,0,1,1,1,1,1,1,1,1],[1,0,0,0,0,0,0,0,0,0],
    [2,3,9,9,9,9,9,9,9,8],[3,2,9,9,9,9,9,9,9,8],
    [1,0,1,0,1,1,1,1,0,0],[0,1,0,1,0,1,1,0,1,1],
]

H_NOT_D = [
    [0,0,0,0,0,0,0,0,0,0],[1,1,1,1,1,1,1,1,1,1],
    [3,1,3,4,9,6,8,5,7,2],[0,1,9,2,3,7,5,8,6,4],
    [0,0,1,1,1,1,1,1,0,0],[0,0,2,0,0,0,0,0,3,1],
    [2,2,2,8,3,9,4,7,9,7],[8,3,2,8,3,9,4,7,3,1],
    [9,2,2,3,8,1,3,7,1,7],[2,2,2,2,4,7,6,7,2,0],
]

SDH = [
    [0,0,0,0,0,0,0,0,0,0],[1,1,1,1,1,1,1,1,1,1],
    [3,3,4,3,7,5,9,6,8,2],[0,1,9,3,2,5,7,4,8,6],
    [0,0,1,1,1,0,0,0,1,1],[2,2,7,2,8,9,4,3,4,2],
    [0,0,6,4,8,7,3,3,4,9],[2,2,6,4,8,9,4,3,4,9],
    [2,2,4,8,4,3,4,4,8,9],[3,4,7,3,9,2,2,9,2,3],
]


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
            i = random.randint(2, N-1)
            j = random.randint(0, N-1)
            v = random.randint(0, N-1)
            s.add(dot[i][j] == v)
        if s.check() == sat:
            table = extract_table(s.model(), dot, N)
            key = tuple(tuple(row) for row in table)
            if key not in {tuple(tuple(r) for r in m) for m in models}:
                models.append(table)
        s.pop()
    print(f"  [{label}] Generated {len(models)}/{n_models}", file=sys.stderr)
    return models


def main():
    print("=" * 72)
    print("LEAN COUNTEREXAMPLE VALIDATION")
    print("=" * 72)

    props = [
        ("H_nontrivial", has_H_nontrivial),
        ("ICP_v1 (≥2 vals)", has_ICP_v1),
        ("ICP_v2 (+c active)", has_ICP_v2),
        ("ICP_v3 (+a→core)", has_ICP_v3),
    ]

    for table, name in [(D_NOT_H, "D⊬H"), (H_NOT_D, "H⊬D"), (SDH, "S+D+H")]:
        print(f"\n  {name}:")
        for pname, pfn in props:
            result, witness = pfn(table)
            print(f"    {pname:<25}: {result}  {witness or ''}")

    # Check: which property correctly gives D⊬H=False, H⊬D=True, SDH=True?
    print("\n  Target: D⊬H=False, H⊬D=True, SDH=True")
    for pname, pfn in props:
        d = pfn(D_NOT_H)[0]
        h = pfn(H_NOT_D)[0]
        s = pfn(SDH)[0]
        ok = (not d) and h and s
        print(f"    {pname:<25}: D⊬H={d}, H⊬D={h}, SDH={s}  {'✓ CORRECT' if ok else '✗ WRONG'}")

    print("\n" + "=" * 72)
    print("SAT VALIDATION ACROSS DIVERSE MODELS")
    print("=" * 72)

    # Generate groups
    print("\nGenerating models...")
    h_models = sample_models(lambda s, d: add_H_axioms(s, d), 50, "WITH H", seed=42)
    no_compose = sample_models(lambda s, d: add_no_compose(s, d), 50, "NO Compose", seed=123)
    kripke_no_h = sample_models(
        lambda s, d: (add_kripke(s, d), add_no_compose(s, d)),
        50, "Kripke+NoCompose", seed=456
    )
    plain = sample_models(lambda s, d: None, 100, "Plain FRM", seed=789)

    all_models = []
    for name, models in [("WITH_H", h_models), ("NO_Compose", no_compose),
                          ("Kripke_noH", kripke_no_h), ("Plain", plain)]:
        for m in models:
            all_models.append((name, m))

    print(f"\nTotal models: {len(all_models)}")

    # Test each property
    for pname, pfn in props:
        h_cnt = 0
        p_cnt = 0
        agree = 0
        h_not_p = 0
        p_not_h = 0

        for group, table in all_models:
            h_r, _ = has_H_nontrivial(table)
            p_r, _ = pfn(table)
            if h_r: h_cnt += 1
            if p_r: p_cnt += 1
            if h_r == p_r: agree += 1
            if h_r and not p_r: h_not_p += 1
            if p_r and not h_r: p_not_h += 1

        total = len(all_models)
        print(f"\n  {pname}:")
        print(f"    H_nontrivial: {h_cnt}/{total}")
        print(f"    {pname}: {p_cnt}/{total}")
        print(f"    Agreement: {agree}/{total} ({agree/total:.1%})")
        print(f"    H ∧ ¬P: {h_not_p}")
        print(f"    P ∧ ¬H: {p_not_h}")
        if agree == total:
            print(f"    ★ PERFECT EQUIVALENCE ★")

    # Detailed analysis of the best candidate
    print("\n" + "=" * 72)
    print("DETAILED DISCREPANCY ANALYSIS FOR ICP_v1")
    print("=" * 72)

    for group, table in all_models:
        h_r, h_w = has_H_nontrivial(table)
        p_r, p_w = has_ICP_v1(table)
        if h_r != p_r:
            print(f"\n  Group={group}: H={h_r}({h_w}), ICP_v1={p_r}({p_w})")
            if p_r and not h_r:
                a, b, c = p_w
                print(f"    ICP but not H:")
                print(f"    a={a}: {[table[a][x] for x in CORE]}")
                print(f"    b={b}: {[table[b][x] for x in CORE]}")
                print(f"    c={c}: {[table[c][x] for x in CORE]}")
                print(f"    c∘b: {[table[c][table[b][x]] for x in CORE]}")
                # Why doesn't H find this?
                # H requires b in core AND c in core
                # ICP allows c to be anything non-absorber
                if c not in set(CORE):
                    print(f"    → c={c} is absorber/not-in-core (H requires c∈core)")

    # Summary table
    print("\n" + "=" * 72)
    print("PROPERTY COMPARISON SUMMARY")
    print("=" * 72)
    print(f"{'Property':<25} | {'D⊬H':>5} | {'H⊬D':>5} | {'SDH':>5} | "
          f"{'SAT equiv':>10} | Verdict")
    print("-" * 80)

    for pname, pfn in props:
        d = pfn(D_NOT_H)[0]
        h = pfn(H_NOT_D)[0]
        s = pfn(SDH)[0]

        agree = sum(1 for _, table in all_models
                    if has_H_nontrivial(table)[0] == pfn(table)[0])
        total = len(all_models)

        disc_ok = (not d) and h and s
        sat_ok = agree == total

        verdict = "✓ IDEAL" if disc_ok and sat_ok else (
            "~ partial" if disc_ok else "✗ fails")

        print(f"  {pname:<23} | {str(d):>5} | {str(h):>5} | {str(s):>5} | "
              f"{agree}/{total:>5} | {verdict}")


if __name__ == "__main__":
    main()

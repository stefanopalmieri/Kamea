#!/usr/bin/env python3
"""
Find the minimal witness for the Kleene wall structure.

Structure: exactly 2 left-zeros, extensionality (all rows distinct),
retraction pair on core, Kleene dichotomy, at least one classifier,
at least one non-classifier non-zero element.

Test N=4,5,6,7,8 in order. Stop at first SAT.
"""

from z3 import (
    Solver, Int, If, And, Or, Not, Implies,
    sat, unsat, unknown
)
import time


def test_kleene_magma(N):
    """Test if a KleeneMagma of size N is satisfiable."""
    print(f"\n{'='*60}")
    print(f"Testing N={N}")
    print(f"{'='*60}")

    s = Solver()
    s.set("timeout", 120 * 1000)

    # Cayley table
    dot = [[Int(f"d_{i}_{j}") for j in range(N)] for i in range(N)]

    # Range constraints
    for i in range(N):
        for j in range(N):
            s.add(dot[i][j] >= 0)
            s.add(dot[i][j] < N)

    # Zero morphisms: rows 0 and 1 are absorbers
    for j in range(N):
        s.add(dot[0][j] == 0)  # zero₁
        s.add(dot[1][j] == 1)  # zero₂

    # No other absorbers
    for x in range(2, N):
        s.add(Or([dot[x][j] != x for j in range(N)]))

    # Extensionality: all rows distinct
    for x in range(N):
        for y in range(x + 1, N):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(N)]))

    # Core range for retraction pair
    # Core = {2, 3, ..., min(5, N-1)} — at least 2 core elements needed
    core_hi = min(6, N)  # exclusive upper bound
    core_lo = 2

    if core_hi - core_lo < 2:
        print(f"  N={N} too small for core (need at least 2 core elements)")
        return None

    # Retraction pair: sec and ret
    # sec and ret are specific elements (not 0 or 1)
    # We need to pick which elements are sec and ret.
    # Let's use variables for sec and ret indices.
    sec_idx = Int("sec")
    ret_idx = Int("ret")
    s.add(sec_idx >= 2, sec_idx < N)
    s.add(ret_idx >= 2, ret_idx < N)
    s.add(sec_idx != ret_idx)

    # ret ∘ sec = id on core
    for x in range(core_lo, core_hi):
        # dot[ret][dot[sec][x]] = x
        # Since sec and ret are variables, we need ITE chains
        sec_x = Int(f"sec_x_{x}")
        s.add(sec_x >= 0, sec_x < N)
        for si in range(2, N):
            s.add(Implies(sec_idx == si, sec_x == dot[si][x]))
        ret_sec_x = Int(f"ret_sec_x_{x}")
        s.add(ret_sec_x >= 0, ret_sec_x < N)
        for ri in range(2, N):
            for v in range(N):
                s.add(Implies(And(ret_idx == ri, sec_x == v), ret_sec_x == dot[ri][v]))
        s.add(ret_sec_x == x)

    # sec ∘ ret = id on core
    for x in range(core_lo, core_hi):
        ret_x = Int(f"ret_x_{x}")
        s.add(ret_x >= 0, ret_x < N)
        for ri in range(2, N):
            s.add(Implies(ret_idx == ri, ret_x == dot[ri][x]))
        sec_ret_x = Int(f"sec_ret_x_{x}")
        s.add(sec_ret_x >= 0, sec_ret_x < N)
        for si in range(2, N):
            for v in range(N):
                s.add(Implies(And(sec_idx == si, ret_x == v), sec_ret_x == dot[si][v]))
        s.add(sec_ret_x == x)

    # Classifier: at least one non-zero element with all-boolean row on non-zeros
    cls_idx = Int("cls")
    s.add(cls_idx >= 2, cls_idx < N)

    # cls has all-boolean row (on ALL inputs, not just non-zeros)
    for j in range(N):
        cls_dot_j = Int(f"cls_dot_{j}")
        s.add(cls_dot_j >= 0, cls_dot_j < N)
        for ci in range(2, N):
            s.add(Implies(cls_idx == ci, cls_dot_j == dot[ci][j]))
        s.add(Or(cls_dot_j == 0, cls_dot_j == 1))

    # Kleene dichotomy: every non-zero element is either all-boolean or
    # all-non-boolean on non-zero inputs
    for a in range(2, N):
        bool_on_nonzero = And([Or(dot[a][x] == 0, dot[a][x] == 1)
                               for x in range(2, N)])
        nonbool_on_nonzero = And([And(dot[a][x] != 0, dot[a][x] != 1)
                                  for x in range(2, N)])
        s.add(Or(bool_on_nonzero, nonbool_on_nonzero))

    # At least one non-classifier non-zero element
    # (some non-zero element has a non-boolean output on a non-zero input)
    has_nonclassifier = Or([
        Or([And(dot[a][x] != 0, dot[a][x] != 1) for x in range(2, N)])
        for a in range(2, N)
    ])
    s.add(has_nonclassifier)

    # cls must be distinct from zero morphisms (needed for the wall to be nontrivial)
    # If cls = zero₁, its row is constant zero₁ which IS all-boolean but trivially so.
    # We need cls to be genuinely non-zero.
    s.add(cls_idx != 0)
    s.add(cls_idx != 1)

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0
    print(f"  Result: {result} ({elapsed:.1f}s)")

    if str(result) == "sat":
        m = s.model()
        print(f"\n  sec = {m.evaluate(sec_idx)}")
        print(f"  ret = {m.evaluate(ret_idx)}")
        print(f"  cls = {m.evaluate(cls_idx)}")

        print(f"\n  Cayley table:")
        table = []
        for i in range(N):
            row = [m.evaluate(dot[i][j]).as_long() for j in range(N)]
            table.append(row)
            print(f"    row {i:2d}: {row}")

        # Analyze categories
        zeros = []
        classifiers = []
        nonclassifiers = []
        for i in range(N):
            row = table[i]
            if all(v == i for v in row):
                zeros.append(i)
            elif all(v in (0, 1) for v in row[2:]):
                classifiers.append(i)
            else:
                nonclassifiers.append(i)

        print(f"\n  Category distribution:")
        print(f"    Zeros ({len(zeros)}): {zeros}")
        print(f"    Classifiers ({len(classifiers)}): {classifiers}")
        print(f"    Non-classifiers ({len(nonclassifiers)}): {nonclassifiers}")

        # Check WL-1 rigidity: do all elements have unique "fingerprints"?
        # Fingerprint = (row, column) for each element
        # Actually WL-1 = 1-dimensional Weisfeiler-Leman: color by row
        row_sigs = [tuple(row) for row in table]
        unique_rows = len(set(row_sigs)) == N
        print(f"\n  All rows unique (extensionality): {unique_rows}")

        # Column signatures
        col_sigs = [tuple(table[i][j] for i in range(N)) for j in range(N)]
        unique_cols = len(set(col_sigs)) == N
        print(f"  All columns unique: {unique_cols}")

        # WL-1: combined (row, col) signature
        combined = [(row_sigs[i], col_sigs[i]) for i in range(N)]
        wl1_rigid = len(set(combined)) == N
        print(f"  WL-1 rigid (unique (row,col) pairs): {wl1_rigid}")

        # Verify retraction pair
        sec_val = m.evaluate(sec_idx).as_long()
        ret_val = m.evaluate(ret_idx).as_long()
        cls_val = m.evaluate(cls_idx).as_long()
        print(f"\n  Retraction pair verification:")
        for x in range(core_lo, core_hi):
            sx = table[sec_val][x]
            rsx = table[ret_val][sx]
            rx = table[ret_val][x]
            srx = table[sec_val][rx]
            print(f"    x={x}: sec·x={sx}, ret·(sec·x)={rsx} {'✓' if rsx == x else '✗'}"
                  f"  |  ret·x={rx}, sec·(ret·x)={srx} {'✓' if srx == x else '✗'}")

        # Verify Kleene dichotomy
        print(f"\n  Kleene dichotomy verification:")
        for a in range(2, N):
            nonzero_outputs = [table[a][x] for x in range(2, N)]
            all_bool = all(v in (0, 1) for v in nonzero_outputs)
            all_nonbool = all(v not in (0, 1) for v in nonzero_outputs)
            status = "classifier" if all_bool else ("computational" if all_nonbool else "MIXED!")
            print(f"    element {a}: {status} (outputs on non-zeros: {nonzero_outputs})")

        return table
    return None


def main():
    for n in [4, 5, 6, 7, 8]:
        result = test_kleene_magma(n)
        if result is not None:
            print(f"\n{'='*60}")
            print(f"MINIMAL WITNESS FOUND AT N={len(result)}")
            print(f"{'='*60}")
            break


if __name__ == "__main__":
    main()

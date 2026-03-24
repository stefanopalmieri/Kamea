"""
N=5 R+D+H coexistence: SAT analysis

Expected outcome: SAT (R+D+H CAN coexist at N=5).

This script:
1. Algebraically analyzes why coexistence is possible at N=5
2. Verifies a hand-constructed N=5 witness
3. Uses Z3 to confirm SAT and enumerate solutions
4. Proves N=4 is truly the UNSAT boundary (ICP needs 3 pairwise distinct
   non-absorbers, but N=4 has only 2 core elements)

Result: The minimum cardinality for R+D+H coexistence is N=5, not N=6.
"""

from itertools import permutations


# ═══════════════════════════════════════════════════════════════
# Part 1: Algebraic analysis
# ═══════════════════════════════════════════════════════════════

def algebraic_analysis():
    """Explain why N=5 R+D+H is satisfiable."""
    print("=" * 70)
    print("ALGEBRAIC ANALYSIS: N=5 R+D+H coexistence")
    print("=" * 70)
    print()
    print("Core = {2,3,4}, |core| = 3.")
    print()
    print("ICP needs 3 pairwise distinct non-absorbers {a,b,c} = perm of {2,3,4}.")
    print("b must be core-preserving → b is a non-classifier.")
    print("sec, ret must biject core → sec, ret are non-classifiers.")
    print()
    print("Partition of {2,3,4} into classifiers (C) and non-classifiers (N):")
    print()
    print("Case |C|=1, |N|=2:")
    print("  b ∈ N. The classifier must be a or c.")
    print("  If classifier = a: a maps core to {0,1}, but a·x = c·(b·x).")
    print("    c ∈ N → c maps core to core → c·(b·x) ∈ core.")
    print("    But a·x ∈ {0,1}. Contradiction: {0,1} ∩ core = ∅.")
    print("  If classifier = c: a ∈ N → a maps core to core → a·x ∈ core.")
    print("    But a·x = c·(b·x) ∈ {0,1} (c is classifier). Same contradiction.")
    print("  → IMPOSSIBLE with 1 classifier.")
    print()
    print("Case |C|=2, |N|=1:")
    print("  sec = ret = b = unique non-classifier.")
    print("  b·(b·x) = x on core (involution). b·0 = 0 (ret_zero₁).")
    print("  {a,c} are classifiers.")
    print("  a·x = c·(b·x) on core. Both sides ∈ {0,1} (both classifiers).")
    print()
    print("  Sub-case b = identity on core:")
    print("    a·x = c·x on core. Both in {0,1}.")
    print("    Need a ≠ c by extensionality → differ on absorber columns.")
    print("    Non-triviality: a takes ≥2 values on core → has both 0 and 1.")
    print("    → SATISFIABLE! (identity retraction, two classifiers)")
    print()
    print("  Sub-case b = transposition (e.g., swap 2↔3, fix 4):")
    print("    a·x = c·(b·x): row c on core is a permutation of row a on core.")
    print("    → Also SATISFIABLE.")
    print()
    print("CONCLUSION: N=5 R+D+H is SAT. The key is |C|=2, |N|=1.")
    print()


# ═══════════════════════════════════════════════════════════════
# Part 2: Hand-constructed witness verification
# ═══════════════════════════════════════════════════════════════

def verify_witness(table, name, z1=0, z2=1):
    """Verify all R+D+H properties for a given Cayley table."""
    N = len(table)
    core = [i for i in range(N) if i != z1 and i != z2]

    def dot(a, b):
        return table[a][b]

    print(f"Verifying witness: {name} (N={N})")
    print(f"  Cayley table:")
    for y in range(N):
        print(f"    Row {y}: {table[y]}")

    errors = []

    # 1. Absorbers
    if not all(dot(z1, x) == z1 for x in range(N)):
        errors.append(f"Row {z1} is not all-{z1}")
    if not all(dot(z2, x) == z2 for x in range(N)):
        errors.append(f"Row {z2} is not all-{z2}")

    # 2. Exactly 2 absorbers
    for y in core:
        if all(dot(y, x) == y for x in range(N)):
            errors.append(f"Row {y} is a left-zero (extra absorber)")

    # 3. Extensionality
    for y1 in range(N):
        for y2 in range(y1 + 1, N):
            if all(dot(y1, x) == dot(y2, x) for x in range(N)):
                errors.append(f"Rows {y1} and {y2} are identical")

    # 4. HasRetractPair
    found_retract = False
    for sec in range(N):
        for ret in range(N):
            ok = True
            for x in core:
                if dot(ret, dot(sec, x)) != x:
                    ok = False
                    break
                if dot(sec, dot(ret, x)) != x:
                    ok = False
                    break
            if ok and dot(ret, z1) == z1:
                print(f"  HasRetractPair: sec={sec}, ret={ret}")
                found_retract = True
                break
        if found_retract:
            break
    if not found_retract:
        errors.append("No retraction pair found")

    # 5. HasDichotomy
    found_cls = None
    for cls in core:
        if all(dot(cls, x) in (z1, z2) for x in range(N)):
            found_cls = cls
            break
    if found_cls is None:
        errors.append("No classifier found")
    else:
        print(f"  HasDichotomy: cls={found_cls}")

    # Check dichotomy for each core element
    for y in core:
        core_outputs = [dot(y, x) for x in core]
        all_abs = all(v in (z1, z2) for v in core_outputs)
        all_core = all(v not in (z1, z2) for v in core_outputs)
        if not (all_abs or all_core):
            errors.append(f"Dichotomy fails for row {y}: {core_outputs}")

    # Non-degeneracy
    has_non_cls = any(
        y != z1 and y != z2 and
        any(x != z1 and x != z2 and dot(y, x) != z1 and dot(y, x) != z2
            for x in range(N))
        for y in range(N)
    )
    if not has_non_cls:
        errors.append("No non-classifier exists (non-degeneracy fails)")

    # 6. HasICP
    found_icp = False
    for a, b, c in permutations(core, 3):
        # b preserves core
        if not all(dot(b, x) not in (z1, z2) for x in core):
            continue
        # Factorization
        if not all(dot(a, x) == dot(c, dot(b, x)) for x in core):
            continue
        # Non-triviality
        a_vals = [dot(a, x) for x in core]
        if len(set(a_vals)) < 2:
            continue
        print(f"  HasICP: a={a}, b={b}, c={c}")
        found_icp = True
        break
    if not found_icp:
        errors.append("No ICP triple found")

    if errors:
        print(f"  FAILED: {errors}")
        return False
    else:
        print(f"  ALL PROPERTIES VERIFIED ✓")
        return True


# ═══════════════════════════════════════════════════════════════
# Part 3: Z3 confirmation
# ═══════════════════════════════════════════════════════════════

def z3_search():
    """Use Z3 to confirm SAT and find solutions."""
    try:
        from z3 import Int, IntVal, Solver, If, And, Or, Not, sat
    except ImportError:
        print("Z3 not available, skipping SAT solver confirmation.")
        return

    print("=" * 70)
    print("Z3 CONFIRMATION")
    print("=" * 70)
    print()

    N = 5
    CORE = [2, 3, 4]

    dot = [[Int(f"d_{y}_{x}") for x in range(N)] for y in range(N)]

    s = Solver()

    # Domain
    for y in range(N):
        for x in range(N):
            s.add(dot[y][x] >= 0, dot[y][x] < N)

    # Absorbers
    for x in range(N):
        s.add(dot[0][x] == 0)
        s.add(dot[1][x] == 1)

    # No extra absorbers
    for y in CORE:
        s.add(Not(And([dot[y][x] == y for x in range(N)])))

    # Extensionality
    for y1 in range(N):
        for y2 in range(y1 + 1, N):
            s.add(Or([dot[y1][x] != dot[y2][x] for x in range(N)]))

    # Helper for symbolic indexing
    def dot_func(a, b):
        result = IntVal(0)
        for y in range(N - 1, -1, -1):
            for x in range(N - 1, -1, -1):
                result = If(And(a == y, b == x), dot[y][x], result)
        return result

    # HasRetractPair
    sec = Int("sec")
    ret = Int("ret")
    s.add(sec >= 0, sec < N, ret >= 0, ret < N)

    for x in CORE:
        s.add(dot_func(ret, dot_func(sec, IntVal(x))) == x)
        s.add(dot_func(sec, dot_func(ret, IntVal(x))) == x)
    s.add(dot_func(ret, IntVal(0)) == 0)

    # HasDichotomy
    cls = Int("cls")
    s.add(cls >= 2, cls < N)

    for x in range(N):
        s.add(Or(dot_func(cls, IntVal(x)) == 0, dot_func(cls, IntVal(x)) == 1))

    for y in CORE:
        all_to_abs = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in CORE])
        all_to_core = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in CORE])
        s.add(Or(all_to_abs, all_to_core))

    s.add(Or([And(dot[y][x] != 0, dot[y][x] != 1) for y in CORE for x in CORE]))

    # HasICP
    a_icp = Int("a_icp")
    b_icp = Int("b_icp")
    c_icp = Int("c_icp")
    s.add(a_icp >= 2, a_icp < N, b_icp >= 2, b_icp < N, c_icp >= 2, c_icp < N)
    s.add(a_icp != b_icp, a_icp != c_icp, b_icp != c_icp)

    for x in CORE:
        s.add(And(dot_func(b_icp, IntVal(x)) != 0,
                  dot_func(b_icp, IntVal(x)) != 1))

    for x in CORE:
        s.add(dot_func(a_icp, IntVal(x)) ==
              dot_func(c_icp, dot_func(b_icp, IntVal(x))))

    s.add(Or([dot_func(a_icp, IntVal(x)) != dot_func(a_icp, IntVal(y))
              for x in CORE for y in CORE if x < y]))

    print("Checking N=5 R+D+H...")
    result = s.check()
    print(f"Result: {result}")
    print()

    if result == sat:
        m = s.model()
        print("Z3 witness:")
        table = []
        for y in range(N):
            row = [m.evaluate(dot[y][x]).as_long() for x in range(N)]
            table.append(row)
            print(f"  Row {y}: {row}")
        print(f"  sec={m.evaluate(sec)}, ret={m.evaluate(ret)}")
        print(f"  cls={m.evaluate(cls)}")
        print(f"  a={m.evaluate(a_icp)}, b={m.evaluate(b_icp)}, c={m.evaluate(c_icp)}")
        print()

        # Verify the Z3 witness
        verify_witness(table, "Z3 solution")
    else:
        print("UNEXPECTED: UNSAT")

    # Also confirm N=4 is UNSAT (ICP impossible)
    print()
    print("-" * 70)
    print("Confirming N=4 R+D+H is UNSAT...")
    print("-" * 70)
    print()
    print("At N=4, core = {2,3} has only 2 elements.")
    print("ICP needs 3 PAIRWISE DISTINCT non-absorbers (a ≠ b ≠ c ≠ a).")
    print("With only 2 non-absorbers, this is impossible.")
    print("→ N=4 R+D+H is trivially UNSAT (no Z3 needed).")
    print()
    print("Therefore: MINIMUM CARDINALITY FOR R+D+H = 5.")


# ═══════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    algebraic_analysis()

    print("=" * 70)
    print("WITNESS VERIFICATION")
    print("=" * 70)
    print()

    # The hand-constructed N=5 witness (identity retraction)
    #
    # Roles: sec=ret=2 (identity on core), cls=3, ICP: a=3, b=2, c=4
    # Partition: {3,4} classifiers, {2} non-classifier
    # Key property: b=identity → factorization reduces to a·x = c·x on core
    witness_5 = [
        [0, 0, 0, 0, 0],  # Row 0: z₁ absorber
        [1, 1, 1, 1, 1],  # Row 1: z₂ absorber
        [0, 2, 2, 3, 4],  # Row 2: sec=ret, identity on core, non-classifier
        [0, 0, 0, 1, 0],  # Row 3: classifier (a in ICP)
        [0, 1, 0, 1, 0],  # Row 4: classifier (c in ICP)
    ]

    ok = verify_witness(witness_5, "Hand-constructed (identity retraction)")
    print()

    if ok:
        print("★ The N=5 witness is VALID.")
        print("★ R+D+H coexistence is POSSIBLE at N=5.")
        print("★ The minimum cardinality is N=5 (not N=6).")
        print()

    z3_search()

    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print("1. N=4: IMPOSSIBLE (ICP needs 3 pairwise distinct non-absorbers)")
    print("2. N=5: POSSIBLE  (witness verified above)")
    print("3. N=6: POSSIBLE  (already Lean-verified in Witness6.lean)")
    print()
    print("OPTIMAL LOWER BOUND: N=5 (not N=6 as previously conjectured)")

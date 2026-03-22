#!/usr/bin/env python3
"""
Investigation: Presentation-independent characterization of H (evaluator internalization).

Tests four candidate properties against the Lean-proved N=10 counterexamples:
  - D⊬H: has Kripke dichotomy, NO Compose  →  should FAIL H-property
  - H⊬D: has Branch+Compose+Y, NO Kripke   →  should SATISFY H-property
  - S+D+H: has all three capabilities       →  should SATISFY H-property

Routes tested:
  1. Compositional Representability (CR): left-multiplication maps closed under composition
  2. Internal Action: programs applied to data stay in data domain
  3. Evaluation Closure: bounded-depth term evaluation stays in S
  4. Weaker factorization variants
"""

import itertools
from collections import defaultdict

# ═══════════════════════════════════════════════════════════════════
# Cayley tables from Lean proofs (Countermodels10.lean, Witness10.lean)
# ═══════════════════════════════════════════════════════════════════

# D⊬H: DichotomicRetractMagma, no Compose (Lean-proved)
D_NOT_H = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],  # ⊤
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],  # ⊥
    [3, 3, 2, 3, 4, 5, 6, 7, 9, 8],  # Q=2
    [0, 1, 2, 3, 4, 5, 6, 7, 9, 8],  # E=3
    [0, 0, 1, 1, 1, 1, 1, 1, 1, 1],  # τ=4
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0],  # f=5
    [2, 3, 9, 9, 9, 9, 9, 9, 9, 8],  # g=6
    [3, 2, 9, 9, 9, 9, 9, 9, 9, 8],  # ρ=7
    [1, 0, 1, 0, 1, 1, 1, 1, 0, 0],  # 8
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 1],  # 9
]

# H⊬D: FaithfulRetractMagma with Branch+Compose+Y, violates Kripke (Lean-proved)
H_NOT_D = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],  # ⊤
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],  # ⊥
    [3, 1, 3, 4, 9, 6, 8, 5, 7, 2],  # Q=2
    [0, 1, 9, 2, 3, 7, 5, 8, 6, 4],  # E=3
    [0, 0, 1, 1, 1, 1, 1, 1, 0, 0],  # τ=4
    [0, 0, 2, 0, 0, 0, 0, 0, 3, 1],  # f=5 (MIXED: violates Kripke)
    [2, 2, 2, 8, 3, 9, 4, 7, 9, 7],  # g=6 (inert)
    [8, 3, 2, 8, 3, 9, 4, 7, 3, 1],  # ρ=7
    [9, 2, 2, 3, 8, 1, 3, 7, 1, 7],  # η=8 (Compose holds)
    [2, 2, 2, 2, 4, 7, 6, 7, 2, 0],  # Y=9
]

# S+D+H witness: all three capabilities (Lean-proved)
SDH = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],  # ⊤
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],  # ⊥
    [3, 3, 4, 3, 7, 5, 9, 6, 8, 2],  # Q=2
    [0, 1, 9, 3, 2, 5, 7, 4, 8, 6],  # E=3
    [0, 0, 1, 1, 1, 0, 0, 0, 1, 1],  # τ=4
    [2, 2, 7, 2, 8, 9, 4, 3, 4, 2],  # f=5
    [0, 0, 6, 4, 8, 7, 3, 3, 4, 9],  # g=6 (inert)
    [2, 2, 6, 4, 8, 9, 4, 3, 4, 9],  # ρ=7
    [2, 2, 4, 8, 4, 3, 4, 4, 8, 9],  # η=8 (Compose holds)
    [3, 4, 7, 3, 9, 2, 2, 9, 2, 3],  # Y=9
]

N = 10
CORE = list(range(2, N))  # {2, 3, ..., 9}
ABS = {0, 1}


def dot(table, a, b):
    return table[a][b]


def core_row(table, a):
    """Row of element a restricted to core inputs."""
    return tuple(table[a][x] for x in CORE)


# ═══════════════════════════════════════════════════════════════════
# ROUTE 1: Compositional Representability (CR)
# ═══════════════════════════════════════════════════════════════════

def test_cr_full(table, name):
    """
    Full CR: For all a, b ∈ S, does there exist c ∈ S such that
    c·x = a·(b·x) for all x in core?

    This tests whether {L_a|_core : a ∈ S} is closed under composition.
    """
    # Build lookup: core_row → element index
    row_to_elem = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_elem:
            row_to_elem[r] = a

    representable = 0
    not_representable = 0
    failing_pairs = []

    for a in range(N):
        for b in range(N):
            # Compute the composite function: x ↦ a·(b·x) on core
            composite = tuple(dot(table, a, dot(table, b, x)) for x in CORE)
            if composite in row_to_elem:
                representable += 1
            else:
                not_representable += 1
                if len(failing_pairs) < 5:
                    failing_pairs.append((a, b))

    total = N * N
    print(f"\n  [{name}] Full CR: {representable}/{total} compositions representable")
    if failing_pairs:
        print(f"    First failing pairs: {failing_pairs}")
    return representable == total


def test_cr_core(table, name):
    """
    Core CR: For all a, b ∈ core, does there exist c ∈ S such that
    c·x = a·(b·x) for all x in core?

    Restricted to core×core compositions.
    """
    row_to_elem = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_elem:
            row_to_elem[r] = a

    representable = 0
    not_representable = 0
    failing_pairs = []

    for a in CORE:
        for b in CORE:
            composite = tuple(dot(table, a, dot(table, b, x)) for x in CORE)
            if composite in row_to_elem:
                representable += 1
            else:
                not_representable += 1
                if len(failing_pairs) < 5:
                    failing_pairs.append((a, b))

    total = len(CORE) ** 2
    print(f"  [{name}] Core CR: {representable}/{total} core compositions representable")
    if failing_pairs:
        print(f"    First failing pairs: {failing_pairs}")
    return representable == total


def test_cr_dispatcher(table, name, rho=7, g=6):
    """
    Dispatcher CR: Does ρ∘g have a representative? (i.e., does Compose hold?)
    Also check: how many compositions involving ρ or g are representable?
    """
    row_to_elem = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_elem:
            row_to_elem[r] = a

    # Check ρ∘g specifically
    rho_g = tuple(dot(table, rho, dot(table, g, x)) for x in CORE)
    has_compose = rho_g in row_to_elem
    if has_compose:
        rep = row_to_elem[rho_g]
        print(f"  [{name}] ρ∘g representable: YES (element {rep})")
    else:
        print(f"  [{name}] ρ∘g representable: NO")

    # Count all compositions involving ρ or g
    rho_composable = 0
    g_composable = 0
    for b in range(N):
        comp_rho_b = tuple(dot(table, rho, dot(table, b, x)) for x in CORE)
        if comp_rho_b in row_to_elem:
            rho_composable += 1
        comp_b_g = tuple(dot(table, b, dot(table, g, x)) for x in CORE)
        if comp_b_g in row_to_elem:
            g_composable += 1

    print(f"    ρ∘_ representable: {rho_composable}/{N}")
    print(f"    _∘g representable: {g_composable}/{N}")

    return has_compose


def cr_fraction(table, name):
    """What fraction of all S×S compositions are representable?"""
    row_to_elem = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_elem:
            row_to_elem[r] = a

    count = 0
    for a in range(N):
        for b in range(N):
            composite = tuple(dot(table, a, dot(table, b, x)) for x in CORE)
            if composite in row_to_elem:
                count += 1

    frac = count / (N * N)
    print(f"  [{name}] CR fraction: {count}/{N*N} = {frac:.1%}")
    return frac


# ═══════════════════════════════════════════════════════════════════
# ROUTE 1 VARIANT: Left-Representable Semigroup (LRS)
# ═══════════════════════════════════════════════════════════════════

def test_lrs(table, name):
    """
    Left-Representable Semigroup: Does the set of core-restricted rows
    form a semigroup under composition?

    More precisely: define L = {core_row(a) : a ∈ S}. Is L closed under
    function composition (where we compose the rows as functions core → S)?

    This is CR restricted to DISTINCT rows only.
    """
    rows = set()
    for a in range(N):
        rows.add(core_row(table, a))

    n_rows = len(rows)
    closed_count = 0
    total = 0

    for r1 in rows:
        for r2 in rows:
            total += 1
            # Compose: (r1 ∘ r2)(x) = r1[r2(x)]
            # r2(x) for x in core gives r2[i] for i in range(len(CORE))
            # but r2[i] might be an absorber, so r1[r2[i]] needs full row, not core row
            # We need the FULL row for r1, not just core restriction
            # Find which element has core_row r1
            pass

    # More careful: build the actual composition
    row_to_full = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_full:
            row_to_full[r] = a  # representative element

    closed = 0
    total = n_rows * n_rows
    for r1 in rows:
        a = row_to_full[r1]
        for r2 in rows:
            b = row_to_full[r2]
            composite = tuple(dot(table, a, dot(table, b, x)) for x in CORE)
            if composite in rows:
                closed += 1

    print(f"  [{name}] LRS: {closed}/{total} row compositions closed ({n_rows} distinct rows)")
    return closed == total


# ═══════════════════════════════════════════════════════════════════
# ROUTE 2: Internal Action
# ═══════════════════════════════════════════════════════════════════

def classify_elements(table):
    """Classify elements by row behavior on core."""
    absorbers = set()
    classifiers = set()
    encoders = set()
    inert = set()

    for a in range(N):
        # Check absorber
        if all(table[a][j] == a for j in range(N)):
            absorbers.add(a)
            continue

        # Check classifier (all outputs on core are boolean)
        core_outputs = [table[a][x] for x in CORE]
        all_bool = all(v in ABS for v in core_outputs)
        any_bool = any(v in ABS for v in core_outputs)
        all_non_bool = all(v not in ABS for v in core_outputs)

        if all_bool:
            classifiers.add(a)
        elif all_non_bool:
            # Check inert: maps core away from absorbers
            if all(table[a][x] not in ABS for x in CORE):
                # Check if row has low diversity (quasi-constant)
                unique_core = len(set(core_outputs))
                # Inert elements typically have specific structure
                # For now, classify as encoder
                encoders.add(a)
            else:
                encoders.add(a)
        else:
            # Mixed: both boolean and non-boolean on core
            encoders.add(a)  # or "mixed"

    return absorbers, classifiers, encoders


def test_internal_action(table, name):
    """
    Internal Action: Define P (programs) and X (data).
    Test whether P applied to X stays in X ∪ {⊤, ⊥}.

    P = non-absorber, non-classifier elements that are "active"
    X = elements reachable by Q-depth encoding from ⊤

    More precisely:
    - X = {⊤, Q·⊤, Q·(Q·⊤), ...} = Q-depth encodings
    - P = core \ X (elements that act on data rather than being data)
    """
    # Compute Q-depth elements (data domain)
    q = 2  # Q index
    x_set = {0}  # Start with ⊤
    current = 0
    for _ in range(N):
        nxt = table[q][current]
        if nxt in x_set:
            break
        x_set.add(nxt)
        current = nxt

    # P = non-absorber, non-X elements
    p_set = set(range(N)) - ABS - x_set

    print(f"  [{name}] Data domain X (Q-depth): {sorted(x_set)} ({len(x_set)} elements)")
    print(f"  [{name}] Program domain P: {sorted(p_set)} ({len(p_set)} elements)")

    # Test closure: for p ∈ P, x ∈ X, is p·x ∈ X ∪ ABS?
    closed_count = 0
    total = len(p_set) * len(x_set)
    escapes = []

    for p in sorted(p_set):
        for x in sorted(x_set):
            result = table[p][x]
            if result in x_set or result in ABS:
                closed_count += 1
            else:
                if len(escapes) < 5:
                    escapes.append((p, x, result))

    if total > 0:
        print(f"  [{name}] P·X ⊆ X∪ABS: {closed_count}/{total} ({closed_count/total:.1%})")
    else:
        print(f"  [{name}] P·X: trivial (empty domain)")

    if escapes:
        print(f"    Escapes: {escapes}")

    # Broader test: for ALL non-absorber a and ALL data x, is a·x ∈ X ∪ ABS ∪ P?
    # (i.e., does application stay within the structured part of the algebra?)
    structured = x_set | ABS | p_set
    full_closed = 0
    full_total = (N - 2) * len(x_set)
    for a in CORE:
        for x in sorted(x_set):
            if table[a][x] in structured:
                full_closed += 1

    if full_total > 0:
        print(f"  [{name}] core·X ⊆ S: {full_closed}/{full_total} ({full_closed/full_total:.1%})")

    return total > 0 and closed_count == total


def test_internal_action_v2(table, name):
    """
    Internal Action v2: Programs-on-programs closure.

    For p1, p2 ∈ P: is p1·p2 ∈ P ∪ ABS?
    (Do programs applied to programs stay in the program domain?)
    """
    q = 2
    x_set = {0}
    current = 0
    for _ in range(N):
        nxt = table[q][current]
        if nxt in x_set:
            break
        x_set.add(nxt)
        current = nxt

    p_set = set(range(N)) - ABS - x_set

    pp_closed = 0
    pp_total = len(p_set) ** 2
    for p1 in sorted(p_set):
        for p2 in sorted(p_set):
            if table[p1][p2] in (p_set | ABS):
                pp_closed += 1

    if pp_total > 0:
        print(f"  [{name}] P·P ⊆ P∪ABS: {pp_closed}/{pp_total} ({pp_closed/pp_total:.1%})")
    return pp_total > 0 and pp_closed == pp_total


# ═══════════════════════════════════════════════════════════════════
# ROUTE 3: Evaluation Closure
# ═══════════════════════════════════════════════════════════════════

def test_eval_closure(table, name, max_depth=4):
    """
    Evaluation Closure: For terms of depth ≤ D over S, does evaluation
    always produce an element of S?

    For any finite magma, ext_eval(t) ∈ S for all finite terms t.
    So this is trivially true. The non-trivial version uses PARTIAL evaluation
    in the term algebra, where some terms don't reduce to atoms.

    Instead, we test: are ALL depth-2 compositions representable?
    depth-2: a·(b·(c·x)) — needs two intermediate storage steps.
    """
    row_to_elem = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_elem:
            row_to_elem[r] = a

    # Depth 1: a·(b·x) — this is just CR
    d1_count = 0
    d1_total = N * N
    for a in range(N):
        for b in range(N):
            comp = tuple(dot(table, a, dot(table, b, x)) for x in CORE)
            if comp in row_to_elem:
                d1_count += 1

    # Depth 2: a·(b·(c·x)) — three-fold composition
    d2_count = 0
    d2_total = 0
    for a in CORE:
        for b in CORE:
            for c in CORE:
                d2_total += 1
                comp = tuple(dot(table, a, dot(table, b, dot(table, c, x))) for x in CORE)
                if comp in row_to_elem:
                    d2_count += 1

    core_size = len(CORE)
    print(f"  [{name}] Depth-1 representable: {d1_count}/{d1_total} ({d1_count/d1_total:.1%})")
    print(f"  [{name}] Depth-2 (core) representable: {d2_count}/{d2_total} ({d2_count/d2_total:.1%})")

    return d1_count, d2_count


# ═══════════════════════════════════════════════════════════════════
# ROUTE 4: Factorization variants
# ═══════════════════════════════════════════════════════════════════

def test_essential_cr(table, name, tau=4, rho=7, g=6, f=5):
    """
    Essential CR: Only test compositions involving the "dispatcher" elements.

    The idea: H requires that the EVALUATION-RELEVANT compositions are representable,
    not ALL compositions. Specifically:

    1. ρ∘g (Compose): dispatcher applied after storage
    2. Projection recovery: ∃ l such that l·(g·x) = x (left-inverse of g on core)
    3. Fixed-point: ∃ y such that ρ·y = y (non-absorber fixed point of ρ)
    """
    row_to_elem = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_elem:
            row_to_elem[r] = a

    results = {}

    # 1. ρ∘g
    rho_g = tuple(dot(table, rho, dot(table, g, x)) for x in CORE)
    results['compose'] = rho_g in row_to_elem

    # 2. g maps core away from absorbers (Inert)
    g_inert = all(table[g][x] not in ABS for x in CORE)
    results['inert'] = g_inert

    # 3. Left-inverse of g: ∃ l such that l·(g·x) = x for all x in core
    has_left_inv = False
    for l in range(N):
        if all(dot(table, l, dot(table, g, x)) == x for x in CORE):
            has_left_inv = True
            results['g_left_inv'] = l
            break
    results['has_g_left_inv'] = has_left_inv

    # 4. Fixed point of ρ: ∃ y ∈ core with ρ·y = y
    fp_rho = [y for y in CORE if table[rho][y] == y]
    results['rho_fixpoints'] = fp_rho

    # 5. ρ fixed point via Y: ∃ Y with Y·ρ = ρ·(Y·ρ)
    y_candidates = []
    for y in range(N):
        yr = table[y][rho]
        if table[rho][yr] == yr and yr not in ABS:
            y_candidates.append((y, yr))
    results['y_combinator'] = y_candidates

    print(f"  [{name}] Essential CR:")
    print(f"    ρ∘g representable (Compose): {results['compose']}")
    print(f"    g inert (maps core from absorbers): {results['inert']}")
    print(f"    g has left-inverse on core: {results['has_g_left_inv']}")
    if results['has_g_left_inv']:
        print(f"      left-inverse element: {results['g_left_inv']}")
    print(f"    ρ fixed points in core: {results['rho_fixpoints']}")
    print(f"    Y-combinator candidates: {results['y_combinator']}")

    return results


def test_evaluator_absorption(table, name, rho=7, g=6, f=5, tau=4):
    """
    Evaluator Absorption (EA): The single-concept candidate.

    "For every evaluation-relevant pair (a, b) ∈ S², the composite L_a ∘ L_b
    restricted to core is representable by some element of S."

    An evaluation-relevant pair is one where a or b plays a role in the
    evaluation pipeline: dispatcher (ρ), storage (g), projection (f, η),
    or classification (τ).

    This is WEAKER than full CR but STRONGER than just Compose.
    """
    row_to_elem = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_elem:
            row_to_elem[r] = a

    eval_relevant = {tau, f, g, rho}  # Elements with evaluation roles

    representable = 0
    total = 0
    failing = []

    for a in range(N):
        for b in range(N):
            if a not in eval_relevant and b not in eval_relevant:
                continue
            total += 1
            comp = tuple(dot(table, a, dot(table, b, x)) for x in CORE)
            if comp in row_to_elem:
                representable += 1
            else:
                if len(failing) < 5:
                    failing.append((a, b))

    print(f"  [{name}] Evaluator Absorption: {representable}/{total} eval-relevant compositions representable")
    if failing:
        print(f"    Failing: {failing}")
    return representable == total


# ═══════════════════════════════════════════════════════════════════
# ROUTE 1 REFINED: Operational Closure (OC)
# ═══════════════════════════════════════════════════════════════════

def test_operational_closure(table, name):
    """
    Operational Closure (OC): The algebra's non-absorber elements form
    a structure where EVERY two-step operation on core data can be
    expressed as a one-step operation.

    This is CR restricted to non-absorber composers:
    For all a, b ∈ core, ∃ c ∈ S: c·x = a·(b·x) for all x ∈ core.

    Key difference from full CR: we don't require compositions involving
    absorbers to be representable (since absorber rows are trivial).
    """
    return test_cr_core(table, name)


# ═══════════════════════════════════════════════════════════════════
# THE KEY CANDIDATE: Compositional Absorption (CA)
# ═══════════════════════════════════════════════════════════════════

def test_compositional_absorption(table, name):
    """
    Compositional Absorption (CA):

    "There exist elements g, ρ ∈ core such that:
     (i)  g maps core to core (storage/inertness)
     (ii) L_ρ ∘ L_g is representable (composition is internal)
     (iii) ρ has a non-absorber fixed point (recursion is internal)"

    This is a SINGLE property: "the algebra has an internal evaluation cycle."
    - g stores (packages data without losing it)
    - ρ processes (dispatches based on structure)
    - η = ρ∘g is the internal step (one evaluation step as one element)
    - The fixed point ensures the cycle can repeat indefinitely

    The cycle: store → process → (result feeds back as input)
    """
    row_to_elem = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_elem:
            row_to_elem[r] = a

    found = False
    witnesses = []

    for g_cand in CORE:
        # (i) g maps core to core
        if not all(table[g_cand][x] not in ABS for x in CORE):
            continue

        for rho_cand in CORE:
            if rho_cand == g_cand:
                continue

            # (ii) ρ∘g representable
            comp = tuple(dot(table, rho_cand, dot(table, g_cand, x)) for x in CORE)
            if comp not in row_to_elem:
                continue

            eta_cand = row_to_elem[comp]

            # (iii) ρ has a non-absorber fixed point
            has_fp = False
            fp_val = None
            for y in range(N):
                yr = table[y][rho_cand]
                if yr not in ABS and table[rho_cand][yr] == yr:
                    has_fp = True
                    fp_val = (y, yr)
                    break

            if has_fp:
                found = True
                witnesses.append({
                    'g': g_cand, 'rho': rho_cand,
                    'eta': eta_cand, 'fixpoint': fp_val
                })

    print(f"  [{name}] Compositional Absorption: {'YES' if found else 'NO'}")
    if witnesses:
        for w in witnesses[:3]:
            print(f"    g={w['g']}, ρ={w['rho']}, η={w['eta']}, "
                  f"Y·ρ path={w['fixpoint']}")
    return found


# ═══════════════════════════════════════════════════════════════════
# NEW CANDIDATE: Evaluation Internalization (EI)
# ═══════════════════════════════════════════════════════════════════

def test_evaluation_internalization(table, name):
    """
    Evaluation Internalization (EI):

    "There exists a triple (g, ρ, η) ∈ core³ with g ≠ ρ ≠ η such that:
     η = ρ ∘ g on core (η represents the composite of ρ after g)"

    This is the MINIMAL version: just the existence of an internal composition.
    No fixed point, no inertness requirement.

    Single sentence: "The algebra contains an element representing the
    composition of two of its own operations."
    """
    row_to_elem = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_elem:
            row_to_elem[r] = a

    triples = []
    for g_cand in CORE:
        for rho_cand in CORE:
            if rho_cand == g_cand:
                continue
            comp = tuple(dot(table, rho_cand, dot(table, g_cand, x)) for x in CORE)
            if comp in row_to_elem:
                eta_cand = row_to_elem[comp]
                if eta_cand != g_cand and eta_cand != rho_cand and eta_cand not in ABS:
                    triples.append((g_cand, rho_cand, eta_cand))

    found = len(triples) > 0
    print(f"  [{name}] Evaluation Internalization (minimal): "
          f"{'YES' if found else 'NO'} ({len(triples)} triples)")
    if triples:
        for t in triples[:5]:
            print(f"    g={t[0]}, ρ={t[1]}, η={t[2]}")
    return found


# ═══════════════════════════════════════════════════════════════════
# COMPREHENSIVE: Count all representable compositions per model
# ═══════════════════════════════════════════════════════════════════

def composition_landscape(table, name):
    """
    Full landscape: for each pair (a, b), is L_a ∘ L_b representable?
    Show which specific compositions are representable.
    """
    row_to_elem = {}
    for a in range(N):
        r = core_row(table, a)
        if r not in row_to_elem:
            row_to_elem[r] = a

    # Build representability matrix
    rep_matrix = [[False] * N for _ in range(N)]
    for a in range(N):
        for b in range(N):
            comp = tuple(dot(table, a, dot(table, b, x)) for x in CORE)
            rep_matrix[a][b] = comp in row_to_elem

    # Print matrix
    print(f"\n  [{name}] Composition representability matrix (a∘b):")
    print("       " + "  ".join(f"{j}" for j in range(N)))
    for a in range(N):
        row_str = "  ".join("■" if rep_matrix[a][b] else "·" for b in range(N))
        count = sum(rep_matrix[a][b] for b in range(N))
        print(f"    {a}: {row_str}  ({count})")

    total_rep = sum(rep_matrix[a][b] for a in range(N) for b in range(N))
    print(f"    Total: {total_rep}/{N*N}")

    # Which rows are "composable" (appear as composites)?
    composite_rows = set()
    for a in range(N):
        for b in range(N):
            comp = tuple(dot(table, a, dot(table, b, x)) for x in CORE)
            if comp in row_to_elem:
                composite_rows.add(row_to_elem[comp])

    print(f"    Elements appearing as composites: {sorted(composite_rows)}")


# ═══════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════

def main():
    models = [
        (D_NOT_H, "D⊬H (Kripke yes, Compose no)"),
        (H_NOT_D, "H⊬D (Compose yes, Kripke no)"),
        (SDH,     "S+D+H (all capabilities)"),
    ]

    print("=" * 72)
    print("ROUTE 1: COMPOSITIONAL REPRESENTABILITY")
    print("=" * 72)
    print("\nFull CR: ∀ a,b ∈ S, ∃ c: c·x = a·(b·x) on core")
    for table, name in models:
        test_cr_full(table, name)

    print("\nCore CR: ∀ a,b ∈ core, ∃ c: c·x = a·(b·x) on core")
    for table, name in models:
        test_cr_core(table, name)

    print("\nDispatcher CR (ρ and g compositions):")
    for table, name in models:
        test_cr_dispatcher(table, name)

    print("\nCR fractions:")
    fracs = {}
    for table, name in models:
        fracs[name] = cr_fraction(table, name)

    print("\nLeft-Representable Semigroup:")
    for table, name in models:
        test_lrs(table, name)

    print("\n" + "=" * 72)
    print("ROUTE 2: INTERNAL ACTION")
    print("=" * 72)
    for table, name in models:
        test_internal_action(table, name)
        test_internal_action_v2(table, name)
        print()

    print("=" * 72)
    print("ROUTE 3: EVALUATION CLOSURE (depth-k representability)")
    print("=" * 72)
    for table, name in models:
        test_eval_closure(table, name)
        print()

    print("=" * 72)
    print("ROUTE 4: FACTORIZATION VARIANTS")
    print("=" * 72)

    print("\nEssential CR (evaluation-relevant elements only):")
    for table, name in models:
        test_essential_cr(table, name)
        print()

    print("Evaluator Absorption (compositions involving eval elements):")
    for table, name in models:
        test_evaluator_absorption(table, name)
        print()

    print("=" * 72)
    print("KEY CANDIDATES")
    print("=" * 72)

    print("\nCompositional Absorption (storage + dispatch + composition + fixpoint):")
    ca_results = {}
    for table, name in models:
        ca_results[name] = test_compositional_absorption(table, name)

    print("\nEvaluation Internalization (minimal: just ∃ representable composition):")
    ei_results = {}
    for table, name in models:
        ei_results[name] = test_evaluation_internalization(table, name)

    print("\n" + "=" * 72)
    print("COMPOSITION LANDSCAPES")
    print("=" * 72)
    for table, name in models:
        composition_landscape(table, name)

    print("\n" + "=" * 72)
    print("SUMMARY: DISCRIMINATION TABLE")
    print("=" * 72)
    print("\nProperty                  | D⊬H  | H⊬D  | S+D+H | Discriminates?")
    print("-" * 72)

    # Recompute key results
    results = {}
    for table, name in models:
        row_to_elem = {}
        for a in range(N):
            r = core_row(table, a)
            if r not in row_to_elem:
                row_to_elem[r] = a

        # Full CR
        full_cr = sum(1 for a in range(N) for b in range(N)
                      if tuple(dot(table, a, dot(table, b, x)) for x in CORE) in row_to_elem)
        results.setdefault('Full CR', []).append(f"{full_cr}/{N*N}")

        # Core CR
        core_cr = sum(1 for a in CORE for b in CORE
                      if tuple(dot(table, a, dot(table, b, x)) for x in CORE) in row_to_elem)
        results.setdefault('Core CR', []).append(f"{core_cr}/{len(CORE)**2}")

        # ρ∘g
        comp = tuple(dot(table, 7, dot(table, 6, x)) for x in CORE)
        results.setdefault('ρ∘g representable', []).append("YES" if comp in row_to_elem else "NO")

        # CA
        results.setdefault('Comp. Absorption', []).append("YES" if ca_results[name] else "NO")

        # EI
        results.setdefault('Eval. Internal.', []).append("YES" if ei_results[name] else "NO")

    for prop, vals in results.items():
        d_not_h, h_not_d, sdh = vals
        # Does it discriminate? D⊬H should be NO/low, H⊬D and S+D+H should be YES/high
        disc = "✓" if (d_not_h in ("NO", "0") or "/" in d_not_h) and h_not_d not in ("NO",) else "?"
        print(f"  {prop:<25} | {d_not_h:5} | {h_not_d:5} | {sdh:5} | {disc}")


if __name__ == "__main__":
    main()

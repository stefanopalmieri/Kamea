#!/usr/bin/env python3
"""
Ψ₁₆ᶠ Black-Box Recovery Demo

Shuffles the 16 elements of Ψ₁₆ᶠ behind opaque labels, then recovers every
element purely from behavioral probing of the dot oracle. Demonstrates that
axiom-enforced properties enable step-by-step identification of all 16 elements.

Two recovery methods:
  behavioral  — 12-step axiom-driven probing (default)
  generation  — steps 1-7 (find ⊤,⊥,g,τ,SEQ,s0,E,Q), then generate remaining
                elements via dot(E,E)=f, dot(Q,Q)=s1, etc. (depth ≤ 2)

Unlike kamea_blackbox.py (48 atoms, term-level operations), this is atom-level
only: the dot function is a 16×16 table lookup. No structured terms.

Usage:
  python psi_blackbox.py                          # single-seed demo
  python psi_blackbox.py --seeds 1000             # batch (behavioral)
  python psi_blackbox.py --method generation      # generation-based demo
  python psi_blackbox.py --seeds 1000 --compare   # side-by-side dot-call cost
"""

import random
import argparse


# ============================================================================
# Ψ₁₆ᶠ Cayley table (from Psi16Full.lean, 83 Lean theorems)
# ============================================================================

PSI_16_FULL = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],              #  0  ⊤ (top)          [absorber]
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],              #  1  ⊥ (bot)          [absorber]
    [5, 1, 13, 7, 11, 5, 6, 8, 2, 5, 11, 9, 4, 14, 3, 15],         #  2  f                [encoder]
    [0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1],              #  3  τ                [tester]
    [0, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11],#  4  g                [inert]
    [0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0],              #  5  SEQ              [tester]
    [15, 0, 5, 9, 3, 15, 14, 14, 2, 12, 8, 14, 12, 4, 12, 8],      #  6  Q / SND / s2     [encoder]
    [0, 1, 8, 4, 13, 2, 11, 2, 14, 3, 15, 12, 14, 15, 6, 5],       #  7  E / INC2 / s7    [encoder]
    [12, 1, 13, 7, 11, 5, 12, 11, 4, 12, 5, 14, 15, 7, 11, 12],    #  8  ρ / s6           [encoder]
    [1, 6, 14, 14, 14, 14, 9, 8, 3, 15, 5, 7, 13, 11, 12, 4],      #  9  η / p10          [encoder]
    [13, 1, 4, 3, 12, 11, 2, 11, 5, 3, 8, 14, 9, 7, 11, 11],       # 10  Y / s4           [encoder]
    [14, 1, 9, 10, 11, 13, 12, 7, 5, 6, 8, 2, 14, 12, 10, 4],      # 11  PAIR / s3        [encoder]
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1],              # 12  s0               [tester]
    [3, 0, 14, 4, 14, 6, 11, 12, 7, 3, 15, 10, 14, 2, 6, 8],       # 13  INC              [encoder]
    [14, 0, 5, 4, 3, 2, 12, 5, 11, 14, 3, 14, 12, 2, 6, 3],        # 14  s1 / GET/FST/SWAP [encoder]
    [1, 3, 13, 15, 3, 7, 14, 8, 15, 4, 11, 6, 7, 14, 12, 10],      # 15  s5 / DEC/PUT     [encoder]
]

# Element name → canonical index
ELEM_NAMES = {
    0: "⊤", 1: "⊥", 2: "f", 3: "τ", 4: "g", 5: "SEQ",
    6: "Q", 7: "E", 8: "ρ", 9: "η", 10: "Y", 11: "PAIR",
    12: "s0", 13: "INC", 14: "s1", 15: "DEC",
}

# Multi-duty annotations
MULTI_DUTY = {
    0: "absorber",
    1: "absorber",
    2: "f / PUT-alias (encoder, branch-if)",
    3: "τ (tester, branch selector)",
    4: "g (inert, branch-else)",
    5: "SEQ (tester, sequencer)",
    6: "Q / SND / s2 (encoder, quote)",
    7: "E / INC2 / s7 (encoder, eval)",
    8: "ρ / s6 (encoder, branch element)",
    9: "η / p10 (encoder, compose)",
    10: "Y / s4 (encoder, Y-combinator)",
    11: "PAIR / s3 (encoder)",
    12: "s0 / p00 (tester, counter zero)",
    13: "INC (encoder, increment)",
    14: "s1 / GET / FST / SWAP (encoder, 4 roles)",
    15: "s5 / DEC / PUT (encoder, 3 roles)",
}


# ============================================================================
# Black-box construction
# ============================================================================

def make_blackbox(seed=11):
    """Shuffle 16 elements behind opaque labels, return (domain, dot_oracle, ground_truth)."""
    rng = random.Random(seed)
    N = 16

    # perm[canonical_index] = hidden_label
    perm = list(range(N))
    rng.shuffle(perm)
    inv = [0] * N
    for i, p in enumerate(perm):
        inv[p] = i

    domain = list(range(N))  # opaque labels 0..15

    def dot(x, y):
        """Black-box dot: hidden_label × hidden_label → hidden_label."""
        return perm[PSI_16_FULL[inv[x]][inv[y]]]

    # ground_truth: canonical_name → hidden_label
    ground_truth = {ELEM_NAMES[i]: perm[i] for i in range(N)}
    return domain, dot, ground_truth


# ============================================================================
# 12-step recovery algorithm
# ============================================================================

def recover_all(domain, dot):
    """Recover all 16 elements from black-box dot access. Returns {name: hidden_label}."""
    N = len(domain)
    rec = {}
    identified = set()

    def row(x):
        return [dot(x, y) for y in domain]

    def image(x):
        return set(row(x))

    # ------------------------------------------------------------------
    # Step 1: Find absorbers ⊤, ⊥ (unoriented)
    #   Constant rows: ∀y: x·y = x
    # ------------------------------------------------------------------
    absorbers = []
    for x in domain:
        r = row(x)
        if all(v == x for v in r):
            absorbers.append(x)
    assert len(absorbers) == 2, f"Expected 2 absorbers, found {len(absorbers)}"
    abs_a, abs_b = absorbers

    # ------------------------------------------------------------------
    # Step 2: Find g (inert) + orient ⊤/⊥
    #   g is the unique non-absorber whose row image has exactly 2 values:
    #   one absorber and one non-absorber. ⊤ = the absorber in g's image.
    # ------------------------------------------------------------------
    abs_set = set(absorbers)
    g = None
    top = None
    for x in domain:
        if x in abs_set:
            continue
        img = image(x)
        if len(img) == 2:
            in_abs = img & abs_set
            out_abs = img - abs_set
            if len(in_abs) == 1 and len(out_abs) == 1:
                g = x
                top = in_abs.pop()
                break
    assert g is not None, "Failed to find inert element g"
    bot = abs_a if top == abs_b else abs_b

    rec["⊤"] = top
    rec["⊥"] = bot
    rec["g"] = g
    identified.update([top, bot, g])

    # ------------------------------------------------------------------
    # Step 3: Find testers (τ, SEQ, s0)
    #   Row image ⊆ {⊤, ⊥}
    # ------------------------------------------------------------------
    testers = []
    for x in domain:
        if x in identified:
            continue
        if image(x) <= {top, bot}:
            testers.append(x)
    assert len(testers) == 3, f"Expected 3 testers, found {len(testers)}"

    # ------------------------------------------------------------------
    # Step 4: Identify SEQ — fewest accepts (⊤ outputs) among testers
    # ------------------------------------------------------------------
    def accept_count(t):
        return sum(1 for y in domain if dot(t, y) == top)

    testers_sorted = sorted(testers, key=accept_count)
    seq = testers_sorted[0]  # fewest accepts
    remaining_testers = [t for t in testers if t != seq]

    rec["SEQ"] = seq
    identified.add(seq)

    # ------------------------------------------------------------------
    # Step 5: τ vs s0 — τ accepts g, s0 rejects g
    # ------------------------------------------------------------------
    t_a, t_b = remaining_testers
    if dot(t_a, g) == top:
        tau, s0 = t_a, t_b
    else:
        tau, s0 = t_b, t_a
    assert dot(tau, g) == top, "τ must accept g"
    assert dot(s0, g) == bot, "s0 must reject g"

    rec["τ"] = tau
    rec["s0"] = s0
    identified.update([tau, s0])

    # ------------------------------------------------------------------
    # Step 6: Find E — unique encoder with E·⊤ = ⊤ and E·⊥ = ⊥
    # ------------------------------------------------------------------
    e_candidates = []
    for x in domain:
        if x in identified:
            continue
        if dot(x, top) == top and dot(x, bot) == bot:
            e_candidates.append(x)
    assert len(e_candidates) == 1, f"Expected 1 E-transparent encoder, found {len(e_candidates)}"
    E = e_candidates[0]
    rec["E"] = E
    identified.add(E)

    # ------------------------------------------------------------------
    # Step 7: Find Q — unique encoder where E·(Q·τ) = τ AND E·(Q·g) = g
    # ------------------------------------------------------------------
    q_candidates = []
    for x in domain:
        if x in identified:
            continue
        if dot(E, dot(x, tau)) == tau and dot(E, dot(x, g)) == g:
            q_candidates.append(x)
    assert len(q_candidates) == 1, f"Expected 1 Q encoder, found {len(q_candidates)}"
    Q = q_candidates[0]
    rec["Q"] = Q
    identified.add(Q)

    # ------------------------------------------------------------------
    # Step 8: Find f — QE full round-trip (both directions) on unidentified,
    #   excluding those that self-identify on ⊤
    # ------------------------------------------------------------------
    f_candidates = []
    for x in domain:
        if x in identified:
            continue
        # Both E·(Q·x) = x and Q·(E·x) = x
        if dot(E, dot(Q, x)) == x and dot(Q, dot(E, x)) == x:
            # Does NOT self-identify on ⊤
            if dot(x, top) != x:
                f_candidates.append(x)
    assert len(f_candidates) == 1, f"Expected 1 f element, found {len(f_candidates)}"
    f = f_candidates[0]
    rec["f"] = f
    identified.add(f)

    # Core = {f, τ, g, SEQ}
    core = [f, tau, g, seq]

    # ------------------------------------------------------------------
    # Step 9: Find ρ — Branch dispatch: ρ·x = f·x for all core x where τ·x = ⊤
    # ------------------------------------------------------------------
    rho_candidates = []
    for x in domain:
        if x in identified:
            continue
        match = True
        for c in core:
            if dot(tau, c) == top:
                if dot(x, c) != dot(f, c):
                    match = False
                    break
            else:
                if dot(x, c) != dot(g, c):
                    match = False
                    break
        if match:
            rho_candidates.append(x)
    assert len(rho_candidates) == 1, f"Expected 1 ρ element, found {len(rho_candidates)}"
    rho = rho_candidates[0]
    rec["ρ"] = rho
    identified.add(rho)

    # ------------------------------------------------------------------
    # Step 10: Find η — Selection: η·ρ = τ
    # ------------------------------------------------------------------
    eta_candidates = []
    for x in domain:
        if x in identified:
            continue
        if dot(x, rho) == tau:
            eta_candidates.append(x)
    assert len(eta_candidates) == 1, f"Expected 1 η element, found {len(eta_candidates)}"
    eta = eta_candidates[0]
    rec["η"] = eta
    identified.add(eta)

    # ------------------------------------------------------------------
    # Step 11: Find INC — creates 8-cycle from s0
    # ------------------------------------------------------------------
    inc_candidates = []
    for x in domain:
        if x in identified:
            continue
        # Follow x starting from s0 for 8 steps
        cur = s0
        cycle = [cur]
        ok = True
        for _ in range(7):
            cur = dot(x, cur)
            if cur in set(cycle):
                ok = False
                break
            cycle.append(cur)
        # Check 8th step returns to s0, and 2nd step hits Q (distinguishes INC from DEC)
        if ok and len(cycle) == 8 and len(set(cycle)) == 8 and dot(x, cur) == s0:
            if cycle[2] == Q:  # INC·(INC·s0) = s2 = Q
                inc_candidates.append((x, cycle))
    assert len(inc_candidates) == 1, f"Expected 1 INC element, found {len(inc_candidates)}"
    INC, counter_cycle = inc_candidates[0]
    rec["INC"] = INC
    identified.add(INC)

    # ------------------------------------------------------------------
    # Step 12: Counter positions identify remaining elements
    #   s0 →INC→ s1 →INC→ s2(=Q) →INC→ s3(=PAIR) →INC→
    #   s4(=Y) →INC→ s5(=DEC) →INC→ s6(=ρ) →INC→ s7(=E) →INC→ s0
    # ------------------------------------------------------------------
    # counter_cycle = [s0, s1, s2, s3, s4, s5, s6, s7]
    # s2 = Q (already known), s6 = ρ (already known), s7 = E (already known)
    s1_val = counter_cycle[1]
    pair_val = counter_cycle[3]  # s3 = PAIR
    y_val = counter_cycle[4]     # s4 = Y
    dec_val = counter_cycle[5]   # s5 = DEC

    rec["s1"] = s1_val
    rec["PAIR"] = pair_val
    rec["Y"] = y_val
    rec["DEC"] = dec_val
    identified.update([s1_val, pair_val, y_val, dec_val])

    assert len(identified) == 16, f"Only identified {len(identified)}/16 elements"
    return rec


# ============================================================================
# Generation-based recovery (replaces steps 8-12 with depth-2 generation)
# ============================================================================

# Generation tree from {⊤,⊥,Q,E}:
#   Depth 0: ⊤, ⊥, Q, E
#   Depth 1: f = dot(E,E),  PAIR = dot(E,Q),  s1 = dot(Q,Q),  DEC = dot(Q,⊤)
#   Depth 2: τ = dot(f,s1), g = dot(PAIR,DEC), SEQ = dot(f,⊤), ρ = dot(f,E),
#            η = dot(f,PAIR), Y = dot(PAIR,s1), s0 = dot(Q,s1), INC = dot(f,f)

def recover_generation(domain, dot):
    """Recover all 16 elements: steps 1-7 behavioral, then depth-2 generation."""
    N = len(domain)
    rec = {}
    identified = set()

    def row(x):
        return [dot(x, y) for y in domain]

    def image(x):
        return set(row(x))

    # Steps 1-7 identical to behavioral recovery
    # Step 1: absorbers
    absorbers = []
    for x in domain:
        r = row(x)
        if all(v == x for v in r):
            absorbers.append(x)
    assert len(absorbers) == 2
    abs_a, abs_b = absorbers
    abs_set = set(absorbers)

    # Step 2: g + orient
    g = top = None
    for x in domain:
        if x in abs_set:
            continue
        img = image(x)
        if len(img) == 2:
            in_abs = img & abs_set
            out_abs = img - abs_set
            if len(in_abs) == 1 and len(out_abs) == 1:
                g = x
                top = in_abs.pop()
                break
    assert g is not None
    bot = abs_a if top == abs_b else abs_b
    rec["⊤"], rec["⊥"], rec["g"] = top, bot, g
    identified.update([top, bot, g])

    # Step 3: testers
    testers = []
    for x in domain:
        if x in identified:
            continue
        if image(x) <= {top, bot}:
            testers.append(x)
    assert len(testers) == 3

    # Step 4: SEQ (fewest accepts)
    testers_sorted = sorted(testers, key=lambda t: sum(1 for y in domain if dot(t, y) == top))
    seq = testers_sorted[0]
    remaining_testers = [t for t in testers if t != seq]
    rec["SEQ"] = seq
    identified.add(seq)

    # Step 5: τ vs s0
    t_a, t_b = remaining_testers
    if dot(t_a, g) == top:
        tau, s0 = t_a, t_b
    else:
        tau, s0 = t_b, t_a
    rec["τ"], rec["s0"] = tau, s0
    identified.update([tau, s0])

    # Step 6: E
    E = None
    for x in domain:
        if x in identified:
            continue
        if dot(x, top) == top and dot(x, bot) == bot:
            E = x
            break
    assert E is not None
    rec["E"] = E
    identified.add(E)

    # Step 7: Q
    Q = None
    for x in domain:
        if x in identified:
            continue
        if dot(E, dot(x, tau)) == tau and dot(E, dot(x, g)) == g:
            Q = x
            break
    assert Q is not None
    rec["Q"] = Q
    identified.add(Q)

    # Generation phase: compute remaining 8 elements from {⊤,⊥,Q,E}
    # Depth 1
    f    = dot(E, E)       # f = E·E
    PAIR = dot(E, Q)       # PAIR = E·Q
    s1   = dot(Q, Q)       # s1 = Q·Q
    DEC  = dot(Q, top)     # DEC = Q·⊤

    # Depth 2
    INC  = dot(f, f)       # INC = f·f
    rho  = dot(f, E)       # ρ = f·E
    eta  = dot(f, PAIR)    # η = f·PAIR = f·(E·Q)
    Y    = dot(PAIR, s1)   # Y = PAIR·s1 = (E·Q)·(Q·Q)

    rec["f"]    = f
    rec["PAIR"] = PAIR
    rec["s1"]   = s1
    rec["DEC"]  = DEC
    rec["INC"]  = INC
    rec["ρ"]    = rho
    rec["η"]    = eta
    rec["Y"]    = Y

    identified.update([f, PAIR, s1, DEC, INC, rho, eta, Y])
    assert len(identified) == 16, f"Only identified {len(identified)}/16 elements"
    return rec


# ============================================================================
# Instrumented blackbox for dot-call counting
# ============================================================================

def make_blackbox_counted(seed=11):
    """Like make_blackbox but dot oracle counts calls."""
    rng = random.Random(seed)
    N = 16
    perm = list(range(N))
    rng.shuffle(perm)
    inv = [0] * N
    for i, p in enumerate(perm):
        inv[p] = i
    domain = list(range(N))
    calls = [0]

    def dot(x, y):
        calls[0] += 1
        return perm[PSI_16_FULL[inv[x]][inv[y]]]

    ground_truth = {ELEM_NAMES[i]: perm[i] for i in range(N)}
    return domain, dot, ground_truth, calls


# ============================================================================
# Verification
# ============================================================================

def verify_axioms(dot, rec):
    """Check axiom properties using recovered elements. Returns list of (name, passed)."""
    results = []
    top, bot = rec["⊤"], rec["⊥"]
    f, tau, g, seq = rec["f"], rec["τ"], rec["g"], rec["SEQ"]
    Q, E = rec["Q"], rec["E"]
    rho, eta = rec["ρ"], rec["η"]
    Y, s0, s1 = rec["Y"], rec["s0"], rec["s1"]
    INC, DEC = rec["INC"], rec["DEC"]
    PAIR = rec["PAIR"]
    core = [f, tau, g, seq]

    # 1. QE round-trip on core
    qe_ok = all(dot(E, dot(Q, c)) == c for c in core)
    results.append(("QE round-trip (core)", qe_ok))

    # 2. Branch dispatch: ρ·x = f·x when τ·x = ⊤, else g·x (on core)
    branch_ok = True
    for c in core:
        if dot(tau, c) == top:
            if dot(rho, c) != dot(f, c):
                branch_ok = False
        else:
            if dot(rho, c) != dot(g, c):
                branch_ok = False
    results.append(("Branch dispatch (core)", branch_ok))

    # 3. Selection: η·ρ = τ
    results.append(("Selection (η·ρ = τ)", dot(eta, rho) == tau))

    # 4. Y fixed point: Y·ρ = ρ·(Y·ρ) and Y·ρ ≥ 2 (not absorber)
    y_rho = dot(Y, rho)
    y_ok = (dot(rho, y_rho) == y_rho) and (y_rho not in (top, bot))
    results.append(("Y fixed point", y_ok))

    # 5. 8-state counter: INC cycles s0 through 8 states back to s0
    cur = s0
    counter_states = []
    for _ in range(8):
        counter_states.append(cur)
        cur = dot(INC, cur)
    counter_ok = (cur == s0) and (len(set(counter_states)) == 8)
    results.append(("8-state counter (INC)", counter_ok))

    # 6. Zero test: τ·s0 = ⊤, τ·sₖ = ⊥ for k≠0
    zero_ok = dot(tau, s0) == top
    for s in counter_states[1:]:
        if dot(tau, s) != bot:
            zero_ok = False
    results.append(("Zero test (τ detects s0)", zero_ok))

    # 7. DEC reverse cycle
    dec_ok = True
    for i in range(8):
        si = counter_states[i]
        si_prev = counter_states[(i - 1) % 8]
        if dot(DEC, si) != si_prev:
            dec_ok = False
    results.append(("DEC reverse cycle", dec_ok))

    # 8. IO roundtrip: GET·(PUT·x) = x on core
    PUT, GET = DEC, s1  # multi-duty: PUT=15(DEC), GET=14(s1)
    io_ok = all(dot(GET, dot(PUT, c)) == c for c in core)
    results.append(("IO roundtrip (GET·PUT·x = x)", io_ok))

    # 9. PAIR/FST/SND (2×2 product on {s0, s1})
    FST, SND = s1, Q  # multi-duty: FST=14(s1), SND=6(Q)
    pair_ok = True
    for si in [s0, s1]:
        for sj in [s0, s1]:
            pij = dot(dot(PAIR, si), sj)
            if dot(FST, pij) != si:
                pair_ok = False
            if dot(SND, pij) != sj:
                pair_ok = False
    results.append(("PAIR/FST/SND (2×2 product)", pair_ok))

    # 10. SWAP involution on core: SWAP·(SWAP·x) = x
    SWAP = s1  # multi-duty: SWAP=14(s1)
    swap_ok = all(dot(SWAP, dot(SWAP, c)) == c for c in core)
    results.append(("SWAP involution (core)", swap_ok))

    return results


# ============================================================================
# Display helpers
# ============================================================================

def format_recovery(rec, ground_truth):
    """Format recovery results showing recovered vs ground truth."""
    inv_gt = {v: k for k, v in ground_truth.items()}
    lines = []
    all_correct = True
    for name in ["⊤", "⊥", "f", "τ", "g", "SEQ", "Q", "E",
                  "ρ", "η", "Y", "PAIR", "s0", "INC", "s1", "DEC"]:
        hidden = rec[name]
        true_name = inv_gt[hidden]
        ok = (true_name == name)
        if not ok:
            all_correct = False
        mark = "✓" if ok else "✗"
        lines.append(f"  {mark} {name:>4s} → label {hidden:2d}  (true: {true_name})")
    return "\n".join(lines), all_correct


# ============================================================================
# Main
# ============================================================================

def main():
    parser = argparse.ArgumentParser(description="Ψ₁₆ᶠ black-box recovery demo")
    parser.add_argument("--seed", type=int, default=11, help="RNG seed for single demo")
    parser.add_argument("--seeds", type=int, default=0, help="Batch test N seeds (1..N)")
    parser.add_argument("--method", choices=["behavioral", "generation"], default="behavioral",
                        help="Recovery method (default: behavioral)")
    parser.add_argument("--compare", action="store_true",
                        help="Compare dot-call costs of both methods (use with --seeds)")
    args = parser.parse_args()

    recover_fn = recover_generation if args.method == "generation" else recover_all

    if args.compare and args.seeds > 0:
        # Side-by-side dot-call comparison
        print(f"Comparing dot-call costs over {args.seeds} seeds...")
        beh_calls, gen_calls = [], []
        beh_fail, gen_fail = 0, 0
        for seed in range(1, args.seeds + 1):
            for method, calls_list, fail_count_ref in [
                (recover_all, beh_calls, "beh"),
                (recover_generation, gen_calls, "gen"),
            ]:
                domain, dot_c, gt, calls = make_blackbox_counted(seed)
                try:
                    rec = method(domain, dot_c)
                    # Verify correctness
                    inv_gt = {v: k for k, v in gt.items()}
                    ok = all(inv_gt[rec[n]] == n for n in rec)
                    if ok:
                        calls_list.append(calls[0])
                    else:
                        if fail_count_ref == "beh":
                            beh_fail += 1
                        else:
                            gen_fail += 1
                except Exception:
                    if fail_count_ref == "beh":
                        beh_fail += 1
                    else:
                        gen_fail += 1

        print(f"\n{'Method':<14s} {'Pass':>6s} {'Mean':>8s} {'Min':>6s} {'Max':>6s}")
        print("-" * 42)
        for label, cl, fl in [("behavioral", beh_calls, beh_fail),
                               ("generation", gen_calls, gen_fail)]:
            n = len(cl)
            if n:
                print(f"{label:<14s} {n:>5d}  {sum(cl)/n:>7.1f} {min(cl):>6d} {max(cl):>6d}")
            else:
                print(f"{label:<14s}     0       -      -      -")
            if fl:
                print(f"  ({fl} failures)")

        if beh_calls and gen_calls:
            saving = sum(beh_calls)/len(beh_calls) - sum(gen_calls)/len(gen_calls)
            pct = 100 * saving / (sum(beh_calls)/len(beh_calls))
            print(f"\nGeneration saves {saving:.1f} calls on average ({pct:.1f}%)")
        return

    if args.seeds > 0:
        # Batch mode
        print(f"Batch testing {args.seeds} seeds ({args.method})...")
        failures = []
        for seed in range(1, args.seeds + 1):
            try:
                domain, dot, gt = make_blackbox(seed)
                rec = recover_fn(domain, dot)
                inv_gt = {v: k for k, v in gt.items()}
                for name, hidden in rec.items():
                    if inv_gt[hidden] != name:
                        failures.append((seed, name, inv_gt[hidden]))
                        break
                results = verify_axioms(dot, rec)
                for check_name, passed in results:
                    if not passed:
                        failures.append((seed, f"verify:{check_name}", "FAIL"))
                        break
            except Exception as e:
                failures.append((seed, "EXCEPTION", str(e)))

        passed = args.seeds - len(failures)
        print(f"Results: {passed}/{args.seeds} passed ({100*passed/args.seeds:.1f}%)")
        if failures:
            print(f"Failures:")
            for seed, name, info in failures[:10]:
                print(f"  seed {seed}: {name} → {info}")
        else:
            print("All seeds passed — 100% recovery + verification.")
        return

    # Single-seed demo
    method_label = "Generation" if args.method == "generation" else "12-Step Behavioral"
    print(f"Ψ₁₆ᶠ Black-Box Recovery — {method_label} (seed={args.seed})")
    print("=" * 60)

    domain, dot_c, gt, calls = make_blackbox_counted(args.seed)
    print(f"\nDomain: {domain}")
    print(f"Ground truth (hidden): { {k: v for k, v in sorted(gt.items(), key=lambda x: x[1])} }")

    print(f"\n— {method_label} Recovery —")
    rec = recover_fn(domain, dot_c)

    text, all_correct = format_recovery(rec, gt)
    print(text)
    print(f"\nRecovery: {'ALL CORRECT' if all_correct else 'ERRORS DETECTED'}")
    print(f"Dot calls: {calls[0]}")

    print("\n— Axiom Verification —")
    results = verify_axioms(dot_c, rec)
    all_pass = True
    for name, passed in results:
        mark = "✓" if passed else "✗"
        if not passed:
            all_pass = False
        print(f"  {mark} {name}")
    print(f"\nVerification: {'ALL PASSED' if all_pass else 'FAILURES DETECTED'}")
    print(f"Total dot calls (recovery + verification): {calls[0]}")


if __name__ == "__main__":
    main()

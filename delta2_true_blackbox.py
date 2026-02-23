#!/usr/bin/env python3
"""
Δ₂ Discoverability Demo — True Black-Box Recovery

This version fixes a critical flaw in the original: the recovery algorithm
no longer uses ground truth (true2hid) to identify p. All 21 atoms are
recovered purely from behavioral probing.

The fix: after identifying booleans and testers, p is discovered as the
unique non-boolean, non-tester element whose left-image contains ⊤.
This works because of Rule 19 (p · ⊤ = ⊤), which is the absorption
breaker — and no other non-boolean, non-tester element produces ⊤
as a left-output on any atom input.

Usage:
  python delta2_true_blackbox.py
  python delta2_true_blackbox.py --seed 42
"""

from dataclasses import dataclass
from typing import Any, Dict, List, Set, Tuple
import random
import itertools
import argparse


# ============================================================================
# Runtime term representations
# ============================================================================

@dataclass(frozen=True)
class Atom:
    name: str

@dataclass(frozen=True)
class Quote:
    term: Any

@dataclass(frozen=True)
class AppNode:
    f: Any
    x: Any

@dataclass(frozen=True)
class UnappBundle:
    f: Any
    x: Any

@dataclass(frozen=True)
class Partial:
    op: str
    a: Any


def A(n: str) -> Atom:
    return Atom(n)


# ============================================================================
# Atom inventory
# ============================================================================

NAMES_D1 = [
    "⊤", "⊥", "i", "k", "a", "b", "e_I",
    "e_D", "e_M", "e_Σ", "e_Δ",
    "d_I", "d_K", "m_I", "m_K", "s_C", "p",
]
NAMES_D2 = ["QUOTE", "EVAL", "APP", "UNAPP"]
ALL_ATOMS = [A(n) for n in (NAMES_D1 + NAMES_D2)]


# ============================================================================
# Δ₁ core: directed application on atoms
# ============================================================================

def dot_iota_d1(x: Atom, y: Atom) -> Atom:
    TOP, BOT = A("⊤"), A("⊥")
    if x == TOP: return TOP
    if x == BOT: return BOT
    if x == A("e_I"): return TOP if y in (A("i"), A("k")) else BOT
    if x == A("d_K"): return TOP if y in (A("a"), A("b")) else BOT
    if x == A("m_K"): return TOP if y == A("a") else BOT
    if x == A("m_I"): return BOT if y == A("p") else TOP
    if x == A("e_D") and y == A("i"): return A("d_I")
    if x == A("e_D") and y == A("k"): return A("d_K")
    if x == A("e_M") and y == A("i"): return A("m_I")
    if x == A("e_M") and y == A("k"): return A("m_K")
    if x == A("e_Σ") and y == A("s_C"): return A("e_Δ")
    if x == A("e_Δ") and y == A("e_D"): return A("d_I")
    if x == A("p") and y == TOP: return TOP
    if y == TOP and x in (A("i"), A("k"), A("a"), A("b"), A("d_I"), A("s_C")):
        return x
    return A("p")


# ============================================================================
# Δ₂ extension
# ============================================================================

def eval_term(t: Any) -> Any:
    if isinstance(t, Atom): return t
    if isinstance(t, Quote): return t
    if isinstance(t, AppNode):
        return dot_iota(eval_term(t.f), eval_term(t.x))
    return A("p")


def dot_iota(x: Any, y: Any) -> Any:
    if isinstance(x, Partial):
        return AppNode(x.a, y) if x.op == "APP" else A("p")
    if x == A("QUOTE"): return Quote(y)
    if x == A("APP"): return Partial("APP", y)
    if x == A("UNAPP"):
        return UnappBundle(y.f, y.x) if isinstance(y, AppNode) else A("p")
    if isinstance(x, UnappBundle):
        if y == A("⊤"): return x.f
        if y == A("⊥"): return x.x
        return A("p")
    if x == A("EVAL"):
        return eval_term(y.term) if isinstance(y, Quote) else A("p")
    if isinstance(y, Quote):
        return A("p")
    if isinstance(x, Atom) and isinstance(y, Atom):
        return dot_iota_d1(x, y)
    return A("p")


# ============================================================================
# Black-box wrapper
# ============================================================================

def make_blackbox(seed: int = 11):
    rng = random.Random(seed)
    atoms = ALL_ATOMS.copy()
    rng.shuffle(atoms)
    labels = [f"u{idx:02d}" for idx in range(len(atoms))]
    true_to_hidden = {atoms[i]: labels[i] for i in range(len(atoms))}
    hidden_to_true = {labels[i]: atoms[i] for i in range(len(atoms))}
    domain = labels.copy()

    def dot_oracle(xh: Any, yh: Any) -> Any:
        def to_true(v):
            return hidden_to_true[v] if isinstance(v, str) and v in hidden_to_true else v
        def to_hidden(v):
            return true_to_hidden[v] if isinstance(v, Atom) else v
        return to_hidden(dot_iota(to_true(xh), to_true(yh)))

    return domain, dot_oracle, true_to_hidden


# ============================================================================
# Phase 1: Discover Δ₁ primitives — TRUE BLACK-BOX (no ground truth)
# ============================================================================

def discover_d1(domain: List[str], dot) -> Dict[str, Any]:
    """
    Recover all 17 Δ₁ atoms from black-box probing.
    
    NO ground truth is used. Every identification is purely behavioral.
    
    The 8-step recovery procedure:
      1. Find booleans (unique left-absorbers)
      2. Find testers (non-boolean elements with boolean-only left-image)
      2.5 Find p (unique non-boolean, non-tester with ⊤ in left-image)
      3. Identify testers by decoded-set cardinality
      4. Distinguish e_I from d_K (rich vs inert right-arguments)
      5. Find e_D and e_M (non-trivial encoders on context tokens)
      6. Distinguish i from k (actuality code cardinality)
      7. Identify remaining elements (a, b, d_I)
      8. Find e_Σ, s_C, e_Δ (unique triple with synthesis + verification)
    """

    def left_image(xh):
        """All outputs of dot(x, ·) restricted to domain elements."""
        return {dot(xh, y) for y in domain}

    def left_image_in_domain(xh):
        """Left-image filtered to outputs that are domain atoms."""
        return {dot(xh, y) for y in domain if dot(xh, y) in domain}

    # ── Step 1: Find booleans ──────────────────────────────────────────
    # Unique property: dot(x, y) = x for all y (left-absorbers)
    absorbers = [x for x in domain if all(dot(x, y) == x for y in domain)]
    assert len(absorbers) == 2, f"Expected 2 absorbers, got {len(absorbers)}"
    B1, B2 = absorbers

    # ── Step 2: Find testers ──────────────────────────────────────────
    # Non-boolean elements whose left-image is exactly {⊤, ⊥}
    def testers_for(top, bot):
        out = []
        for x in domain:
            if x in (top, bot):
                continue
            im = left_image(x)
            if im.issubset({top, bot}) and len(im) == 2:
                out.append(x)
        return out

    # Orient booleans: choose top/bot labeling where tester cardinalities
    # give the expected signature [1, 2, 2, 16+]
    chosen = None
    for top, bot in [(B1, B2), (B2, B1)]:
        testers = testers_for(top, bot)
        if len(testers) != 4:
            continue
        Dec = lambda t, top=top: {y for y in domain if dot(t, y) == top}
        sizes = sorted(len(Dec(t)) for t in testers)
        if sizes[0] == 1 and sizes[1] == 2 and sizes[2] == 2:
            chosen = (top, bot, testers, Dec)
            break
    assert chosen is not None, "Failed to orient booleans"
    top, bot, testers, Dec = chosen

    # ── Step 2.5: Find p (the default/sink element) ───────────────────
    # p is the UNIQUE non-boolean, non-tester element whose left-image
    # (restricted to domain) contains top.
    #
    # Why: Rule 19 (p · ⊤ = ⊤) makes p the only such element.
    # - Passive elements: Im_L = {self, p}. No ⊤.
    # - Encoders (e_D, e_M, e_Σ, e_Δ): Im_L = {codes, p}. No ⊤.
    # - QUOTE, APP: produce structured values, Im_L ∩ domain = ∅.
    # - EVAL, UNAPP: produce only p on atom inputs.
    p_candidates = [
        x for x in domain
        if x not in (top, bot) and x not in testers
        and top in left_image_in_domain(x)
    ]
    assert len(p_candidates) == 1, (
        f"Expected exactly 1 p-candidate, got {len(p_candidates)}: {p_candidates}"
    )
    p_tok = p_candidates[0]

    # ── Step 3: Identify testers by cardinality ───────────────────────
    sizes = {t: len(Dec(t)) for t in testers}
    # m_K: Dec size 1 (accepts only a)
    m_K = [t for t in testers if sizes[t] == 1][0]
    # m_I: largest Dec (accepts everything except p)
    m_I = max(testers, key=lambda t: sizes[t])
    # Two testers with Dec size 2: e_I and d_K
    two = [t for t in testers if sizes[t] == 2]
    assert len(two) == 2, f"Expected 2 testers with |Dec|=2, got {len(two)}"

    # ── Step 4: Distinguish e_I from d_K ──────────────────────────────
    # Dec(e_I) = {i, k} contains "productive" right-arguments:
    #   some non-tester f has dot(f, ctx_token) ∉ {⊤, ⊥, p}
    # Dec(d_K) = {a, b} does NOT (all non-testers map them to {⊤, ⊥, p})
    def has_productive_args(decoded_set):
        for f in domain:
            if f in (top, bot) or f in testers:
                continue
            for x in decoded_set:
                out = dot(f, x)
                if out in domain and out not in (top, bot, p_tok):
                    return True
        return False

    t1, t2 = two
    e_I, d_K = (t1, t2) if has_productive_args(Dec(t1)) else (t2, t1)
    ctx = list(Dec(e_I))  # {i, k} in some order

    # ── Step 5: Find e_D and e_M ─────────────────────────────────────
    # These are the only elements that map BOTH context tokens to
    # non-trivial (non-boolean, non-p) domain outputs.
    def is_encoder(f):
        if f in (top, bot) or f in testers:
            return False
        outs = [dot(f, x) for x in ctx]
        return (all(o in domain for o in outs) and
                all(o not in (top, bot, p_tok) for o in outs))

    enc = [f for f in domain if is_encoder(f)]
    assert len(enc) == 2, f"Expected 2 encoders, got {len(enc)}"

    # e_M maps both context tokens to TESTERS (m_I, m_K)
    # e_D maps to a MIXED pair (d_I is not a tester, d_K is)
    def maps_both_to_testers(f):
        return all(dot(f, x) in testers for x in ctx)

    e_M = enc[0] if maps_both_to_testers(enc[0]) else enc[1]
    e_D = enc[1] if e_M == enc[0] else enc[0]

    # ── Step 6: Distinguish i from k ─────────────────────────────────
    # e_M · i = m_I (Dec size 16+), e_M · k = m_K (Dec size 1)
    outA, outB = dot(e_M, ctx[0]), dot(e_M, ctx[1])
    if len(Dec(outA)) > len(Dec(outB)):
        i_tok, k_tok = ctx[0], ctx[1]
    else:
        i_tok, k_tok = ctx[1], ctx[0]

    # ── Step 7: Identify a, b, d_I ───────────────────────────────────
    ab = list(Dec(d_K))  # {a, b} in some order
    a_tok = next(x for x in ab if dot(m_K, x) == top)
    b_tok = next(x for x in ab if x != a_tok)
    d_I = dot(e_D, i_tok)

    # ── Step 8: Find e_Σ, s_C, e_Δ ──────────────────────────────────
    # Unique triple (f, g, h) among remaining elements where:
    #   dot(f, g) = h  AND  dot(h, e_D) = d_I
    known = {top, bot, e_I, d_K, m_K, m_I, e_M, e_D,
             i_tok, k_tok, a_tok, b_tok, d_I, p_tok}
    remaining = [x for x in domain if x not in known]

    e_S = sC = e_Delta = None
    for f, g in itertools.product(remaining, repeat=2):
        h = dot(f, g)
        if h not in domain or h in (top, bot, p_tok):
            continue
        if dot(h, e_D) == d_I:
            e_S, sC, e_Delta = f, g, h
            break
    assert e_S is not None, "Failed to recover e_Σ/s_C/e_Δ"

    return {
        "⊤": top, "⊥": bot, "p": p_tok,
        "e_I": e_I, "e_D": e_D, "e_M": e_M, "e_Σ": e_S, "e_Δ": e_Delta,
        "i": i_tok, "k": k_tok, "a": a_tok, "b": b_tok,
        "d_I": d_I, "d_K": d_K, "m_I": m_I, "m_K": m_K, "s_C": sC,
        "_testers": set(testers),
    }


# ============================================================================
# Phase 2: Discover Δ₂ primitives — TRUE BLACK-BOX
# ============================================================================

def discover_d2(domain: List[str], dot, d1: Dict[str, Any]) -> Dict[str, Any]:
    """
    Recover QUOTE, EVAL, APP, UNAPP by probing behavior.
    No ground truth used — only behavioral signatures.
    """
    top, bot = d1["⊤"], d1["⊥"]
    testers = d1["_testers"]
    p_tok = d1["p"]

    # Candidates: everything not yet identified in d1
    d1_identified = {v for k, v in d1.items() if k != "_testers"}
    cand = [x for x in domain if x not in d1_identified]

    # Use full domain as probe set
    sample = domain

    # ── Find QUOTE and EVAL jointly ──────────────────────────────────
    # QUOTE: produces many structured (non-domain) outputs
    # EVAL: inverts QUOTE on atoms — dot(e, dot(q, x)) == x
    QUOTE = EVAL = None
    for q in cand:
        structured = sum(1 for x in sample if dot(q, x) not in domain)
        if structured < len(sample) // 2:
            continue
        for e in cand:
            if e == q:
                continue
            inv = sum(1 for x in sample if dot(e, dot(q, x)) == x)
            if inv >= len(sample) * 2 // 3:
                QUOTE, EVAL = q, e
                break
        if QUOTE:
            break
    assert QUOTE is not None, "Failed to recover QUOTE/EVAL"

    # ── Find APP and UNAPP ───────────────────────────────────────────
    # APP: curried constructor — dot(APP, f) produces a non-domain value,
    #   then dot(that, x) produces another non-domain value (AppNode)
    # UNAPP: opens AppNodes into bundles queryable by booleans
    cand2 = [x for x in cand if x not in (QUOTE, EVAL)]

    # Use a variety of known atoms as test arguments
    test_fs = [d1[k] for k in ["e_D", "e_M", "e_I", "d_K", "m_I", "e_Σ"]]
    test_xs = [d1[k] for k in ["i", "k", "a", "b", "s_C"]] + [top, bot]

    APP = UNAPP = None
    for app in cand2:
        for f in test_fs:
            mid = dot(app, f)
            if mid in domain:
                continue
            for x in test_xs:
                node = dot(mid, x)
                if node in domain:
                    continue
                for unapp in cand2:
                    if unapp == app:
                        continue
                    bundle = dot(unapp, node)
                    if bundle in domain:
                        continue
                    left = dot(bundle, top)
                    right = dot(bundle, bot)
                    if left != p_tok and right != p_tok and left != right:
                        APP, UNAPP = app, unapp
                        break
                if APP:
                    break
            if APP:
                break
        if APP:
            break
    assert APP is not None, "Failed to recover APP/UNAPP"

    return {"QUOTE": QUOTE, "EVAL": EVAL, "APP": APP, "UNAPP": UNAPP}


# ============================================================================
# Demo programs
# ============================================================================

def demo_eval_quote_app(dot, d1, d2):
    """eval(quote(app(e_D, k))) → d_K"""
    node = dot(dot(d2["APP"], d1["e_D"]), d1["k"])
    return dot(d2["EVAL"], dot(d2["QUOTE"], node))


def demo_unapp_inspect(dot, d1, d2):
    """Build app(e_D, k), decompose with UNAPP, query with booleans."""
    node = dot(dot(d2["APP"], d1["e_D"]), d1["k"])
    bundle = dot(d2["UNAPP"], node)
    left = dot(bundle, d1["⊤"])
    right = dot(bundle, d1["⊥"])
    return node, bundle, left, right


def demo_nested_eval(dot, d1, d2):
    """eval(quote(app(e_M, k))) → m_K"""
    node = dot(dot(d2["APP"], d1["e_M"]), d1["k"])
    return dot(d2["EVAL"], dot(d2["QUOTE"], node))


def demo_self_model_query(dot, d1, d2):
    """Use the self-model: e_D · k = d_K, then d_K · a = ⊤, d_K · i = ⊥."""
    domain_code = dot(d1["e_D"], d1["k"])
    membership = dot(domain_code, d1["a"])
    non_membership = dot(domain_code, d1["i"])
    return domain_code, membership, non_membership


# ============================================================================
# Verification: check recovered labels against ground truth
# ============================================================================

def verify(label: str, recovered: str, true2hid: Dict[Atom, str]) -> str:
    expected = true2hid[A(label)]
    return "✓" if recovered == expected else f"✗ (expected {expected})"


# ============================================================================
# Main
# ============================================================================

def main():
    parser = argparse.ArgumentParser(description="Δ₂ True Black-Box Recovery Demo")
    parser.add_argument("--seed", type=int, default=11, help="Random seed for shuffling")
    parser.add_argument("--seeds", type=int, default=0,
                        help="If > 0, run this many seeds and report pass/fail")
    args = parser.parse_args()

    if args.seeds > 0:
        # Batch mode: test many seeds
        print(f"Testing {args.seeds} seeds...")
        failures = []
        for seed in range(args.seeds):
            try:
                domain, dot, true2hid = make_blackbox(seed)
                d1 = discover_d1(domain, dot)
                d2 = discover_d2(domain, dot, d1)
                # Verify all identifications
                for k in ["⊤", "⊥", "e_I", "e_D", "e_M", "e_Σ", "e_Δ",
                          "i", "k", "a", "b", "d_I", "d_K", "m_I", "m_K",
                          "s_C", "p"]:
                    if d1[k] != true2hid[A(k)]:
                        failures.append((seed, k, "d1"))
                        break
                for k in ["QUOTE", "EVAL", "APP", "UNAPP"]:
                    if d2[k] != true2hid[A(k)]:
                        failures.append((seed, k, "d2"))
                        break
            except Exception as e:
                failures.append((seed, str(e), "crash"))
        if failures:
            print(f"FAILED on {len(failures)} seeds:")
            for seed, key, phase in failures[:10]:
                print(f"  seed={seed}: {phase} failed at {key}")
        else:
            print(f"All {args.seeds} seeds passed. ✓")
        return

    # Single seed demo mode
    domain, dot, true2hid = make_blackbox(args.seed)

    print("=" * 60)
    print("  Δ₂ TRUE BLACK-BOX RECOVERY DEMO")
    print("=" * 60)
    print(f"\nBlack-box seed: {args.seed}")
    print(f"Atom domain: {len(domain)} opaque labels")
    print(f"  (Δ₁ core: 17 atoms + Δ₂ extensions: 4 operators)")
    print(f"\nNO ground truth is used during recovery.")
    print(f"Ground truth is used ONLY for post-hoc verification (✓/✗).")

    # Phase 1 — no true2hid passed!
    print("\n" + "-" * 60)
    print("  PHASE 1: Recover Δ₁ primitives from behavior")
    print("-" * 60)
    d1 = discover_d1(domain, dot)
    for k in ["⊤", "⊥", "p", "e_I", "e_D", "e_M", "e_Σ", "e_Δ",
              "i", "k", "a", "b", "d_I", "d_K", "m_I", "m_K", "s_C"]:
        status = verify(k, d1[k], true2hid)
        print(f"  {k:4s} → {d1[k]}  {status}")

    # Phase 2
    print("\n" + "-" * 60)
    print("  PHASE 2: Recover Δ₂ primitives (QUOTE/EVAL/APP/UNAPP)")
    print("-" * 60)
    d2 = discover_d2(domain, dot, d1)
    for k in ["QUOTE", "EVAL", "APP", "UNAPP"]:
        status = verify(k, d2[k], true2hid)
        print(f"  {k:5s} → {d2[k]}  {status}")

    # Phase 3
    print("\n" + "-" * 60)
    print("  PHASE 3: Run programs using recovered primitives")
    print("-" * 60)

    out = demo_eval_quote_app(dot, d1, d2)
    print(f"\n  Program 1: eval(quote(app(e_D, k)))")
    print(f"    Result:   {out}")
    print(f"    Expected: {d1['d_K']}  (d_K)")
    print(f"    {'✓ Correct' if out == d1['d_K'] else '✗ MISMATCH'}")

    node, bundle, left, right = demo_unapp_inspect(dot, d1, d2)
    print(f"\n  Program 2: unapp(app(e_D, k)) → bundle, query with booleans")
    print(f"    bundle·⊤ = {left}  (expected e_D = {d1['e_D']})  "
          f"{'✓' if left == d1['e_D'] else '✗'}")
    print(f"    bundle·⊥ = {right}  (expected k = {d1['k']})  "
          f"{'✓' if right == d1['k'] else '✗'}")

    out3 = demo_nested_eval(dot, d1, d2)
    print(f"\n  Program 3: eval(quote(app(e_M, k)))")
    print(f"    Result:   {out3}")
    print(f"    Expected: {d1['m_K']}  (m_K)")
    print(f"    {'✓ Correct' if out3 == d1['m_K'] else '✗ MISMATCH'}")

    dc, mem, nonmem = demo_self_model_query(dot, d1, d2)
    print(f"\n  Program 4: Self-model query — is 'a' in D(κ)?")
    print(f"    e_D · k = {dc}  (domain code for κ)")
    print(f"    d_K · a = {mem}  (expected ⊤ = {d1['⊤']})  "
          f"{'✓' if mem == d1['⊤'] else '✗'}")
    print(f"    d_K · i = {nonmem}  (expected ⊥ = {d1['⊥']})  "
          f"{'✓' if nonmem == d1['⊥'] else '✗'}")

    print("\n" + "=" * 60)
    print("  All phases complete.")
    print("=" * 60)


if __name__ == "__main__":
    main()

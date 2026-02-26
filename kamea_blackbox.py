#!/usr/bin/env python3
"""
Δ₂+74181 Discoverability Demo — True Black-Box Recovery

Extends the 21-atom Δ₂ algebra with 26 new atoms for a 74181 ALU + IO extension:
  - 16 nibble atoms N0–NF (4-bit data values / operation selectors)
  - 3 ALU dispatch atoms (ALU_LOGIC, ALU_ARITH, ALU_ARITHC)
  - 2 predicate atoms (ALU_ZERO, ALU_COUT)
  - 1 nibble successor atom (N_SUCC)
  - 4 IO atoms (IO_PUT, IO_GET, IO_RDY, IO_SEQ) with all-p Cayley rows

Total: 47 atoms. All 47 are uniquely recoverable from black-box access
to the dot operation alone. Recovery proceeds in two phases:
  Phase 1a: Recover all 17 Δ₁ atoms from Cayley-level probing
  Phase 1b: Recover 22 extension atoms (nibbles, ALU, N_SUCC) from Cayley-level
  Phase 2:  Recover 8 opaque atoms (D2 + IO) via term-level probing

The 74181 chip's 32 operations are encoded as 3 dispatch atoms × 16
nibble selectors, invoked via curried application:
  (ALU-ARITH N9 a b)  →  A plus B

Usage:
  python delta2_74181_blackbox.py              # single-seed demo
  python delta2_74181_blackbox.py --seed 42    # specific seed
  python delta2_74181_blackbox.py --seeds 1000 # batch test
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

@dataclass(frozen=True)
class ALUPartial1:
    """ALU dispatch with selector applied, waiting for operand A."""
    mode: str       # "logic", "arith", "arithc"
    selector: int   # 0-15

@dataclass(frozen=True)
class ALUPartial2:
    """ALU dispatch with selector and operand A applied, waiting for B."""
    mode: str
    selector: int
    a: int          # 0-15

@dataclass(frozen=True)
class IOPutPartial:
    """IO_PUT with high nibble applied, awaiting low nibble."""
    hi: int  # high nibble 0-15

@dataclass(frozen=True)
class IOSeqPartial:
    """IO_SEQ with first action result applied, awaiting second."""
    first: Any


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
NAMES_NIBBLES = [f"N{i:X}" for i in range(16)]
NAMES_ALU_DISPATCH = ["ALU_LOGIC", "ALU_ARITH", "ALU_ARITHC"]
NAMES_ALU_PRED = ["ALU_ZERO", "ALU_COUT"]
NAMES_ALU_MISC = ["N_SUCC"]
NAMES_IO = ["IO_PUT", "IO_GET", "IO_RDY", "IO_SEQ"]

ALL_NAMES = (NAMES_D1 + NAMES_D2 + NAMES_NIBBLES +
             NAMES_ALU_DISPATCH + NAMES_ALU_PRED + NAMES_ALU_MISC + NAMES_IO)
ALL_ATOMS = [A(n) for n in ALL_NAMES]

NIBBLE_ATOMS = frozenset(A(f"N{i:X}") for i in range(16))
ALU_DISPATCH_ATOMS = frozenset(A(n) for n in NAMES_ALU_DISPATCH)
ALU_PRED_ATOMS = frozenset(A(n) for n in NAMES_ALU_PRED)
IO_ATOMS = frozenset(A(n) for n in NAMES_IO)
D1_ATOMS = frozenset(A(n) for n in NAMES_D1)
D2_EXT_ATOMS = frozenset(A(n) for n in NAMES_D2)


# ============================================================================
# Nibble helpers
# ============================================================================

def is_nibble(x: Any) -> bool:
    return isinstance(x, Atom) and x in NIBBLE_ATOMS

def nibble_val(x: Atom) -> int:
    return int(x.name[1:], 16)

def nibble(n: int) -> Atom:
    return A(f"N{n % 16:X}")


# ============================================================================
# 74181 ALU computation
# ============================================================================

def alu_74181(mode: str, selector: int, a: int, b: int) -> tuple:
    """
    Compute one 74181 operation.

    Args:
        mode: "logic", "arith", or "arithc"
        selector: 0-15 (S0-S3)
        a: 0-15 (4-bit input A)
        b: 0-15 (4-bit input B)

    Returns:
        (result: 0-15, carry_out: bool, zero: bool)
    """
    assert 0 <= selector <= 15 and 0 <= a <= 15 and 0 <= b <= 15

    if mode == "logic":
        result = _alu_logic(selector, a, b)
        return (result, False, result == 0)

    carry_in = 1 if mode == "arithc" else 0
    result, carry_out = _alu_arith(selector, a, b, carry_in)
    return (result, carry_out, result == 0)


def _alu_logic(selector: int, a: int, b: int) -> int:
    """Compute 74181 logic operation (active-high)."""
    result = 0
    for bit in range(4):
        ai = (a >> bit) & 1
        bi = (b >> bit) & 1
        result |= (_logic_bit(selector, ai, bi) << bit)
    return result & 0xF


def _logic_bit(selector: int, ai: int, bi: int) -> int:
    """Compute one bit of the 74181 logic function (active-high)."""
    na, nb = 1 - ai, 1 - bi
    _table = [
        na,              # 0: NOT A
        1 - (ai | bi),   # 1: NOR
        na & bi,          # 2: (NOT A) AND B
        0,                # 3: Logical 0
        1 - (ai & bi),   # 4: NAND
        nb,              # 5: NOT B
        ai ^ bi,          # 6: XOR
        ai & nb,          # 7: A AND (NOT B)
        na | bi,          # 8: (NOT A) OR B
        1 - (ai ^ bi),   # 9: XNOR
        bi,              # A: B
        ai & bi,          # B: A AND B
        1,                # C: Logical 1
        ai | nb,          # D: A OR (NOT B)
        ai | bi,          # E: A OR B
        ai,              # F: A
    ]
    return _table[selector]


def _alu_arith(selector: int, a: int, b: int, carry_in: int) -> tuple:
    """Compute 74181 arithmetic operation (active-high).

    Returns (result: 0-15, carry_out: bool)
    """
    nb = (~b) & 0xF
    base_table = [
        a,                      # 0: A
        a | b,                  # 1: A OR B
        a | nb,                 # 2: A OR (NOT B)
        0xF,                    # 3: minus 1 (all ones)
        a + (a & nb),           # 4: A plus (A AND NOT B)
        (a | b) + (a & nb),     # 5: (A OR B) plus (A AND NOT B)
        a + nb,                 # 6: A minus B minus 1
        (a & nb) + 0xF,         # 7: (A AND NOT B) minus 1
        a + (a & b),            # 8: A plus (A AND B)
        a + b,                  # 9: A plus B
        (a | nb) + (a & b),     # A: (A OR NOT B) plus (A AND B)
        (a & b) + 0xF,          # B: (A AND B) minus 1
        a + a,                  # C: A plus A (left shift)
        (a | b) + a,            # D: (A OR B) plus A
        (a | nb) + a,           # E: (A OR NOT B) plus A
        a + 0xF,                # F: A minus 1
    ]
    raw = base_table[selector] + carry_in
    result = raw & 0xF
    carry_out = bool(raw > 0xF)
    return (result, carry_out)


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
# Atom-atom Cayley table (47 × 47)
# ============================================================================

def atom_dot(x: Atom, y: Atom) -> Atom:
    """Cayley table for all 47 atoms.

    Design principles:
    - Preserves all 21×21 original D1/D2 entries exactly
    - D1 atoms use dot_iota_d1 for ALL right arguments (testers stay pure boolean)
    - Nibbles form Z/16Z under addition mod 16
    - ALU dispatch: identity/successor/double-successor on nibbles
    - ALU predicates: tester-like on nibbles, self-id on ⊤
    - N_SUCC: successor on nibbles, reset on ⊥
    - IO atoms: all-p rows (effects happen at term level)
    """
    TOP, BOT = A("⊤"), A("⊥")

    # ── D1 atom on left: dot_iota_d1 for ALL right arguments ──
    if x in D1_ATOMS:
        return dot_iota_d1(x, y)

    # ── D2 atoms × anything: atom-level fallback is p ──
    if x in D2_EXT_ATOMS:
        return A("p")

    # ── IO atoms × anything: all-p (effects happen at term level) ──
    if x in IO_ATOMS:
        return A("p")

    # ── Nibble self-identification on ⊤ ──
    if is_nibble(x) and y == TOP:
        return x

    # ── Nibble × Nibble: Z/16Z under addition ──
    if is_nibble(x) and is_nibble(y):
        return nibble((nibble_val(x) + nibble_val(y)) % 16)

    # ── ALU dispatch self-identification on ⊤ ──
    if x in ALU_DISPATCH_ATOMS and y == TOP:
        return x

    # ── ALU dispatch × Nibble: distinguishing mappings ──
    if x == A("ALU_LOGIC") and is_nibble(y):
        return y  # identity
    if x == A("ALU_ARITH") and is_nibble(y):
        return nibble((nibble_val(y) + 1) % 16)  # successor
    if x == A("ALU_ARITHC") and is_nibble(y):
        return nibble((nibble_val(y) + 2) % 16)  # double successor

    # ── ALU predicate self-identification on ⊤ ──
    if x in ALU_PRED_ATOMS and y == TOP:
        return x

    # ── ALU_ZERO: tester on nibbles ──
    if x == A("ALU_ZERO") and is_nibble(y):
        return TOP if y == A("N0") else BOT

    # ── ALU_COUT: tester on nibbles (high bit = carry) ──
    if x == A("ALU_COUT") and is_nibble(y):
        return TOP if nibble_val(y) >= 8 else BOT

    # ── N_SUCC: successor on nibbles (16-cycle) ──
    if x == A("N_SUCC") and y == TOP:
        return x
    if x == A("N_SUCC") and y == BOT:
        return A("N0")  # reset on ⊥ (distinguishes from ALU_ARITH at atom level)
    if x == A("N_SUCC") and is_nibble(y):
        return nibble((nibble_val(y) + 1) % 16)

    # ── Default ──
    return A("p")


# ============================================================================
# Extended dot operation (full term-level)
# ============================================================================

def eval_term(t: Any) -> Any:
    if isinstance(t, Atom): return t
    if isinstance(t, Quote): return t
    if isinstance(t, AppNode):
        return dot_iota(eval_term(t.f), eval_term(t.x))
    return A("p")


def dot_iota(x: Any, y: Any) -> Any:
    """The full Δ₂+74181 operation on terms."""

    # --- Partial applications (inherited from Δ₂) ---
    if isinstance(x, Partial):
        return AppNode(x.a, y) if x.op == "APP" else A("p")

    # --- ALUPartial1: dispatch + selector applied, waiting for operand A ---
    if isinstance(x, ALUPartial1):
        if isinstance(y, Atom) and is_nibble(y):
            return ALUPartial2(x.mode, x.selector, nibble_val(y))
        return A("p")

    # --- ALUPartial2: dispatch + selector + A applied, waiting for B ---
    if isinstance(x, ALUPartial2):
        if isinstance(y, Atom) and is_nibble(y):
            result, carry, zero = alu_74181(x.mode, x.selector, x.a, nibble_val(y))
            return nibble(result)
        return A("p")

    # --- QUOTE ---
    if x == A("QUOTE"): return Quote(y)

    # --- APP ---
    if x == A("APP"): return Partial("APP", y)

    # --- UNAPP ---
    if x == A("UNAPP"):
        return UnappBundle(y.f, y.x) if isinstance(y, AppNode) else A("p")

    # --- Bundle queries ---
    if isinstance(x, UnappBundle):
        if y == A("⊤"): return x.f
        if y == A("⊥"): return x.x
        return A("p")

    # --- EVAL ---
    if x == A("EVAL"):
        return eval_term(y.term) if isinstance(y, Quote) else A("p")

    # --- ALU dispatch atoms: first application produces ALUPartial1 ---
    if x == A("ALU_LOGIC") and isinstance(y, Atom) and is_nibble(y):
        return ALUPartial1("logic", nibble_val(y))
    if x == A("ALU_ARITH") and isinstance(y, Atom) and is_nibble(y):
        return ALUPartial1("arith", nibble_val(y))
    if x == A("ALU_ARITHC") and isinstance(y, Atom) and is_nibble(y):
        return ALUPartial1("arithc", nibble_val(y))

    # --- ALU_ZERO on nibble at term level ---
    if x == A("ALU_ZERO") and isinstance(y, Atom) and is_nibble(y):
        return A("⊤") if y == A("N0") else A("⊥")

    # --- ALU_COUT on nibble at term level ---
    if x == A("ALU_COUT") and isinstance(y, Atom) and is_nibble(y):
        return A("⊤") if nibble_val(y) >= 8 else A("⊥")

    # --- IO_PUT + nibble → IOPutPartial ---
    if x == A("IO_PUT") and isinstance(y, Atom) and is_nibble(y):
        return IOPutPartial(nibble_val(y))

    # --- IOPutPartial + nibble → ⊤ (pure: no actual stdout write) ---
    if isinstance(x, IOPutPartial):
        if isinstance(y, Atom) and is_nibble(y):
            return A("⊤")
        return A("p")

    # --- IO_GET + ⊤ → p (pure: no actual stdin read) ---
    if x == A("IO_GET"):
        if y == A("⊤"):
            return A("p")

    # --- IO_RDY + ⊤ → ⊤ ---
    if x == A("IO_RDY"):
        if y == A("⊤"):
            return A("⊤")

    # --- IO_SEQ + any → IOSeqPartial ---
    if x == A("IO_SEQ"):
        return IOSeqPartial(y)

    # --- IOSeqPartial + any → return right (effects already fired) ---
    if isinstance(x, IOSeqPartial):
        return y

    # --- Atoms acting on non-atom structured terms → p ---
    if isinstance(x, Atom) and not isinstance(y, Atom):
        return A("p")

    # --- Atom × Atom: Cayley table ---
    if isinstance(x, Atom) and isinstance(y, Atom):
        return atom_dot(x, y)

    # --- Default ---
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
      2.5 Find p (unique non-boolean, non-tester with dot(x,⊤)=⊤)
      3. Identify testers by decoded-set cardinality
      4. Distinguish e_I from d_K (rich vs inert right-arguments)
      5. Find e_D and e_M (non-trivial encoders on context tokens)
      6. Distinguish i from k (actuality code cardinality)
      7. Identify remaining elements (a, b, d_I)
      8. Find e_Σ, s_C, e_Δ (unique triple with synthesis + verification)
    """

    def left_image(xh):
        return {dot(xh, y) for y in domain}

    def left_image_in_domain(xh):
        return {dot(xh, y) for y in domain if dot(xh, y) in domain}

    # ── Step 1: Find booleans ──
    absorbers = [x for x in domain if all(dot(x, y) == x for y in domain)]
    assert len(absorbers) == 2, f"Expected 2 absorbers, got {len(absorbers)}"
    B1, B2 = absorbers

    # ── Step 2: Find testers ──
    def testers_for(top, bot):
        out = []
        for x in domain:
            if x in (top, bot):
                continue
            im = left_image(x)
            if im.issubset({top, bot}) and len(im) == 2:
                out.append(x)
        return out

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

    # ── Step 3: Identify testers by cardinality (moved before p-detection) ──
    sizes = {t: len(Dec(t)) for t in testers}
    m_K = [t for t in testers if sizes[t] == 1][0]
    m_I = max(testers, key=lambda t: sizes[t])
    two = [t for t in testers if sizes[t] == 2]
    assert len(two) == 2

    # ── Step 2.5: Find p ──
    # p is the unique non-boolean, non-tester element where dot(x, ⊤) = ⊤
    # AND dot(m_I, x) = ⊥ (m_I maps only p to ⊥; all others to ⊤).
    p_candidates = [
        x for x in domain
        if x not in (top, bot) and x not in testers
        and dot(x, top) == top
        and dot(m_I, x) == bot
    ]
    assert len(p_candidates) == 1, (
        f"Expected exactly 1 p-candidate, got {len(p_candidates)}"
    )
    p_tok = p_candidates[0]

    # ── Step 4: Distinguish e_I from d_K ──
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
    ctx = list(Dec(e_I))

    # ── Step 5: Find e_D and e_M ──
    def is_encoder(f):
        if f in (top, bot) or f in testers:
            return False
        outs = [dot(f, x) for x in ctx]
        return (all(o in domain for o in outs) and
                all(o not in (top, bot, p_tok) for o in outs))

    enc = [f for f in domain if is_encoder(f)]
    assert len(enc) == 2, f"Expected 2 encoders, got {len(enc)}"

    def maps_both_to_testers(f):
        return all(dot(f, x) in testers for x in ctx)

    e_M = enc[0] if maps_both_to_testers(enc[0]) else enc[1]
    e_D = enc[1] if e_M == enc[0] else enc[0]

    # ── Step 6: Distinguish i from k ──
    outA, outB = dot(e_M, ctx[0]), dot(e_M, ctx[1])
    if len(Dec(outA)) > len(Dec(outB)):
        i_tok, k_tok = ctx[0], ctx[1]
    else:
        i_tok, k_tok = ctx[1], ctx[0]

    # ── Step 7: Identify a, b, d_I ──
    ab = list(Dec(d_K))
    a_tok = next(x for x in ab if dot(m_K, x) == top)
    b_tok = next(x for x in ab if x != a_tok)
    d_I = dot(e_D, i_tok)

    # ── Step 8: Find e_Σ, s_C, e_Δ ──
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
    """Recover QUOTE, EVAL, APP, UNAPP by probing behavior."""
    top, bot = d1["⊤"], d1["⊥"]
    testers = d1["_testers"]
    p_tok = d1["p"]

    d1_identified = {v for k, v in d1.items() if k != "_testers"}
    cand = [x for x in domain if x not in d1_identified]
    sample = domain

    # ── Find QUOTE and EVAL jointly ──
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

    # ── Find APP and UNAPP ──
    cand2 = [x for x in cand if x not in (QUOTE, EVAL)]
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
# Phase 3: Discover 74181 extension atoms — TRUE BLACK-BOX
# ============================================================================

def discover_74181_with_logs(domain: List[str], dot, d1: Dict[str, Any],
                             verbose: bool = False) -> Tuple[Dict[str, Any], List[str]]:
    """
    Phase 1b: Recover 22 new atoms from Cayley-level probing and separate
    8 opaque (all-p) atoms for Phase 2 term-level recovery.

    Returns:
        (ext_dict, opaque_list): ext_dict maps atom names to hidden labels
        for the 22 identifiable atoms; opaque_list contains the 8 hidden
        labels with identical all-p Cayley rows (D2 + IO atoms).
    """
    top = d1["⊤"]
    bot = d1["⊥"]
    p_tok = d1["p"]

    def log(msg):
        if verbose:
            print(f"    [Phase 1b] {msg}")

    d1_identified = {v for k, v in d1.items() if k != "_testers"}
    remaining = [x for x in domain if x not in d1_identified]
    assert len(remaining) == 30, f"Expected 30 remaining atoms, got {len(remaining)}"
    log(f"Starting with {len(remaining)} unidentified atoms")

    # ── Step 0: Compute domain-restricted left images ─────────────────
    domain_set = set(domain)

    def left_image(x):
        return {r for r in [dot(x, y) for y in domain] if isinstance(r, str) and r in domain_set}

    # ── Step 1: Identify predicate atoms ──────────────────────────────
    predicates = []
    for x in remaining:
        li = left_image(x)
        if top in li and bot in li and x in li:
            predicates.append(x)

    assert len(predicates) == 2, f"Expected 2 predicates, got {len(predicates)}"
    log(f"Predicates identified: {predicates}")

    # ── Step 2: Separate nibbles from non-nibbles ─────────────────────
    non_pred = [x for x in remaining if x not in predicates]
    non_pred_set = set(non_pred)
    nibbles = []
    non_nibbles = []
    for x in non_pred:
        xx = dot(x, x)
        if isinstance(xx, str) and xx in non_pred_set and xx != p_tok:
            nibbles.append(x)
        else:
            non_nibbles.append(x)

    assert len(nibbles) == 16, f"Expected 16 nibbles, got {len(nibbles)}"
    log(f"Nibbles: {len(nibbles)}, Non-nibbles: {len(non_nibbles)}")

    # ── Step 3: Identify N_SUCC ───────────────────────────────────────
    nibble_set = set(nibbles)
    n_succ_tok = None
    non_nibble_rest = []
    for x in non_nibbles:
        images = [dot(x, n) for n in nibbles]
        maps_all_to_nibbles = all(isinstance(img, str) and img in nibble_set for img in images)
        if maps_all_to_nibbles and len(set(images)) == 16:
            n_succ_tok = x
        else:
            non_nibble_rest.append(x)

    assert n_succ_tok is not None, "Failed to identify N_SUCC"
    log(f"N_SUCC identified: {n_succ_tok}")

    # ── Step 4: Distinguish ALU_ZERO from ALU_COUT ────────────────────
    pred_a, pred_b = predicates
    dec_a = sum(1 for n in nibbles if dot(pred_a, n) == top)
    dec_b = sum(1 for n in nibbles if dot(pred_b, n) == top)

    if dec_a == 1:
        alu_zero_tok, alu_cout_tok = pred_a, pred_b
    else:
        alu_zero_tok, alu_cout_tok = pred_b, pred_a
    log(f"ALU_ZERO identified: {alu_zero_tok} (accepts {min(dec_a, dec_b)} nibbles)")
    log(f"ALU_COUT identified: {alu_cout_tok} (accepts {max(dec_a, dec_b)} nibbles)")

    # ── Step 5: Find N0 (anchor via ALU_ZERO) ─────────────────────────
    n0_candidates = [n for n in nibbles if dot(alu_zero_tok, n) == top]
    assert len(n0_candidates) == 1, f"Expected 1 N0, got {len(n0_candidates)}"
    n0_tok = n0_candidates[0]
    log(f"N0 identified: {n0_tok}")

    # ── Step 6: Order all 16 nibbles by walking N_SUCC from N0 ────────
    nibble_order = [n0_tok]
    current = n0_tok
    for _ in range(15):
        current = dot(n_succ_tok, current)
        nibble_order.append(current)
    assert len(set(nibble_order)) == 16, "Nibble ordering failed"
    log(f"Nibble order: N0={nibble_order[0]}, N1={nibble_order[1]}, ..., NF={nibble_order[15]}")

    # ── Step 7: Separate dispatch from opaque, then identify dispatch ─
    # Dispatch atoms self-identify on ⊤: dot(x, ⊤) == x.
    # D2/IO atoms produce structured values or p when applied to ⊤.
    dispatch = []
    opaque = []
    for x in non_nibble_rest:
        if dot(x, top) == x:
            dispatch.append(x)
        else:
            opaque.append(x)

    assert len(dispatch) == 3, f"Expected 3 dispatch, got {len(dispatch)}"
    assert len(opaque) == 8, f"Expected 8 opaque (D2+IO) atoms, got {len(opaque)}"

    # Identify ALU_LOGIC / ALU_ARITH / ALU_ARITHC via curried probe
    n0 = nibble_order[0]
    n5 = nibble_order[5]
    na = nibble_order[10]
    n6 = nibble_order[6]

    alu_logic_tok = alu_arith_tok = alu_arithc_tok = None
    for d in dispatch:
        partial1 = dot(d, n0)
        partial2 = dot(partial1, n5)
        result = dot(partial2, n0)

        if result == na:
            alu_logic_tok = d
        elif result == n5:
            alu_arith_tok = d
        elif result == n6:
            alu_arithc_tok = d

    assert alu_logic_tok is not None, "Failed to identify ALU_LOGIC"
    assert alu_arith_tok is not None, "Failed to identify ALU_ARITH"
    assert alu_arithc_tok is not None, "Failed to identify ALU_ARITHC"
    log(f"ALU_LOGIC identified: {alu_logic_tok}")
    log(f"ALU_ARITH identified: {alu_arith_tok}")
    log(f"ALU_ARITHC identified: {alu_arithc_tok}")
    log(f"Opaque (D2+IO) atoms: {len(opaque)} — deferred to Phase 2")

    result = {}
    for i in range(16):
        result[f"N{i:X}"] = nibble_order[i]
    result["N_SUCC"] = n_succ_tok
    result["ALU_LOGIC"] = alu_logic_tok
    result["ALU_ARITH"] = alu_arith_tok
    result["ALU_ARITHC"] = alu_arithc_tok
    result["ALU_ZERO"] = alu_zero_tok
    result["ALU_COUT"] = alu_cout_tok

    log(f"Phase 1b complete: {len(result)} atoms identified, {len(opaque)} opaque remain")
    return result, opaque


# ============================================================================
# Phase 2: Term-level recovery of 8 opaque atoms (D2 + IO)
# ============================================================================

def discover_phase2(opaque: List[str], dot, d1: Dict[str, Any],
                    ext: Dict[str, Any], verbose: bool = False) -> Dict[str, Any]:
    """
    Phase 2: Identify all 8 opaque atoms via term-level probing.

    These 8 atoms have identical all-p Cayley rows and are indistinguishable
    at the atom-atom level. Term-level application reveals their identities:

      Step 1: Apply each to N0 → identifies QUOTE (produces Quote),
              EVAL (returns atom unchanged), and partitions the rest
              into partial group (APP, IO_PUT, IO_SEQ) and p group
              (UNAPP, IO_GET, IO_RDY).
      Step 2: Resolve partial group via partial(N0)(N1).
      Step 3: Resolve p group via application to ⊤.
      Step 4: Confirm UNAPP via AppNode destructure; IO_GET by exclusion.
    """
    assert len(opaque) == 8, f"Expected 8 opaque atoms, got {len(opaque)}"

    top = d1["⊤"]
    bot = d1["⊥"]
    p_tok = d1["p"]
    n0 = ext["N0"]
    n1 = ext["N1"]

    def log(msg):
        if verbose:
            print(f"    [Phase 2] {msg}")

    log(f"Starting with {len(opaque)} opaque atoms")

    all_known = set()
    for k, v in d1.items():
        if k != "_testers":
            all_known.add(v)
    for v in ext.values():
        all_known.add(v)
    domain_set = all_known | set(opaque)

    # ── Step 1: Apply each opaque atom to N0 ──────────────────────────
    QUOTE_tok = EVAL_tok = None
    partial_group = []
    p_group = []

    for x in opaque:
        result = dot(x, n0)

        if result == p_tok:
            p_group.append(x)
        elif isinstance(result, str) and result in domain_set:
            p_group.append(x)
        else:
            partial_group.append(x)

    log(f"Step 1: applied to N0 → partial group = {partial_group}, p group = {p_group}")

    # partial_group = {QUOTE, APP, IO_PUT, IO_SEQ} (produce structured values)
    # p_group = {EVAL, UNAPP, IO_GET, IO_RDY} (return p)
    assert len(partial_group) == 4, f"Expected 4 in partial group, got {len(partial_group)}"
    assert len(p_group) == 4, f"Expected 4 in p group, got {len(p_group)}"

    # ── Step 1b: Identify QUOTE from partial group ────────────────────
    for q in list(partial_group):
        q_n0 = dot(q, n0)
        for e in list(p_group):
            if dot(e, q_n0) == n0:
                QUOTE_tok = q
                EVAL_tok = e
                break
        if QUOTE_tok:
            break

    assert QUOTE_tok is not None, "Failed to identify QUOTE/EVAL"
    partial_group.remove(QUOTE_tok)
    p_group.remove(EVAL_tok)
    log(f"Step 1: QUOTE identified ({QUOTE_tok})")
    log(f"Step 1: EVAL identified ({EVAL_tok})")

    # ── Step 2: Resolve partial group (APP, IO_PUT, IO_SEQ) ──────────
    APP_tok = IO_PUT_tok = IO_SEQ_tok = None

    for x in partial_group:
        partial_val = dot(x, n0)
        result = dot(partial_val, n1)

        if result == top:
            IO_PUT_tok = x
            log(f"Step 2: partial({x})(N0)(N1) = ⊤ → IO_PUT identified ({x})")
        elif result == n1:
            IO_SEQ_tok = x
            log(f"Step 2: partial({x})(N0)(N1) returned N1 → IO_SEQ identified ({x})")
        else:
            APP_tok = x
            log(f"Step 2: partial({x})(N0)(N1) built AppNode → APP identified ({x})")

    assert APP_tok is not None, "Failed to identify APP"
    assert IO_PUT_tok is not None, "Failed to identify IO_PUT"
    assert IO_SEQ_tok is not None, "Failed to identify IO_SEQ"

    # ── Step 3: Resolve p group (UNAPP, IO_GET, IO_RDY) ──────────────
    IO_RDY_tok = None
    p_subgroup = []

    for x in p_group:
        result = dot(x, top)
        if result == top:
            IO_RDY_tok = x
            log(f"Step 3: {x}(⊤) returned ⊤ → IO_RDY identified ({x})")
        else:
            p_subgroup.append(x)

    assert IO_RDY_tok is not None, "Failed to identify IO_RDY"
    assert len(p_subgroup) == 2, f"Expected 2 remaining in p group, got {len(p_subgroup)}"

    # ── Step 4: Confirm UNAPP, IO_GET by exclusion ────────────────────
    app_partial = dot(APP_tok, n0)
    app_node = dot(app_partial, n1)

    UNAPP_tok = IO_GET_tok = None
    for x in p_subgroup:
        bundle = dot(x, app_node)
        left = dot(bundle, top)
        if left == n0:
            UNAPP_tok = x
            log(f"Step 4: UNAPP confirmed via AppNode destructure ({x})")
        else:
            IO_GET_tok = x

    if UNAPP_tok is None:
        for x in p_subgroup:
            if x != IO_GET_tok:
                UNAPP_tok = x
                break

    assert UNAPP_tok is not None, "Failed to identify UNAPP"
    if IO_GET_tok is None:
        IO_GET_tok = [x for x in p_subgroup if x != UNAPP_tok][0]
    log(f"Step 4: IO_GET identified by exclusion ({IO_GET_tok})")
    log(f"Phase 2 complete: 8/8 opaque atoms identified")

    return {
        "QUOTE": QUOTE_tok,
        "EVAL": EVAL_tok,
        "APP": APP_tok,
        "UNAPP": UNAPP_tok,
        "IO_PUT": IO_PUT_tok,
        "IO_GET": IO_GET_tok,
        "IO_RDY": IO_RDY_tok,
        "IO_SEQ": IO_SEQ_tok,
    }


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


def demo_alu_xor(dot, d1, d2, ext):
    """XOR two nibbles: (ALU-LOGIC N6 a b)"""
    n3 = ext["N3"]
    n5 = ext["N5"]
    partial1 = dot(ext["ALU_LOGIC"], ext["N6"])
    partial2 = dot(partial1, n3)
    result = dot(partial2, n5)
    # 3 XOR 5 = 6
    return result, ext["N6"]


def demo_alu_add(dot, d1, d2, ext):
    """Add two nibbles: (ALU-ARITH N9 a b)"""
    n7 = ext["N7"]
    n5 = ext["N5"]
    partial1 = dot(ext["ALU_ARITH"], ext["N9"])
    partial2 = dot(partial1, n7)
    result = dot(partial2, n5)
    # 7 + 5 = 12 = NC
    return result, ext["NC"]


def demo_alu_sub(dot, d1, d2, ext):
    """Subtract: A minus B via (ALU-ARITHC N6 a b)"""
    na = ext["NA"]
    n3 = ext["N3"]
    partial1 = dot(ext["ALU_ARITHC"], ext["N6"])
    partial2 = dot(partial1, na)
    result = dot(partial2, n3)
    # A - 3 = 7
    return result, ext["N7"]


def demo_alu_not(dot, d1, d2, ext):
    """NOT A: (ALU-LOGIC N0 a N0)"""
    n5 = ext["N5"]
    partial1 = dot(ext["ALU_LOGIC"], ext["N0"])
    partial2 = dot(partial1, n5)
    result = dot(partial2, ext["N0"])
    # NOT 5 = 0xA = 10
    return result, ext["NA"]


def demo_zero_test(dot, d1, d2, ext):
    """Zero test: (ALU-ZERO result)"""
    zero = dot(ext["ALU_ZERO"], ext["N0"])
    nonzero = dot(ext["ALU_ZERO"], ext["N5"])
    return zero, nonzero, d1["⊤"], d1["⊥"]


# ============================================================================
# Verification helpers
# ============================================================================

def verify(label: str, recovered: str, true2hid: Dict[Atom, str]) -> str:
    expected = true2hid[A(label)]
    return "✓" if recovered == expected else f"✗ (expected {expected})"


# ============================================================================
# Main
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Δ₂+74181 True Black-Box Recovery Demo")
    parser.add_argument("--seed", type=int, default=11,
                        help="Random seed for shuffling")
    parser.add_argument("--seeds", type=int, default=0,
                        help="If > 0, run this many seeds and report pass/fail")
    args = parser.parse_args()

    if args.seeds > 0:
        # Batch mode: Phase 1a (D1) + Phase 1b (74181) + Phase 2 (opaque)
        print(f"Testing {args.seeds} seeds (Phase 1 + Phase 2)...")
        failures = []
        for seed in range(args.seeds):
            try:
                domain, dot, true2hid = make_blackbox(seed)

                # Phase 1a: D1
                d1 = discover_d1(domain, dot)
                for k in ["⊤", "⊥", "e_I", "e_D", "e_M", "e_Σ", "e_Δ",
                          "i", "k", "a", "b", "d_I", "d_K", "m_I", "m_K",
                          "s_C", "p"]:
                    if d1[k] != true2hid[A(k)]:
                        failures.append((seed, k, "d1"))
                        break

                # Phase 1b: 74181 (Cayley-level)
                ext, opaque = discover_74181_with_logs(domain, dot, d1, verbose=False)
                for k in ext:
                    if ext[k] != true2hid[A(k)]:
                        failures.append((seed, k, "74181"))
                        break

                # Phase 2: Term-level recovery of 8 opaque atoms
                p2 = discover_phase2(opaque, dot, d1, ext, verbose=False)
                for k in p2:
                    if p2[k] != true2hid[A(k)]:
                        failures.append((seed, k, "phase2"))
                        break

            except Exception as e:
                failures.append((seed, str(e), "crash"))

            if (seed + 1) % 100 == 0:
                print(f"  ... {seed + 1}/{args.seeds} seeds tested")

        if failures:
            print(f"FAILED on {len(failures)} seeds:")
            for seed, key, phase in failures[:20]:
                print(f"  seed={seed}: {phase} failed at {key}")
        else:
            print(f"All {args.seeds} seeds passed — 47/47 atoms, 100% recovery rate. ✓")
        return

    # ── Single seed demo mode ──
    domain, dot, true2hid = make_blackbox(args.seed)

    print("=" * 60)
    print("  Δ₂+74181 TRUE BLACK-BOX RECOVERY DEMO")
    print("=" * 60)
    print(f"\nBlack-box seed: {args.seed}")
    print(f"Atom domain: {len(domain)} opaque labels")
    print(f"  (Δ₁ core: 17 + Δ₂ ext: 4 + 74181 ext: 22 + IO: 4 = 47 atoms)")
    print(f"\nNO ground truth is used during recovery.")
    print(f"Ground truth is used ONLY for post-hoc verification (✓/✗).")

    # Phase 1a: Δ₁
    print("\n" + "-" * 60)
    print("  PHASE 1a: Recover Δ₁ primitives from behavior")
    print("-" * 60)
    d1 = discover_d1(domain, dot)
    for k in ["⊤", "⊥", "p", "e_I", "e_D", "e_M", "e_Σ", "e_Δ",
              "i", "k", "a", "b", "d_I", "d_K", "m_I", "m_K", "s_C"]:
        status = verify(k, d1[k], true2hid)
        print(f"  {k:4s} → {d1[k]}  {status}")

    # Phase 1b: 74181 extension atoms (Cayley-level)
    print("\n" + "-" * 60)
    print("  PHASE 1b: Recover 74181 extension atoms (Cayley-level)")
    print("-" * 60)
    ext, opaque = discover_74181_with_logs(domain, dot, d1, verbose=True)
    print()
    for k in ext:
        status = verify(k, ext[k], true2hid)
        print(f"  {k:12s} → {ext[k]}  {status}")

    all_ok = all(ext[k] == true2hid[A(k)] for k in ext)
    if all_ok:
        print(f"  ✓ All {len(ext)} Phase 1b atoms correctly recovered")

    # Phase 2: Term-level recovery of 8 opaque atoms
    print("\n" + "-" * 60)
    print("  PHASE 2: Recover 8 opaque atoms (term-level)")
    print("-" * 60)
    p2 = discover_phase2(opaque, dot, d1, ext, verbose=True)
    print()
    for k in p2:
        status = verify(k, p2[k], true2hid)
        print(f"  {k:12s} → {p2[k]}  {status}")

    all_ok_p2 = all(p2[k] == true2hid[A(k)] for k in p2)
    if all_ok_p2:
        print(f"  ✓ All {len(p2)} Phase 2 atoms correctly recovered")

    if all_ok and all_ok_p2:
        print(f"\n  ✓ All 47 atoms identified — complete recovery")

    # Merge for demos
    d2 = {k: p2[k] for k in ["QUOTE", "EVAL", "APP", "UNAPP"]}

    # Phase 3: Run programs
    print("\n" + "-" * 60)
    print("  PHASE 3: Run programs using recovered primitives")
    print("-" * 60)

    # D2 demos
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

    # 74181 ALU demos
    result, expected = demo_alu_xor(dot, d1, d2, ext)
    print(f"\n  Program 3: (ALU-LOGIC N6 N3 N5) — XOR(3,5)")
    print(f"    Result:   {result}")
    print(f"    Expected: {expected}  (N6 = 6)")
    print(f"    {'✓ Correct' if result == expected else '✗ MISMATCH'}")

    result, expected = demo_alu_add(dot, d1, d2, ext)
    print(f"\n  Program 4: (ALU-ARITH N9 N7 N5) — ADD(7,5)")
    print(f"    Result:   {result}")
    print(f"    Expected: {expected}  (NC = 12)")
    print(f"    {'✓ Correct' if result == expected else '✗ MISMATCH'}")

    result, expected = demo_alu_sub(dot, d1, d2, ext)
    print(f"\n  Program 5: (ALU-ARITHC N6 NA N3) — SUB(10,3)")
    print(f"    Result:   {result}")
    print(f"    Expected: {expected}  (N7 = 7)")
    print(f"    {'✓ Correct' if result == expected else '✗ MISMATCH'}")

    result, expected = demo_alu_not(dot, d1, d2, ext)
    print(f"\n  Program 6: (ALU-LOGIC N0 N5 N0) — NOT(5)")
    print(f"    Result:   {result}")
    print(f"    Expected: {expected}  (NA = 10)")
    print(f"    {'✓ Correct' if result == expected else '✗ MISMATCH'}")

    zero, nonzero, exp_t, exp_f = demo_zero_test(dot, d1, d2, ext)
    print(f"\n  Program 7: (ALU-ZERO N0) and (ALU-ZERO N5)")
    print(f"    ALU-ZERO(N0) = {zero}  (expected ⊤ = {exp_t})  "
          f"{'✓' if zero == exp_t else '✗'}")
    print(f"    ALU-ZERO(N5) = {nonzero}  (expected ⊥ = {exp_f})  "
          f"{'✓' if nonzero == exp_f else '✗'}")

    print("\n" + "=" * 60)
    print("  All phases complete.")
    print("=" * 60)


if __name__ == "__main__":
    main()

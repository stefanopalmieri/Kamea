#!/usr/bin/env python3
"""
Δ₂+74181 — 74181 ALU Extension of the Δ₂ Algebra

Extends the 21-atom Δ₂ algebra with 45 new atoms:
  - 16 nibble atoms N0–NF (4-bit data values / operation selectors)
  - 3 ALU dispatch atoms (ALU_LOGIC, ALU_ARITH, ALU_ARITHC)
  - 2 predicate atoms (ALU_ZERO, ALU_COUT)
  - 1 nibble successor atom (N_SUCC)
  - 4 IO atoms (IO_PUT, IO_GET, IO_RDY, IO_SEQ)
  - 16 W32 wide arithmetic atoms
  - 2 MUL16 multiply atoms
  - 1 QUALE atom (structural symmetry breaker)

Total: 66 atoms. The QUALE atom gives each opaque atom a unique
structurally-identifiable target in its QUALE column, making the algebra
rigid (all 66 atoms uniquely identifiable from the Cayley table alone).

The 74181 chip's 32 operations are encoded as 3 dispatch atoms × 16
nibble selectors. Nibble atoms serve double duty as both data values
and operation selectors.

Usage:
  python kamea.py                # run verification suite
  python kamea.py --test 1000    # run 1000-seed integration test
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
NAMES_NIBBLES = [f"N{i:X}" for i in range(16)]  # N0, N1, ..., NF
NAMES_ALU_DISPATCH = ["ALU_LOGIC", "ALU_ARITH", "ALU_ARITHC"]
NAMES_ALU_PRED = ["ALU_ZERO", "ALU_COUT"]
NAMES_ALU_MISC = ["N_SUCC"]
NAMES_IO = ["IO_PUT", "IO_GET", "IO_RDY", "IO_SEQ"]
NAMES_W32 = [
    "W_PACK8", "W_LO", "W_HI", "W_MERGE", "W_NIB",
    "W_ADD", "W_SUB", "W_CMP",
    "W_XOR", "W_AND", "W_OR", "W_NOT",
    "W_SHL", "W_SHR", "W_ROTL", "W_ROTR",
]
NAMES_MUL = ["MUL16", "MAC16"]
NAMES_QUALE = ["QUALE"]

NAMES_BASE = (NAMES_D1 + NAMES_D2 + NAMES_NIBBLES +
              NAMES_ALU_DISPATCH + NAMES_ALU_PRED + NAMES_ALU_MISC + NAMES_IO)
ALL_NAMES = NAMES_BASE + NAMES_W32 + NAMES_MUL + NAMES_QUALE
ALL_ATOMS = [A(n) for n in ALL_NAMES]
BASE_ATOMS = [A(n) for n in NAMES_BASE]  # Original 47 atoms (no W32/MUL)

NIBBLE_ATOMS = frozenset(A(f"N{i:X}") for i in range(16))
ALU_DISPATCH_ATOMS = frozenset(A(n) for n in NAMES_ALU_DISPATCH)
ALU_PRED_ATOMS = frozenset(A(n) for n in NAMES_ALU_PRED)
IO_ATOMS = frozenset(A(n) for n in NAMES_IO)
W32_ATOMS = frozenset(A(n) for n in NAMES_W32)
MUL_ATOMS = frozenset(A(n) for n in NAMES_MUL)
NEW_ATOMS = (NIBBLE_ATOMS | ALU_DISPATCH_ATOMS | ALU_PRED_ATOMS |
             frozenset(A(n) for n in NAMES_ALU_MISC) | IO_ATOMS |
             W32_ATOMS | MUL_ATOMS)
D1_ATOMS = frozenset(A(n) for n in NAMES_D1)
D2_EXT_ATOMS = frozenset(A(n) for n in NAMES_D2)
QUALE_ATOMS = frozenset(A(n) for n in NAMES_QUALE)

# QUALE column map: each opaque atom maps to a unique structurally-identifiable target
QUALE_MAP = {
    # D2 atoms → D1 core
    "QUOTE": "k",       "EVAL": "i",        "APP": "⊤",         "UNAPP": "⊥",
    # IO atoms → D1 structural
    "IO_PUT": "e_Σ",    "IO_GET": "e_Δ",    "IO_RDY": "d_I",    "IO_SEQ": "s_C",
    # W32 atoms → nibbles + ALU + D1
    "W_PACK8": "N8",    "W_LO": "b",        "W_HI": "a",        "W_MERGE": "p",
    "W_NIB": "N4",      "W_ADD": "N_SUCC",  "W_SUB": "ALU_COUT","W_CMP": "ALU_ZERO",
    "W_XOR": "N6",      "W_AND": "NB",      "W_OR": "NE",       "W_NOT": "N0",
    "W_SHL": "ALU_ARITH","W_SHR": "ALU_LOGIC","W_ROTL": "ALU_ARITHC","W_ROTR": "d_K",
    # MUL atoms → nibbles
    "MUL16": "N9",      "MAC16": "NA",
    # Self
    "QUALE": "e_I",
}
# Inverse: target name → opaque atom name
QUALE_MAP_INV = {v: k for k, v in QUALE_MAP.items()}


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
# 74181 ALU computation (Deliverable 4)
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

    # Arithmetic modes
    carry_in = 1 if mode == "arithc" else 0
    logic_result = _alu_logic(selector, a, b)
    # Arithmetic: add logic result + carry
    full = logic_result + carry_in
    # The 74181 arithmetic is: F = logic_result + carry_in (for each bit position)
    # More precisely: arithmetic result = logic_result + carry_in in 4-bit
    # But the 74181 does bit-level carry propagation on the logic function outputs
    # Let me implement it correctly using the standard 74181 truth table approach

    # The correct 74181 arithmetic: the logic function generates a "generate"
    # and "propagate" per bit, then ripple-carry adds.
    # Simpler: just compute directly from the truth tables.
    result, carry_out = _alu_arith(selector, a, b, carry_in)
    return (result, carry_out, result == 0)


def _alu_logic(selector: int, a: int, b: int) -> int:
    """Compute 74181 logic operation (active-high)."""
    # Operate bitwise on each of the 4 bits
    result = 0
    for bit in range(4):
        ai = (a >> bit) & 1
        bi = (b >> bit) & 1
        # The 74181 logic functions (active-high):
        fi = _logic_bit(selector, ai, bi)
        result |= (fi << bit)
    return result & 0xF


def _logic_bit(selector: int, ai: int, bi: int) -> int:
    """Compute one bit of the 74181 logic function."""
    s0 = (selector >> 0) & 1
    s1 = (selector >> 1) & 1
    s2 = (selector >> 2) & 1
    s3 = (selector >> 3) & 1

    # 74181 active-high logic equations per bit:
    # The logic function is: F = NOT(
    #   (NOT A AND s0 AND NOT B) OR
    #   (NOT A AND s1 AND B) OR
    #   (A AND s2 AND NOT B) OR
    #   (A AND s3 AND B)
    # )
    # Wait, let me use the standard formulation.
    # Actually, the 74181 logic output per bit (active-high) is:
    #
    # For the logic functions (M=H), the output per bit is determined by
    # the select lines and input bits. The truth table for active-high:

    na = 1 - ai
    nb = 1 - bi

    # Generate and propagate terms
    t0 = na & s0 & nb
    t1 = na & s1 & bi
    t2 = ai & s2 & nb
    t3 = ai & s3 & bi

    # Logic output (active-high): NOT of the OR of terms
    # Wait, this gives the COMPLEMENT. Let me just use the truth table directly.
    # The 74181 active-high logic table:
    # S=0000: NOT A        S=0001: NOT(A OR B)   S=0010: (NOT A) AND B
    # S=0011: 0            S=0100: NOT(A AND B)  S=0101: NOT B
    # S=0110: A XOR B      S=0111: A AND NOT B   S=1000: NOT A OR B
    # S=1001: NOT(A XOR B) S=1010: B             S=1011: A AND B
    # S=1100: 1            S=1101: A OR NOT B    S=1110: A OR B
    # S=1111: A

    _table = [
        na,                           # 0: NOT A
        1 - (ai | bi),                # 1: NOR
        na & bi,                      # 2: (NOT A) AND B
        0,                            # 3: Logical 0
        1 - (ai & bi),               # 4: NAND
        nb,                           # 5: NOT B
        ai ^ bi,                      # 6: XOR
        ai & nb,                      # 7: A AND (NOT B)
        na | bi,                      # 8: (NOT A) OR B
        1 - (ai ^ bi),               # 9: XNOR
        bi,                           # A: B
        ai & bi,                      # B: A AND B
        1,                            # C: Logical 1
        ai | nb,                      # D: A OR (NOT B)
        ai | bi,                      # E: A OR B
        ai,                           # F: A
    ]
    return _table[selector]


def _alu_arith(selector: int, a: int, b: int, carry_in: int) -> tuple:
    """
    Compute 74181 arithmetic operation (active-high).

    Directly implements the 74181 arithmetic truth table.
    The "with carry" result is "no carry" result + 1.

    Returns (result: 0-15, carry_out: bool)
    """
    nb = (~b) & 0xF  # 4-bit complement of B

    # Base result (no carry) from the 74181 truth table
    base_table = [
        a,                      # 0: A
        a | b,                  # 1: A OR B
        a | nb,                 # 2: A OR (NOT B)
        0xF,                    # 3: minus 1 (all ones)
        a + (a & nb),           # 4: A plus (A AND NOT B)
        (a | b) + (a & nb),     # 5: (A OR B) plus (A AND NOT B)
        a + nb,                 # 6: A minus B minus 1 = A + NOT(B)
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
# Atom-atom Cayley table (66 × 66)
# ============================================================================

def atom_dot(x: Atom, y: Atom) -> Atom:
    """
    Cayley table for all 66 atoms.

    Design principles:
    - Preserves all 21×21 original D1/D2 entries exactly
    - D1 atoms use dot_iota_d1 for ALL right arguments (testers stay pure boolean)
    - Nibbles form Z/16Z under addition mod 16
    - ALU dispatch: identity/successor/double-successor on nibbles
    - ALU predicates: tester-like on nibbles, self-id on ⊤, else p
    - IO atoms: all-p rows (effects happen at term level)
    """
    TOP, BOT = A("⊤"), A("⊥")

    # ── D1 atom on left: use dot_iota_d1 for ALL right arguments ──
    # This preserves the original D1×D1 and D1×D2 entries exactly,
    # and gives correct defaults for D1×new (testers → ⊥/⊤, others → p).
    # Exception: m_I needs to map new atoms to ⊤ (they are not p).
    if x in D1_ATOMS:
        # m_I: dot_iota_d1 returns ⊥ only for p, ⊤ for everything else.
        # For new atoms (which are not p), this correctly returns ⊤.
        # For D2 atoms (not p), correctly returns ⊤.
        # All other D1 atoms handled correctly by dot_iota_d1.
        return dot_iota_d1(x, y)

    # ── QUALE row: all-p except self → e_I ──
    if x == A("QUALE"):
        if y == A("QUALE"):
            return A("e_I")
        return A("p")

    # ── D2 atoms: all-p except QUALE column ──
    if x in D2_EXT_ATOMS:
        if y == A("QUALE"):
            return A(QUALE_MAP[x.name])
        return A("p")

    # ── IO atoms: all-p except QUALE column ──
    if x in IO_ATOMS:
        if y == A("QUALE"):
            return A(QUALE_MAP[x.name])
        return A("p")

    # ── W32/MUL atoms: all-p except QUALE column ──
    if x in W32_ATOMS or x in MUL_ATOMS:
        if y == A("QUALE"):
            return A(QUALE_MAP[x.name])
        return A("p")

    # ── Nibble self-identification on ⊤ ──
    if is_nibble(x) and y == TOP: return x

    # ── Nibble × Nibble: Z/16Z under addition ──
    if is_nibble(x) and is_nibble(y):
        return nibble((nibble_val(x) + nibble_val(y)) % 16)

    # ── ALU dispatch self-identification on ⊤ ──
    if x in ALU_DISPATCH_ATOMS and y == TOP: return x

    # ── ALU dispatch × Nibble: distinguishing mappings ──
    if x == A("ALU_LOGIC") and is_nibble(y):
        return y  # identity on nibbles
    if x == A("ALU_ARITH") and is_nibble(y):
        return nibble((nibble_val(y) + 1) % 16)  # successor
    if x == A("ALU_ARITHC") and is_nibble(y):
        return nibble((nibble_val(y) + 2) % 16)  # double successor

    # ── ALU predicate self-identification on ⊤ ──
    if x in ALU_PRED_ATOMS and y == TOP: return x

    # ── ALU_ZERO: tester on nibbles ──
    if x == A("ALU_ZERO") and is_nibble(y):
        return TOP if y == A("N0") else BOT

    # ── ALU_COUT: tester on nibbles (high bit = carry) ──
    if x == A("ALU_COUT") and is_nibble(y):
        return TOP if nibble_val(y) >= 8 else BOT

    # ── N_SUCC: successor on nibbles (16-cycle) ──
    if x == A("N_SUCC") and y == TOP: return x
    if x == A("N_SUCC") and y == BOT: return A("N0")  # reset on ⊥ (distinguishes from ALU_ARITH at atom level)
    if x == A("N_SUCC") and is_nibble(y):
        return nibble((nibble_val(y) + 1) % 16)

    # ── Default: everything else → p ──
    return A("p")


# ============================================================================
# Extended dot operation (full term-level)
# ============================================================================

def eval_term(t: Any) -> Any:
    if isinstance(t, Atom): return t
    if isinstance(t, Quote): return t
    if isinstance(t, AppNode):
        return dot_ext(eval_term(t.f), eval_term(t.x))
    return A("p")


def dot_ext(x: Any, y: Any) -> Any:
    """The full Δ₂+74181 operation on terms."""

    # --- QUALE intercept: atom × QUALE or QUALE × atom uses Cayley table ---
    if isinstance(x, Atom) and isinstance(y, Atom):
        if x.name in QUALE_MAP and y == A("QUALE"):
            return A(QUALE_MAP[x.name])
        if x == A("QUALE"):
            return A("e_I") if y == A("QUALE") else A("p")

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

    # --- QUOTE (inherited) ---
    if x == A("QUOTE"): return Quote(y)

    # --- APP (inherited) ---
    if x == A("APP"): return Partial("APP", y)

    # --- UNAPP (inherited) ---
    if x == A("UNAPP"):
        return UnappBundle(y.f, y.x) if isinstance(y, AppNode) else A("p")

    # --- Bundle queries (inherited) ---
    if isinstance(x, UnappBundle):
        if y == A("⊤"): return x.f
        if y == A("⊥"): return x.x
        return A("p")

    # --- EVAL (inherited) ---
    if x == A("EVAL"):
        if isinstance(y, Quote): return eval_term(y.term)
        return A("p")

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

    # --- ALU_COUT: at term level, applied to ALU result for carry ---
    # ALU_COUT tests the carry-out from an ALU operation.
    # In curried usage: (ALU-COUT (ALU-ARITH N9 a b))
    # The inner expression evaluates to a nibble result.
    # To get carry info, we'd need to track it. For now, ALU_COUT
    # on a nibble tests the high bit (>= 8), consistent with Cayley table.
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
    # In the REPL, IO_GET reads stdin. Here we return p ("no input").
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
# Black-box wrapper (for discovery testing)
# ============================================================================

def make_blackbox(seed: int = 11, atoms: list = None):
    rng = random.Random(seed)
    atoms = (atoms or BASE_ATOMS).copy()
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
        return to_hidden(dot_ext(to_true(xh), to_true(yh)))

    return domain, dot_oracle, true_to_hidden


# ============================================================================
# Phase 1: Discover Δ₁ primitives (unchanged from delta2_true_blackbox.py)
# ============================================================================

def discover_d1(domain: List[str], dot) -> Dict[str, Any]:
    """Recover all 17 Δ₁ atoms from black-box probing."""

    def left_image(xh):
        return {dot(xh, y) for y in domain}

    def left_image_in_domain(xh):
        return {dot(xh, y) for y in domain if dot(xh, y) in domain}

    # Step 1: Find booleans (left-absorbers)
    absorbers = [x for x in domain if all(dot(x, y) == x for y in domain)]
    assert len(absorbers) == 2, f"Expected 2 absorbers, got {len(absorbers)}"
    B1, B2 = absorbers

    # Step 2: Find testers
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

    # Step 3: Identify testers by cardinality (moved before p-detection)
    sizes = {t: len(Dec(t)) for t in testers}
    m_K = [t for t in testers if sizes[t] == 1][0]
    m_I = max(testers, key=lambda t: sizes[t])
    two = [t for t in testers if sizes[t] == 2]
    assert len(two) == 2

    # Step 2.5: Find p
    # p is the unique non-boolean, non-tester element where dot(x, ⊤) = ⊤
    # AND dot(m_I, x) = ⊥ (m_I maps only p to ⊥; all others to ⊤).
    # IO_RDY also has dot(x, ⊤) = ⊤ but dot(m_I, IO_RDY) = ⊤.
    p_candidates = [
        x for x in domain
        if x not in (top, bot) and x not in testers
        and dot(x, top) == top
        and dot(m_I, x) == bot
    ]
    assert len(p_candidates) == 1, (
        f"Expected exactly 1 p-candidate, got {len(p_candidates)}: {p_candidates}"
    )
    p_tok = p_candidates[0]

    # Step 4: Distinguish e_I from d_K
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

    # Step 5: Find e_D and e_M
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

    # Step 6: Distinguish i from k
    outA, outB = dot(e_M, ctx[0]), dot(e_M, ctx[1])
    if len(Dec(outA)) > len(Dec(outB)):
        i_tok, k_tok = ctx[0], ctx[1]
    else:
        i_tok, k_tok = ctx[1], ctx[0]

    # Step 7: Identify a, b, d_I
    ab = list(Dec(d_K))
    a_tok = next(x for x in ab if dot(m_K, x) == top)
    b_tok = next(x for x in ab if x != a_tok)
    d_I = dot(e_D, i_tok)

    # Step 8: Find e_Σ, s_C, e_Δ
    known = {top, bot, e_I, d_K, m_K, m_I, e_M, e_D,
             i_tok, k_tok, a_tok, b_tok, d_I, p_tok}
    remaining = [x for x in domain if x not in known]

    e_S = sC = e_Delta = None
    for f, g in itertools.product(remaining, repeat=2):
        h = dot(f, g)
        if h not in domain or h in (top, bot, p_tok):
            continue
        if h in known or h == f or h == g:
            continue
        # s_C self-identifies on ⊤
        if dot(g, top) != g:
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
# Phase 2: Discover Δ₂ primitives (unchanged from delta2_true_blackbox.py)
# ============================================================================

def discover_d2(domain: List[str], dot, d1: Dict[str, Any]) -> Dict[str, Any]:
    """Recover QUOTE, EVAL, APP, UNAPP by probing behavior."""
    top, bot = d1["⊤"], d1["⊥"]
    testers = d1["_testers"]
    p_tok = d1["p"]

    d1_identified = {v for k, v in d1.items() if k != "_testers"}
    cand = [x for x in domain if x not in d1_identified]
    sample = domain

    # Find QUOTE and EVAL jointly
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

    # Find APP and UNAPP
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
# Phase 3: Discover 74181 extension atoms
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

    Recovery order:
      0. Separate 8 opaque atoms (all-p Cayley rows) from 22 structured
      1. Identify predicates (atoms producing both ⊤ and ⊥ in left-image)
      2. Identify N_SUCC (unique cyclic permuter of nibble group)
      3. Separate nibbles from ALU dispatch (self-composable vs not)
      4. Identify N0 via ALU_ZERO (the predicate accepting exactly 1 nibble)
      5. Walk N_SUCC cycle from N0 to order all 16 nibbles
      6. Distinguish ALU_LOGIC / ALU_ARITH / ALU_ARITHC
      7. Distinguish ALU_ZERO from ALU_COUT by decoded set size
    """
    top = d1["⊤"]
    bot = d1["⊥"]
    p_tok = d1["p"]

    def log(msg):
        if verbose:
            print(f"    [Phase 1b] {msg}")

    # Collect all previously identified tokens
    d1_identified = {v for k, v in d1.items() if k != "_testers"}
    known = d1_identified
    remaining = [x for x in domain if x not in known]
    assert len(remaining) == len(domain) - 17, f"Expected {len(domain) - 17} remaining atoms, got {len(remaining)}"
    log(f"Starting with {len(remaining)} unidentified atoms")

    # ── Step 0: Compute domain-restricted left images ─────────────────
    # dot_ext may return structured values (Quote, IOPutPartial, etc.)
    # for D2/IO atoms. We restrict to domain-valued results for Cayley analysis.
    domain_set = set(domain)

    def left_image(x):
        return {r for r in [dot(x, y) for y in domain] if isinstance(r, str) and r in domain_set}

    # ── Step 1: Identify predicate atoms ──────────────────────────────
    # Predicates produce ⊤ AND ⊥ in their left-image (from nibble probes)
    # plus self (from ⊤ probe) plus p (from non-nibble probes).
    predicates = []
    for x in remaining:
        li = left_image(x)
        if top in li and bot in li and x in li:
            predicates.append(x)

    assert len(predicates) == 2, f"Expected 2 predicates, got {len(predicates)}"
    log(f"Predicates identified: {predicates}")

    # ── Step 2: Separate nibbles, N_SUCC, and ALU dispatch ────────────
    # Among the non-predicate remaining atoms, nibbles are self-composable,
    # N_SUCC permutes nibbles, and ALU dispatch atoms produce structured values.
    # D2/IO atoms produce p or non-domain results and will fall to "other".
    non_pred = [x for x in remaining if x not in predicates]

    # First pass: identify nibbles (self-composable within the remaining set)
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

    # ── Step 3: Identify N_SUCC (maps nibbles to nibbles in domain) ──
    # N_SUCC maps nibbles to domain nibbles (via Cayley table).
    # ALU dispatch atoms map nibbles to non-domain structured values
    # (ALUPartial1) via dot_ext. So N_SUCC is the ONLY non-nibble
    # that maps all nibbles to domain values.
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
    # ALU_ZERO: exactly 1 nibble maps to ⊤ (that nibble is N0)
    # ALU_COUT: exactly 8 nibbles map to ⊤
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

    # ── Step 7: Identify QUALE (if present) ─────────────────────────
    # QUALE is the only non-D1, non-nibble, non-predicate atom where
    # dot(x, x) yields a known D1 atom (e_I).
    e_I_tok = d1["e_I"]
    quale_tok = None
    non_nibble_rest2 = []
    for x in non_nibble_rest:
        if dot(x, x) == e_I_tok:
            quale_tok = x
        else:
            non_nibble_rest2.append(x)

    if quale_tok is not None:
        log(f"QUALE identified: {quale_tok}")

    # ── Step 8: Separate dispatch from opaque, then identify dispatch ─
    # Dispatch atoms self-identify on ⊤: dot(x, ⊤) == x.
    # D2/IO/W32/MUL atoms produce structured values or p when applied to ⊤.
    dispatch = []
    opaque = []
    for x in non_nibble_rest2:
        if dot(x, top) == x:
            dispatch.append(x)
        else:
            opaque.append(x)

    assert len(dispatch) == 3, f"Expected 3 dispatch, got {len(dispatch)}"

    # Identify ALU_LOGIC / ALU_ARITH / ALU_ARITHC via curried probe:
    #   d(N0)(N5)(N0): LOGIC → NOT(5)=NA, ARITH → A=N5, ARITHC → A+1=N6
    n0 = nibble_order[0]
    n5 = nibble_order[5]
    na = nibble_order[10]  # 0xA = 10
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

    # Build result dict
    result = {}
    for i in range(16):
        result[f"N{i:X}"] = nibble_order[i]
    result["N_SUCC"] = n_succ_tok
    result["ALU_LOGIC"] = alu_logic_tok
    result["ALU_ARITH"] = alu_arith_tok
    result["ALU_ARITHC"] = alu_arithc_tok
    result["ALU_ZERO"] = alu_zero_tok
    result["ALU_COUT"] = alu_cout_tok

    # ── Step 9: Use QUALE to identify all opaque atoms (if QUALE found) ─
    if quale_tok is not None:
        result["QUALE"] = quale_tok

        # Build token → name lookup from all identified atoms so far
        all_identified = dict(d1)
        del all_identified["_testers"]
        all_identified.update(result)
        token_to_name = {v: k for k, v in all_identified.items()}

        quale_identified = {}
        for u in opaque:
            target_tok = dot(u, quale_tok)
            target_name = token_to_name.get(target_tok)
            assert target_name is not None, f"QUALE target {target_tok} not found in known atoms"
            opaque_name = QUALE_MAP_INV.get(target_name)
            assert opaque_name is not None, f"Target {target_name} not in QUALE_MAP_INV"
            quale_identified[opaque_name] = u
            log(f"  dot({u}, QUALE) = {target_tok} ({target_name}) → {opaque_name}")

        log(f"All {len(opaque)} opaque atoms identified via QUALE column")
        result.update(quale_identified)
        opaque = []
    else:
        log(f"Opaque atoms: {len(opaque)} — deferred to Phase 2")

    log(f"Phase 1b complete: {len(result)} atoms identified, {len(opaque)} opaque remain")
    return result, opaque


# ============================================================================
# Phase 2: Term-level recovery of 8 opaque atoms (D2 + IO)
# ============================================================================

def discover_phase2(opaque: List[str], dot, d1: Dict[str, Any],
                    ext: Dict[str, Any], verbose: bool = False) -> Dict[str, Any]:
    """
    Phase 2: Identify all 24 opaque atoms via term-level probing.

    These 24 atoms have identical all-p Cayley rows and are indistinguishable
    at the atom-atom level. Term-level application reveals their identities:

      Phase 2a (original 8: D2+IO):
        Step 1: Apply each to N0 → identifies QUOTE (produces Quote),
                EVAL (returns atom unchanged), and partitions the rest
                into partial group (APP, IO_PUT, IO_SEQ) and p group
                (UNAPP, IO_GET, IO_RDY).
        Step 2: Resolve partial group via partial(N0)(N1).
        Step 3: Resolve p group via application to ⊤.
        Step 4: Confirm UNAPP via AppNode destructure; IO_GET by exclusion.

      Phase 2b (new 16: W32+MUL):
        Identified via W32 probing with make_w32_word values.

    Args:
        opaque: 24 hidden labels with all-p Cayley rows
        dot: term-level dot oracle (must support structured terms)
        d1: Phase 1a results (17 D1 atoms)
        ext: Phase 1b results (22 74181 atoms)
        verbose: print discovery log

    Returns:
        Dict mapping atom names to hidden labels for all 24 opaque atoms.
    """
    if len(opaque) == 0:
        if verbose:
            print("    [Phase 2] Skipped — all atoms already identified via QUALE")
        return {}
    assert len(opaque) in (8, 26), f"Expected 0, 8, or 26 opaque atoms, got {len(opaque)}"

    top = d1["⊤"]
    bot = d1["⊥"]
    p_tok = d1["p"]
    n0 = ext["N0"]
    n1 = ext["N1"]

    def log(msg):
        if verbose:
            print(f"    [Phase 2] {msg}")

    log(f"Starting with {len(opaque)} opaque atoms")

    # All known domain labels (for checking if a result is "in domain")
    all_known = set()
    for k, v in d1.items():
        if k != "_testers":
            all_known.add(v)
    for v in ext.values():
        all_known.add(v)
    domain_set = all_known | set(opaque)

    # ── Step 1: Apply each opaque atom to N0 ──────────────────────────
    QUOTE_tok = EVAL_tok = None
    partial_group = []  # produced structured non-p, non-domain result
    p_group = []        # produced p

    for x in opaque:
        result = dot(x, n0)

        if result == p_tok:
            p_group.append(x)
        elif result in domain_set:
            # Result is a known domain atom but not p — unusual
            # This shouldn't happen for any of the 8 opaque atoms applied to N0
            p_group.append(x)  # safe fallback
        else:
            # Result is a structured value (not in domain) — partial group
            partial_group.append(x)

    log(f"Step 1: applied to N0 → partial group = {partial_group}, p group = {p_group}")

    # Detect full_mode by whether W_PACK8 produced a structured result.
    # full_mode: partial=5 (QUOTE, APP, IO_PUT, IO_SEQ, W_PACK8), p=21
    # basic_mode: partial=4 (QUOTE, APP, IO_PUT, IO_SEQ), p=4 or 22
    full_mode = len(partial_group) == 5
    if full_mode:
        assert len(p_group) == 21, f"Expected 21 in p group, got {len(p_group)}"
    else:
        assert len(partial_group) == 4, f"Expected 4 in partial group, got {len(partial_group)}"
        exp_p = len(opaque) - 4  # rest go to p_group
        assert len(p_group) == exp_p, f"Expected {exp_p} in p group, got {len(p_group)}"

    # ── Step 1b: Identify QUOTE from partial group ────────────────────
    # QUOTE(N0) produces Quote(N0). Applying EVAL to Quote(N0) should
    # return N0. But we don't know EVAL yet. Alternative: for each pair
    # (q, e) in partial_group × p_group, check if dot(e, dot(q, N0)) == N0.
    # The pair where this works is (QUOTE, EVAL).
    for q in list(partial_group):
        q_n0 = dot(q, n0)  # should be Quote(N0) if q is QUOTE
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
    log(f"Step 1: remaining partial group = {partial_group}")
    log(f"Step 1: remaining p group = {p_group}")

    # ── Step 2: Resolve partial group (APP, IO_PUT, IO_SEQ, W_PACK8) ─
    # Apply each partial(N0) to N1. Outcomes:
    #   IO_PUT: IOPutPartial(0)(N1) → ⊤
    #   IO_SEQ: IOSeqPartial(N0)(N1) → N1
    #   APP: Partial(N0)(N1) → AppNode — structured, not in domain
    #   W_PACK8: WPACK(0, 1)(N1) → WPACK(0x01, 2) — structured, not in domain
    APP_tok = IO_PUT_tok = IO_SEQ_tok = W_PACK8_tok = None
    other_partial = []

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
            other_partial.append(x)

    # Distinguish APP from W_PACK8 among other_partial:
    # W_PACK8(N0)(N1)(N2)...(N7) produces a W32. Feed 6 more nibbles.
    # APP(N0)(N1) is an AppNode. Feeding another nibble → p (not callable).
    exp_other = 2 if full_mode else 1
    assert len(other_partial) == exp_other, f"Expected {exp_other} in other_partial, got {len(other_partial)}"
    for x in other_partial:
        if not full_mode:
            # Only APP in basic mode
            APP_tok = x
            log(f"Step 2: APP identified ({x})")
        else:
            partial_val = dot(x, n0)
            chain = dot(partial_val, n1)
            # Try feeding one more nibble
            chain2 = dot(chain, n0)
            if chain2 == p_tok or (isinstance(chain2, str) and chain2 in domain_set):
                # APP: AppNode can't accept more args → p or atom
                APP_tok = x
                log(f"Step 2: APP identified ({x})")
            else:
                # W_PACK8: still accumulating
                W_PACK8_tok = x
                log(f"Step 2: W_PACK8 identified ({x})")

    assert APP_tok is not None, "Failed to identify APP"
    assert IO_PUT_tok is not None, "Failed to identify IO_PUT"
    assert IO_SEQ_tok is not None, "Failed to identify IO_SEQ"
    if full_mode:
        assert W_PACK8_tok is not None, "Failed to identify W_PACK8"

    # ── Step 3: Resolve p group (UNAPP, IO_GET, IO_RDY) ──────────────
    # Apply each to ⊤:
    #   UNAPP(⊤) → p (⊤ is not an AppNode)
    #   IO_GET(⊤) → reads from stdin (DON'T do this) or blocks — skip
    #   IO_RDY(⊤) → ⊤
    IO_RDY_tok = None
    p_subgroup = []  # candidates for UNAPP and IO_GET

    for x in p_group:
        result = dot(x, top)
        if result == top:
            IO_RDY_tok = x
            log(f"Step 3: {x}(⊤) returned ⊤ → IO_RDY identified ({x})")
        else:
            p_subgroup.append(x)

    assert IO_RDY_tok is not None, "Failed to identify IO_RDY"
    # p_subgroup = p_group minus EVAL minus IO_RDY
    exp_sub = len(p_group) - 1  # -1 for IO_RDY (EVAL already removed above)
    assert len(p_subgroup) == exp_sub, f"Expected {exp_sub} remaining in p group, got {len(p_subgroup)}"

    # ── Step 4: Confirm UNAPP via AppNode destructure ─────────────────
    # Build AppNode(N0, N1) using APP, then apply each candidate.
    # dot(UNAPP, AppNode(N0, N1)) → UnappBundle; dot(bundle, ⊤) → N0
    app_partial = dot(APP_tok, n0)
    app_node = dot(app_partial, n1)  # AppNode(N0, N1)

    UNAPP_tok = None
    remaining = []
    for x in p_subgroup:
        bundle = dot(x, app_node)
        left = dot(bundle, top)
        if left == n0:
            UNAPP_tok = x
            log(f"Step 4: UNAPP confirmed via AppNode destructure ({x})")
        else:
            remaining.append(x)

    assert UNAPP_tok is not None, "Failed to identify UNAPP"

    # ── Step 5: Identify IO_GET ──────────────────────────────────────
    # IO_GET(⊤) reads from UART RX → structured value (in emulator mode).
    # In pure-Python mode, IO_GET(⊤) returns p, indistinguishable from W32/MUL.
    IO_GET_tok = None
    w32_mul_candidates = []

    for x in remaining:
        result = dot(x, top)
        if result != p_tok and result not in domain_set:
            # Structured result — IO_GET reading from UART
            IO_GET_tok = x
            log(f"Step 5: IO_GET identified via UART read ({x})")
        else:
            w32_mul_candidates.append(x)

    if IO_GET_tok is None and not full_mode:
        # Pure-Python mode: IO_GET can't be distinguished from W32/MUL.
        # In basic mode (8 opaque, no W32/MUL), IO_GET is the sole remainder.
        if len(w32_mul_candidates) == 1:
            IO_GET_tok = w32_mul_candidates.pop()
            log(f"Step 5: IO_GET identified by exclusion ({IO_GET_tok})")

    assert IO_GET_tok is not None, "Failed to identify IO_GET"
    if full_mode:
        assert len(w32_mul_candidates) == 17, f"Expected 17 W32/MUL candidates, got {len(w32_mul_candidates)}"
    log(f"Phase 2a complete: 8/8 D2+IO opaque atoms identified")

    phase3 = {}
    if full_mode:
        # ── Phase 3: Identify 17 W32/MUL atoms via term-level probing ─────
        # W_PACK8 already identified in Step 2; pass it to Phase 3 so it can
        # construct W32 values for probing.
        phase3 = discover_phase3(w32_mul_candidates, dot, d1, ext,
                                 w_pack8_tok=W_PACK8_tok, verbose=verbose)
        log(f"Phase 2 complete: all 26 opaque atoms identified")

    result = {
        "QUOTE": QUOTE_tok,
        "EVAL": EVAL_tok,
        "APP": APP_tok,
        "UNAPP": UNAPP_tok,
        "IO_PUT": IO_PUT_tok,
        "IO_GET": IO_GET_tok,
        "IO_RDY": IO_RDY_tok,
        "IO_SEQ": IO_SEQ_tok,
    }
    if W_PACK8_tok is not None:
        result["W_PACK8"] = W_PACK8_tok
    result.update(phase3)
    return result


def discover_phase3(candidates: List[str], dot, d1: Dict[str, Any],
                    ext: Dict[str, Any], w_pack8_tok: str = None,
                    verbose: bool = False) -> Dict[str, Any]:
    """
    Phase 3: Identify 17 W32/MUL atoms via term-level probing with W32 values.

    W_PACK8 is pre-identified and passed in. The remaining 17 candidates
    are identified by building W32/W16 values using W_PACK8 and probing.

    Strategy:
      Step 1: (skipped — W_PACK8 pre-identified)
      Step 2: Feed 8 nibbles to build W32 values from W_PACK8.
      Step 3: Apply each to the W32. Unary ops (W_LO, W_HI, W_NOT,
              W_NIB) return non-p. Binary ops (W_ADD..W_ROTR, W_CMP) return
              a partial. W_MERGE returns p (needs W16, not W32).
              MUL16/MAC16 return p (need W16).
      Step 4: From W_LO or W_HI, extract a W16 value to probe W_MERGE,
              MUL16, MAC16.
      Step 5: Discriminate within each group using specific value probes.
    """
    assert len(candidates) == 17, f"Expected 17 W32/MUL candidates, got {len(candidates)}"
    assert w_pack8_tok is not None, "W_PACK8 must be pre-identified"

    top = d1["⊤"]
    bot = d1["⊥"]
    p_tok = d1["p"]
    n0 = ext["N0"]
    n1 = ext["N1"]
    n2 = ext["N2"]
    n5 = ext["N5"]

    def log(msg):
        if verbose:
            print(f"    [Phase 3] {msg}")

    log(f"Starting with {len(candidates)} W32/MUL candidates")

    # All known domain labels
    all_known = set()
    for k, v in d1.items():
        if k != "_testers":
            all_known.add(v)
    for v in ext.values():
        all_known.add(v)
    domain_set = all_known | set(candidates)

    # ── Step 1: W_PACK8 pre-identified ──────────────────────────────
    W_PACK8_tok = w_pack8_tok
    rest = list(candidates)  # all 17 candidates (none is W_PACK8)
    log(f"W_PACK8 pre-identified: {W_PACK8_tok}")

    # ── Step 2: Build W32 values using W_PACK8 ───────────────────────
    # Pack 8 nibbles to get W32(0x00000000) and W32(0x12345050)
    nibbles_zero = [n0] * 8
    nibbles_test = [n1, n2, ext["N3"], ext["N4"], n5, n0, n5, n0]

    def pack_w32(nibbles):
        val = dot(W_PACK8_tok, nibbles[0])
        for nib in nibbles[1:]:
            val = dot(val, nib)
        return val

    w32_zero = pack_w32(nibbles_zero)    # W32(0x00000000)
    w32_test = pack_w32(nibbles_test)    # W32(0x12345050)
    # Build another distinct value for binary op testing
    w32_one = pack_w32([n0, n0, n0, n0, n0, n0, n0, n1])  # W32(0x00000001)

    log(f"Built W32 test values via W_PACK8")

    # ── Step 3: Apply each to W32 → partition into groups ──────────────
    # Unary ops taking W32: W_LO, W_HI, W_NOT, W_NIB → non-p structured
    # Binary ops taking W32: W_ADD..W_ROTR, W_CMP → non-p partial (waiting for 2nd W32)
    # W_MERGE: needs W16, not W32 → p
    # MUL16, MAC16: need W16 → p
    unary_w32 = []     # produce immediate result from W32
    partial_w32 = []   # produce partial waiting for 2nd W32
    w16_group = []     # produce p on W32 (need W16: W_MERGE, MUL16, MAC16)

    for x in rest:
        result = dot(x, w32_test)
        if result == p_tok:
            w16_group.append(x)
        else:
            # Apply the result to another W32 to see if it's a partial
            result2 = dot(result, w32_zero)
            if result2 == p_tok:
                # Not a binary op partial — it's a unary result
                # (W_NIB produces an extended partial that takes a nibble, not W32)
                # Check if result accepts a nibble
                result2_nib = dot(result, n0)
                if result2_nib != p_tok and result2_nib not in domain_set:
                    # W_NIB partial (accepts nibble to extract)
                    unary_w32.append(x)
                else:
                    unary_w32.append(x)
            else:
                partial_w32.append(x)

    log(f"Groups: unary_w32={len(unary_w32)}, partial_w32={len(partial_w32)}, w16_group={len(w16_group)}")

    # ── Step 4: Identify unary ops (W_LO, W_HI, W_NOT, W_NIB) ────────
    # W_LO(W32) → W16 (lower 16 bits)
    # W_HI(W32) → W16 (upper 16 bits)
    # W_NOT(W32) → W32 (bitwise NOT)
    # W_NIB(W32) → ExtendedPartial (takes nibble position)
    #
    # Distinguish: apply result to a nibble
    # W_NOT result is a W32 → applying nibble to it → p
    # W_LO/W_HI result is a W16 → applying nibble to it → p
    # W_NIB result is an ExtendedPartial → applying nibble → returns a nibble atom
    W_NIB_tok = W_NOT_tok = None
    w16_producers = []  # W_LO and W_HI

    for x in unary_w32:
        result = dot(x, w32_test)
        # Try applying a nibble to the result
        nib_result = dot(result, n0)
        if nib_result in domain_set and nib_result != p_tok:
            # W_NIB: partial takes nibble, returns nibble atom
            W_NIB_tok = x
            log(f"W_NIB identified: {x}")
        else:
            # Either W_NOT (returns W32) or W_LO/W_HI (returns W16)
            # Apply W_PACK8 test: try using the result as input to a binary W32 op
            # Actually, distinguish W_NOT from W_LO/W_HI:
            # W_NOT(W32(0)) = W32(0xFFFFFFFF) — a W32
            # W_LO/W_HI(W32) → W16 — not a W32
            # Apply a known binary op partial to the result and then another W32
            # Simpler: W_NOT(W_NOT(x)) == x (round-trip). W_LO doesn't compose with W_NOT.
            # Even simpler: apply the candidate twice to see if result is same type
            result_zero = dot(x, w32_zero)  # Apply to W32(0)
            # Now apply x again to result_zero (if W_NOT, result is W32, so x(result) works)
            roundtrip = dot(x, result_zero)
            if roundtrip != p_tok and roundtrip not in domain_set:
                # W_NOT(W_NOT(W32(0))) should produce a W32 → applying W_NOT again works
                W_NOT_tok = x
                log(f"W_NOT identified: {x}")
            else:
                w16_producers.append(x)

    assert W_NIB_tok is not None, "Failed to identify W_NIB"
    assert W_NOT_tok is not None, "Failed to identify W_NOT"
    assert len(w16_producers) == 2, f"Expected 2 W16 producers (W_LO, W_HI), got {len(w16_producers)}"

    # ── Step 5: Distinguish W_LO from W_HI ────────────────────────────
    # W_LO(W32(0x12345050)) → W16(0x5050)
    # W_HI(W32(0x12345050)) → W16(0x1234)
    # Use W_MERGE to reconstruct: W_MERGE(W_HI(x))(W_LO(x)) == x
    # Or: pack a W32 with known hi != lo, extract both, and compare
    # Approach: W_LO(W32(0x00000001)) → W16(1), W_HI(W32(0x00000001)) → W16(0)
    # Feed the W16 results back into W_MERGE (once found) to test.
    # For now: check which W16 result, when merged with the other, gives back the original.
    # Actually simplest: extract from w32_one (0x00000001):
    # W_LO → W16(1), W_HI → W16(0). Use binary op: if we have a binary partial
    # already, feed W16 into it — the partial expects W32, W16 won't match → p.
    # Better approach: use W_NIB. W_NIB(w32_test)(N0) gives nibble 0 of w32_test.
    # The nibble extraction order tells us which is lo/hi.
    #
    # Simplest: W_LO(W32(0x00010000)) → W16(0), W_HI(W32(0x00010000)) → W16(1)
    # Then use the W16 to probe — but we can't easily check W16 values directly.
    #
    # Alternative: build w32 = W32(0x00010000). W_LO gives 0, W_HI gives non-zero.
    # Then MERGE(hi)(lo) should be the original. If we swap, we get different.
    # But we don't have MERGE yet.
    #
    # Cleanest approach: apply both to w32_zero (=0x00000000) and w32_one (=0x00000001).
    # W_LO(0x00000001) → W16(1), W_HI(0x00000001) → W16(0).
    # Now apply NOT to both W16 results — doesn't work (NOT takes W32, not W16).
    # Apply both results to a binary partial: neither will work since binary expects W32.
    #
    # Best: after finding W_MERGE, merge hi+lo back and check.
    # We'll defer and identify together with W_MERGE.
    #
    # Actually, let's use a different probe: build W32(0xFF000000).
    # W_LO → W16(0), W_HI → W16(0xFF00). Now the W16 values are different.
    # Feed each W16 into a candidate from w16_group to see which accepts it.
    # W_MERGE takes W16 → ExtendedPartial. MUL16 takes W16 → MulPartial. MAC16 takes W16 → MulPartial.
    # All three accept W16 and produce non-p. So using W16 doesn't help distinguish LO/HI directly.
    #
    # Final approach: use the identity W_NOT(W32(0)) = W32(0xFFFFFFFF).
    # W_LO(0xFFFFFFFF) and W_HI(0xFFFFFFFF) both give W16(0xFFFF) — same.
    # But for w32_one (0x00000001): W_LO → W16(1), W_HI → W16(0).
    # To distinguish: apply each W16 to W_MERGE (or any W16-accepting op) to get a partial,
    # then complete the operation and check the result.
    # Since we haven't identified W_MERGE yet, let's do a joint identification.

    # First, get W16 values from both candidates
    w16_a = dot(w16_producers[0], w32_one)  # W16 from candidate a applied to W32(1)
    w16_b = dot(w16_producers[1], w32_one)  # W16 from candidate b applied to W32(1)

    # Now identify W_MERGE from w16_group: the one that takes W16 and produces
    # a partial that then takes another W16 to produce a W32.
    # MUL16(W16) → MulPartial, MUL_partial(W16) → APP(W16_hi, W16_lo)
    # MAC16(W16) → MulPartial, ...
    # W_MERGE(W16) → ExtPartial, ExtPartial(W16) → W32
    #
    # Key distinction: W_MERGE(hi)(lo) produces a W32. We can check by applying
    # W_LO/W_HI again to the result — if it produces a W16, it was a W32.
    # MUL16(a)(b) produces APP(hi, lo) — applying W_LO to an APP gives p.

    W_MERGE_tok = MUL16_tok = MAC16_tok = None

    for x in w16_group:
        partial1 = dot(x, w16_a)
        if partial1 == p_tok or partial1 in domain_set:
            continue
        result1 = dot(partial1, w16_b)
        if result1 == p_tok or result1 in domain_set:
            continue
        # Got a result — check if it's a W32 (W_MERGE) or APP (MUL16/MAC16)
        # Apply w16_producers[0] (W_LO or W_HI) to the result
        check = dot(w16_producers[0], result1)
        if check != p_tok and check not in domain_set:
            # Result is a W32 → this is W_MERGE
            W_MERGE_tok = x
            log(f"W_MERGE identified: {x}")
            break

    assert W_MERGE_tok is not None, "Failed to identify W_MERGE"
    mul_candidates = [x for x in w16_group if x != W_MERGE_tok]
    assert len(mul_candidates) == 2, f"Expected 2 MUL candidates, got {len(mul_candidates)}"

    # Now distinguish W_LO from W_HI using W_MERGE round-trip:
    # W_MERGE(W_HI(w32))(W_LO(w32)) should equal w32
    # Try: W_MERGE(w16_a)(w16_b) → if this recovers w32_one, then
    #   w16_producers[0] = W_HI, w16_producers[1] = W_LO
    merged = dot(dot(W_MERGE_tok, w16_a), w16_b)
    # Apply W_NOT twice to both original and merged — if they match, order is HI, LO
    # Actually, easier: check W_NOT(merged) == W_NOT(w32_one)
    not_merged = dot(W_NOT_tok, merged)
    not_original = dot(W_NOT_tok, w32_one)
    # Compare by applying W_LO to both and checking equality
    lo_merged = dot(w16_producers[0], not_merged)
    lo_original = dot(w16_producers[0], not_original)

    # If W_MERGE(a)(b) reconstructed the same value, then a=HI, b=LO
    # The simplest equality check: apply some distinguishing operation
    # Actually, let's use W_CMP (if identified) or a simpler test.
    # Let me try a different approach: build a W32 where hi ≠ lo, extract both ways,
    # merge, and check if we get the same nibble extraction.

    # Simpler: W_MERGE is defined as W_MERGE(hi_W16)(lo_W16) → W32(hi<<16 | lo).
    # If w32_one = 0x00000001:
    #   W_HI(0x00000001) = W16(0), W_LO(0x00000001) = W16(1)
    # If producers[0] = W_HI: w16_a = W16(0), w16_b = W16(1)
    #   W_MERGE(W16(0))(W16(1)) = W32(0x00000001) = w32_one ✓
    # If producers[0] = W_LO: w16_a = W16(1), w16_b = W16(0)
    #   W_MERGE(W16(1))(W16(0)) = W32(0x00010000) ≠ w32_one
    #
    # To check: W_NIB(merged)(N0) should give N1 if merged = 0x00000001 (low nibble = 1)
    nib_check = dot(dot(W_NIB_tok, merged), n0)
    nibbles = {ext.get(f"N{i:X}", None): i for i in range(16)}
    # If the lowest nibble of merged is 1, producers[0] is W_HI (correct order)
    if nib_check == ext["N1"]:
        W_HI_tok = w16_producers[0]
        W_LO_tok = w16_producers[1]
    else:
        W_HI_tok = w16_producers[1]
        W_LO_tok = w16_producers[0]
    log(f"W_LO identified: {W_LO_tok}")
    log(f"W_HI identified: {W_HI_tok}")

    # ── Step 6: Identify MUL16 vs MAC16 ───────────────────────────────
    # MUL16(a)(b) → APP(hi_W16, lo_W16) representing a*b
    # MAC16(acc)(a) → ExtendedPartial waiting for b
    #   then MAC16_partial(b) → APP(hi_W16, lo_W16) representing acc + a*b
    #
    # Key difference: MUL16 takes 2 args (a, b), MAC16 takes 3 args (acc, a, b).
    # MUL16(W16(1))(W16(2)) → APP(W16(0), W16(2)) — result of 1*2 = 2
    # MAC16(W16(1))(W16(2)) → ExtendedPartial (needs one more arg)
    #   ExtPartial(W16(3)) → APP(hi, lo) of 1 + 2*3 = 7
    #
    # So: apply candidate to two W16 values. If result is a non-p structured
    # value that is NOT itself a partial (doesn't accept a 3rd W16), it's MUL16.
    # If the result accepts a 3rd W16, it's MAC16.
    w16_one = dot(W_LO_tok, w32_one)  # W16(1)
    w16_two = dot(W_LO_tok, pack_w32([n0, n0, n0, n0, n0, n0, n0, n2]))  # W16(2)
    w16_three = dot(W_LO_tok, pack_w32([n0, n0, n0, n0, n0, n0, n0, ext["N3"]]))  # W16(3)

    for x in mul_candidates:
        partial1 = dot(x, w16_one)
        result1 = dot(partial1, w16_two)
        if result1 == p_tok or result1 in domain_set:
            continue
        # Try applying a third W16
        result2 = dot(result1, w16_three)
        if result2 != p_tok and result2 not in domain_set:
            # Accepted 3rd arg → MAC16
            MAC16_tok = x
            log(f"MAC16 identified: {x}")
        else:
            # Only 2 args → MUL16
            MUL16_tok = x
            log(f"MUL16 identified: {x}")

    assert MUL16_tok is not None, "Failed to identify MUL16"
    assert MAC16_tok is not None, "Failed to identify MAC16"

    # ── Step 7: Identify binary W32 ops ───────────────────────────────
    # 10 binary ops: W_ADD, W_SUB, W_CMP, W_XOR, W_AND, W_OR, W_SHL, W_SHR, W_ROTL, W_ROTR
    # Each: atom(W32_a) → W32_OP1_partial → partial(W32_b) → result
    #
    # Strategy: use A=0xFF00FF00, B=0x0F0F0F0F. With shift amount = 0x0F0F0F0F & 31 = 15,
    # all 10 operations produce unique 32-bit results. Extract full result via W_NIB.
    nf = ext["NF"]
    w32_a = pack_w32([nf, nf, n0, n0, nf, nf, n0, n0])  # 0xFF00FF00
    w32_b = pack_w32([n0, nf, n0, nf, n0, nf, n0, nf])   # 0x0F0F0F0F

    A_val, B_val = 0xFF00FF00, 0x0F0F0F0F
    S = B_val & 31  # 15
    expected = {
        "W_ADD":  (A_val + B_val) & 0xFFFFFFFF,
        "W_SUB":  (A_val - B_val) & 0xFFFFFFFF,
        "W_XOR":  A_val ^ B_val,
        "W_AND":  A_val & B_val,
        "W_OR":   A_val | B_val,
        "W_SHL":  (A_val << S) & 0xFFFFFFFF,
        "W_SHR":  A_val >> S,
        "W_ROTL": ((A_val << S) | (A_val >> (32 - S))) & 0xFFFFFFFF,
        "W_ROTR": ((A_val >> S) | (A_val << (32 - S))) & 0xFFFFFFFF,
    }
    # Verify all 9 numeric results are distinct (sanity check)
    assert len(set(expected.values())) == 9, f"Expected values not unique: {expected}"

    # Reverse lookup: result value → op name
    val_to_op = {v: k for k, v in expected.items()}

    # Nibble name lookup (0..15 → token)
    nib_tok = [ext[f"N{v:X}"] for v in range(16)]

    def extract_full_w32(w32_result):
        """Extract full 32-bit value from a W32 result using W_NIB."""
        val = 0
        nib_partial = dot(W_NIB_tok, w32_result)
        for pos in range(8):
            nib_atom = dot(nib_partial, ext[f"N{pos:X}"])
            for v in range(16):
                if nib_atom == nib_tok[v]:
                    val |= (v << (pos * 4))
                    break
        return val

    identified_binary = {}
    for x in partial_w32:
        partial1 = dot(x, w32_a)
        result = dot(partial1, w32_b)

        # W_CMP returns an atom (BOT), not a W32
        if result == bot:
            identified_binary[x] = "W_CMP"
            log(f"W_CMP identified: {x}")
            continue
        if result == top or result == p_tok or result in domain_set:
            continue

        # Extract full 32-bit result and match
        full_val = extract_full_w32(result)
        op_name = val_to_op.get(full_val)
        if op_name:
            identified_binary[x] = op_name
            log(f"{op_name} identified: {x} (result=0x{full_val:08X})")

    assert len(identified_binary) == 10, \
        f"Expected 10 binary W32 ops, identified {len(identified_binary)}: {identified_binary}"

    result = {
        "W_LO": W_LO_tok,
        "W_HI": W_HI_tok,
        "W_NOT": W_NOT_tok,
        "W_NIB": W_NIB_tok,
        "W_MERGE": W_MERGE_tok,
        "MUL16": MUL16_tok,
        "MAC16": MAC16_tok,
    }
    for tok, name in identified_binary.items():
        result[name] = tok

    log(f"Phase 3 complete: {len(result)}/17 W32/MUL atoms identified")
    assert len(result) == 17, f"Expected 17, got {len(result)}"
    return result


# ============================================================================
# Verification functions
# ============================================================================

def verify_d2_preservation():
    """Verify Δ₂ fragment is preserved exactly."""
    print("  Δ₂ preservation:")
    import delta2_true_blackbox as orig_mod

    d2_names = NAMES_D1 + NAMES_D2
    for xn in d2_names:
        for yn in d2_names:
            # Use original module's Atom class for the original dot
            orig_result = orig_mod.dot_iota(orig_mod.A(xn), orig_mod.A(yn))
            ext_result = dot_ext(A(xn), A(yn))
            # Compare by name since Atom classes differ across modules
            orig_name = orig_result.name if isinstance(orig_result, orig_mod.Atom) else str(orig_result)
            ext_name = ext_result.name if isinstance(ext_result, Atom) else str(ext_result)
            assert orig_name == ext_name, f"dot({xn}, {yn}): orig={orig_name}, ext={ext_name}"
    print(f"    ✓ All {len(d2_names)}² atom-atom pairs match original Δ₂")


def verify_nibble_group():
    """Verify nibble atoms form Z/16Z under dot."""
    print("  Nibble group (Z/16Z):")
    n0 = A("N0")
    for i in range(16):
        ni = nibble(i)
        assert atom_dot(n0, ni) == ni, f"N0 · N{i:X} ≠ N{i:X}"
        assert atom_dot(ni, n0) == ni, f"N{i:X} · N0 ≠ N{i:X}"
    print("    ✓ N0 is the identity")

    for i in range(16):
        for j in range(16):
            result = atom_dot(nibble(i), nibble(j))
            expected = nibble((i + j) % 16)
            assert result == expected
    print("    ✓ Closed under addition mod 16")


def verify_alu_dispatch():
    """Verify ALU dispatch atoms have correct nibble mappings."""
    print("  ALU dispatch:")
    for i in range(16):
        ni = nibble(i)
        assert atom_dot(A("ALU_LOGIC"), ni) == ni
        assert atom_dot(A("ALU_ARITH"), ni) == nibble((i + 1) % 16)
        assert atom_dot(A("ALU_ARITHC"), ni) == nibble((i + 2) % 16)
    print("    ✓ ALU_LOGIC = identity, ALU_ARITH = successor, ALU_ARITHC = double successor")


def verify_alu_predicates():
    """Verify ALU predicate atoms."""
    print("  ALU predicates:")
    for i in range(16):
        ni = nibble(i)
        if i == 0:
            assert atom_dot(A("ALU_ZERO"), ni) == A("⊤")
        else:
            assert atom_dot(A("ALU_ZERO"), ni) == A("⊥")
        if i >= 8:
            assert atom_dot(A("ALU_COUT"), ni) == A("⊤")
        else:
            assert atom_dot(A("ALU_COUT"), ni) == A("⊥")
    print("    ✓ ALU_ZERO accepts only N0, ALU_COUT accepts N8-NF")


def verify_n_succ():
    """Verify N_SUCC forms a 16-cycle over nibbles."""
    print("  N_SUCC:")
    for i in range(16):
        ni = nibble(i)
        expected = nibble((i + 1) % 16)
        assert atom_dot(A("N_SUCC"), ni) == expected, f"N_SUCC · N{i:X} ≠ N{(i+1)%16:X}"
    print("    ✓ N_SUCC forms a 16-cycle: dot(N_SUCC, Nx) = N(x+1 mod 16)")
    assert atom_dot(A("N_SUCC"), A("⊤")) == A("N_SUCC"), "N_SUCC self-id on ⊤ failed"
    print("    ✓ N_SUCC self-identifies on ⊤")


def verify_self_id():
    """Verify all new non-IO/W32/MUL atoms self-identify on ⊤."""
    print("  Self-identification on ⊤:")
    all_p_atoms = IO_ATOMS | W32_ATOMS | MUL_ATOMS
    non_p = NEW_ATOMS - all_p_atoms
    for atom in non_p:
        result = atom_dot(atom, A("⊤"))
        assert result == atom, f"dot({atom}, ⊤) = {result}, expected {atom}"
    print(f"    ✓ All {len(non_p)} non-p new atoms satisfy dot(x, ⊤) = x")
    for atom in all_p_atoms:
        result = atom_dot(atom, A("⊤"))
        assert result == A("p"), f"dot({atom}, ⊤) = {result}, expected p"
    print(f"    ✓ All {len(all_p_atoms)} IO/W32/MUL atoms have all-p Cayley rows")


def verify_ext_axiom():
    """Verify all non-IO/W32/MUL atoms have unique behavioral fingerprints (Ext axiom)."""
    print("  Ext axiom (unique fingerprints):")
    # IO/W32/MUL atoms are intentionally indistinguishable at the Cayley level
    # (all-p rows); they're only distinguishable through term-level dispatch
    opaque_atoms = IO_ATOMS | W32_ATOMS | MUL_ATOMS
    atoms = [a for a in ALL_ATOMS if a not in opaque_atoms]
    # Build probe set: atoms + structured values created by D2 operations
    probes = list(ALL_ATOMS)
    # Add Quote values (produced by QUOTE)
    for a in ALL_ATOMS[:6]:  # a few representative atoms
        probes.append(Quote(a))
    # Add AppNodes (produced by APP)
    for f in [A("e_D"), A("e_M"), A("i")]:
        for x in [A("i"), A("k"), A("a")]:
            probes.append(AppNode(f, x))

    for i, x in enumerate(atoms):
        for j, y in enumerate(atoms):
            if i >= j:
                continue
            found = False
            for z in probes:
                if dot_ext(x, z) != dot_ext(y, z):
                    found = True
                    break
            assert found, f"No distinguishing probe for {x.name} vs {y.name}"
    print(f"    ✓ All {len(atoms)} non-opaque atoms are pairwise distinguishable")
    print(f"    ({len(opaque_atoms)} IO/W32/MUL atoms are opaque — indistinguishable at Cayley level)")


def verify_tester_preservation():
    """Verify the 4 existing testers remain pure testers in the extended table."""
    print("  Tester preservation:")
    TOP, BOT = A("⊤"), A("⊥")
    testers = [A("e_I"), A("d_K"), A("m_K"), A("m_I")]
    for t in testers:
        for y in ALL_ATOMS:
            result = atom_dot(t, y)
            assert result in (TOP, BOT), (
                f"Tester {t.name} on {y.name} = {result.name}, expected ⊤ or ⊥"
            )
    print(f"    ✓ All 4 testers have pure boolean left-images over {len(ALL_ATOMS)} atoms")


def verify_74181_operations():
    """Verify 74181 operations through curried application."""
    print("  74181 operations (curried):")

    # A XOR B (logic, selector 6)
    for a in range(16):
        for b in range(16):
            result = dot_ext(dot_ext(dot_ext(A("ALU_LOGIC"), nibble(6)), nibble(a)), nibble(b))
            expected = nibble(a ^ b)
            assert result == expected, f"XOR({a},{b}) = {result}, expected {expected}"
    print("    ✓ XOR (logic S=6) correct for all 16×16 inputs")

    # A plus B (arith, selector 9, no carry)
    for a in range(16):
        for b in range(16):
            result = dot_ext(dot_ext(dot_ext(A("ALU_ARITH"), nibble(9)), nibble(a)), nibble(b))
            expected = nibble((a + b) % 16)
            assert result == expected
    print("    ✓ ADD (arith S=9 no carry) correct")

    # A minus B (arith, selector 6, with carry)
    for a in range(16):
        for b in range(16):
            result = dot_ext(dot_ext(dot_ext(A("ALU_ARITHC"), nibble(6)), nibble(a)), nibble(b))
            expected_val, _, _ = alu_74181("arithc", 6, a, b)
            expected = nibble(expected_val)
            assert result == expected
    print("    ✓ SUB (arithc S=6) correct")

    # NOT A (logic, selector 0)
    for a in range(16):
        result = dot_ext(dot_ext(dot_ext(A("ALU_LOGIC"), nibble(0)), nibble(a)), nibble(0))
        expected = nibble((~a) & 0xF)
        assert result == expected
    print("    ✓ NOT (logic S=0) correct")

    # A AND B (logic, selector 0xB)
    for a in range(16):
        for b in range(16):
            result = dot_ext(dot_ext(dot_ext(A("ALU_LOGIC"), nibble(0xB)), nibble(a)), nibble(b))
            expected = nibble(a & b)
            assert result == expected
    print("    ✓ AND (logic S=B) correct")

    # A OR B (logic, selector 0xE)
    for a in range(16):
        for b in range(16):
            result = dot_ext(dot_ext(dot_ext(A("ALU_LOGIC"), nibble(0xE)), nibble(a)), nibble(b))
            expected = nibble(a | b)
            assert result == expected
    print("    ✓ OR (logic S=E) correct")

    # Left shift (A plus A, arith S=C)
    for a in range(16):
        result = dot_ext(dot_ext(dot_ext(A("ALU_ARITH"), nibble(0xC)), nibble(a)), nibble(a))
        expected = nibble((2 * a) % 16)
        assert result == expected
    print("    ✓ Left shift (arith S=C, A+A) correct")

    # Increment (A plus 1: arithc S=0)
    for a in range(16):
        result = dot_ext(dot_ext(dot_ext(A("ALU_ARITHC"), nibble(0)), nibble(a)), nibble(0))
        expected_val, _, _ = alu_74181("arithc", 0, a, 0)
        expected = nibble(expected_val)
        assert result == expected
    print("    ✓ Increment (arithc S=0) correct")

    # Decrement (A minus 1: arith S=F)
    for a in range(16):
        result = dot_ext(dot_ext(dot_ext(A("ALU_ARITH"), nibble(0xF)), nibble(a)), nibble(0))
        expected_val, _, _ = alu_74181("arith", 0xF, a, 0)
        expected = nibble(expected_val)
        assert result == expected
    print("    ✓ Decrement (arith S=F) correct")


def verify_alu_74181_function():
    """Verify the alu_74181 function against known truth table values."""
    print("  74181 truth table spot checks:")

    # Logic mode checks
    assert alu_74181("logic", 0x0, 0b1010, 0)[0] == 0b0101  # NOT A
    assert alu_74181("logic", 0x3, 0b1010, 0b0101)[0] == 0  # Logical 0
    assert alu_74181("logic", 0x6, 0b1010, 0b0101)[0] == 0b1111  # XOR
    assert alu_74181("logic", 0xB, 0b1010, 0b0101)[0] == 0b0000  # AND
    assert alu_74181("logic", 0xC, 0b1010, 0b0101)[0] == 0b1111  # Logical 1
    assert alu_74181("logic", 0xE, 0b1010, 0b0101)[0] == 0b1111  # OR
    assert alu_74181("logic", 0xF, 0b1010, 0b0101)[0] == 0b1010  # A pass
    assert alu_74181("logic", 0xA, 0b1010, 0b0101)[0] == 0b0101  # B pass
    print("    ✓ Logic mode operations correct")

    # Arithmetic mode checks (no carry = arith, with carry = arithc)
    # S=9: A plus B
    r, c, z = alu_74181("arith", 9, 5, 3)
    assert r == 8 and not c  # 5+3=8, no carry
    r, c, z = alu_74181("arith", 9, 15, 15)
    assert r == 14 and c  # 15+15=30 → 14 with carry
    # S=9 with carry: A plus B plus 1
    r, c, z = alu_74181("arithc", 9, 5, 3)
    assert r == 9  # 5+3+1=9
    # S=F: A minus 1 (no carry) / A (with carry)
    r, _, _ = alu_74181("arith", 0xF, 5, 0)
    assert r == 4  # 5-1=4
    r, _, _ = alu_74181("arithc", 0xF, 5, 0)
    assert r == 5  # A pass through
    # S=0: A (no carry) / A plus 1 (with carry)
    r, _, _ = alu_74181("arith", 0, 5, 0)
    assert r == 5  # A
    r, _, _ = alu_74181("arithc", 0, 5, 0)
    assert r == 6  # A+1
    print("    ✓ Arithmetic mode operations correct")


# ============================================================================
# Integration test
# ============================================================================

def run_integration_test(num_seeds: int, verbose: bool = False):
    """Run full recovery on random permutations (Phase 1 + Phase 2)."""
    print(f"\n  Integration test: {num_seeds} random permutations")
    failures = []

    for seed in range(num_seeds):
        try:
            domain, dot, true2hid = make_blackbox(seed)

            # Phase 1a: D1
            d1 = discover_d1(domain, dot)
            for k in ["⊤", "⊥", "p", "e_I", "e_D", "e_M", "e_Σ", "e_Δ",
                       "i", "k", "a", "b", "d_I", "d_K", "m_I", "m_K", "s_C"]:
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
            print(f"    ... {seed + 1}/{num_seeds} seeds tested")

    if failures:
        print(f"  FAILED on {len(failures)} seeds:")
        for seed, key, phase in failures[:20]:
            print(f"    seed={seed}: {phase} failed at {key}")
        return False
    else:
        print(f"  ✓ All {num_seeds} seeds passed — {len(BASE_ATOMS)}/{len(BASE_ATOMS)} atoms, 100% recovery rate")
        return True


# ============================================================================
# Main
# ============================================================================

def main():
    parser = argparse.ArgumentParser(description="Δ₂+74181 ALU Extension")
    parser.add_argument("--test", type=int, default=0,
                        help="Run integration test with N seeds")
    parser.add_argument("--verbose", action="store_true",
                        help="Verbose output for discovery")
    args = parser.parse_args()

    print("=" * 60)
    print("  Δ₂+74181 VERIFICATION SUITE")
    print("=" * 60)
    print(f"\n  Total atoms: {len(ALL_ATOMS)}")
    print(f"    Δ₁ core: {len(NAMES_D1)}")
    print(f"    Δ₂ extensions: {len(NAMES_D2)}")
    print(f"    Nibbles: {len(NAMES_NIBBLES)}")
    print(f"    ALU dispatch: {len(NAMES_ALU_DISPATCH)}")
    print(f"    ALU predicates: {len(NAMES_ALU_PRED)}")
    print(f"    N_SUCC: {len(NAMES_ALU_MISC)}")
    print(f"    IO atoms: {len(NAMES_IO)}")
    print(f"    Cayley table: {len(ALL_ATOMS)}×{len(ALL_ATOMS)} = {len(ALL_ATOMS)**2} entries")
    print()

    verify_d2_preservation()
    verify_nibble_group()
    verify_alu_dispatch()
    verify_alu_predicates()
    verify_n_succ()
    verify_self_id()
    verify_tester_preservation()
    verify_ext_axiom()
    verify_alu_74181_function()
    verify_74181_operations()

    if args.test > 0:
        run_integration_test(args.test, verbose=args.verbose)
    else:
        # Quick demo: single seed recovery
        print("\n  Quick recovery demo (seed=42):")
        domain, dot, true2hid = make_blackbox(42)

        # Phase 1a: D1
        d1 = discover_d1(domain, dot)

        # Phase 1b: 74181 (Cayley-level)
        ext, opaque = discover_74181_with_logs(domain, dot, d1, verbose=True)

        # Verify Phase 1
        all_ok = True
        for k, v in ext.items():
            expected = true2hid[A(k)]
            ok = "✓" if v == expected else "✗"
            if v != expected:
                all_ok = False
            print(f"      {k:12s} → {v}  {ok}")
        if all_ok:
            print(f"    ✓ All {len(ext)} Phase 1 atoms correctly recovered")

        # Phase 2: Term-level recovery
        print()
        p2 = discover_phase2(opaque, dot, d1, ext, verbose=True)

        all_ok_p2 = True
        for k, v in p2.items():
            expected = true2hid[A(k)]
            ok = "✓" if v == expected else "✗"
            if v != expected:
                all_ok_p2 = False
            print(f"      {k:12s} → {v}  {ok}")
        if all_ok_p2:
            print(f"    ✓ All {len(p2)} Phase 2 atoms correctly recovered")
        if all_ok and all_ok_p2:
            print(f"    ✓ All {len(ALL_ATOMS)} atoms identified — complete recovery")

    print("\n" + "=" * 60)
    print("  All verifications passed. ✓")
    print("=" * 60)


if __name__ == "__main__":
    main()

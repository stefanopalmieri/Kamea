"""
Cayley ROM builder for the Kamea machine.

Generates the 47×47 atom-level Cayley table as a flat byte array
suitable for EEPROM, plus atom name/index constants.
"""

from __future__ import annotations

import sys
import os

# Add parent directory so we can import kamea
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from kamea import ALL_NAMES, A, atom_dot

# ---------------------------------------------------------------------------
# Atom name ↔ index mapping
# ---------------------------------------------------------------------------

NUM_ATOMS = len(ALL_NAMES)  # 47

# Name → 6-bit index
NAME_TO_IDX: dict[str, int] = {name: i for i, name in enumerate(ALL_NAMES)}

# Index → name
IDX_TO_NAME: list[str] = list(ALL_NAMES)

# Convenient constants (indices)
TOP       = NAME_TO_IDX["⊤"]         # 0
BOT       = NAME_TO_IDX["⊥"]         # 1
P         = NAME_TO_IDX["p"]         # 16
QUOTE     = NAME_TO_IDX["QUOTE"]     # 17
EVAL      = NAME_TO_IDX["EVAL"]      # 18
APP       = NAME_TO_IDX["APP"]       # 19
UNAPP     = NAME_TO_IDX["UNAPP"]     # 20
N0        = NAME_TO_IDX["N0"]        # 21
NF        = NAME_TO_IDX["NF"]        # 36
ALU_LOGIC = NAME_TO_IDX["ALU_LOGIC"] # 37
ALU_ARITH = NAME_TO_IDX["ALU_ARITH"] # 38
ALU_ARITHC = NAME_TO_IDX["ALU_ARITHC"] # 39
ALU_ZERO  = NAME_TO_IDX["ALU_ZERO"]  # 40
ALU_COUT  = NAME_TO_IDX["ALU_COUT"]  # 41
N_SUCC    = NAME_TO_IDX["N_SUCC"]    # 42
IO_PUT    = NAME_TO_IDX["IO_PUT"]    # 43
IO_GET    = NAME_TO_IDX["IO_GET"]    # 44
IO_RDY    = NAME_TO_IDX["IO_RDY"]    # 45
IO_SEQ    = NAME_TO_IDX["IO_SEQ"]    # 46

# W32/MUL atom indices (47-64)
W_PACK8   = NAME_TO_IDX["W_PACK8"]  # 47
W_LO      = NAME_TO_IDX["W_LO"]     # 48
W_HI      = NAME_TO_IDX["W_HI"]     # 49
W_MERGE   = NAME_TO_IDX["W_MERGE"]  # 50
W_NIB     = NAME_TO_IDX["W_NIB"]    # 51
W_ADD     = NAME_TO_IDX["W_ADD"]    # 52
W_SUB     = NAME_TO_IDX["W_SUB"]    # 53
W_CMP     = NAME_TO_IDX["W_CMP"]    # 54
W_XOR     = NAME_TO_IDX["W_XOR"]    # 55
W_AND     = NAME_TO_IDX["W_AND"]    # 56
W_OR      = NAME_TO_IDX["W_OR"]     # 57
W_NOT     = NAME_TO_IDX["W_NOT"]    # 58
W_SHL     = NAME_TO_IDX["W_SHL"]    # 59
W_SHR     = NAME_TO_IDX["W_SHR"]    # 60
W_ROTL    = NAME_TO_IDX["W_ROTL"]   # 61
W_ROTR    = NAME_TO_IDX["W_ROTR"]   # 62
MUL16     = NAME_TO_IDX["MUL16"]    # 63
MAC16     = NAME_TO_IDX["MAC16"]    # 64

NIBBLE_BASE = N0  # 21
NIBBLE_END  = NF  # 36 (inclusive)

ALU_DISPATCH_SET = frozenset([ALU_LOGIC, ALU_ARITH, ALU_ARITHC])
ALU_PRED_SET     = frozenset([ALU_ZERO, ALU_COUT])
IO_SET           = frozenset([IO_PUT, IO_GET, IO_RDY, IO_SEQ])
D2_SET           = frozenset([QUOTE, EVAL, APP, UNAPP])
W32_SET          = frozenset([W_PACK8, W_LO, W_HI, W_MERGE, W_NIB,
                              W_ADD, W_SUB, W_CMP, W_XOR, W_AND, W_OR, W_NOT,
                              W_SHL, W_SHR, W_ROTL, W_ROTR])
MUL_SET          = frozenset([MUL16, MAC16])


def is_nibble(idx: int) -> bool:
    return NIBBLE_BASE <= idx <= NIBBLE_END


def nibble_val(idx: int) -> int:
    """Extract numeric value (0-15) from nibble atom index."""
    return idx - NIBBLE_BASE


def nibble_idx(val: int) -> int:
    """Convert numeric value (0-15) to nibble atom index."""
    return NIBBLE_BASE + (val & 0xF)


# ---------------------------------------------------------------------------
# Cayley ROM construction
# ---------------------------------------------------------------------------

def build_cayley_rom() -> bytes:
    """
    Build the 47×47 Cayley table as a flat byte array.

    Layout: rom[x * NUM_ATOMS + y] = atom_dot(x, y) as 6-bit index.
    Total size: 47 * 47 = 2209 bytes.
    """
    rom = bytearray(NUM_ATOMS * NUM_ATOMS)
    for xi, xn in enumerate(ALL_NAMES):
        for yi, yn in enumerate(ALL_NAMES):
            result = atom_dot(A(xn), A(yn))
            ri = NAME_TO_IDX[result.name]
            rom[xi * NUM_ATOMS + yi] = ri
    return bytes(rom)


def build_cayley_rom_scrambled(seed: int) -> tuple[bytes, list[int]]:
    """
    Build a scrambled Cayley ROM (for black-box recovery testing).

    Returns (rom_bytes, perm) where perm[i] = original index of scrambled index i.
    """
    import random
    rng = random.Random(seed)

    # Create a random permutation of atom indices
    perm = list(range(NUM_ATOMS))
    rng.shuffle(perm)
    inv_perm = [0] * NUM_ATOMS
    for i, p in enumerate(perm):
        inv_perm[p] = i

    # Build the scrambled ROM
    rom = bytearray(NUM_ATOMS * NUM_ATOMS)
    for xi, xn in enumerate(ALL_NAMES):
        for yi, yn in enumerate(ALL_NAMES):
            result = atom_dot(A(xn), A(yn))
            ri = NAME_TO_IDX[result.name]
            # Scramble: inv_perm maps original → scrambled
            sx = inv_perm[xi]
            sy = inv_perm[yi]
            sr = inv_perm[ri]
            rom[sx * NUM_ATOMS + sy] = sr
    return bytes(rom), perm


if __name__ == "__main__":
    rom = build_cayley_rom()
    print(f"Cayley ROM: {len(rom)} bytes ({NUM_ATOMS}×{NUM_ATOMS})")
    # Verify a few entries
    assert rom[TOP * NUM_ATOMS + BOT] == TOP, "⊤·⊥ should be ⊤"
    assert rom[BOT * NUM_ATOMS + TOP] == BOT, "⊥·⊤ should be ⊥"
    assert rom[QUOTE * NUM_ATOMS + TOP] == P, "QUOTE·⊤ should be p"
    assert rom[N0 * NUM_ATOMS + N0] == N0, "N0·N0 should be N0"
    n1 = NAME_TO_IDX["N1"]
    n2 = NAME_TO_IDX["N2"]
    assert rom[n1 * NUM_ATOMS + n1] == n2, "N1+N1 should be N2"
    print("All spot-checks passed.")

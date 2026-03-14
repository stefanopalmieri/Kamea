"""
Structural fingerprints for the Kamea machine.

Each atom gets a canonical fingerprint ordinal derived deterministically
from the Cayley table via WL-1 color refinement. Fingerprints are natural
keys — structurally derived, permutation-invariant, and reproducible by
anyone given only the raw table.

Programs store fingerprints in atom words. The Cayley ROM is addressed and
valued entirely in fingerprint space, so no runtime translation is needed.
"""

from __future__ import annotations

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from kamea import ALL_NAMES, A, atom_dot
from .wl_fingerprint import canonical_wl

# ---------------------------------------------------------------------------
# Build raw Cayley table and run canonical WL
# ---------------------------------------------------------------------------

_NUM_ATOMS = len(ALL_NAMES)  # 66
_NAME_TO_PHYS = {name: i for i, name in enumerate(ALL_NAMES)}

_raw_table: list[list[int]] = [[0] * _NUM_ATOMS for _ in range(_NUM_ATOMS)]
for _xi, _xn in enumerate(ALL_NAMES):
    for _yi, _yn in enumerate(ALL_NAMES):
        _result = atom_dot(A(_xn), A(_yn))
        _raw_table[_xi][_yi] = _NAME_TO_PHYS[_result.name]

_ordinals = canonical_wl(_raw_table)

assert len(set(_ordinals)) == _NUM_ATOMS, (
    f"WL failed to fully discriminate: {len(set(_ordinals))} unique colors "
    f"for {_NUM_ATOMS} atoms"
)

# ---------------------------------------------------------------------------
# Canonical fingerprint ordinals (computed from WL)
# ---------------------------------------------------------------------------

NUM_FP = _NUM_ATOMS

# Name → fingerprint ordinal
NAME_TO_FP: dict[str, int] = {
    name: _ordinals[i] for i, name in enumerate(ALL_NAMES)
}

# Fingerprint ordinal → name
FP_TO_NAME: dict[int, str] = {v: k for k, v in NAME_TO_FP.items()}

# Generate all FP_* constants dynamically
# Nibbles
FP_N0  = NAME_TO_FP["N0"];  FP_N1  = NAME_TO_FP["N1"]
FP_N2  = NAME_TO_FP["N2"];  FP_N3  = NAME_TO_FP["N3"]
FP_N4  = NAME_TO_FP["N4"];  FP_N5  = NAME_TO_FP["N5"]
FP_N6  = NAME_TO_FP["N6"];  FP_N7  = NAME_TO_FP["N7"]
FP_N8  = NAME_TO_FP["N8"];  FP_N9  = NAME_TO_FP["N9"]
FP_NA  = NAME_TO_FP["NA"];  FP_NB  = NAME_TO_FP["NB"]
FP_NC  = NAME_TO_FP["NC"];  FP_ND  = NAME_TO_FP["ND"]
FP_NE  = NAME_TO_FP["NE"];  FP_NF  = NAME_TO_FP["NF"]

# D1 core
FP_TOP = NAME_TO_FP["⊤"];     FP_BOT = NAME_TO_FP["⊥"]
FP_I   = NAME_TO_FP["i"];     FP_K   = NAME_TO_FP["k"]
FP_A   = NAME_TO_FP["a"];     FP_B   = NAME_TO_FP["b"]
FP_E_I = NAME_TO_FP["e_I"];   FP_D_K = NAME_TO_FP["d_K"]
FP_M_I = NAME_TO_FP["m_I"];   FP_M_K = NAME_TO_FP["m_K"]
FP_E_D = NAME_TO_FP["e_D"];   FP_E_M = NAME_TO_FP["e_M"]
FP_D_I = NAME_TO_FP["d_I"];   FP_E_S = NAME_TO_FP["e_Σ"]
FP_S_C = NAME_TO_FP["s_C"];   FP_E_DELTA = NAME_TO_FP["e_Δ"]

# Extras
FP_P         = NAME_TO_FP["p"]
FP_ALU_LOGIC = NAME_TO_FP["ALU_LOGIC"]
FP_ALU_ARITH = NAME_TO_FP["ALU_ARITH"]
FP_ALU_ARITHC = NAME_TO_FP["ALU_ARITHC"]
FP_ALU_ZERO  = NAME_TO_FP["ALU_ZERO"]
FP_ALU_COUT  = NAME_TO_FP["ALU_COUT"]
FP_N_SUCC    = NAME_TO_FP["N_SUCC"]
FP_QUALE     = NAME_TO_FP["QUALE"]

# D2
FP_QUOTE  = NAME_TO_FP["QUOTE"];  FP_EVAL  = NAME_TO_FP["EVAL"]
FP_APP    = NAME_TO_FP["APP"];    FP_UNAPP = NAME_TO_FP["UNAPP"]
FP_IO_PUT = NAME_TO_FP["IO_PUT"]; FP_IO_GET = NAME_TO_FP["IO_GET"]
FP_IO_RDY = NAME_TO_FP["IO_RDY"]; FP_IO_SEQ = NAME_TO_FP["IO_SEQ"]

# W32 atoms
FP_W_PACK8 = NAME_TO_FP["W_PACK8"]; FP_W_LO   = NAME_TO_FP["W_LO"]
FP_W_HI    = NAME_TO_FP["W_HI"];    FP_W_MERGE = NAME_TO_FP["W_MERGE"]
FP_W_NIB   = NAME_TO_FP["W_NIB"];   FP_W_ADD   = NAME_TO_FP["W_ADD"]
FP_W_SUB   = NAME_TO_FP["W_SUB"];   FP_W_CMP   = NAME_TO_FP["W_CMP"]
FP_W_XOR   = NAME_TO_FP["W_XOR"];   FP_W_AND   = NAME_TO_FP["W_AND"]
FP_W_OR    = NAME_TO_FP["W_OR"];    FP_W_NOT   = NAME_TO_FP["W_NOT"]
FP_W_SHL   = NAME_TO_FP["W_SHL"];   FP_W_SHR   = NAME_TO_FP["W_SHR"]
FP_W_ROTL  = NAME_TO_FP["W_ROTL"];  FP_W_ROTR  = NAME_TO_FP["W_ROTR"]

# MUL atoms
FP_MUL16 = NAME_TO_FP["MUL16"]; FP_MAC16 = NAME_TO_FP["MAC16"]

# ---------------------------------------------------------------------------
# Precomputed sets for dispatch
# ---------------------------------------------------------------------------

FP_ALU_DISPATCH_SET = frozenset({FP_ALU_LOGIC, FP_ALU_ARITH, FP_ALU_ARITHC})

FP_W32_BINARY_OPS: dict[int, int] = {
    FP_W_ADD: 0, FP_W_SUB: 1, FP_W_CMP: 2,
    FP_W_XOR: 3, FP_W_AND: 4, FP_W_OR: 5,
    FP_W_SHL: 6, FP_W_SHR: 7, FP_W_ROTL: 8, FP_W_ROTR: 9,
}

# Nibble fingerprint set and lookup tables (for machine.py)
FP_NIBBLES = frozenset({
    FP_N0, FP_N1, FP_N2, FP_N3, FP_N4, FP_N5, FP_N6, FP_N7,
    FP_N8, FP_N9, FP_NA, FP_NB, FP_NC, FP_ND, FP_NE, FP_NF,
})

# fp → nibble value (0-15)
FP_TO_NIBBLE_VAL: dict[int, int] = {
    NAME_TO_FP[f"N{i:X}"]: i for i in range(16)
}

# nibble value (0-15) → fp
NIBBLE_VAL_TO_FP: list[int] = [NAME_TO_FP[f"N{i:X}"] for i in range(16)]

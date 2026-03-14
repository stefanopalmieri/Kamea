"""
Kamea machine — clocked eval/apply state machine for the 66-atom DS algebra.

Models the hardware architecture: Cayley ROM, IC74181 ALU, SRAM heap,
hardware stack, UART FIFOs, and a microcode-driven state machine.

Atom words store structural fingerprints (not physical indices). The Cayley
ROM is addressed and valued entirely in fingerprint space — no runtime
translation or scanner needed.
"""

from __future__ import annotations

from .chips import EEPROM, IC74181, SRAM, Register, FIFO
from . import cayley
from .fingerprint import (
    NUM_FP,
    FP_N0, FP_N1, FP_N2, FP_N3, FP_N4, FP_N5, FP_N6, FP_N7,
    FP_N8, FP_N9, FP_NA, FP_NB, FP_NC, FP_ND, FP_NE, FP_NF,
    FP_TOP, FP_BOT, FP_P,
    FP_I, FP_K, FP_QUOTE, FP_EVAL, FP_APP, FP_UNAPP,
    FP_ALU_LOGIC, FP_ALU_ARITH, FP_ALU_ARITHC,
    FP_ALU_ZERO, FP_ALU_COUT, FP_N_SUCC, FP_QUALE,
    FP_IO_PUT, FP_IO_GET, FP_IO_RDY, FP_IO_SEQ,
    FP_W_PACK8, FP_W_LO, FP_W_HI, FP_W_MERGE, FP_W_NIB,
    FP_W_NOT, FP_MUL16, FP_MAC16,
    FP_ALU_DISPATCH_SET, FP_W32_BINARY_OPS,
    FP_NIBBLES, FP_TO_NIBBLE_VAL, NIBBLE_VAL_TO_FP,
)


# ---------------------------------------------------------------------------
# Word format: 4-bit tag | 24-bit left | 24-bit right | 12-bit metadata
# (64 bits total, targeting ULX3S ECP5-85F with 32MB SDRAM)
# ---------------------------------------------------------------------------

TAG_BITS   = 4
LEFT_BITS  = 24
RIGHT_BITS = 24
META_BITS  = 12
WORD_BITS  = TAG_BITS + LEFT_BITS + RIGHT_BITS + META_BITS  # 64

META_SHIFT  = 0
RIGHT_SHIFT = META_BITS                          # 12
LEFT_SHIFT  = META_BITS + RIGHT_BITS             # 36
TAG_SHIFT   = META_BITS + RIGHT_BITS + LEFT_BITS # 60

TAG_MASK   = 0xF
LEFT_MASK  = 0xFFFFFF
RIGHT_MASK = 0xFFFFFF
META_MASK  = 0xFFF

# Reserved metadata bits (no behavior yet — for future GC)
META_GC_FORWARD = 1 << 0   # GC: this word has been forwarded
META_GC_GEN     = 1 << 1   # GC: generation (nursery/tenured)
META_IMMUTABLE  = 1 << 2   # quoted terms
META_PINNED     = 1 << 3   # don't relocate (key material)

# Tag constants
TAG_ATOM      = 0x0  # left = 7-bit structural fingerprint
TAG_QUOTED    = 0x1  # left = heap addr of inner term
TAG_APP       = 0x2  # left = heap addr of f, right = heap addr of x
TAG_ALUP1     = 0x3  # left = mode(2)|selector(4), right = unused
TAG_ALUP2     = 0x4  # left = mode(2)|selector(4), right = A nibble (4b)
TAG_IOPUTP    = 0x5  # left = hi nibble (4b)
TAG_IOSEQP    = 0x6  # left = heap addr of first-result
TAG_BUNDLE    = 0x7  # left = heap addr of f, right = heap addr of x
TAG_PARTIAL   = 0x8  # left = heap addr of f
TAG_COUT_PROBE = 0x9  # left = mode(2)|selector(4), right = A nibble (4b)
TAG_W32        = 0xA  # left = high 16 bits (zero-padded to 24), right = low 16 bits
TAG_W16        = 0xB  # left = 16-bit value (zero-padded to 24)
TAG_WPACK      = 0xC  # left = accumulated value, right = count (0-7)
TAG_W32_OP1    = 0xD  # left = opcode, right = heap addr of operand A
TAG_MUL_OP1    = 0xE  # left = sub-opcode, right = heap addr of operand
TAG_EXTENDED   = 0xF  # left[23:20] = sub-type, rest varies

# W32 operation codes (stored in TAG_W32_OP1 left field)
W32_OP_ADD  = 0
W32_OP_SUB  = 1
W32_OP_CMP  = 2
W32_OP_XOR  = 3
W32_OP_AND  = 4
W32_OP_OR   = 5
W32_OP_SHL  = 6
W32_OP_SHR  = 7
W32_OP_ROTL = 8
W32_OP_ROTR = 9

# MUL sub-opcodes (in TAG_MUL_OP1 left field)
MUL_OP_MUL16 = 0
MUL_OP_MAC1  = 1

# Extended sub-types (in TAG_EXTENDED left[23:20])
EXT_MAC2  = 0
EXT_MERGE = 1
EXT_NIB   = 2

# ALU mode encoding (2 bits)
MODE_LOGIC  = 0
MODE_ARITH  = 1
MODE_ARITHC = 2

# State machine states
S_FETCH   = 0
S_DECODE  = 1
S_EVAL_R  = 2
S_EVAL_R2 = 3   # about to resume with right-side result
S_APPLY   = 4
S_DOT     = 5
S_ALU     = 6
S_IO      = 7
S_RETURN  = 8
S_DONE    = 9
S_HALTED  = 10

MAX_CYCLES = 100_000


def pack_word(tag: int, left: int, right: int, meta: int = 0) -> int:
    return ((tag & TAG_MASK) << TAG_SHIFT) | \
           ((left & LEFT_MASK) << LEFT_SHIFT) | \
           ((right & RIGHT_MASK) << RIGHT_SHIFT) | \
           (meta & META_MASK)


def unpack_word(word: int) -> tuple[int, int, int, int]:
    tag   = (word >> TAG_SHIFT) & TAG_MASK
    left  = (word >> LEFT_SHIFT) & LEFT_MASK
    right = (word >> RIGHT_SHIFT) & RIGHT_MASK
    meta  = word & META_MASK
    return (tag, left, right, meta)


def make_atom_word(idx: int) -> int:
    return pack_word(TAG_ATOM, idx & 0x7F, 0)


def make_quoted_word(inner_addr: int) -> int:
    return pack_word(TAG_QUOTED, inner_addr, 0)


def make_app_word(f_addr: int, x_addr: int) -> int:
    return pack_word(TAG_APP, f_addr, x_addr)


def make_bundle_word(f_addr: int, x_addr: int) -> int:
    return pack_word(TAG_BUNDLE, f_addr, x_addr)


def make_partial_word(f_addr: int) -> int:
    return pack_word(TAG_PARTIAL, f_addr, 0)


def make_alup1_word(mode: int, selector: int) -> int:
    ms = ((mode & 0x3) << 4) | (selector & 0xF)
    return pack_word(TAG_ALUP1, ms, 0)


def make_alup2_word(mode: int, selector: int, a_val: int) -> int:
    ms = ((mode & 0x3) << 4) | (selector & 0xF)
    return pack_word(TAG_ALUP2, ms, a_val & 0xF)


def make_ioputp_word(hi_nibble: int) -> int:
    return pack_word(TAG_IOPUTP, hi_nibble & 0xF, 0)


def make_ioseqp_word(first_addr: int) -> int:
    return pack_word(TAG_IOSEQP, first_addr, 0)


def make_cout_probe_word(mode: int, selector: int, a_val: int) -> int:
    ms = ((mode & 0x3) << 4) | (selector & 0xF)
    return pack_word(TAG_COUT_PROBE, ms, a_val & 0xF)


def make_w32_word(val: int) -> int:
    """Pack a 32-bit value into a W32 word (high 16 in left, low 16 in right)."""
    return pack_word(TAG_W32, (val >> 16) & 0xFFFF, val & 0xFFFF)


def w32_from_word(word: int) -> int:
    """Extract a 32-bit value from a W32 word."""
    _, left, right, _ = unpack_word(word)
    return ((left & 0xFFFF) << 16) | (right & 0xFFFF)


def make_w16_word(val: int) -> int:
    """Pack a 16-bit value into a W16 word."""
    return pack_word(TAG_W16, val & 0xFFFF, 0)


def w16_from_word(word: int) -> int:
    """Extract a 16-bit value from a W16 word."""
    _, left, _, _ = unpack_word(word)
    return left & 0xFFFF


def make_wpack_word(acc: int, count: int) -> int:
    """Pack a WPACK accumulator word.
    Layout: left = acc[23:0], right = acc[31:24] << 8 | count[7:0]
    """
    lo24 = acc & 0xFFFFFF
    hi8 = (acc >> 24) & 0xFF
    return pack_word(TAG_WPACK, lo24, (hi8 << 8) | (count & 0xFF))


def wpack_unpack(word: int) -> tuple[int, int]:
    """Extract (acc, count) from a WPACK word."""
    _, left, right, _ = unpack_word(word)
    lo24 = left & 0xFFFFFF
    hi8 = (right >> 8) & 0xFF
    count = right & 0xFF
    acc = (hi8 << 24) | lo24
    return acc, count


def make_w32_op1_word(opcode: int, a_addr: int) -> int:
    """Pack a W32 binary op partial word."""
    return pack_word(TAG_W32_OP1, opcode & 0xFF, a_addr)


def make_mul_op1_word(sub_op: int, addr: int) -> int:
    """Pack a MUL/MAC partial word."""
    return pack_word(TAG_MUL_OP1, sub_op & 0xFF, addr)


def make_extended_word(sub_type: int, right_val: int) -> int:
    """Pack an extended word. sub_type goes in left[23:20]."""
    left = (sub_type & 0xF) << 20
    return pack_word(TAG_EXTENDED, left, right_val)


def atom_idx_from_word(word: int) -> int:
    """Extract atom index from an atom word."""
    return (word >> LEFT_SHIFT) & 0x7F


# ---------------------------------------------------------------------------
# Machine
# ---------------------------------------------------------------------------

class KameaMachine:
    """Clocked eval/apply state machine for the 66-atom DS algebra.

    Atom words store structural fingerprints (compile-time constants),
    not physical ROM indices. Dispatch decisions compare fingerprints
    directly. Physical indices are only needed for Cayley ROM lookups,
    resolved lazily via FingerprintCache on first access.
    """

    ADDR_BITS   = 24   # 16M heap words (ULX3S 32MB SDRAM)
    STACK_BITS  = 16   # 64K stack entries
    ATOM_BITS   = 7

    def __init__(self, cayley_rom: bytes | None = None,
                 atom_map: dict[str, int] | None = None):
        # --- Chips ---
        rom = cayley_rom or cayley.build_fingerprint_rom()
        self.cayley_rom = EEPROM(13, 7, rom)
        self.alu = IC74181()
        self.heap = SRAM(self.ADDR_BITS, WORD_BITS)
        self.stack = SRAM(self.STACK_BITS, WORD_BITS)

        # --- Registers ---
        self.tp = Register(self.ADDR_BITS)      # term pointer
        self.hp = Register(self.ADDR_BITS)      # heap free pointer
        self.sp = Register(self.STACK_BITS)     # stack pointer
        self.state = Register(4)                # current state
        self.result = Register(WORD_BITS)       # result word

        # --- IO ---
        self.uart_tx = FIFO(16)
        self.uart_rx = FIFO(16)

        # --- Internal latches ---
        self._current_word = 0
        self._io_op: str = ""

        # --- Counters ---
        self.cycles = 0
        self.rom_reads = 0
        self.alu_ops = 0
        self.heap_reads = 0
        self.heap_writes = 0
        self.io_ops = 0
        self.stack_peak = 0

    # -------------------------------------------------------------------
    # Fingerprint-based nibble helpers (set/dict lookups — O(1))
    # -------------------------------------------------------------------

    @staticmethod
    def _is_nibble(fp: int) -> bool:
        return fp in FP_NIBBLES

    @staticmethod
    def _nibble_val(fp: int) -> int:
        return FP_TO_NIBBLE_VAL[fp]

    @staticmethod
    def _nibble_fp(val: int) -> int:
        return NIBBLE_VAL_TO_FP[val & 0xF]

    # -------------------------------------------------------------------
    # Cache management
    # -------------------------------------------------------------------

    # -------------------------------------------------------------------
    # Memory helpers
    # -------------------------------------------------------------------

    def heap_read(self, addr: int) -> int:
        self.heap_reads += 1
        return self.heap.read(addr)

    def heap_write(self, addr: int, val: int):
        self.heap_writes += 1
        self.heap.write(addr, val)

    def alloc(self, word: int) -> int:
        """Allocate a word on the heap, return its address."""
        addr = self.hp.value
        self.heap_write(addr, word)
        self.hp.load(addr + 1)
        return addr

    def stack_push(self, val: int):
        sp = self.sp.value
        self.stack.write(sp, val)
        self.sp.load(sp + 1)
        if self.sp.value > self.stack_peak:
            self.stack_peak = self.sp.value

    def stack_pop(self) -> int:
        sp = self.sp.value - 1
        self.sp.load(sp)
        return self.stack.read(sp)

    # -------------------------------------------------------------------
    # State machine
    # -------------------------------------------------------------------

    def tick(self) -> bool:
        """One clock cycle. Returns True if still running."""
        self.cycles += 1
        if self.cycles > MAX_CYCLES:
            self.state.load(S_HALTED)
            return False

        s = self.state.value

        if s == S_FETCH:
            self._current_word = self.heap_read(self.tp.value)
            self.state.load(S_DECODE)

        elif s == S_DECODE:
            tag, left, right, _meta = unpack_word(self._current_word)

            if tag == TAG_APP:
                # Application: eval left, then right, then apply
                self.stack_push(right)    # save arg addr
                self.stack_push(S_EVAL_R) # return to EVAL_R after left
                self.tp.load(left)        # recurse into function
                self.state.load(S_FETCH)
            else:
                # Everything else is a value — return it
                self.result.load(self._current_word)
                self.state.load(S_RETURN)

        elif s == S_EVAL_R:
            # Left side evaluated (result in self.result).
            # Pop arg addr, push function result, evaluate arg.
            f_word = self.result.value
            arg_addr = self.stack_pop()
            self.stack_push(f_word)       # save function result
            self.stack_push(S_APPLY)      # after arg eval, apply
            self.tp.load(arg_addr)
            self.state.load(S_FETCH)

        elif s == S_APPLY:
            # Both sides evaluated.
            x_word = self.result.value    # argument (just evaluated)
            f_word = self.stack_pop()     # function
            self._dispatch_apply(f_word, x_word)

        elif s == S_DOT:
            # Cayley ROM lookup — fingerprints address the ROM directly
            _, f_fp, x_fp, _ = unpack_word(self.result.value)
            f_fp &= 0x7F
            x_fp &= 0x7F
            addr = f_fp * NUM_FP + x_fp
            result_fp = self.cayley_rom.read(addr)
            self.rom_reads += 1
            self.result.load(make_atom_word(result_fp))
            self.state.load(S_RETURN)

        elif s == S_ALU:
            self._execute_alu()

        elif s == S_IO:
            self._execute_io()

        elif s == S_RETURN:
            if self.sp.value == 0:
                self.state.load(S_DONE)
            else:
                return_state = self.stack_pop()
                self.state.load(return_state)

        elif s in (S_DONE, S_HALTED):
            return False

        return self.state.value not in (S_DONE, S_HALTED)

    # -------------------------------------------------------------------
    # Allocation helpers
    # -------------------------------------------------------------------

    def _return_value(self, word: int):
        """Return a word as the result. No heap allocation."""
        self.result.load(word)
        self.state.load(S_RETURN)

    def _return_p(self):
        """Return atom p (fingerprint constant)."""
        self.result.load(make_atom_word(FP_P))
        self.state.load(S_RETURN)

    # -------------------------------------------------------------------
    # Dispatch logic (all comparisons use fingerprint constants)
    # -------------------------------------------------------------------

    def _dispatch_apply(self, f_word: int, x_word: int):
        """Route f(x) to the correct handler based on f's tag and fingerprint."""
        f_tag, f_left, f_right, _f_meta = unpack_word(f_word)
        x_tag, x_left, x_right, _x_meta = unpack_word(x_word)

        if f_tag == TAG_ATOM:
            f_fp = f_left & 0x7F
            self._dispatch_atom_apply(f_fp, f_word, x_word, x_tag, x_left, x_right)

        elif f_tag == TAG_PARTIAL:
            x_addr = self.alloc(x_word)
            result = make_app_word(f_left, x_addr)
            self._return_value(result)

        elif f_tag == TAG_BUNDLE:
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if x_fp == FP_TOP:
                    self.result.load(self.heap_read(f_left))
                    self.state.load(S_RETURN)
                    return
                elif x_fp == FP_BOT:
                    self.result.load(self.heap_read(f_right))
                    self.state.load(S_RETURN)
                    return
            self._return_p()

        elif f_tag == TAG_ALUP1:
            mode = (f_left >> 4) & 0x3
            sel = f_left & 0xF
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if self._is_nibble(x_fp):
                    a_val = self._nibble_val(x_fp)
                    result = make_alup2_word(mode, sel, a_val)
                    self._return_value(result)
                    return
            self._return_p()

        elif f_tag == TAG_ALUP2:
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if self._is_nibble(x_fp):
                    mode = (f_left >> 4) & 0x3
                    sel = f_left & 0xF
                    a_val = f_right & 0xF
                    b_val = self._nibble_val(x_fp)
                    self._fire_alu(mode, sel, a_val, b_val)
                    return
            self._return_p()

        elif f_tag == TAG_IOPUTP:
            hi = f_left & 0xF
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if self._is_nibble(x_fp):
                    lo = self._nibble_val(x_fp)
                    self.uart_tx.push((hi << 4) | lo)
                    self.io_ops += 1
                    self.result.load(make_atom_word(FP_TOP))
                    self.state.load(S_RETURN)
                    return
            self._return_p()

        elif f_tag == TAG_IOSEQP:
            self.result.load(x_word)
            self.state.load(S_RETURN)

        elif f_tag == TAG_COUT_PROBE:
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if self._is_nibble(x_fp):
                    mode = (f_left >> 4) & 0x3
                    sel = f_left & 0xF
                    a_val = f_right & 0xF
                    b_val = self._nibble_val(x_fp)
                    self._fire_alu_carry(mode, sel, a_val, b_val)
                    return
            self._return_p()

        elif f_tag == TAG_W32_OP1:
            if x_tag == TAG_W32:
                opcode = f_left & 0xFF
                a_word = self.heap_read(f_right)
                a_val = w32_from_word(a_word)
                b_val = w32_from_word(x_word)
                if opcode == W32_OP_CMP:
                    r = FP_TOP if a_val == b_val else FP_BOT
                    self._return_value(make_atom_word(r))
                else:
                    self._return_value(make_w32_word(self._compute_w32(opcode, a_val, b_val)))
                return
            self._return_p()

        elif f_tag == TAG_WPACK:
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if self._is_nibble(x_fp):
                    acc, count = wpack_unpack(f_word)
                    nv = self._nibble_val(x_fp)
                    new_val = (acc << 4) | nv
                    if count == 7:
                        self._return_value(make_w32_word(new_val & 0xFFFFFFFF))
                    else:
                        self._return_value(make_wpack_word(new_val, count + 1))
                    return
            self._return_p()

        elif f_tag == TAG_MUL_OP1:
            sub_op = f_left & 0xFF
            if sub_op == MUL_OP_MUL16:
                if x_tag == TAG_W16:
                    a_word = self.heap_read(f_right)
                    a_val = w16_from_word(a_word)
                    b_val = x_left & 0xFFFF
                    product = a_val * b_val
                    hi = (product >> 16) & 0xFFFF
                    lo = product & 0xFFFF
                    hi_addr = self.alloc(make_w16_word(hi))
                    lo_addr = self.alloc(make_w16_word(lo))
                    self._return_value(make_app_word(hi_addr, lo_addr))
                    return
                self._return_p()
            elif sub_op == MUL_OP_MAC1:
                if x_tag == TAG_W16:
                    a_addr = self.alloc(x_word)
                    app_word = make_app_word(f_right, a_addr)
                    app_addr = self.alloc(app_word)
                    self._return_value(make_extended_word(EXT_MAC2, app_addr))
                    return
                self._return_p()
            else:
                self._return_p()

        elif f_tag == TAG_EXTENDED:
            sub_type = (f_left >> 20) & 0xF
            if sub_type == EXT_MAC2:
                if x_tag == TAG_W16:
                    app_word = self.heap_read(f_right)
                    _, app_left, app_right, _ = unpack_word(app_word)
                    acc_word = self.heap_read(app_left)
                    a_word = self.heap_read(app_right)
                    acc_val = w16_from_word(acc_word)
                    a_val = w16_from_word(a_word)
                    b_val = x_left & 0xFFFF
                    result = acc_val + a_val * b_val
                    hi = (result >> 16) & 0xFFFF
                    lo = result & 0xFFFF
                    hi_addr = self.alloc(make_w16_word(hi))
                    lo_addr = self.alloc(make_w16_word(lo))
                    self._return_value(make_app_word(hi_addr, lo_addr))
                    return
                self._return_p()
            elif sub_type == EXT_MERGE:
                if x_tag == TAG_W16:
                    hi_word = self.heap_read(f_right)
                    hi_val = w16_from_word(hi_word)
                    lo_val = x_left & 0xFFFF
                    self._return_value(make_w32_word((hi_val << 16) | lo_val))
                    return
                self._return_p()
            elif sub_type == EXT_NIB:
                if x_tag == TAG_ATOM:
                    x_fp = x_left & 0x7F
                    if self._is_nibble(x_fp):
                        pos = self._nibble_val(x_fp)
                        w32_word = self.heap_read(f_right)
                        val = w32_from_word(w32_word)
                        nib = (val >> (pos * 4)) & 0xF
                        self._return_value(make_atom_word(self._nibble_fp(nib)))
                        return
                self._return_p()
            else:
                self._return_p()

        else:
            self._return_p()

    def _dispatch_atom_apply(self, f_fp: int, f_word: int,
                              x_word: int, x_tag: int,
                              x_left: int, x_right: int):
        """Handle atom(f) applied to x. All comparisons use fingerprint constants."""

        # --- QUALE intercept: any atom applied to QUALE uses Cayley ROM ---
        if x_tag == TAG_ATOM and (x_left & 0x7F) == FP_QUALE:
            self._cayley_or_default(f_fp, x_word, x_tag, x_left)
            return

        # --- QUALE row: QUALE applied to anything returns Cayley result ---
        if f_fp == FP_QUALE:
            self._cayley_or_default(f_fp, x_word, x_tag, x_left)
            return

        # --- QUOTE ---
        if f_fp == FP_QUOTE:
            x_addr = self.alloc(x_word)
            result = make_quoted_word(x_addr)
            self._return_value(result)
            return

        # --- EVAL ---
        if f_fp == FP_EVAL:
            if x_tag == TAG_QUOTED:
                self.tp.load(x_left)
                self.state.load(S_FETCH)
                return
            elif x_tag == TAG_APP:
                f_inner = self.heap_read(x_left)
                x_inner = self.heap_read(x_right)
                f_inner_tag = (f_inner >> TAG_SHIFT) & TAG_MASK
                x_inner_tag = (x_inner >> TAG_SHIFT) & TAG_MASK
                if f_inner_tag == TAG_ATOM and x_inner_tag == TAG_ATOM:
                    fi = (f_inner >> LEFT_SHIFT) & 0x7F
                    xi = (x_inner >> LEFT_SHIFT) & 0x7F
                    self.result.load(pack_word(0, fi, xi))
                    self.state.load(S_DOT)
                    return
                self._return_p()
                return
            self._return_p()
            return

        # --- APP ---
        if f_fp == FP_APP:
            x_addr = self.alloc(x_word)
            result = make_partial_word(x_addr)
            self._return_value(result)
            return

        # --- UNAPP ---
        if f_fp == FP_UNAPP:
            if x_tag == TAG_APP:
                result = make_bundle_word(x_left, x_right)
                self._return_value(result)
                return
            self._return_p()
            return

        # --- ALU dispatch ---
        if f_fp in FP_ALU_DISPATCH_SET:
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if self._is_nibble(x_fp):
                    if f_fp == FP_ALU_LOGIC:
                        mode = MODE_LOGIC
                    elif f_fp == FP_ALU_ARITH:
                        mode = MODE_ARITH
                    else:
                        mode = MODE_ARITHC
                    sel = self._nibble_val(x_fp)
                    result = make_alup1_word(mode, sel)
                    self._return_value(result)
                    return
            self._cayley_or_default(f_fp, x_word, x_tag, x_left)
            return

        # --- ALU_ZERO ---
        if f_fp == FP_ALU_ZERO:
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if self._is_nibble(x_fp):
                    r = FP_TOP if x_fp == FP_N0 else FP_BOT
                    self.result.load(make_atom_word(r))
                    self.state.load(S_RETURN)
                    return
            self._cayley_or_default(f_fp, x_word, x_tag, x_left)
            return

        # --- ALU_COUT ---
        if f_fp == FP_ALU_COUT:
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if self._is_nibble(x_fp):
                    r = FP_TOP if self._nibble_val(x_fp) >= 8 else FP_BOT
                    self.result.load(make_atom_word(r))
                    self.state.load(S_RETURN)
                    return
            if x_tag == TAG_ALUP2:
                mode = (x_left >> 4) & 0x3
                sel = x_left & 0xF
                a_val = x_right & 0xF
                result = make_cout_probe_word(mode, sel, a_val)
                self._return_value(result)
                return
            self._cayley_or_default(f_fp, x_word, x_tag, x_left)
            return

        # --- IO_PUT ---
        if f_fp == FP_IO_PUT:
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if self._is_nibble(x_fp):
                    hi = self._nibble_val(x_fp)
                    result = make_ioputp_word(hi)
                    self._return_value(result)
                    return
            self._return_p()
            return

        # --- IO_GET ---
        if f_fp == FP_IO_GET:
            if x_tag == TAG_ATOM and (x_left & 0x7F) == FP_TOP:
                self._io_op = "get"
                self.state.load(S_IO)
                return
            self._return_p()
            return

        # --- IO_RDY ---
        if f_fp == FP_IO_RDY:
            if x_tag == TAG_ATOM and (x_left & 0x7F) == FP_TOP:
                r = FP_TOP if self.uart_rx.ready() else FP_BOT
                self.result.load(make_atom_word(r))
                self.io_ops += 1
                self.state.load(S_RETURN)
                return
            self._return_p()
            return

        # --- IO_SEQ ---
        if f_fp == FP_IO_SEQ:
            x_addr = self.alloc(x_word)
            result = make_ioseqp_word(x_addr)
            self._return_value(result)
            return

        # --- W_PACK8 ---
        if f_fp == FP_W_PACK8:
            if x_tag == TAG_ATOM:
                x_fp = x_left & 0x7F
                if self._is_nibble(x_fp):
                    nv = self._nibble_val(x_fp)
                    self._return_value(make_wpack_word(nv, 1))
                    return
            self._return_p()
            return

        # --- W_LO ---
        if f_fp == FP_W_LO:
            if x_tag == TAG_W32:
                lo = x_right & 0xFFFF
                self._return_value(make_w16_word(lo))
                return
            self._return_p()
            return

        # --- W_HI ---
        if f_fp == FP_W_HI:
            if x_tag == TAG_W32:
                hi = x_left & 0xFFFF
                self._return_value(make_w16_word(hi))
                return
            self._return_p()
            return

        # --- W_NOT ---
        if f_fp == FP_W_NOT:
            if x_tag == TAG_W32:
                val = w32_from_word(x_word)
                self._return_value(make_w32_word((~val) & 0xFFFFFFFF))
                return
            self._return_p()
            return

        # --- W_MERGE ---
        if f_fp == FP_W_MERGE:
            if x_tag == TAG_W16:
                addr = self.alloc(x_word)
                self._return_value(make_extended_word(EXT_MERGE, addr))
                return
            self._return_p()
            return

        # --- W_NIB ---
        if f_fp == FP_W_NIB:
            if x_tag == TAG_W32:
                addr = self.alloc(x_word)
                self._return_value(make_extended_word(EXT_NIB, addr))
                return
            self._return_p()
            return

        # --- Binary W32 ops ---
        if f_fp in FP_W32_BINARY_OPS:
            if x_tag == TAG_W32:
                opcode = FP_W32_BINARY_OPS[f_fp]
                addr = self.alloc(x_word)
                self._return_value(make_w32_op1_word(opcode, addr))
                return
            self._return_p()
            return

        # --- MUL16 ---
        if f_fp == FP_MUL16:
            if x_tag == TAG_W16:
                addr = self.alloc(x_word)
                self._return_value(make_mul_op1_word(MUL_OP_MUL16, addr))
                return
            self._return_p()
            return

        # --- MAC16 ---
        if f_fp == FP_MAC16:
            if x_tag == TAG_W16:
                addr = self.alloc(x_word)
                self._return_value(make_mul_op1_word(MUL_OP_MAC1, addr))
                return
            self._return_p()
            return

        # --- Default: atom applied to something → Cayley or p ---
        self._cayley_or_default(f_fp, x_word, x_tag, x_left)

    def _cayley_or_default(self, f_fp: int, x_word: int,
                            x_tag: int, x_left: int):
        """Atom x Atom -> Cayley lookup (direct fingerprint ROM), Atom x structured -> p."""
        if x_tag == TAG_ATOM:
            x_fp = x_left & 0x7F
            addr = f_fp * NUM_FP + x_fp
            result_fp = self.cayley_rom.read(addr)
            self.rom_reads += 1
            self.result.load(make_atom_word(result_fp))
        else:
            self.result.load(make_atom_word(FP_P))
        self.state.load(S_RETURN)

    # -------------------------------------------------------------------
    # ALU execution
    # -------------------------------------------------------------------

    def _fire_alu(self, mode: int, sel: int, a_val: int, b_val: int):
        """Fire the IC74181 and return result nibble (as fingerprint)."""
        m = (mode == MODE_LOGIC)
        cn = (mode != MODE_ARITHC)
        f_result, cn4, a_eq_b = self.alu(a_val, b_val, sel, m, cn)
        self.alu_ops += 1
        self.result.load(make_atom_word(self._nibble_fp(f_result)))
        self.state.load(S_RETURN)

    def _fire_alu_carry(self, mode: int, sel: int, a_val: int, b_val: int):
        """Fire the IC74181 and return carry-out as boolean fingerprint."""
        m = (mode == MODE_LOGIC)
        cn = (mode != MODE_ARITHC)
        f_result, cn4, a_eq_b = self.alu(a_val, b_val, sel, m, cn)
        self.alu_ops += 1
        carry = not cn4
        self.result.load(make_atom_word(FP_TOP if carry else FP_BOT))
        self.state.load(S_RETURN)

    # -------------------------------------------------------------------
    # W32 computation
    # -------------------------------------------------------------------

    @staticmethod
    def _compute_w32(op: int, a: int, b: int) -> int:
        M = 0xFFFFFFFF
        if op == W32_OP_ADD:  return (a + b) & M
        if op == W32_OP_SUB:  return (a - b) & M
        if op == W32_OP_XOR:  return a ^ b
        if op == W32_OP_AND:  return a & b
        if op == W32_OP_OR:   return a | b
        if op == W32_OP_SHL:  return (a << (b & 31)) & M
        if op == W32_OP_SHR:  return a >> (b & 31)
        if op == W32_OP_ROTL:
            n = b & 31
            return ((a << n) | (a >> (32 - n))) & M if n else a
        if op == W32_OP_ROTR:
            n = b & 31
            return ((a >> n) | (a << (32 - n))) & M if n else a
        return 0

    # -------------------------------------------------------------------
    # IO execution
    # -------------------------------------------------------------------

    def _execute_io(self):
        """Handle IO operations."""
        if self._io_op == "get":
            byte = self.uart_rx.pop()
            if byte is None:
                self.result.load(make_atom_word(FP_P))
                self.state.load(S_RETURN)
                return
            hi = (byte >> 4) & 0xF
            lo = byte & 0xF
            hi_word = make_atom_word(self._nibble_fp(hi))
            lo_word = make_atom_word(self._nibble_fp(lo))
            hi_addr = self.alloc(hi_word)
            lo_addr = self.alloc(lo_word)
            result = make_app_word(hi_addr, lo_addr)
            self._return_value(result)
            self.io_ops += 1

    # -------------------------------------------------------------------
    # Run to completion
    # -------------------------------------------------------------------

    def run(self) -> int:
        """Run the machine until S_DONE or S_HALTED. Returns result word."""
        while self.tick():
            pass
        return self.result.value

    def reset_counters(self):
        self.cycles = 0
        self.rom_reads = 0
        self.alu_ops = 0
        self.heap_reads = 0
        self.heap_writes = 0
        self.io_ops = 0
        self.stack_peak = 0

    def stats(self) -> dict:
        return {
            "cycles": self.cycles,
            "rom_reads": self.rom_reads,
            "alu_ops": self.alu_ops,
            "heap_reads": self.heap_reads,
            "heap_writes": self.heap_writes,
            "io_ops": self.io_ops,
            "heap_used": self.hp.value,
            "stack_peak": self.stack_peak,
        }

    def stats_summary(self) -> str:
        s = self.stats()
        return (
            f"Cycles: {s['cycles']}\n"
            f"ROM reads: {s['rom_reads']}\n"
            f"ALU ops: {s['alu_ops']}\n"
            f"Heap: {s['heap_reads']}R/{s['heap_writes']}W "
            f"({s['heap_used']} words allocated)\n"
            f"IO: {s['io_ops']} operations\n"
            f"Stack peak: {s['stack_peak']}"
        )

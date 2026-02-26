"""
Kamea machine — clocked eval/apply state machine for the 47-atom DS algebra.

Models the hardware architecture: Cayley ROM, IC74181 ALU, SRAM heap,
hardware stack, UART FIFOs, and a microcode-driven state machine.
"""

from __future__ import annotations

from .chips import EEPROM, IC74181, SRAM, Register, FIFO
from . import cayley


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
TAG_ATOM      = 0x0  # left = 6-bit atom index
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
    """Clocked eval/apply state machine for the 47-atom DS algebra."""

    ADDR_BITS   = 24   # 16M heap words (ULX3S 32MB SDRAM)
    STACK_BITS  = 16   # 64K stack entries
    ATOM_BITS   = 7

    def __init__(self, cayley_rom: bytes | None = None,
                 atom_map: dict[str, int] | None = None):
        # --- Chips ---
        rom = cayley_rom or cayley.build_cayley_rom()
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

        # --- Dispatch constants ---
        # These map semantic roles to atom indices in this machine's ROM.
        # Default: canonical cayley indices. Override for scrambled ROMs.
        am = atom_map or {}
        self.TOP       = am.get("⊤", cayley.TOP)
        self.BOT       = am.get("⊥", cayley.BOT)
        self.P         = am.get("p", cayley.P)
        self.QUOTE     = am.get("QUOTE", cayley.QUOTE)
        self.EVAL      = am.get("EVAL", cayley.EVAL)
        self.APP       = am.get("APP", cayley.APP)
        self.UNAPP     = am.get("UNAPP", cayley.UNAPP)
        self.ALU_LOGIC = am.get("ALU_LOGIC", cayley.ALU_LOGIC)
        self.ALU_ARITH = am.get("ALU_ARITH", cayley.ALU_ARITH)
        self.ALU_ARITHC = am.get("ALU_ARITHC", cayley.ALU_ARITHC)
        self.ALU_ZERO  = am.get("ALU_ZERO", cayley.ALU_ZERO)
        self.ALU_COUT  = am.get("ALU_COUT", cayley.ALU_COUT)
        self.N_SUCC    = am.get("N_SUCC", cayley.N_SUCC)
        self.IO_PUT    = am.get("IO_PUT", cayley.IO_PUT)
        self.IO_GET    = am.get("IO_GET", cayley.IO_GET)
        self.IO_RDY    = am.get("IO_RDY", cayley.IO_RDY)
        self.IO_SEQ    = am.get("IO_SEQ", cayley.IO_SEQ)
        self.N0        = am.get("N0", cayley.N0)
        self.NF        = am.get("NF", cayley.NF)
        # Build nibble set and val/idx tables for scrambled ROM support
        self._nibble_set = frozenset(
            am.get(f"N{i:X}", cayley.NIBBLE_BASE + i) for i in range(16)
        )
        self._nibble_to_val = {
            am.get(f"N{i:X}", cayley.NIBBLE_BASE + i): i for i in range(16)
        }
        self._val_to_nibble = {v: k for k, v in self._nibble_to_val.items()}
        self.ALU_DISPATCH_SET = frozenset({self.ALU_LOGIC, self.ALU_ARITH, self.ALU_ARITHC})

        # W32/MUL dispatch constants
        self.W_PACK8 = am.get("W_PACK8", cayley.W_PACK8)
        self.W_LO    = am.get("W_LO", cayley.W_LO)
        self.W_HI    = am.get("W_HI", cayley.W_HI)
        self.W_MERGE = am.get("W_MERGE", cayley.W_MERGE)
        self.W_NIB   = am.get("W_NIB", cayley.W_NIB)
        self.W_ADD   = am.get("W_ADD", cayley.W_ADD)
        self.W_SUB   = am.get("W_SUB", cayley.W_SUB)
        self.W_CMP   = am.get("W_CMP", cayley.W_CMP)
        self.W_XOR   = am.get("W_XOR", cayley.W_XOR)
        self.W_AND   = am.get("W_AND", cayley.W_AND)
        self.W_OR    = am.get("W_OR", cayley.W_OR)
        self.W_NOT   = am.get("W_NOT", cayley.W_NOT)
        self.W_SHL   = am.get("W_SHL", cayley.W_SHL)
        self.W_SHR   = am.get("W_SHR", cayley.W_SHR)
        self.W_ROTL  = am.get("W_ROTL", cayley.W_ROTL)
        self.W_ROTR  = am.get("W_ROTR", cayley.W_ROTR)
        self.MUL16   = am.get("MUL16", cayley.MUL16)
        self.MAC16   = am.get("MAC16", cayley.MAC16)

        self.W32_BINARY_OPS = {
            self.W_ADD: W32_OP_ADD, self.W_SUB: W32_OP_SUB, self.W_CMP: W32_OP_CMP,
            self.W_XOR: W32_OP_XOR, self.W_AND: W32_OP_AND, self.W_OR: W32_OP_OR,
            self.W_SHL: W32_OP_SHL, self.W_SHR: W32_OP_SHR,
            self.W_ROTL: W32_OP_ROTL, self.W_ROTR: W32_OP_ROTR,
        }

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
    # Nibble helpers (use instance constants for scrambled ROM support)
    # -------------------------------------------------------------------

    def _is_nibble(self, idx: int) -> bool:
        return idx in self._nibble_set

    def _nibble_val(self, idx: int) -> int:
        return self._nibble_to_val[idx]

    def _nibble_idx(self, val: int) -> int:
        return self._val_to_nibble[val & 0xF]

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
            # Cayley ROM lookup — indices packed via pack_word(0, fi, xi)
            _, x_idx, y_idx, _ = unpack_word(self.result.value)
            addr = x_idx * cayley.NUM_ATOMS + y_idx
            result_idx = self.cayley_rom.read(addr)
            self.rom_reads += 1
            self.result.load(make_atom_word(result_idx))
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
        """Return atom p."""
        self.result.load(make_atom_word(self.P))
        self.state.load(S_RETURN)

    # -------------------------------------------------------------------
    # Dispatch logic
    # -------------------------------------------------------------------

    def _dispatch_apply(self, f_word: int, x_word: int):
        """Route f(x) to the correct handler based on f's tag and atom."""
        f_tag, f_left, f_right, _f_meta = unpack_word(f_word)
        x_tag, x_left, x_right, _x_meta = unpack_word(x_word)

        if f_tag == TAG_ATOM:
            f_atom = f_left & 0x7F
            self._dispatch_atom_apply(f_atom, f_word, x_word, x_tag, x_left, x_right)

        elif f_tag == TAG_PARTIAL:
            # Partial(f_addr) + x → AppNode(f_addr, x_addr)
            # Store x on heap, then make app node
            x_addr = self.alloc(x_word)
            result = make_app_word(f_left, x_addr)
            self._return_value(result)

        elif f_tag == TAG_BUNDLE:
            # Bundle(f_addr, x_addr) applied to ⊤ or ⊥
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if x_atom == self.TOP:
                    self.result.load(self.heap_read(f_left))
                    self.state.load(S_RETURN)
                    return
                elif x_atom == self.BOT:
                    self.result.load(self.heap_read(f_right))
                    self.state.load(S_RETURN)
                    return
            self.result.load(make_atom_word(self.P))
            self.state.load(S_RETURN)

        elif f_tag == TAG_ALUP1:
            # ALUPartial1(mode, sel) + nibble → ALUPartial2(mode, sel, A)
            mode = (f_left >> 4) & 0x3
            sel = f_left & 0xF
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if self._is_nibble(x_atom):
                    a_val = self._nibble_val(x_atom)
                    result = make_alup2_word(mode, sel, a_val)
                    self._return_value(result)
                    return
            self.result.load(make_atom_word(self.P))
            self.state.load(S_RETURN)

        elif f_tag == TAG_ALUP2:
            # ALUPartial2(mode, sel, A) + nibble → fire 74181
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if self._is_nibble(x_atom):
                    mode = (f_left >> 4) & 0x3
                    sel = f_left & 0xF
                    a_val = f_right & 0xF
                    b_val = self._nibble_val(x_atom)
                    self._fire_alu(mode, sel, a_val, b_val)
                    return
            self.result.load(make_atom_word(self.P))
            self.state.load(S_RETURN)

        elif f_tag == TAG_IOPUTP:
            # IOPutPartial(hi) + nibble → UART TX byte
            hi = f_left & 0xF
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if self._is_nibble(x_atom):
                    lo = self._nibble_val(x_atom)
                    self.uart_tx.push((hi << 4) | lo)
                    self.io_ops += 1
                    self.result.load(make_atom_word(self.TOP))
                    self.state.load(S_RETURN)
                    return
            self.result.load(make_atom_word(self.P))
            self.state.load(S_RETURN)

        elif f_tag == TAG_IOSEQP:
            # IOSeqPartial(first) + anything → return x (discard first)
            self.result.load(x_word)
            self.state.load(S_RETURN)

        elif f_tag == TAG_COUT_PROBE:
            # CoutProbe(mode, sel, A) + nibble → fire 74181, return carry
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if self._is_nibble(x_atom):
                    mode = (f_left >> 4) & 0x3
                    sel = f_left & 0xF
                    a_val = f_right & 0xF
                    b_val = self._nibble_val(x_atom)
                    self._fire_alu_carry(mode, sel, a_val, b_val)
                    return
            self._return_p()

        elif f_tag == TAG_W32_OP1:
            # W32 binary op partial(opcode, a_addr) + W32 → compute result
            if x_tag == TAG_W32:
                opcode = f_left & 0xFF
                a_word = self.heap_read(f_right)
                a_val = w32_from_word(a_word)
                b_val = w32_from_word(x_word)
                if opcode == W32_OP_CMP:
                    r = self.TOP if a_val == b_val else self.BOT
                    self._return_value(make_atom_word(r))
                else:
                    self._return_value(make_w32_word(self._compute_w32(opcode, a_val, b_val)))
                return
            self._return_p()

        elif f_tag == TAG_WPACK:
            # WPACK(acc, count) + nibble → accumulate or produce W32
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if self._is_nibble(x_atom):
                    acc, count = wpack_unpack(f_word)
                    nv = self._nibble_val(x_atom)
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
                # MUL16 partial(a_addr) + W16 → fire multiply
                if x_tag == TAG_W16:
                    a_word = self.heap_read(f_right)
                    a_val = w16_from_word(a_word)
                    b_val = x_left & 0xFFFF
                    product = a_val * b_val
                    hi = (product >> 16) & 0xFFFF
                    lo = product & 0xFFFF
                    hi_word = make_w16_word(hi)
                    lo_word = make_w16_word(lo)
                    hi_addr = self.alloc(hi_word)
                    lo_addr = self.alloc(lo_word)
                    self._return_value(make_app_word(hi_addr, lo_addr))
                    return
                self._return_p()
            elif sub_op == MUL_OP_MAC1:
                # MAC16 stage 1: acc partial(acc_addr) + W16(a) → ExtendedPartial(MAC2, app_addr)
                if x_tag == TAG_W16:
                    # Store APP(acc, a) on heap
                    a_word = x_word
                    a_addr = self.alloc(a_word)
                    app_word = make_app_word(f_right, a_addr)  # f_right = acc_addr
                    app_addr = self.alloc(app_word)
                    self._return_value(make_extended_word(EXT_MAC2, app_addr))
                    return
                self._return_p()
            else:
                self._return_p()

        elif f_tag == TAG_EXTENDED:
            sub_type = (f_left >> 20) & 0xF
            if sub_type == EXT_MAC2:
                # MAC16 stage 2: partial(app_addr) + W16(b) → acc + a*b
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
                    hi_word = make_w16_word(hi)
                    lo_word = make_w16_word(lo)
                    hi_addr = self.alloc(hi_word)
                    lo_addr = self.alloc(lo_word)
                    self._return_value(make_app_word(hi_addr, lo_addr))
                    return
                self._return_p()
            elif sub_type == EXT_MERGE:
                # W_MERGE partial(hi_addr) + W16(lo) → W32(hi<<16 | lo)
                if x_tag == TAG_W16:
                    hi_word = self.heap_read(f_right)
                    hi_val = w16_from_word(hi_word)
                    lo_val = x_left & 0xFFFF
                    self._return_value(make_w32_word((hi_val << 16) | lo_val))
                    return
                self._return_p()
            elif sub_type == EXT_NIB:
                # W_NIB partial(w32_addr) + nibble → extract nibble at position
                if x_tag == TAG_ATOM:
                    x_atom = x_left & 0x7F
                    if self._is_nibble(x_atom):
                        pos = self._nibble_val(x_atom)
                        w32_word = self.heap_read(f_right)
                        val = w32_from_word(w32_word)
                        nib = (val >> (pos * 4)) & 0xF
                        self._return_value(make_atom_word(self._nibble_idx(nib)))
                        return
                self._return_p()
            else:
                self._return_p()

        else:
            # Unknown tag in function position → p
            self._return_p()

    def _dispatch_atom_apply(self, f_atom: int, f_word: int,
                              x_word: int, x_tag: int,
                              x_left: int, x_right: int):
        """Handle atom(f) applied to x."""

        # --- QUOTE ---
        if f_atom == self.QUOTE:
            # Store x_word on heap, wrap address as quoted
            x_addr = self.alloc(x_word)
            result = make_quoted_word(x_addr)
            self._return_value(result)
            return

        # --- EVAL ---
        if f_atom == self.EVAL:
            if x_tag == TAG_QUOTED:
                # EVAL(quoted(addr)) → evaluate inner term
                self.tp.load(x_left)
                self.state.load(S_FETCH)
                return
            elif x_tag == TAG_APP:
                # EVAL(app-node(f,x)) → flat eval: dot(f_atom, x_atom)
                # Load f and x from heap, do Cayley lookup
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
                self.result.load(make_atom_word(self.P))
                self.state.load(S_RETURN)
                return
            # EVAL of anything else → p
            self.result.load(make_atom_word(self.P))
            self.state.load(S_RETURN)
            return

        # --- APP ---
        if f_atom == self.APP:
            # Store x_word on heap, return partial
            x_addr = self.alloc(x_word)
            result = make_partial_word(x_addr)
            self._return_value(result)
            return

        # --- UNAPP ---
        if f_atom == self.UNAPP:
            if x_tag == TAG_APP:
                # UNAPP(app-node) → bundle
                result = make_bundle_word(x_left, x_right)
                self._return_value(result)
                return
            self.result.load(make_atom_word(self.P))
            self.state.load(S_RETURN)
            return

        # --- ALU dispatch ---
        if f_atom in self.ALU_DISPATCH_SET:
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if self._is_nibble(x_atom):
                    if f_atom == self.ALU_LOGIC:
                        mode = MODE_LOGIC
                    elif f_atom == self.ALU_ARITH:
                        mode = MODE_ARITH
                    else:
                        mode = MODE_ARITHC
                    sel = self._nibble_val(x_atom)
                    result = make_alup1_word(mode, sel)
                    self._return_value(result)
                    return
            # Non-nibble → Cayley fallback
            self._cayley_or_default(f_atom, x_word, x_tag, x_left)
            return

        # --- ALU_ZERO ---
        if f_atom == self.ALU_ZERO:
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if self._is_nibble(x_atom):
                    r = self.TOP if x_atom == self.N0 else self.BOT
                    self.result.load(make_atom_word(r))
                    self.state.load(S_RETURN)
                    return
            self._cayley_or_default(f_atom, x_word, x_tag, x_left)
            return

        # --- ALU_COUT ---
        if f_atom == self.ALU_COUT:
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if self._is_nibble(x_atom):
                    r = self.TOP if self._nibble_val(x_atom) >= 8 else self.BOT
                    self.result.load(make_atom_word(r))
                    self.state.load(S_RETURN)
                    return
            # ALU_COUT on ALUPartial2 → CoutProbe
            if x_tag == TAG_ALUP2:
                mode = (x_left >> 4) & 0x3
                sel = x_left & 0xF
                a_val = x_right & 0xF
                result = make_cout_probe_word(mode, sel, a_val)
                self._return_value(result)
                return
            self._cayley_or_default(f_atom, x_word, x_tag, x_left)
            return

        # --- IO_PUT ---
        if f_atom == self.IO_PUT:
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if self._is_nibble(x_atom):
                    hi = self._nibble_val(x_atom)
                    result = make_ioputp_word(hi)
                    self._return_value(result)
                    return
            self.result.load(make_atom_word(self.P))
            self.state.load(S_RETURN)
            return

        # --- IO_GET ---
        if f_atom == self.IO_GET:
            if x_tag == TAG_ATOM and (x_left & 0x7F) == self.TOP:
                self._io_op = "get"
                self.state.load(S_IO)
                return
            self.result.load(make_atom_word(self.P))
            self.state.load(S_RETURN)
            return

        # --- IO_RDY ---
        if f_atom == self.IO_RDY:
            if x_tag == TAG_ATOM and (x_left & 0x7F) == self.TOP:
                r = self.TOP if self.uart_rx.ready() else self.BOT
                self.result.load(make_atom_word(r))
                self.io_ops += 1
                self.state.load(S_RETURN)
                return
            self.result.load(make_atom_word(self.P))
            self.state.load(S_RETURN)
            return

        # --- IO_SEQ ---
        if f_atom == self.IO_SEQ:
            x_addr = self.alloc(x_word)
            result = make_ioseqp_word(x_addr)
            self._return_value(result)
            return

        # --- W_PACK8: nibble → WPACK(val, 1) ---
        if f_atom == self.W_PACK8:
            if x_tag == TAG_ATOM:
                x_atom = x_left & 0x7F
                if self._is_nibble(x_atom):
                    nv = self._nibble_val(x_atom)
                    self._return_value(make_wpack_word(nv, 1))
                    return
            self._return_p()
            return

        # --- W_LO: W32 → W16(lo16) ---
        if f_atom == self.W_LO:
            if x_tag == TAG_W32:
                lo = x_right & 0xFFFF
                self._return_value(make_w16_word(lo))
                return
            self._return_p()
            return

        # --- W_HI: W32 → W16(hi16) ---
        if f_atom == self.W_HI:
            if x_tag == TAG_W32:
                hi = x_left & 0xFFFF
                self._return_value(make_w16_word(hi))
                return
            self._return_p()
            return

        # --- W_NOT: W32 → W32(~val) ---
        if f_atom == self.W_NOT:
            if x_tag == TAG_W32:
                val = w32_from_word(x_word)
                self._return_value(make_w32_word((~val) & 0xFFFFFFFF))
                return
            self._return_p()
            return

        # --- W_MERGE: W16 → ExtendedPartial(MERGE, hi_addr) ---
        if f_atom == self.W_MERGE:
            if x_tag == TAG_W16:
                addr = self.alloc(x_word)
                self._return_value(make_extended_word(EXT_MERGE, addr))
                return
            self._return_p()
            return

        # --- W_NIB: W32 → ExtendedPartial(NIB, w32_addr) ---
        if f_atom == self.W_NIB:
            if x_tag == TAG_W32:
                addr = self.alloc(x_word)
                self._return_value(make_extended_word(EXT_NIB, addr))
                return
            self._return_p()
            return

        # --- Binary W32 ops: W32 → W32_OP1(opcode, a_addr) ---
        if f_atom in self.W32_BINARY_OPS:
            if x_tag == TAG_W32:
                opcode = self.W32_BINARY_OPS[f_atom]
                addr = self.alloc(x_word)
                self._return_value(make_w32_op1_word(opcode, addr))
                return
            self._return_p()
            return

        # --- MUL16: W16 → MulOp1(MUL16, a_addr) ---
        if f_atom == self.MUL16:
            if x_tag == TAG_W16:
                addr = self.alloc(x_word)
                self._return_value(make_mul_op1_word(MUL_OP_MUL16, addr))
                return
            self._return_p()
            return

        # --- MAC16: W16 → MulOp1(MAC1, acc_addr) ---
        if f_atom == self.MAC16:
            if x_tag == TAG_W16:
                addr = self.alloc(x_word)
                self._return_value(make_mul_op1_word(MUL_OP_MAC1, addr))
                return
            self._return_p()
            return

        # --- Default: atom applied to something ---
        self._cayley_or_default(f_atom, x_word, x_tag, x_left)

    def _cayley_or_default(self, f_atom: int, x_word: int,
                            x_tag: int, x_left: int):
        """Atom × Atom → Cayley lookup, Atom × structured → p."""
        if x_tag == TAG_ATOM:
            x_atom = x_left & 0x7F
            addr = f_atom * cayley.NUM_ATOMS + x_atom
            result_idx = self.cayley_rom.read(addr)
            self.rom_reads += 1
            self.result.load(make_atom_word(result_idx))
        else:
            # Atom applied to non-atom structured value → p
            self.result.load(make_atom_word(self.P))
        self.state.load(S_RETURN)

    # -------------------------------------------------------------------
    # ALU execution
    # -------------------------------------------------------------------

    def _fire_alu(self, mode: int, sel: int, a_val: int, b_val: int):
        """Fire the IC74181 and return result nibble."""
        m = (mode == MODE_LOGIC)
        cn = (mode != MODE_ARITHC)  # active-low: arithc has carry
        f_result, cn4, a_eq_b = self.alu(a_val, b_val, sel, m, cn)
        self.alu_ops += 1
        self.result.load(make_atom_word(self._nibble_idx(f_result)))
        self.state.load(S_RETURN)

    def _fire_alu_carry(self, mode: int, sel: int, a_val: int, b_val: int):
        """Fire the IC74181 and return carry-out as boolean."""
        m = (mode == MODE_LOGIC)
        cn = (mode != MODE_ARITHC)
        f_result, cn4, a_eq_b = self.alu(a_val, b_val, sel, m, cn)
        self.alu_ops += 1
        # cn4 is active-low: False means carry out occurred
        carry = not cn4
        self.result.load(make_atom_word(self.TOP if carry else self.BOT))
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
                # No data available — return p (matches algebraic semantics)
                self.result.load(make_atom_word(self.P))
                self.state.load(S_RETURN)
                return
            hi = (byte >> 4) & 0xF
            lo = byte & 0xF
            # Allocate two atom words for nibbles, then an app-node
            hi_word = make_atom_word(self._nibble_idx(hi))
            lo_word = make_atom_word(self._nibble_idx(lo))
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

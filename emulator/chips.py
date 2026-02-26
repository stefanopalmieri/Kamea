"""
Chip primitives for the Kamea machine.

Models discrete hardware components: EEPROM, IC74181 ALU, SRAM, Register, FIFO.
"""

from __future__ import annotations

import collections


class EEPROM:
    """Generic ROM. Used for Cayley table and microcode."""

    def __init__(self, addr_bits: int, data_bits: int, contents: bytes):
        self.data = contents
        self.addr_bits = addr_bits
        self.data_bits = data_bits
        self._mask = (1 << data_bits) - 1

    def read(self, addr: int) -> int:
        addr &= (1 << self.addr_bits) - 1
        if addr < len(self.data):
            return self.data[addr] & self._mask
        return 0


class IC74181:
    """
    Pin-accurate 74181 4-bit ALU (active-high data).

    Interface mirrors the physical chip:
      a, b:  4-bit operands (0-15)
      s:     4-bit function select (0-15)
      m:     mode — True = logic, False = arithmetic
      cn:    carry-in — active low (True = no carry, False = carry)

    Returns: (f: 4-bit result, cn4: carry-out active-low, a_eq_b: equality)
    """

    def __call__(self, a: int, b: int, s: int, m: bool, cn: bool) -> tuple[int, bool, bool]:
        a &= 0xF
        b &= 0xF
        s &= 0xF

        if m:
            # Logic mode
            result = self._logic(s, a, b)
            return (result, True, result == 0xF)  # cn4 inactive (high), A=B when all 1s

        # Arithmetic mode
        carry_in = 0 if cn else 1  # active-low: cn=False means carry=1
        result, carry_out = self._arith(s, a, b, carry_in)
        # cn4 is active-low: True means no carry out
        cn4 = not carry_out
        a_eq_b = (result == 0xF)
        return (result, cn4, a_eq_b)

    @staticmethod
    def _logic_bit(s: int, ai: int, bi: int) -> int:
        """Compute one bit of the 74181 logic function (active-high)."""
        na = 1 - ai
        nb = 1 - bi
        table = [
            na,              # 0: NOT A
            1 - (ai | bi),   # 1: NOR
            na & bi,         # 2: (NOT A) AND B
            0,               # 3: Logical 0
            1 - (ai & bi),   # 4: NAND
            nb,              # 5: NOT B
            ai ^ bi,         # 6: XOR
            ai & nb,         # 7: A AND (NOT B)
            na | bi,         # 8: (NOT A) OR B
            1 - (ai ^ bi),  # 9: XNOR
            bi,              # A: B
            ai & bi,         # B: A AND B
            1,               # C: Logical 1
            ai | nb,         # D: A OR (NOT B)
            ai | bi,         # E: A OR B
            ai,              # F: A
        ]
        return table[s]

    @classmethod
    def _logic(cls, s: int, a: int, b: int) -> int:
        """Compute 74181 logic operation (all 4 bits)."""
        result = 0
        for bit in range(4):
            ai = (a >> bit) & 1
            bi = (b >> bit) & 1
            fi = cls._logic_bit(s, ai, bi)
            result |= fi << bit
        return result & 0xF

    @staticmethod
    def _arith(s: int, a: int, b: int, carry_in: int) -> tuple[int, bool]:
        """Compute 74181 arithmetic operation (active-high)."""
        nb = (~b) & 0xF
        base_table = [
            a,                   # 0: A
            a | b,               # 1: A OR B
            a | nb,              # 2: A OR (NOT B)
            0xF,                 # 3: minus 1
            a + (a & nb),        # 4: A plus (A AND NOT B)
            (a | b) + (a & nb),  # 5: (A OR B) plus (A AND NOT B)
            a + nb,              # 6: A minus B minus 1
            (a & nb) + 0xF,      # 7: (A AND NOT B) minus 1
            a + (a & b),         # 8: A plus (A AND B)
            a + b,               # 9: A plus B
            (a | nb) + (a & b),  # A: (A OR NOT B) plus (A AND B)
            (a & b) + 0xF,       # B: (A AND B) minus 1
            a + a,               # C: A plus A (shift left)
            (a | b) + a,         # D: (A OR B) plus A
            (a | nb) + a,        # E: (A OR NOT B) plus A
            a + 0xF,             # F: A minus 1
        ]
        raw = base_table[s] + carry_in
        result = raw & 0xF
        carry_out = bool(raw > 0xF)
        return (result, carry_out)


class SRAM:
    """Static RAM, configurable width and depth. Sparse backing store."""

    def __init__(self, addr_bits: int, data_bits: int):
        self.data: dict[int, int] = {}
        self.addr_bits = addr_bits
        self.data_bits = data_bits
        self._addr_mask = (1 << addr_bits) - 1
        self._data_mask = (1 << data_bits) - 1

    def read(self, addr: int) -> int:
        return self.data.get(addr & self._addr_mask, 0)

    def write(self, addr: int, val: int):
        self.data[addr & self._addr_mask] = val & self._data_mask


class Register:
    """N-bit clocked register."""

    def __init__(self, width: int):
        self.width = width
        self.value = 0
        self._mask = (1 << width) - 1

    def load(self, val: int):
        self.value = val & self._mask


class FIFO:
    """UART TX/RX buffer. Models the 16550 FIFO."""

    def __init__(self, depth: int = 16):
        self.buffer: collections.deque[int] = collections.deque(maxlen=depth)

    def push(self, byte: int):
        self.buffer.append(byte & 0xFF)

    def pop(self) -> int | None:
        return self.buffer.popleft() if self.buffer else None

    def ready(self) -> bool:
        return len(self.buffer) > 0

    def __len__(self) -> int:
        return len(self.buffer)

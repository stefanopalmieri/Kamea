"""
EmulatorHost — high-level interface to the Kamea machine.

Provides term loading (S-expression → heap), evaluation, and result decoding.
"""

from __future__ import annotations

from . import cayley
from .machine import (
    KameaMachine, S_FETCH, S_APPLY, S_DONE, S_HALTED,
    make_atom_word, make_app_word, make_quoted_word,
    unpack_word, atom_idx_from_word,
    TAG_ATOM, TAG_QUOTED, TAG_APP, TAG_ALUP1, TAG_ALUP2,
    TAG_IOPUTP, TAG_IOSEQP, TAG_BUNDLE, TAG_PARTIAL, TAG_COUT_PROBE, TAG_W32,
    MODE_LOGIC, MODE_ARITH, MODE_ARITHC,
)


class EmulatorHost:
    """High-level interface to the Kamea machine."""

    def __init__(self, cayley_rom: bytes | None = None,
                 atom_map: dict[str, int] | None = None):
        self.machine = KameaMachine(cayley_rom, atom_map)

    # -------------------------------------------------------------------
    # Term loading: nested tuples/strings → heap words
    # -------------------------------------------------------------------

    def load_term(self, term) -> int:
        """
        Load a term into the machine's heap, return root address.

        Term format:
          - str: atom name (e.g. "⊤", "N0", "QUOTE")
          - int: atom index directly
          - (f, x): application (f applied to x)
          - ("QUOTED", inner): quoted term
        """
        if isinstance(term, str):
            idx = cayley.NAME_TO_IDX[term]
            word = make_atom_word(idx)
            return self.machine.alloc(word)

        if isinstance(term, int):
            word = make_atom_word(term)
            return self.machine.alloc(word)

        if isinstance(term, tuple):
            if len(term) == 2:
                if term[0] == "QUOTED":
                    inner_addr = self.load_term(term[1])
                    word = make_quoted_word(inner_addr)
                    return self.machine.alloc(word)
                else:
                    f_addr = self.load_term(term[0])
                    x_addr = self.load_term(term[1])
                    word = make_app_word(f_addr, x_addr)
                    return self.machine.alloc(word)

        raise ValueError(f"Cannot load term: {term!r}")

    # -------------------------------------------------------------------
    # Evaluation
    # -------------------------------------------------------------------

    def eval(self, term) -> dict:
        """
        Load a term and evaluate it to completion.

        Returns dict with result, decoded result, cycle count, and stats.
        """
        # Reset machine state (keep heap, reset stack/state/counters)
        self.machine.sp.load(0)
        self.machine.state.load(S_FETCH)
        self.machine.reset_counters()

        addr = self.load_term(term)
        self.machine.tp.load(addr)
        self.machine.state.load(S_FETCH)

        result_word = self.machine.run()

        return {
            "ok": self.machine.state.value == S_DONE,
            "result_word": result_word,
            "result": self.decode_word(result_word),
            "stats": self.machine.stats(),
        }

    def dispatch_word(self, f_word: int, x_word: int) -> int:
        """
        Apply f_word to x_word through the machine's dispatch unit.

        Both operands are pre-evaluated machine words. Sets up the
        machine to enter S_APPLY directly — no heap scratch, no
        eval loop for the operands. The dispatch unit itself may
        allocate on the heap (QUOTE, APP, etc.) and those persist.

        Does NOT reset counters — stats accumulate across calls.
        """
        self.machine.sp.load(0)
        self.machine.stack_push(f_word)
        self.machine.result.load(x_word)
        self.machine.state.load(S_APPLY)
        return self.machine.run()

    def dot(self, x_name: str, y_name: str) -> str:
        """Single Cayley ROM lookup by atom name."""
        xi = cayley.NAME_TO_IDX[x_name]
        yi = cayley.NAME_TO_IDX[y_name]
        addr = xi * cayley.NUM_ATOMS + yi
        ri = self.machine.cayley_rom.read(addr)
        self.machine.rom_reads += 1
        return cayley.IDX_TO_NAME[ri]

    def dot_idx(self, xi: int, yi: int) -> int:
        """Single Cayley ROM lookup by atom index."""
        addr = xi * cayley.NUM_ATOMS + yi
        ri = self.machine.cayley_rom.read(addr)
        self.machine.rom_reads += 1
        return ri

    # -------------------------------------------------------------------
    # UART interface
    # -------------------------------------------------------------------

    def uart_send(self, data: bytes):
        """Feed bytes into the machine's UART RX FIFO."""
        for b in data:
            self.machine.uart_rx.push(b)

    def uart_recv(self) -> bytes:
        """Drain the machine's UART TX FIFO."""
        out = []
        while True:
            b = self.machine.uart_tx.pop()
            if b is None:
                break
            out.append(b)
        return bytes(out)

    # -------------------------------------------------------------------
    # Result decoding
    # -------------------------------------------------------------------

    def decode_word(self, word: int, depth: int = 0) -> str:
        """Decode a machine word into a human-readable string."""
        if depth > 20:
            return "..."

        tag, left, right, _meta = unpack_word(word)

        if tag == TAG_ATOM:
            idx = left & 0x3F
            if 0 <= idx < cayley.NUM_ATOMS:
                return cayley.IDX_TO_NAME[idx]
            return f"?atom({idx})"

        if tag == TAG_QUOTED:
            inner = self.machine.heap_read(left)
            return f"(QUOTE {self.decode_word(inner, depth + 1)})"

        if tag == TAG_APP:
            f_word = self.machine.heap_read(left)
            x_word = self.machine.heap_read(right)
            return f"({self.decode_word(f_word, depth + 1)} . {self.decode_word(x_word, depth + 1)})"

        if tag == TAG_BUNDLE:
            f_word = self.machine.heap_read(left)
            x_word = self.machine.heap_read(right)
            return f"#bundle[{self.decode_word(f_word, depth + 1)}, {self.decode_word(x_word, depth + 1)}]"

        if tag == TAG_PARTIAL:
            f_word = self.machine.heap_read(left)
            return f"#partial[{self.decode_word(f_word, depth + 1)}]"

        if tag == TAG_ALUP1:
            mode = (left >> 4) & 0x3
            sel = left & 0xF
            mode_name = ["logic", "arith", "arithc"][mode] if mode < 3 else "?"
            return f"#alu1[{mode_name}, S={sel:X}]"

        if tag == TAG_ALUP2:
            mode = (left >> 4) & 0x3
            sel = left & 0xF
            a_val = right & 0xF
            mode_name = ["logic", "arith", "arithc"][mode] if mode < 3 else "?"
            return f"#alu2[{mode_name}, S={sel:X}, A={a_val:X}]"

        if tag == TAG_IOPUTP:
            hi = left & 0xF
            return f"#io-put[N{hi:X}]"

        if tag == TAG_IOSEQP:
            first = self.machine.heap_read(left)
            return f"#io-seq[{self.decode_word(first, depth + 1)}]"

        if tag == TAG_COUT_PROBE:
            mode = (left >> 4) & 0x3
            sel = left & 0xF
            a_val = right & 0xF
            mode_name = ["logic", "arith", "arithc"][mode] if mode < 3 else "?"
            return f"#cout[{mode_name}, S={sel:X}, A={a_val:X}]"

        if tag == TAG_W32:
            val = ((left & 0xFFFF) << 16) | (right & 0xFFFF)
            return f"#w32[0x{val:08X}]"

        return f"?tag({tag})"


# ---------------------------------------------------------------------------
# CLI demo
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    host = EmulatorHost()

    # Test: atom self-id on ⊤
    print("=== Atom application tests ===")
    r = host.eval(("i", "⊤"))
    print(f"(i ⊤) = {r['result']}  [{r['stats']['cycles']} cycles]")

    r = host.eval(("⊤", "⊥"))
    print(f"(⊤ ⊥) = {r['result']}  [{r['stats']['cycles']} cycles]")

    # Test: nibble addition
    r = host.eval(("N3", "N5"))
    print(f"(N3 N5) = {r['result']}  [{r['stats']['cycles']} cycles]")

    # Test: QUOTE/EVAL roundtrip
    r = host.eval(("EVAL", ("QUOTE", "N7")))
    print(f"(EVAL (QUOTE N7)) = {r['result']}  [{r['stats']['cycles']} cycles]")

    # Test: APP/UNAPP roundtrip
    r = host.eval(("UNAPP", (("APP", "N3"), "N5")))
    print(f"(UNAPP ((APP N3) N5)) = {r['result']}  [{r['stats']['cycles']} cycles]")

    # Test: ALU
    r = host.eval(((("ALU_ARITH", "N9"), "N3"), "N5"))
    print(f"(((ALU_ARITH N9) N3) N5) = {r['result']}  [{r['stats']['cycles']} cycles, {r['stats']['alu_ops']} ALU ops]")

    # Test: IO_PUT
    r = host.eval((("IO_PUT", "N4"), "N8"))
    tx = host.uart_recv()
    print(f"((IO_PUT N4) N8) = {r['result']}, TX: {tx!r}  [{r['stats']['cycles']} cycles]")

    # Test: IO_SEQ
    r = host.eval((("IO_SEQ", ("⊤", "⊤")), ("N3", "N5")))
    print(f"((IO_SEQ (⊤ ⊤)) (N3 N5)) = {r['result']}  [{r['stats']['cycles']} cycles]")

    print(f"\n=== Stats ===\n{host.machine.stats_summary()}")

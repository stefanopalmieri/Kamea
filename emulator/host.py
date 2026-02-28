"""
EmulatorHost — high-level interface to the Kamea machine.

Provides term loading (S-expression → heap), evaluation, and result decoding.
Programs use structural fingerprints, making them permutation-invariant.
"""

from __future__ import annotations

from . import cayley
from .fingerprint import NAME_TO_FP, FP_TO_NAME, NUM_FP
from .scanner import CayleyScanner
from .machine import (
    KameaMachine, S_FETCH, S_APPLY, S_DONE, S_HALTED,
    make_atom_word, make_app_word, make_quoted_word,
    unpack_word, atom_idx_from_word,
    TAG_ATOM, TAG_QUOTED, TAG_APP, TAG_ALUP1, TAG_ALUP2,
    TAG_IOPUTP, TAG_IOSEQP, TAG_BUNDLE, TAG_PARTIAL, TAG_COUT_PROBE, TAG_W32,
    TAG_W16, TAG_WPACK, TAG_W32_OP1, TAG_MUL_OP1, TAG_EXTENDED,
    MODE_LOGIC, MODE_ARITH, MODE_ARITHC,
    w32_from_word, w16_from_word, wpack_unpack,
    W32_OP_ADD, W32_OP_SUB, W32_OP_CMP, W32_OP_XOR, W32_OP_AND, W32_OP_OR,
    W32_OP_SHL, W32_OP_SHR, W32_OP_ROTL, W32_OP_ROTR,
    MUL_OP_MUL16, MUL_OP_MAC1,
    EXT_MAC2, EXT_MERGE, EXT_NIB,
)


class EmulatorHost:
    """High-level interface to the Kamea machine.

    Args:
        cayley_rom: Optional ROM bytes. Defaults to canonical fingerprint ROM.
        atom_map: Optional atom name→index mapping (legacy).
        backend: "rom" (default), "neural", or "llm". When "neural", uses a
            6-hidden-dim MLP. When "llm", uses a local LLM via Ollama.
        neural_table: Pre-trained NeuralCayleyTable to use. If None and
            backend="neural", trains a fresh one automatically.
        llm_backend: Pre-created LLM backend to use. If None and
            backend="llm", creates one automatically (Ollama or mock).
        llm_injection: When True and backend="llm", enables prompt injection.
    """

    def __init__(self, cayley_rom: bytes | None = None,
                 atom_map: dict[str, int] | None = None,
                 backend: str = "rom",
                 neural_table: "NeuralCayleyTable | None" = None,
                 llm_backend: "LLMDotBackend | MockLLMBackend | None" = None,
                 llm_injection: bool = False):
        if backend == "llm":
            import sys
            from .llm_dot import LLMDotBackend, MockLLMBackend, _ollama_available
            from .llm_machine import LLMKameaMachine
            if llm_backend is None:
                rom_bytes = cayley.build_fingerprint_rom()
                if _ollama_available():
                    print("Using Ollama LLM backend for dot...",
                          file=sys.stderr, flush=True)
                    llm_backend = LLMDotBackend(
                        rom_bytes, injection=llm_injection)
                else:
                    print("Ollama not available, using mock LLM backend...",
                          file=sys.stderr, flush=True)
                    llm_backend = MockLLMBackend(
                        rom_bytes, injection=llm_injection)
            self.machine = LLMKameaMachine(llm_backend, cayley_rom, atom_map)
            self.llm_backend = llm_backend
        elif backend == "neural":
            import sys
            from pathlib import Path
            from .neural_dot import NeuralCayleyTable
            from .neural_machine import NeuralKameaMachine
            if neural_table is None:
                cache_dir = Path(__file__).parent / ".cache"
                cache_path = cache_dir / "cayley_mlp.pt"
                if cache_path.exists():
                    print("Loading cached neural Cayley table...",
                          file=sys.stderr, flush=True)
                    neural_table = NeuralCayleyTable.load(cache_path, device="cpu")
                    acc, correct, total = neural_table.accuracy()
                    if correct == total:
                        print(f"Loaded ({neural_table.parameter_count()} params, "
                              f"{correct}/{total} accuracy)",
                              file=sys.stderr, flush=True)
                    else:
                        print(f"Cached model stale ({correct}/{total}), retraining...",
                              file=sys.stderr, flush=True)
                        neural_table = None
                if neural_table is None:
                    # dim=6 is at the capacity edge; retry up to 5 times
                    for attempt in range(5):
                        print(f"Training neural Cayley table (dim=6, attempt {attempt + 1}/5)...",
                              file=sys.stderr, flush=True)
                        neural_table = NeuralCayleyTable(hidden_dim=6, device="cpu")
                        stats = neural_table.train(
                            epochs=20000, lr=1e-3, target_accuracy=1.0,
                        )
                        if stats["final_accuracy"] >= 1.0:
                            print(f"Trained in {stats['epochs']} epochs "
                                  f"({stats['training_time']:.1f}s), "
                                  f"{neural_table.parameter_count()} params",
                                  file=sys.stderr, flush=True)
                            break
                    else:
                        # Fall back to dim=8 which reliably converges
                        print("Falling back to dim=8...",
                              file=sys.stderr, flush=True)
                        neural_table = NeuralCayleyTable(hidden_dim=8, device="cpu")
                        stats = neural_table.train(
                            epochs=20000, lr=1e-3, target_accuracy=1.0,
                        )
                        print(f"Trained in {stats['epochs']} epochs "
                              f"({stats['training_time']:.1f}s), "
                              f"{neural_table.parameter_count()} params",
                              file=sys.stderr, flush=True)
                    # Cache for next time
                    cache_dir.mkdir(exist_ok=True)
                    neural_table.save(cache_path)
            self.machine = NeuralKameaMachine(neural_table, cayley_rom, atom_map)
            self.neural_table = neural_table
        else:
            self.machine = KameaMachine(cayley_rom, atom_map)
            self.neural_table = None
        if backend != "llm":
            self.llm_backend = None
        self.backend = backend

    # -------------------------------------------------------------------
    # Term loading: nested tuples/strings → heap words (fingerprint-based)
    # -------------------------------------------------------------------

    def load_term(self, term) -> int:
        """
        Load a term into the machine's heap, return root address.

        Term format:
          - str: atom name (e.g. "⊤", "N0", "QUOTE") → fingerprint atom word
          - int: fingerprint ordinal directly
          - (f, x): application (f applied to x)
          - ("QUOTED", inner): quoted term
        """
        if isinstance(term, str):
            fp = NAME_TO_FP[term]
            word = make_atom_word(fp)
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
        x_fp = NAME_TO_FP[x_name]
        y_fp = NAME_TO_FP[y_name]
        r_fp = self.machine.cayley_rom.read(x_fp * NUM_FP + y_fp)
        self.machine.rom_reads += 1
        return FP_TO_NAME[r_fp]

    def dot_idx(self, x_fp: int, y_fp: int) -> int:
        """Single Cayley ROM lookup by fingerprint. Returns result fingerprint."""
        r_fp = self.machine.cayley_rom.read(x_fp * NUM_FP + y_fp)
        self.machine.rom_reads += 1
        return r_fp

    # -------------------------------------------------------------------
    # Hardware scanner (boot-time recovery)
    # -------------------------------------------------------------------

    def scan_at_boot(self) -> dict[str, int]:
        """Use hardware scanner to recover atom_map from Cayley ROM."""
        scanner = CayleyScanner(self.machine.cayley_rom, cayley.NUM_ATOMS)
        return scanner.scan()

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
    # Result decoding (fingerprint-based)
    # -------------------------------------------------------------------

    def decode_word(self, word: int, depth: int = 0) -> str:
        """Decode a machine word into a human-readable string."""
        if depth > 20:
            return "..."

        tag, left, right, _meta = unpack_word(word)

        if tag == TAG_ATOM:
            fp = left & 0x7F
            name = FP_TO_NAME.get(fp)
            if name is not None:
                return name
            return f"?fp({fp})"

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

        if tag == TAG_W16:
            val = left & 0xFFFF
            return f"#w16[0x{val:04X}]"

        if tag == TAG_WPACK:
            acc, count = wpack_unpack(word)
            return f"#wpack[0x{acc:X}, {count}]"

        if tag == TAG_W32_OP1:
            opcode = left & 0xFF
            op_names = {
                W32_OP_ADD: "ADD", W32_OP_SUB: "SUB", W32_OP_CMP: "CMP",
                W32_OP_XOR: "XOR", W32_OP_AND: "AND", W32_OP_OR: "OR",
                W32_OP_SHL: "SHL", W32_OP_SHR: "SHR",
                W32_OP_ROTL: "ROTL", W32_OP_ROTR: "ROTR",
            }
            name = op_names.get(opcode, f"?{opcode}")
            a_word = self.machine.heap_read(right)
            return f"#w32op1[{name}, A={self.decode_word(a_word, depth + 1)}]"

        if tag == TAG_MUL_OP1:
            sub = left & 0xFF
            sub_name = {MUL_OP_MUL16: "MUL16", MUL_OP_MAC1: "MAC1"}.get(sub, f"?{sub}")
            operand = self.machine.heap_read(right)
            return f"#mulop1[{sub_name}, {self.decode_word(operand, depth + 1)}]"

        if tag == TAG_EXTENDED:
            sub_type = (left >> 20) & 0xF
            if sub_type == EXT_MAC2:
                app_word = self.machine.heap_read(right)
                return f"#mac2[{self.decode_word(app_word, depth + 1)}]"
            elif sub_type == EXT_MERGE:
                hi_word = self.machine.heap_read(right)
                return f"#merge[hi={self.decode_word(hi_word, depth + 1)}]"
            elif sub_type == EXT_NIB:
                w32_word = self.machine.heap_read(right)
                return f"#nib[{self.decode_word(w32_word, depth + 1)}]"
            return f"#ext[sub={sub_type}]"

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
    r = host.eval(("EVAL", ("QUOTED", "N7")))
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

"""
Verification suite for the Kamea machine emulator.

Tests the emulator against the reference implementations in kamea.py
and ds_repl.py to ensure behavioral equivalence.
"""

from __future__ import annotations

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from kamea import (
    ALL_NAMES, A, atom_dot, dot_ext, alu_74181,
    Atom, Quote, AppNode, UnappBundle, Partial,
    ALUPartial1, ALUPartial2, IOPutPartial, IOSeqPartial,
    is_nibble, nibble_val, nibble,
    NAMES_W32, NAMES_MUL,
)
from emulator import cayley
from emulator.machine import (
    KameaMachine, make_atom_word, make_app_word, unpack_word,
    make_w32_word, make_w16_word, w32_from_word, w16_from_word,
    TAG_ATOM, TAG_QUOTED, TAG_APP, TAG_BUNDLE, TAG_PARTIAL,
    TAG_ALUP1, TAG_ALUP2, TAG_IOPUTP, TAG_IOSEQP, TAG_COUT_PROBE,
    TAG_W32, TAG_W16, TAG_WPACK, TAG_W32_OP1, TAG_MUL_OP1, TAG_EXTENDED,
    S_DONE, S_HALTED, S_FETCH,
)
from emulator.host import EmulatorHost


def test_cayley_rom():
    """Verify all N×N Cayley ROM entries match atom_dot."""
    rom = cayley.build_cayley_rom()
    n = cayley.NUM_ATOMS
    total = n * n
    errors = 0
    for xi, xn in enumerate(ALL_NAMES):
        for yi, yn in enumerate(ALL_NAMES):
            expected = atom_dot(A(xn), A(yn))
            expected_idx = cayley.NAME_TO_IDX[expected.name]
            actual_idx = rom[xi * n + yi]
            if actual_idx != expected_idx:
                print(f"  FAIL: {xn}·{yn} = {cayley.IDX_TO_NAME[actual_idx]} "
                      f"(expected {expected.name})")
                errors += 1
    print(f"Cayley ROM: {total - errors}/{total} correct")
    return errors == 0


def test_atom_pairs():
    """
    Test atom×atom applications through the eval/apply machine
    against dot_ext from kamea.py.
    """
    host = EmulatorHost()
    errors = 0
    total = 0

    # W32/MUL atoms have term-level dispatch not modeled by dot_ext
    w32_mul_names = frozenset(NAMES_W32 + NAMES_MUL)

    for xn in ALL_NAMES:
        for yn in ALL_NAMES:
            # Skip IO_RDY·⊤: machine checks real FIFO (returns ⊥ when empty),
            # while the pure reference always returns ⊤.
            if xn == "IO_RDY" and yn == "⊤":
                continue

            # Skip W32/MUL atoms in function position: term-level dispatch
            # produces structured values not modeled by the pure reference.
            if xn in w32_mul_names:
                continue

            total += 1
            # Reference
            ref = dot_ext(A(xn), A(yn))

            # Machine
            host.machine.sp.load(0)
            host.machine.state.load(S_FETCH)
            host.machine.reset_counters()

            addr = host.load_term((xn, yn))
            host.machine.tp.load(addr)
            host.machine.state.load(S_FETCH)
            result_word = host.machine.run()

            # Compare
            machine_str = host.decode_word(result_word)
            ref_str = _format_ref(ref)

            if not _results_match(ref, result_word, host):
                if errors < 20:
                    print(f"  FAIL: ({xn} {yn}) → machine={machine_str}, ref={ref_str}")
                errors += 1

    print(f"Atom pairs: {total - errors}/{total} correct")
    return errors == 0


def test_alu_operations():
    """Test ALU operations through the machine against alu_74181."""
    host = EmulatorHost()
    errors = 0
    total = 0

    for mode_name, mode_str in [("logic", "ALU_LOGIC"), ("arith", "ALU_ARITH"),
                                 ("arithc", "ALU_ARITHC")]:
        for sel in range(16):
            for a_val in [0, 5, 10, 15]:
                for b_val in [0, 3, 7, 15]:
                    total += 1
                    # Reference
                    ref_result, ref_carry, ref_zero = alu_74181(mode_name, sel, a_val, b_val)

                    # Machine: (((ALU_X N_sel) N_a) N_b)
                    sel_name = f"N{sel:X}"
                    a_name = f"N{a_val:X}"
                    b_name = f"N{b_val:X}"
                    term = (((mode_str, sel_name), a_name), b_name)

                    r = host.eval(term)
                    result_str = r["result"]
                    expected_name = f"N{ref_result:X}"

                    if result_str != expected_name:
                        if errors < 20:
                            print(f"  FAIL: {mode_str} S={sel:X} A={a_val:X} B={b_val:X} → "
                                  f"machine={result_str}, expected={expected_name}")
                        errors += 1

    print(f"ALU operations: {total - errors}/{total} correct")
    return errors == 0


def test_alu_cout_probe():
    """Test ALU_COUT carry extraction through CoutProbe."""
    host = EmulatorHost()
    errors = 0
    total = 0

    for sel in [0, 9, 12, 15]:
        for a_val in [0, 7, 8, 15]:
            for b_val in [0, 5, 10, 15]:
                total += 1
                # Reference
                _, ref_carry, _ = alu_74181("arith", sel, a_val, b_val)

                # Machine: ((ALU_COUT ((ALU_ARITH N_sel) N_a)) N_b)
                sel_name = f"N{sel:X}"
                a_name = f"N{a_val:X}"
                b_name = f"N{b_val:X}"
                term = (("ALU_COUT", (("ALU_ARITH", sel_name), a_name)), b_name)

                r = host.eval(term)
                expected = "⊤" if ref_carry else "⊥"

                if r["result"] != expected:
                    if errors < 20:
                        print(f"  FAIL: COUT arith S={sel:X} A={a_val:X} B={b_val:X} → "
                              f"machine={r['result']}, expected={expected}")
                    errors += 1

    print(f"ALU COUT probe: {total - errors}/{total} correct")
    return errors == 0


def test_quote_eval():
    """Test QUOTE/EVAL roundtrip."""
    host = EmulatorHost()
    errors = 0
    total = 0

    for name in ALL_NAMES:
        total += 1
        r = host.eval(("EVAL", ("QUOTE", name)))
        if r["result"] != name:
            print(f"  FAIL: (EVAL (QUOTE {name})) = {r['result']}")
            errors += 1

    print(f"QUOTE/EVAL roundtrip: {total - errors}/{total} correct")
    return errors == 0


def test_app_unapp():
    """Test APP/UNAPP with bundle queries."""
    host = EmulatorHost()
    errors = 0

    # Test a sample of pairs
    test_pairs = [("N0", "N1"), ("⊤", "⊥"), ("i", "k"), ("QUOTE", "EVAL"),
                  ("N7", "NA"), ("ALU_LOGIC", "p")]

    for f_name, x_name in test_pairs:
        # Build and decompose
        r = host.eval((("UNAPP", (("APP", f_name), x_name)), "⊤"))
        if r["result"] != f_name:
            print(f"  FAIL: bundle({f_name},{x_name})·⊤ = {r['result']}")
            errors += 1

        r = host.eval((("UNAPP", (("APP", f_name), x_name)), "⊥"))
        if r["result"] != x_name:
            print(f"  FAIL: bundle({f_name},{x_name})·⊥ = {r['result']}")
            errors += 1

    total = len(test_pairs) * 2
    print(f"APP/UNAPP roundtrip: {total - errors}/{total} correct")
    return errors == 0


def test_io_put():
    """Test IO_PUT produces correct UART TX bytes."""
    host = EmulatorHost()
    errors = 0

    test_cases = [(4, 8, 0x48, "H"), (6, 9, 0x69, "i"), (0, 0, 0x00, "\\x00")]

    for hi, lo, expected_byte, desc in test_cases:
        host.machine.uart_tx = __import__("emulator.chips", fromlist=["FIFO"]).FIFO(16)
        r = host.eval((("IO_PUT", f"N{hi:X}"), f"N{lo:X}"))

        if r["result"] != "⊤":
            print(f"  FAIL: IO_PUT N{hi:X} N{lo:X} result = {r['result']}, expected ⊤")
            errors += 1
            continue

        tx_data = host.uart_recv()
        if len(tx_data) != 1 or tx_data[0] != expected_byte:
            print(f"  FAIL: IO_PUT N{hi:X} N{lo:X} TX = {tx_data!r}, expected {bytes([expected_byte])!r}")
            errors += 1

    total = len(test_cases)
    print(f"IO_PUT: {total - errors}/{total} correct")
    return errors == 0


def test_io_get():
    """Test IO_GET reads UART RX and produces nibble pair."""
    host = EmulatorHost()
    errors = 0

    test_bytes = [0x48, 0x00, 0xFF, 0x7A]

    for byte_val in test_bytes:
        host.uart_send(bytes([byte_val]))
        r = host.eval(("IO_GET", "⊤"))
        expected_hi = f"N{(byte_val >> 4) & 0xF:X}"
        expected_lo = f"N{byte_val & 0xF:X}"

        # Result should be an app-node(N_hi, N_lo)
        tag, left, right, _meta = unpack_word(r["result_word"])
        if tag != TAG_APP:
            print(f"  FAIL: IO_GET 0x{byte_val:02X} → tag={tag}, expected TAG_APP")
            errors += 1
            continue

        f_word = host.machine.heap_read(left)
        x_word = host.machine.heap_read(right)
        hi_str = host.decode_word(f_word)
        lo_str = host.decode_word(x_word)

        if hi_str != expected_hi or lo_str != expected_lo:
            print(f"  FAIL: IO_GET 0x{byte_val:02X} → ({hi_str}, {lo_str}), "
                  f"expected ({expected_hi}, {expected_lo})")
            errors += 1

    total = len(test_bytes)
    print(f"IO_GET: {total - errors}/{total} correct")
    return errors == 0


def test_io_rdy():
    """Test IO_RDY checks UART RX FIFO status."""
    host = EmulatorHost()

    # Empty FIFO → BOT
    r = host.eval(("IO_RDY", "⊤"))
    ok1 = r["result"] == "⊥"

    # Non-empty FIFO → TOP
    host.uart_send(b"\x42")
    r = host.eval(("IO_RDY", "⊤"))
    ok2 = r["result"] == "⊤"

    passed = int(ok1) + int(ok2)
    if not ok1:
        print(f"  FAIL: IO_RDY on empty FIFO = {r['result']}, expected ⊥")
    if not ok2:
        print(f"  FAIL: IO_RDY on non-empty FIFO = {r['result']}, expected ⊤")
    print(f"IO_RDY: {passed}/2 correct")
    return passed == 2


def test_io_seq():
    """Test IO_SEQ discards first, returns second."""
    host = EmulatorHost()

    # (IO_SEQ a) b → b
    r = host.eval((("IO_SEQ", "N3"), "N7"))
    ok = r["result"] == "N7"
    if not ok:
        print(f"  FAIL: ((IO_SEQ N3) N7) = {r['result']}, expected N7")
    print(f"IO_SEQ: {'1/1' if ok else '0/1'} correct")
    return ok


def test_nested_expressions():
    """Test various nested expressions."""
    host = EmulatorHost()
    errors = 0

    test_data = [
        (("N_SUCC", "N3"), "N4"),
        (("e_I", "i"), "⊤"),
        (("e_I", "a"), "⊥"),
        (("ALU_ZERO", "N0"), "⊤"),
        (("ALU_ZERO", "N1"), "⊥"),
    ]

    # Compute ALU expected values — full 3-arg applications
    alu_tests = [
        ("logic", 15, 3, 5),
        ("arith", 9, 3, 5),
        ("arithc", 6, 10, 5),
    ]
    for mode, sel, a, b in alu_tests:
        res, _, _ = alu_74181(mode, sel, a, b)
        mode_atom = {"logic": "ALU_LOGIC", "arith": "ALU_ARITH", "arithc": "ALU_ARITHC"}[mode]
        test_data.append((
            (((mode_atom, f"N{sel:X}"), f"N{a:X}"), f"N{b:X}"),
            f"N{res:X}",
        ))

    for term, expected in test_data:
        r = host.eval(term)
        if r["result"] != expected:
            print(f"  FAIL: {term} → {r['result']}, expected {expected}")
            errors += 1

    total = len(test_data)
    print(f"Nested expressions: {total - errors}/{total} correct")
    return errors == 0


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _format_ref(val) -> str:
    """Format a reference value from dot_ext for comparison."""
    if isinstance(val, Atom):
        return val.name
    if isinstance(val, Quote):
        return f"(QUOTE {_format_ref(val.term)})"
    if isinstance(val, AppNode):
        return f"({_format_ref(val.f)} . {_format_ref(val.x)})"
    if isinstance(val, UnappBundle):
        return f"#bundle[{_format_ref(val.f)}, {_format_ref(val.x)}]"
    if isinstance(val, Partial):
        return f"#partial[{_format_ref(val.a)}]"
    if isinstance(val, ALUPartial1):
        return f"#alu1[{val.mode}, S={val.selector:X}]"
    if isinstance(val, ALUPartial2):
        return f"#alu2[{val.mode}, S={val.selector:X}, A={val.a:X}]"
    if isinstance(val, IOPutPartial):
        return f"#io-put[N{val.hi:X}]"
    if isinstance(val, IOSeqPartial):
        return f"#io-seq[{_format_ref(val.first)}]"
    return str(val)


def _results_match(ref, result_word: int, host: EmulatorHost) -> bool:
    """Check if machine result matches reference value."""
    tag, left, right, _meta = unpack_word(result_word)

    if isinstance(ref, Atom):
        if tag != TAG_ATOM:
            return False
        return (left & 0x7F) == cayley.NAME_TO_IDX.get(ref.name, -1)

    if isinstance(ref, Quote):
        if tag != TAG_QUOTED:
            return False
        inner_word = host.machine.heap_read(left)
        return _results_match(ref.term, inner_word, host)

    if isinstance(ref, AppNode):
        if tag != TAG_APP:
            return False
        f_word = host.machine.heap_read(left)
        x_word = host.machine.heap_read(right)
        return _results_match(ref.f, f_word, host) and _results_match(ref.x, x_word, host)

    if isinstance(ref, Partial):
        if tag != TAG_PARTIAL:
            return False
        f_word = host.machine.heap_read(left)
        return _results_match(ref.a, f_word, host)

    if isinstance(ref, ALUPartial1):
        if tag != TAG_ALUP1:
            return False
        mode_map = {"logic": 0, "arith": 1, "arithc": 2}
        return ((left >> 4) & 0x3) == mode_map[ref.mode] and (left & 0xF) == ref.selector

    if isinstance(ref, ALUPartial2):
        if tag != TAG_ALUP2:
            return False
        mode_map = {"logic": 0, "arith": 1, "arithc": 2}
        return (((left >> 4) & 0x3) == mode_map[ref.mode] and
                (left & 0xF) == ref.selector and
                (right & 0xF) == ref.a)

    if isinstance(ref, IOPutPartial):
        if tag != TAG_IOPUTP:
            return False
        return (left & 0xF) == ref.hi

    if isinstance(ref, IOSeqPartial):
        if tag != TAG_IOSEQP:
            return False
        first_word = host.machine.heap_read(left)
        return _results_match(ref.first, first_word, host)

    # Unknown ref type
    return False


# ---------------------------------------------------------------------------
# W32/MUL Tests
# ---------------------------------------------------------------------------

def _w32_dispatch(host, f_word, x_word):
    """Helper: dispatch f_word applied to x_word, return result word."""
    return host.dispatch_word(f_word, x_word)


def test_w32_pack8():
    """Test W_PACK8: packing 8 nibbles into a W32."""
    host = EmulatorHost()
    m = host.machine
    errors = 0

    # Pack 0x12345678
    pack_atom = make_atom_word(m.W_PACK8)
    nibbles = [1, 2, 3, 4, 5, 6, 7, 8]

    val = _w32_dispatch(host, pack_atom, make_atom_word(m._nibble_idx(nibbles[0])))
    for nib in nibbles[1:]:
        val = _w32_dispatch(host, val, make_atom_word(m._nibble_idx(nib)))

    tag, _, _, _ = unpack_word(val)
    if tag != TAG_W32:
        print(f"  FAIL: W_PACK8 result tag = {tag}, expected TAG_W32")
        errors += 1
    else:
        result = w32_from_word(val)
        if result != 0x12345678:
            print(f"  FAIL: W_PACK8 result = 0x{result:08X}, expected 0x12345678")
            errors += 1

    # Pack 0x00000000
    val = _w32_dispatch(host, pack_atom, make_atom_word(m._nibble_idx(0)))
    for _ in range(7):
        val = _w32_dispatch(host, val, make_atom_word(m._nibble_idx(0)))
    result = w32_from_word(val)
    if result != 0:
        print(f"  FAIL: W_PACK8 zeros = 0x{result:08X}, expected 0x00000000")
        errors += 1

    # Pack 0xFFFFFFFF
    val = _w32_dispatch(host, pack_atom, make_atom_word(m._nibble_idx(0xF)))
    for _ in range(7):
        val = _w32_dispatch(host, val, make_atom_word(m._nibble_idx(0xF)))
    result = w32_from_word(val)
    if result != 0xFFFFFFFF:
        print(f"  FAIL: W_PACK8 FFs = 0x{result:08X}, expected 0xFFFFFFFF")
        errors += 1

    total = 3
    print(f"W_PACK8: {total - errors}/{total} correct")
    return errors == 0


def test_w32_lo_hi():
    """Test W_LO and W_HI: extract 16-bit halves from W32."""
    host = EmulatorHost()
    m = host.machine
    errors = 0

    test_vals = [0x12345678, 0x00000000, 0xFFFFFFFF, 0xABCD0000, 0x0000BEEF]
    for v in test_vals:
        w = make_w32_word(v)
        lo = _w32_dispatch(host, make_atom_word(m.W_LO), w)
        hi = _w32_dispatch(host, make_atom_word(m.W_HI), w)

        tag_lo, _, _, _ = unpack_word(lo)
        tag_hi, _, _, _ = unpack_word(hi)
        if tag_lo != TAG_W16:
            print(f"  FAIL: W_LO(0x{v:08X}) tag = {tag_lo}")
            errors += 1
            continue
        if tag_hi != TAG_W16:
            print(f"  FAIL: W_HI(0x{v:08X}) tag = {tag_hi}")
            errors += 1
            continue

        lo_val = w16_from_word(lo)
        hi_val = w16_from_word(hi)
        if lo_val != (v & 0xFFFF):
            print(f"  FAIL: W_LO(0x{v:08X}) = 0x{lo_val:04X}, expected 0x{v & 0xFFFF:04X}")
            errors += 1
        if hi_val != ((v >> 16) & 0xFFFF):
            print(f"  FAIL: W_HI(0x{v:08X}) = 0x{hi_val:04X}, expected 0x{(v >> 16) & 0xFFFF:04X}")
            errors += 1

    total = len(test_vals) * 2
    print(f"W_LO/W_HI: {total - errors}/{total} correct")
    return errors == 0


def test_w32_merge():
    """Test W_MERGE: combine two W16 halves into W32, round-trip with W_LO/W_HI."""
    host = EmulatorHost()
    m = host.machine
    errors = 0

    test_vals = [0x12345678, 0xABCD1234, 0x00000001, 0xFFFF0000]
    for v in test_vals:
        w = make_w32_word(v)
        lo = _w32_dispatch(host, make_atom_word(m.W_LO), w)
        hi = _w32_dispatch(host, make_atom_word(m.W_HI), w)
        # W_MERGE(hi)(lo) → W32
        merge_partial = _w32_dispatch(host, make_atom_word(m.W_MERGE), hi)
        merged = _w32_dispatch(host, merge_partial, lo)

        tag, _, _, _ = unpack_word(merged)
        if tag != TAG_W32:
            print(f"  FAIL: W_MERGE round-trip tag = {tag}")
            errors += 1
            continue
        result = w32_from_word(merged)
        if result != v:
            print(f"  FAIL: W_MERGE round-trip 0x{v:08X} → 0x{result:08X}")
            errors += 1

    total = len(test_vals)
    print(f"W_MERGE: {total - errors}/{total} correct")
    return errors == 0


def test_w32_not():
    """Test W_NOT: bitwise NOT of W32."""
    host = EmulatorHost()
    m = host.machine
    errors = 0

    test_vals = [0x00000000, 0xFFFFFFFF, 0x12345678, 0xAAAA5555]
    for v in test_vals:
        w = make_w32_word(v)
        result = _w32_dispatch(host, make_atom_word(m.W_NOT), w)
        tag, _, _, _ = unpack_word(result)
        if tag != TAG_W32:
            print(f"  FAIL: W_NOT(0x{v:08X}) tag = {tag}")
            errors += 1
            continue
        r = w32_from_word(result)
        expected = (~v) & 0xFFFFFFFF
        if r != expected:
            print(f"  FAIL: W_NOT(0x{v:08X}) = 0x{r:08X}, expected 0x{expected:08X}")
            errors += 1

    total = len(test_vals)
    print(f"W_NOT: {total - errors}/{total} correct")
    return errors == 0


def test_w32_arithmetic():
    """Test W_ADD, W_SUB, W_CMP."""
    host = EmulatorHost()
    m = host.machine
    errors = 0
    total = 0

    M = 0xFFFFFFFF
    test_pairs = [
        (0, 0), (1, 0), (0, 1), (100, 200),
        (0xFFFFFFFF, 1),  # overflow
        (0, 0xFFFFFFFF),  # underflow for sub
        (0x80000000, 0x80000000),
        (0x12345678, 0x12345678),  # equal for CMP
    ]

    for a, b in test_pairs:
        wa = make_w32_word(a)
        wb = make_w32_word(b)

        # W_ADD
        total += 1
        partial = _w32_dispatch(host, make_atom_word(m.W_ADD), wa)
        result = _w32_dispatch(host, partial, wb)
        r = w32_from_word(result)
        expected = (a + b) & M
        if r != expected:
            print(f"  FAIL: W_ADD(0x{a:08X}, 0x{b:08X}) = 0x{r:08X}, expected 0x{expected:08X}")
            errors += 1

        # W_SUB
        total += 1
        partial = _w32_dispatch(host, make_atom_word(m.W_SUB), wa)
        result = _w32_dispatch(host, partial, wb)
        r = w32_from_word(result)
        expected = (a - b) & M
        if r != expected:
            print(f"  FAIL: W_SUB(0x{a:08X}, 0x{b:08X}) = 0x{r:08X}, expected 0x{expected:08X}")
            errors += 1

        # W_CMP
        total += 1
        partial = _w32_dispatch(host, make_atom_word(m.W_CMP), wa)
        result = _w32_dispatch(host, partial, wb)
        tag, left, _, _ = unpack_word(result)
        atom_idx = left & 0x7F
        expected_atom = m.TOP if a == b else m.BOT
        if tag != TAG_ATOM or atom_idx != expected_atom:
            print(f"  FAIL: W_CMP(0x{a:08X}, 0x{b:08X}) = {host.decode_word(result)}, expected {'⊤' if a == b else '⊥'}")
            errors += 1

    print(f"W_ADD/SUB/CMP: {total - errors}/{total} correct")
    return errors == 0


def test_w32_bitwise():
    """Test W_XOR, W_AND, W_OR."""
    host = EmulatorHost()
    m = host.machine
    errors = 0
    total = 0

    test_pairs = [
        (0xFF00FF00, 0x0F0F0F0F),
        (0xAAAAAAAA, 0x55555555),
        (0x00000000, 0xFFFFFFFF),
        (0x12345678, 0x9ABCDEF0),
    ]

    ops = [
        (m.W_XOR, "W_XOR", lambda a, b: a ^ b),
        (m.W_AND, "W_AND", lambda a, b: a & b),
        (m.W_OR,  "W_OR",  lambda a, b: a | b),
    ]

    for a, b in test_pairs:
        wa = make_w32_word(a)
        wb = make_w32_word(b)
        for atom_idx, name, fn in ops:
            total += 1
            partial = _w32_dispatch(host, make_atom_word(atom_idx), wa)
            result = _w32_dispatch(host, partial, wb)
            r = w32_from_word(result)
            expected = fn(a, b)
            if r != expected:
                print(f"  FAIL: {name}(0x{a:08X}, 0x{b:08X}) = 0x{r:08X}, expected 0x{expected:08X}")
                errors += 1

    print(f"W_XOR/AND/OR: {total - errors}/{total} correct")
    return errors == 0


def test_w32_shifts():
    """Test W_SHL, W_SHR, W_ROTL, W_ROTR including ChaCha20 amounts."""
    host = EmulatorHost()
    m = host.machine
    errors = 0
    total = 0

    M = 0xFFFFFFFF
    test_cases = [
        # (value, shift_amount)
        (0x00000001, 0), (0x00000001, 1), (0x00000001, 16), (0x00000001, 31),
        (0x80000001, 1), (0x80000001, 7), (0x80000001, 8), (0x80000001, 12),
        (0x80000001, 16),
        (0xDEADBEEF, 7), (0xDEADBEEF, 8), (0xDEADBEEF, 12), (0xDEADBEEF, 16),
    ]

    for val, shift in test_cases:
        wv = make_w32_word(val)
        ws = make_w32_word(shift)

        # SHL
        total += 1
        partial = _w32_dispatch(host, make_atom_word(m.W_SHL), wv)
        result = _w32_dispatch(host, partial, ws)
        r = w32_from_word(result)
        expected = (val << shift) & M
        if r != expected:
            print(f"  FAIL: SHL(0x{val:08X}, {shift}) = 0x{r:08X}, expected 0x{expected:08X}")
            errors += 1

        # SHR
        total += 1
        partial = _w32_dispatch(host, make_atom_word(m.W_SHR), wv)
        result = _w32_dispatch(host, partial, ws)
        r = w32_from_word(result)
        expected = val >> shift
        if r != expected:
            print(f"  FAIL: SHR(0x{val:08X}, {shift}) = 0x{r:08X}, expected 0x{expected:08X}")
            errors += 1

        # ROTL
        total += 1
        partial = _w32_dispatch(host, make_atom_word(m.W_ROTL), wv)
        result = _w32_dispatch(host, partial, ws)
        r = w32_from_word(result)
        n = shift & 31
        expected = ((val << n) | (val >> (32 - n))) & M if n else val
        if r != expected:
            print(f"  FAIL: ROTL(0x{val:08X}, {shift}) = 0x{r:08X}, expected 0x{expected:08X}")
            errors += 1

        # ROTR
        total += 1
        partial = _w32_dispatch(host, make_atom_word(m.W_ROTR), wv)
        result = _w32_dispatch(host, partial, ws)
        r = w32_from_word(result)
        expected = ((val >> n) | (val << (32 - n))) & M if n else val
        if r != expected:
            print(f"  FAIL: ROTR(0x{val:08X}, {shift}) = 0x{r:08X}, expected 0x{expected:08X}")
            errors += 1

    print(f"W_SHL/SHR/ROTL/ROTR: {total - errors}/{total} correct")
    return errors == 0


def test_w32_nib():
    """Test W_NIB: extract nibbles from a W32."""
    host = EmulatorHost()
    m = host.machine
    errors = 0

    val = 0x12345678
    w = make_w32_word(val)
    nib_atom = make_atom_word(m.W_NIB)

    for pos in range(8):
        partial = _w32_dispatch(host, nib_atom, w)
        result = _w32_dispatch(host, partial, make_atom_word(m._nibble_idx(pos)))
        tag, left, _, _ = unpack_word(result)
        if tag != TAG_ATOM:
            print(f"  FAIL: W_NIB(0x{val:08X}, {pos}) tag = {tag}")
            errors += 1
            continue
        idx = left & 0x7F
        expected_nib = (val >> (pos * 4)) & 0xF
        expected_idx = m._nibble_idx(expected_nib)
        if idx != expected_idx:
            print(f"  FAIL: W_NIB(0x{val:08X}, {pos}) = N{m._nibble_val(idx):X}, expected N{expected_nib:X}")
            errors += 1

    total = 8
    print(f"W_NIB: {total - errors}/{total} correct")
    return errors == 0


def test_mul16():
    """Test MUL16: 16-bit multiply."""
    host = EmulatorHost()
    m = host.machine
    errors = 0
    total = 0

    test_pairs = [
        (0, 0), (1, 1), (2, 3), (0xFF, 0xFF),
        (0xFFFF, 0xFFFF),  # max overflow
        (100, 200), (0x1234, 0x5678),
    ]

    for a, b in test_pairs:
        total += 1
        wa = make_w16_word(a)
        wb = make_w16_word(b)

        partial = _w32_dispatch(host, make_atom_word(m.MUL16), wa)
        result = _w32_dispatch(host, partial, wb)

        # Result should be APP(W16_hi, W16_lo)
        tag, left, right, _ = unpack_word(result)
        if tag != TAG_APP:
            print(f"  FAIL: MUL16({a}, {b}) tag = {tag}, expected TAG_APP")
            errors += 1
            continue

        hi_word = m.heap_read(left)
        lo_word = m.heap_read(right)
        hi_val = w16_from_word(hi_word)
        lo_val = w16_from_word(lo_word)
        product = (hi_val << 16) | lo_val
        expected = a * b

        if product != expected:
            print(f"  FAIL: MUL16({a}, {b}) = {product}, expected {expected}")
            errors += 1

    print(f"MUL16: {total - errors}/{total} correct")
    return errors == 0


def test_mac16():
    """Test MAC16: multiply-accumulate (acc + a * b)."""
    host = EmulatorHost()
    m = host.machine
    errors = 0
    total = 0

    test_cases = [
        # (acc, a, b)
        (0, 2, 3),       # 0 + 2*3 = 6
        (10, 5, 4),      # 10 + 5*4 = 30
        (0xFFFF, 1, 1),  # 0xFFFF + 1 = 0x10000
        (100, 0xFF, 0xFF),  # 100 + 255*255 = 65225
    ]

    for acc, a, b in test_cases:
        total += 1
        w_acc = make_w16_word(acc)
        w_a = make_w16_word(a)
        w_b = make_w16_word(b)

        # MAC16(acc)(a)(b)
        partial1 = _w32_dispatch(host, make_atom_word(m.MAC16), w_acc)
        partial2 = _w32_dispatch(host, partial1, w_a)
        result = _w32_dispatch(host, partial2, w_b)

        tag, left, right, _ = unpack_word(result)
        if tag != TAG_APP:
            print(f"  FAIL: MAC16({acc}, {a}, {b}) tag = {tag}, expected TAG_APP")
            errors += 1
            continue

        hi_word = m.heap_read(left)
        lo_word = m.heap_read(right)
        hi_val = w16_from_word(hi_word)
        lo_val = w16_from_word(lo_word)
        product = (hi_val << 16) | lo_val
        expected = acc + a * b

        if product != expected:
            print(f"  FAIL: MAC16({acc}, {a}, {b}) = {product}, expected {expected}")
            errors += 1

    print(f"MAC16: {total - errors}/{total} correct")
    return errors == 0


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 60)
    print("Kamea Machine Emulator — Verification Suite")
    print("=" * 60)

    all_pass = True

    print("\n--- Cayley ROM ---")
    all_pass &= test_cayley_rom()

    print(f"\n--- Atom Pairs ({cayley.NUM_ATOMS}×{cayley.NUM_ATOMS} tests) ---")
    all_pass &= test_atom_pairs()

    print("\n--- ALU Operations ---")
    all_pass &= test_alu_operations()

    print("\n--- ALU COUT Probe ---")
    all_pass &= test_alu_cout_probe()

    print("\n--- QUOTE/EVAL ---")
    all_pass &= test_quote_eval()

    print("\n--- APP/UNAPP ---")
    all_pass &= test_app_unapp()

    print("\n--- IO_PUT ---")
    all_pass &= test_io_put()

    print("\n--- IO_GET ---")
    all_pass &= test_io_get()

    print("\n--- IO_RDY ---")
    all_pass &= test_io_rdy()

    print("\n--- IO_SEQ ---")
    all_pass &= test_io_seq()

    print("\n--- Nested Expressions ---")
    all_pass &= test_nested_expressions()

    print("\n--- W_PACK8 ---")
    all_pass &= test_w32_pack8()

    print("\n--- W_LO/W_HI ---")
    all_pass &= test_w32_lo_hi()

    print("\n--- W_MERGE ---")
    all_pass &= test_w32_merge()

    print("\n--- W_NOT ---")
    all_pass &= test_w32_not()

    print("\n--- W_ADD/SUB/CMP ---")
    all_pass &= test_w32_arithmetic()

    print("\n--- W_XOR/AND/OR ---")
    all_pass &= test_w32_bitwise()

    print("\n--- W_SHL/SHR/ROTL/ROTR ---")
    all_pass &= test_w32_shifts()

    print("\n--- W_NIB ---")
    all_pass &= test_w32_nib()

    print("\n--- MUL16 ---")
    all_pass &= test_mul16()

    print("\n--- MAC16 ---")
    all_pass &= test_mac16()

    print("\n" + "=" * 60)
    if all_pass:
        print("ALL TESTS PASSED")
    else:
        print("SOME TESTS FAILED")
        sys.exit(1)


if __name__ == "__main__":
    main()

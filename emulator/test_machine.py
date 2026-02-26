"""
Verification suite for the Kamea machine emulator.

Tests the emulator against the reference implementations in delta2_74181.py
and ds_repl.py to ensure behavioral equivalence.
"""

from __future__ import annotations

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from delta2_74181 import (
    ALL_NAMES, A, atom_dot, dot_ext, alu_74181,
    Atom, Quote, AppNode, UnappBundle, Partial,
    ALUPartial1, ALUPartial2, IOPutPartial, IOSeqPartial,
    is_nibble, nibble_val, nibble,
)
from emulator import cayley
from emulator.machine import (
    KameaMachine, make_atom_word, make_app_word, unpack_word,
    TAG_ATOM, TAG_QUOTED, TAG_APP, TAG_BUNDLE, TAG_PARTIAL,
    TAG_ALUP1, TAG_ALUP2, TAG_IOPUTP, TAG_IOSEQP, TAG_COUT_PROBE,
    S_DONE, S_HALTED, S_FETCH,
)
from emulator.host import EmulatorHost


def test_cayley_rom():
    """Verify all 47×47 = 2209 Cayley ROM entries match atom_dot."""
    rom = cayley.build_cayley_rom()
    errors = 0
    for xi, xn in enumerate(ALL_NAMES):
        for yi, yn in enumerate(ALL_NAMES):
            expected = atom_dot(A(xn), A(yn))
            expected_idx = cayley.NAME_TO_IDX[expected.name]
            actual_idx = rom[xi * cayley.NUM_ATOMS + yi]
            if actual_idx != expected_idx:
                print(f"  FAIL: {xn}·{yn} = {cayley.IDX_TO_NAME[actual_idx]} "
                      f"(expected {expected.name})")
                errors += 1
    print(f"Cayley ROM: {2209 - errors}/2209 correct")
    return errors == 0


def test_atom_pairs():
    """
    Test all 47×47 atom×atom applications through the eval/apply machine
    against dot_ext from delta2_74181.py.
    """
    host = EmulatorHost()
    errors = 0
    total = 0

    for xn in ALL_NAMES:
        for yn in ALL_NAMES:
            # Skip IO_RDY·⊤: machine checks real FIFO (returns ⊥ when empty),
            # while the pure reference always returns ⊤.
            if xn == "IO_RDY" and yn == "⊤":
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
        tag, left, right = unpack_word(r["result_word"])
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
    tag, left, right = unpack_word(result_word)

    if isinstance(ref, Atom):
        if tag != TAG_ATOM:
            return False
        return (left & 0x3F) == cayley.NAME_TO_IDX.get(ref.name, -1)

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
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 60)
    print("Kamea Machine Emulator — Verification Suite")
    print("=" * 60)

    all_pass = True

    print("\n--- Cayley ROM ---")
    all_pass &= test_cayley_rom()

    print("\n--- Atom Pairs (47×47 = 2209 tests) ---")
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

    print("\n" + "=" * 60)
    if all_pass:
        print("ALL TESTS PASSED")
    else:
        print("SOME TESTS FAILED")
        sys.exit(1)


if __name__ == "__main__":
    main()

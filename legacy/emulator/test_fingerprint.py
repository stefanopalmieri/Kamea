"""
Tests for structural fingerprints and fingerprint-addressed ROM.

Verifies that the fingerprint ROM correctly encodes the Kamea algebra,
and that programs produce correct results using fingerprint-addressed dispatch.
"""

import pytest
from . import cayley
from .fingerprint import (
    NAME_TO_FP, FP_TO_NAME, NUM_FP,
    FP_TOP, FP_BOT, FP_N0, FP_NF, FP_QUOTE, FP_EVAL,
    FP_P, FP_QUALE,
)
from .host import EmulatorHost
from .machine import (
    KameaMachine, make_atom_word, unpack_word, TAG_ATOM,
    pack_word,
)
from .coordinate_free import (
    CoordinateFreeProgram, run_coordinate_free,
)


# ---------------------------------------------------------------------------
# Fingerprint ROM tests
# ---------------------------------------------------------------------------

class TestFingerprintRom:

    def test_rom_size(self):
        """Fingerprint ROM is NUM_FP * NUM_FP bytes."""
        rom = cayley.build_fingerprint_rom()
        assert len(rom) == NUM_FP * NUM_FP

    def test_deterministic(self):
        """Building ROM twice gives identical bytes."""
        rom1 = cayley.build_fingerprint_rom()
        rom2 = cayley.build_fingerprint_rom()
        assert rom1 == rom2

    def test_absorber_top(self):
        """top * x = top for all x."""
        rom = cayley.build_fingerprint_rom()
        for x_fp in range(NUM_FP):
            assert rom[FP_TOP * NUM_FP + x_fp] == FP_TOP

    def test_absorber_bot(self):
        """bot * x = bot for all x."""
        rom = cayley.build_fingerprint_rom()
        for x_fp in range(NUM_FP):
            assert rom[FP_BOT * NUM_FP + x_fp] == FP_BOT

    def test_quote_top_is_p(self):
        """QUOTE * top = p."""
        rom = cayley.build_fingerprint_rom()
        assert rom[FP_QUOTE * NUM_FP + FP_TOP] == FP_P

    def test_nibble_addition(self):
        """N0 + N0 = N0 (nibble self-dot)."""
        rom = cayley.build_fingerprint_rom()
        assert rom[FP_N0 * NUM_FP + FP_N0] == FP_N0

    def test_all_entries_match_algebra(self):
        """Every entry matches atom_dot."""
        from kamea import ALL_NAMES, A, atom_dot
        rom = cayley.build_fingerprint_rom()
        for xn in ALL_NAMES:
            for yn in ALL_NAMES:
                result = atom_dot(A(xn), A(yn))
                x_fp = NAME_TO_FP[xn]
                y_fp = NAME_TO_FP[yn]
                r_fp = NAME_TO_FP[result.name]
                actual = rom[x_fp * NUM_FP + y_fp]
                assert actual == r_fp, (
                    f"{xn}*{yn}: expected fp {r_fp} ({result.name}), "
                    f"got {actual} ({FP_TO_NAME.get(actual, '?')})"
                )

    def test_all_results_valid(self):
        """Every ROM result is a valid fingerprint."""
        rom = cayley.build_fingerprint_rom()
        for i in range(len(rom)):
            assert rom[i] < NUM_FP, f"Invalid fp at offset {i}: {rom[i]}"


# ---------------------------------------------------------------------------
# Fingerprint encoding tests
# ---------------------------------------------------------------------------

class TestFingerprintEncoding:

    def test_nibble_fingerprints_distinct(self):
        """All 16 nibble fingerprints are distinct."""
        nibble_fps = {NAME_TO_FP[f"N{i:X}"] for i in range(16)}
        assert len(nibble_fps) == 16

    def test_all_fingerprints_in_range(self):
        """All fingerprints are in [0, NUM_FP)."""
        for name, fp in NAME_TO_FP.items():
            assert 0 <= fp < NUM_FP, f"{name} has fp {fp} outside [0, {NUM_FP})"

    def test_atom_word_stores_fingerprint(self):
        """make_atom_word stores fingerprint in left field."""
        for name, fp in NAME_TO_FP.items():
            word = make_atom_word(fp)
            tag, left, right, meta = unpack_word(word)
            assert tag == TAG_ATOM
            assert (left & 0x7F) == fp
            assert right == 0

    def test_all_fingerprints_assigned(self):
        """All 66 fingerprints are assigned."""
        assert len(NAME_TO_FP) == cayley.NUM_ATOMS
        assert len(FP_TO_NAME) == cayley.NUM_ATOMS


# ---------------------------------------------------------------------------
# EmulatorHost tests (fingerprint-based)
# ---------------------------------------------------------------------------

class TestEmulatorHostFingerprint:

    def test_absorber(self):
        """(top bot) = top."""
        host = EmulatorHost()
        r = host.eval(("⊤", "⊥"))
        assert r["ok"]
        assert r["result"] == "⊤"

    def test_alu_add(self):
        """ALU 3+5=8."""
        host = EmulatorHost()
        r = host.eval(((("ALU_ARITH", "N9"), "N3"), "N5"))
        assert r["ok"]
        assert r["result"] == "N8"

    def test_io_put(self):
        """IO_PUT produces correct UART byte."""
        host = EmulatorHost()
        r = host.eval((("IO_PUT", "N4"), "N8"))
        assert r["ok"]
        assert host.uart_recv() == b"H"

    def test_quote_eval(self):
        """QUOTE/EVAL roundtrip."""
        host = EmulatorHost()
        r = host.eval(("EVAL", ("QUOTED", "N7")))
        assert r["ok"]
        assert r["result"] == "N7"

    def test_app_unapp(self):
        """APP/UNAPP roundtrip."""
        host = EmulatorHost()
        r = host.eval(("UNAPP", (("APP", "N3"), "N5")))
        assert r["ok"]

    def test_io_seq(self):
        """IO_SEQ chains two outputs."""
        host = EmulatorHost()
        r = host.eval(
            (("IO_SEQ", (("IO_PUT", "N4"), "N8")),
             (("IO_PUT", "N6"), "N9"))
        )
        assert r["ok"]
        assert host.uart_recv() == b"Hi"

    def test_dot_method(self):
        """Host dot() works."""
        host = EmulatorHost()
        assert host.dot("⊤", "⊥") == "⊤"
        assert host.dot("⊥", "⊤") == "⊥"


# ---------------------------------------------------------------------------
# Coordinate-free integration
# ---------------------------------------------------------------------------

class TestCoordinateFreeIntegration:

    def test_io_put(self):
        prog = CoordinateFreeProgram((("IO_PUT", "N4"), "N8"), name="put_H")
        result, host = run_coordinate_free(prog)
        assert result["ok"]
        assert host.uart_recv() == b"H"

    def test_alu_add(self):
        prog = CoordinateFreeProgram(
            ((("ALU_ARITH", "N9"), "N3"), "N5"), name="add_3_5")
        result, host = run_coordinate_free(prog)
        assert result["ok"]
        assert result["result"] == "N8"

"""
Tests for coordinate-free programs.

Verifies that programs produce correct results using the fingerprint-addressed
Cayley ROM.
"""

import pytest
from . import cayley
from .fingerprint import NAME_TO_FP
from .coordinate_free import (
    StructuralResolver,
    CoordinateFreeProgram,
    InvariantLoader,
    run_coordinate_free,
)


# ---------------------------------------------------------------------------
# Resolver tests
# ---------------------------------------------------------------------------

class TestStructuralResolver:

    def test_returns_fingerprint_mapping(self):
        """Resolver returns fingerprint mapping."""
        rom = cayley.build_fingerprint_rom()
        resolver = StructuralResolver(rom)
        atom_map = resolver.resolve()
        assert len(atom_map) == cayley.NUM_ATOMS
        for name, fp in NAME_TO_FP.items():
            assert atom_map[name] == fp, f"{name}: expected {fp}, got {atom_map[name]}"

    def test_caching(self):
        """Resolver returns consistent dicts."""
        rom = cayley.build_fingerprint_rom()
        resolver = StructuralResolver(rom)
        m1 = resolver.resolve()
        m2 = resolver.resolve()
        assert m1 == m2

    def test_resolve_name(self):
        """resolve_name() works for individual atoms."""
        rom = cayley.build_fingerprint_rom()
        resolver = StructuralResolver(rom)
        assert resolver.resolve_name("⊤") == NAME_TO_FP["⊤"]
        assert resolver.resolve_name("IO_PUT") == NAME_TO_FP["IO_PUT"]

    def test_resolve_name_unknown(self):
        """resolve_name() raises on unknown atom."""
        rom = cayley.build_fingerprint_rom()
        resolver = StructuralResolver(rom)
        with pytest.raises(ValueError, match="Unknown atom"):
            resolver.resolve_name("NONEXISTENT")


# ---------------------------------------------------------------------------
# CoordinateFreeProgram tests
# ---------------------------------------------------------------------------

class TestCoordinateFreeProgram:

    def test_valid_atom(self):
        """Single atom name is valid."""
        p = CoordinateFreeProgram("N0")
        assert p.term == "N0"

    def test_valid_application(self):
        """Application of two atoms is valid."""
        p = CoordinateFreeProgram(("IO_PUT", "N4"))
        assert p.atom_names() == {"IO_PUT", "N4"}

    def test_valid_nested(self):
        """Nested applications are valid."""
        p = CoordinateFreeProgram(((("ALU_ARITH", "N9"), "N3"), "N5"))
        assert p.atom_names() == {"ALU_ARITH", "N9", "N3", "N5"}

    def test_valid_quoted(self):
        """Quoted terms are valid."""
        p = CoordinateFreeProgram(("EVAL", ("QUOTED", "N7")))
        assert p.atom_names() == {"EVAL", "N7"}

    def test_rejects_int(self):
        """Raw integer index is rejected."""
        with pytest.raises(ValueError, match="raw integer"):
            CoordinateFreeProgram(42)

    def test_rejects_nested_int(self):
        """Nested raw integer is rejected."""
        with pytest.raises(ValueError, match="raw integer"):
            CoordinateFreeProgram(("IO_PUT", 4))

    def test_rejects_bad_tuple(self):
        """Non-pair tuple is rejected."""
        with pytest.raises(ValueError, match="Invalid term"):
            CoordinateFreeProgram(("a", "b", "c"))


# ---------------------------------------------------------------------------
# InvariantLoader + integration tests
# ---------------------------------------------------------------------------

class TestInvariantLoader:

    def test_io_put(self):
        """IO_PUT produces correct UART byte."""
        prog = CoordinateFreeProgram((("IO_PUT", "N4"), "N8"), name="put_H")
        result, host = run_coordinate_free(prog)
        assert result["ok"]
        assert host.uart_recv() == b"H"

    def test_alu_add(self):
        """ALU addition 3+5=8."""
        prog = CoordinateFreeProgram(
            ((("ALU_ARITH", "N9"), "N3"), "N5"),
            name="add_3_5",
        )
        result, host = run_coordinate_free(prog)
        assert result["ok"]
        assert result["result"] == "N8"

    def test_quote_eval(self):
        """QUOTE/EVAL roundtrip."""
        prog = CoordinateFreeProgram(
            ("EVAL", ("QUOTED", "N7")),
            name="quote_eval",
        )
        result, _ = run_coordinate_free(prog)
        assert result["ok"]
        assert result["result"] == "N7"

    def test_absorber(self):
        """Left absorber: (top bot) = top."""
        prog = CoordinateFreeProgram(("⊤", "⊥"), name="absorber")
        result, _ = run_coordinate_free(prog)
        assert result["ok"]
        assert result["result"] == "⊤"

    def test_io_seq(self):
        """IO_SEQ chains two outputs."""
        prog = CoordinateFreeProgram(
            (("IO_SEQ", (("IO_PUT", "N4"), "N8")),
             (("IO_PUT", "N6"), "N9")),
            name="hi",
        )
        result, host = run_coordinate_free(prog)
        assert result["ok"]
        assert host.uart_recv() == b"Hi"

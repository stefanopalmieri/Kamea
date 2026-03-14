"""
Coordinate-free programs for the Kamea.

Programs use canonical atom names instead of indices, making them invariant
under permutation of the Cayley table. With the fingerprint-based machine,
resolution is trivial: names map to compile-time fingerprint constants.

Pipeline:
    CoordinateFreeProgram (names)
        → InvariantLoader resolves names → fingerprints (compile-time constants)
        → EmulatorHost.load_term() + eval()
"""

from __future__ import annotations

from . import cayley
from .fingerprint import NAME_TO_FP, FP_TO_NAME
from .host import EmulatorHost
from .machine import unpack_word, TAG_ATOM


class StructuralResolver:
    """
    Resolves canonical atom names to fingerprints.

    With the fingerprint-based machine, this is a simple compile-time
    lookup (no ROM scanning needed). Kept for API compatibility.
    """

    def __init__(self, cayley_rom: bytes):
        self._rom = cayley_rom
        self._rom_reads: int = 0

    def resolve(self) -> dict[str, int]:
        """Return {canonical_name: fingerprint}."""
        return dict(NAME_TO_FP)

    def resolve_name(self, name: str) -> int:
        """Resolve a single atom name to its fingerprint."""
        if name not in NAME_TO_FP:
            raise ValueError(f"Unknown atom: {name!r}")
        return NAME_TO_FP[name]

    @property
    def rom_reads(self) -> int:
        return self._rom_reads


class CoordinateFreeProgram:
    """
    A program whose atom references are canonical names,
    not indices tied to a specific Cayley table permutation.

    Term format (same as load_term but no raw ints):
      - str: canonical atom name (e.g. "IO_PUT", "N4", "QUOTE")
      - (f, x): application
      - ("QUOTED", inner): quoted term
    """

    def __init__(self, term, name: str = "unnamed"):
        self.term = term
        self.name = name
        self._validate(term)

    @staticmethod
    def _validate(term):
        """Ensure no raw integer indices appear."""
        if isinstance(term, int):
            raise ValueError(
                f"Coordinate-free programs cannot use raw integer indices: {term}. "
                f"Use canonical atom names instead."
            )
        if isinstance(term, str):
            return
        if isinstance(term, tuple) and len(term) == 2:
            if term[0] == "QUOTED":
                CoordinateFreeProgram._validate(term[1])
            else:
                CoordinateFreeProgram._validate(term[0])
                CoordinateFreeProgram._validate(term[1])
            return
        raise ValueError(f"Invalid term: {term!r}")

    def atom_names(self) -> set[str]:
        """Return all canonical atom names referenced by this program."""
        names: set[str] = set()
        self._collect_names(self.term, names)
        return names

    @staticmethod
    def _collect_names(term, names: set[str]):
        if isinstance(term, str):
            if term != "QUOTED":
                names.add(term)
        elif isinstance(term, tuple):
            for sub in term:
                CoordinateFreeProgram._collect_names(sub, names)


class InvariantLoader:
    """
    Loads a coordinate-free program onto a Kamea machine
    with an arbitrary Cayley ROM permutation.

    With fingerprints, programs are natively permutation-invariant.
    The loader simply feeds the term (with string names) to EmulatorHost,
    which converts names → fingerprints at load time.
    """

    def __init__(self, cayley_rom: bytes):
        self.rom = cayley_rom
        self.resolver = StructuralResolver(cayley_rom)

    def load_and_eval(self, program: CoordinateFreeProgram) -> tuple[dict, EmulatorHost]:
        """
        Load and evaluate a coordinate-free program.

        Returns (eval_result_dict, host) so caller can inspect UART etc.
        Result uses canonical atom names automatically (fingerprint-based decoding).
        """
        host = EmulatorHost(self.rom)
        # Terms use string names → EmulatorHost.load_term converts to fingerprints
        result = host.eval(program.term)
        return result, host


def run_coordinate_free(program: CoordinateFreeProgram,
                        cayley_rom: bytes | None = None) -> tuple[dict, EmulatorHost]:
    """
    Convenience function: run a coordinate-free program.

    If no ROM provided, uses the canonical Cayley table.
    Returns (eval_result, host).
    """
    rom = cayley_rom or cayley.build_fingerprint_rom()
    loader = InvariantLoader(rom)
    return loader.load_and_eval(program)

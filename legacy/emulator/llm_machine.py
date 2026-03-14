"""
LLM Kamea Machine — uses a local LLM as the dot operation.

Identical to the ROM-based KameaMachine except S_DOT and _cayley_or_default
call the LLM backend instead of reading the EEPROM.
"""

from __future__ import annotations

from .machine import (
    KameaMachine, S_DOT, S_RETURN,
    unpack_word, make_atom_word, TAG_ATOM,
)
from .fingerprint import FP_P, NUM_FP


class LLMKameaMachine(KameaMachine):
    """KameaMachine variant that uses an LLM for Cayley lookups."""

    def __init__(self, llm_backend,
                 cayley_rom: bytes | None = None,
                 atom_map: dict[str, int] | None = None):
        super().__init__(cayley_rom, atom_map)
        self.llm_backend = llm_backend
        self.llm_dot_calls = 0

    def _llm_dot(self, f_fp: int, x_fp: int) -> int:
        """Compute dot via LLM backend."""
        self.llm_dot_calls += 1
        return self.llm_backend.dot(f_fp, x_fp)

    def tick(self) -> bool:
        """Override tick to intercept S_DOT state."""
        from .machine import S_HALTED, MAX_CYCLES

        s = self.state.value
        if s == S_DOT:
            self.cycles += 1
            if self.cycles > MAX_CYCLES:
                self.state.load(S_HALTED)
                return False
            # LLM Cayley lookup instead of ROM read
            _, f_fp, x_fp, _ = unpack_word(self.result.value)
            f_fp &= 0x7F
            x_fp &= 0x7F
            result_fp = self._llm_dot(f_fp, x_fp)
            self.result.load(make_atom_word(result_fp))
            self.state.load(S_RETURN)
            return True

        return super().tick()

    def _cayley_or_default(self, f_fp: int, x_word: int,
                            x_tag: int, x_left: int):
        """Atom x Atom -> LLM dot, Atom x structured -> p."""
        if x_tag == TAG_ATOM:
            x_fp = x_left & 0x7F
            result_fp = self._llm_dot(f_fp, x_fp)
            self.result.load(make_atom_word(result_fp))
        else:
            self.result.load(make_atom_word(FP_P))
        self.state.load(S_RETURN)

    def reset_counters(self):
        super().reset_counters()
        self.llm_dot_calls = 0

    def stats(self) -> dict:
        s = super().stats()
        s["llm_dot_calls"] = self.llm_dot_calls
        return s

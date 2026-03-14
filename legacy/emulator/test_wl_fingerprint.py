"""
Tests for canonical WL-1 fingerprinting.

Verifies determinism, full discrimination, and permutation invariance
of the WL-derived canonical ordinals.
"""

from __future__ import annotations

import random
import pytest

from kamea import ALL_NAMES, A, atom_dot
from .wl_fingerprint import canonical_wl


def _build_raw_table() -> list[list[int]]:
    """Build the 66×66 Cayley table as list-of-lists (physical index space)."""
    n = len(ALL_NAMES)
    idx = {name: i for i, name in enumerate(ALL_NAMES)}
    table = [[0] * n for _ in range(n)]
    for xi, xn in enumerate(ALL_NAMES):
        for yi, yn in enumerate(ALL_NAMES):
            result = atom_dot(A(xn), A(yn))
            table[xi][yi] = idx[result.name]
    return table


def _scramble_table(table: list[list[int]], seed: int) -> tuple[list[list[int]], list[int]]:
    """Apply a random permutation to a Cayley table.

    Returns (scrambled_table, perm) where perm[scrambled_idx] = original_idx.
    """
    n = len(table)
    rng = random.Random(seed)
    perm = list(range(n))
    rng.shuffle(perm)
    # inv_perm: original → scrambled
    inv = [0] * n
    for i, p in enumerate(perm):
        inv[p] = i

    scrambled = [[0] * n for _ in range(n)]
    for x in range(n):
        for y in range(n):
            scrambled[inv[x]][inv[y]] = inv[table[x][y]]
    return scrambled, perm


class TestCanonicalWL:

    def test_deterministic(self):
        """Same table gives same ordinals on repeated calls."""
        table = _build_raw_table()
        ord1 = canonical_wl(table)
        ord2 = canonical_wl(table)
        assert ord1 == ord2

    def test_full_discrimination(self):
        """All 66 elements get unique colors for the Kamea."""
        table = _build_raw_table()
        ordinals = canonical_wl(table)
        assert len(set(ordinals)) == 66

    @pytest.mark.parametrize("seed", list(range(20)))
    def test_permutation_invariance(self, seed):
        """Scrambled table produces same ordinals (modulo permutation)."""
        table = _build_raw_table()
        ordinals_orig = canonical_wl(table)

        scrambled, perm = _scramble_table(table, seed)
        ordinals_scram = canonical_wl(scrambled)

        # For each scrambled index s, perm[s] is the original index.
        # The ordinal assigned to s in the scrambled table should equal
        # the ordinal assigned to perm[s] in the original table.
        n = len(table)
        inv = [0] * n
        for i, p in enumerate(perm):
            inv[p] = i

        for orig_idx in range(n):
            scram_idx = inv[orig_idx]
            assert ordinals_orig[orig_idx] == ordinals_scram[scram_idx], (
                f"seed={seed}, orig_idx={orig_idx}: "
                f"orig_ord={ordinals_orig[orig_idx]}, "
                f"scram_ord={ordinals_scram[scram_idx]}"
            )

    def test_rom_invariance(self):
        """Fingerprint ROM built from original and scrambled tables is identical."""
        table = _build_raw_table()
        n = len(table)
        ordinals_orig = canonical_wl(table)

        # Build ROM from original
        rom_orig = bytearray(n * n)
        for x in range(n):
            for y in range(n):
                rom_orig[ordinals_orig[x] * n + ordinals_orig[y]] = ordinals_orig[table[x][y]]

        # Scramble and rebuild
        for seed in range(5):
            scrambled, perm = _scramble_table(table, seed)
            ordinals_scram = canonical_wl(scrambled)

            rom_scram = bytearray(n * n)
            for x in range(n):
                for y in range(n):
                    rom_scram[ordinals_scram[x] * n + ordinals_scram[y]] = ordinals_scram[scrambled[x][y]]

            assert bytes(rom_orig) == bytes(rom_scram), f"ROM mismatch at seed={seed}"

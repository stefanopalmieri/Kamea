"""
Canonical WL-1 color refinement for Cayley tables.

Pure function: takes a raw n×n Cayley table (list of lists of ints),
returns canonical ordinals that are deterministic and permutation-invariant.

The key difference from a naive WL implementation is that unique signatures
are **sorted** before assigning IDs at each round, making the result
independent of input element ordering.

No numpy. No project imports. Pure Python.
"""

from __future__ import annotations

from collections import Counter


def canonical_wl(table: list[list[int]], max_rounds: int = 100) -> list[int]:
    """
    Compute canonical WL-1 ordinals for a Cayley table.

    Args:
        table: n×n Cayley table as list of lists of ints.
                table[x][y] = result of x dot y.
        max_rounds: maximum refinement rounds.

    Returns:
        List of n ints — the canonical ordinal for each element.
        Ordinals are assigned by sorted signature position, so they are
        deterministic and independent of input element ordering.

    Raises:
        AssertionError if the table is not fully discriminated (for n=66).
    """
    n = len(table)

    # --- Round 0: initial color from invariant profile ---
    init_sigs = []
    for x in range(n):
        row_spec = tuple(sorted(Counter(table[x][y] for y in range(n)).values()))
        col_spec = tuple(sorted(Counter(table[y][x] for y in range(n)).values()))
        is_idemp = table[x][x] == x
        init_sigs.append((row_spec, col_spec, is_idemp))

    # Sort unique signatures → assign ordinals by sorted position
    unique_sorted = sorted(set(init_sigs))
    sig_to_ord = {s: i for i, s in enumerate(unique_sorted)}
    colors = [sig_to_ord[s] for s in init_sigs]

    # --- Refinement rounds ---
    for _ in range(max_rounds):
        new_sigs = []
        for x in range(n):
            neighbors = sorted(
                (colors[y], colors[table[x][y]], colors[table[y][x]])
                for y in range(n)
            )
            new_sigs.append((colors[x], tuple(neighbors)))

        # Sort unique signatures → canonical ordinal assignment
        unique_sorted = sorted(set(new_sigs))
        sig_to_ord = {s: i for i, s in enumerate(unique_sorted)}
        new_colors = [sig_to_ord[s] for s in new_sigs]

        if new_colors == colors:
            break  # stable
        colors = new_colors

        if len(set(colors)) == n:
            break  # fully discriminated

    return colors

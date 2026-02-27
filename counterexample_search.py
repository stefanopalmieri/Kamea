#!/usr/bin/env python3
"""
Counterexample search: Can structureless rigid magmas be efficiently recovered?

Uses Weisfeiler-Leman (WL-1) color refinement on Cayley tables to detect
polynomial-time canonicalizability WITHOUT self-model sub-algebras.

If structureless rigid magmas are WL-discriminable, that's a concrete
counterexample to the claim that self-modeling is necessary for efficient
scramble-resilience.

Usage:
  uv run python counterexample_search.py census --max-n 5 --samples 1000
  uv run python counterexample_search.py kamea
  uv run python counterexample_search.py sat --n 8
"""

import argparse
import itertools
import os
import sys
import time
from collections import defaultdict

import numpy as np


# ── WL-1 Color Refinement ─────────────────────────────────────


def wl_refine(table: np.ndarray, n: int, max_rounds: int = 100):
    """
    WL-1 color refinement for Cayley tables.

    Initial color: isomorphism-invariant profile based on the frequency
    spectrum of each row/column and the idempotent flag.  The frequency
    spectrum (sorted tuple of value-counts) is unchanged when both the
    domain and codomain are relabeled by the same permutation.

    Refine: color(x) <- hash(color(x), sorted multiset of
        (color(y), color(T[x,y]), color(T[y,x])) for all y).
    Repeat until stable.

    Returns (num_distinct_colors, num_rounds, color_array).
    Full discrimination iff num_distinct_colors == n.
    """
    from collections import Counter

    # Initial coloring: frequency spectrum of row and column + idempotent flag.
    # These are genuine isomorphism invariants.
    init_sigs = {}
    colors = np.zeros(n, dtype=np.int64)
    for x in range(n):
        row_spec = tuple(sorted(Counter(int(v) for v in table[x, :]).values()))
        col_spec = tuple(sorted(Counter(int(v) for v in table[:, x]).values()))
        is_idemp = int(table[x, x]) == x
        sig = (row_spec, col_spec, is_idemp)
        if sig not in init_sigs:
            init_sigs[sig] = len(init_sigs)
        colors[x] = init_sigs[sig]

    for round_num in range(max_rounds):
        # Build signature for each element
        sig_to_id = {}
        new_colors = np.zeros(n, dtype=np.int64)

        for x in range(n):
            neighbors = []
            for y in range(n):
                neighbors.append(
                    (int(colors[y]),
                     int(colors[table[x, y]]),
                     int(colors[table[y, x]]))
                )
            neighbors.sort()
            sig = (int(colors[x]), tuple(neighbors))

            if sig not in sig_to_id:
                sig_to_id[sig] = len(sig_to_id)
            new_colors[x] = sig_to_id[sig]

        num_old = len(set(colors))
        num_new = len(set(new_colors))

        colors = new_colors

        # Stable: no new colors were created
        if num_new == num_old:
            return num_new, round_num + 1, colors

        # Fully discriminated
        if num_new == n:
            return n, round_num + 1, colors

    return len(set(colors)), max_rounds, colors


# ── Magma Generation ──────────────────────────────────────────


def random_magma(n: int, rng: np.random.Generator) -> np.ndarray:
    return rng.integers(0, n, size=(n, n))


def all_magmas(n: int):
    cells = n * n
    for combo in itertools.product(range(n), repeat=cells):
        yield np.array(combo, dtype=np.int64).reshape(n, n)


# ── Automorphism Check ────────────────────────────────────────


def has_nontrivial_automorphism(table: np.ndarray, n: int) -> bool:
    """Check if any non-identity permutation is an automorphism. Early-exit."""
    for perm in itertools.permutations(range(n)):
        if all(perm[i] == i for i in range(n)):
            continue  # skip identity
        sigma = np.array(perm, dtype=np.int64)
        lhs = sigma[table]
        rhs = table[np.ix_(sigma, sigma)]
        if np.array_equal(lhs, rhs):
            return True
    return False


# ── Structure Analysis ────────────────────────────────────────


def analyze_structure(table: np.ndarray, n: int) -> dict:
    props = {}
    elems = np.arange(n)

    props["left_absorber"] = any(
        np.all(table[e, :] == e) for e in range(n)
    )
    props["right_absorber"] = any(
        np.all(table[:, e] == e) for e in range(n)
    )
    props["left_identity"] = any(
        np.array_equal(table[e, :], elems) for e in range(n)
    )
    props["right_identity"] = any(
        np.array_equal(table[:, e], elems) for e in range(n)
    )
    props["idempotent"] = any(table[e, e] == e for e in range(n))

    props["all_rows_distinct"] = len(set(map(tuple, table))) == n
    props["all_cols_distinct"] = len(set(map(tuple, table.T))) == n

    props["nontrivial_sub"] = False
    for size in range(2, n):
        for subset in itertools.combinations(range(n), size):
            s = set(subset)
            closed = True
            for a in subset:
                for b in subset:
                    if table[a, b] not in s:
                        closed = False
                        break
                if not closed:
                    break
            if closed:
                props["nontrivial_sub"] = True
                break
        if props["nontrivial_sub"]:
            break

    props["structureless"] = (
        props["all_rows_distinct"]
        and not props["left_absorber"]
        and not props["right_absorber"]
        and not props["left_identity"]
        and not props["right_identity"]
        and not props["nontrivial_sub"]
    )

    return props


# ── Census Mode ───────────────────────────────────────────────


def run_wl_census(n: int, samples: int, exhaustive: bool):
    stats = defaultdict(int)
    stats["total"] = 0
    counterexamples = []

    # Track WL rounds for averages
    wl_rounds_structured = []
    wl_rounds_structureless = []
    wl_colors_structured_fail = []
    wl_colors_structureless_fail = []

    if exhaustive:
        source = all_magmas(n)
        target = n ** (n * n)
        label = f"n={n}, exhaustive ({target:,} magmas)"
    else:
        rng = np.random.default_rng(seed=42 + n)
        target = samples
        label = f"n={n}, {samples:,} samples"

    t0 = time.time()
    count = 0

    while count < target:
        if exhaustive:
            try:
                table = next(source)
            except StopIteration:
                break
        else:
            table = random_magma(n, rng)

        count += 1
        stats["total"] += 1

        # WL-first: run color refinement
        num_colors, rounds, _ = wl_refine(table, n)
        wl_discriminated = num_colors == n

        if wl_discriminated:
            # WL full discrimination guarantees rigidity
            is_rigid = True
        else:
            # Must brute-force check automorphism
            is_rigid = not has_nontrivial_automorphism(table, n)

        if not is_rigid:
            stats["not_rigid"] += 1
            continue

        stats["rigid"] += 1
        props = analyze_structure(table, n)
        is_structureless = props["structureless"]

        if is_structureless:
            stats["structureless"] += 1
        else:
            stats["structured"] += 1

        if wl_discriminated:
            stats["wl_disc"] += 1
            if is_structureless:
                stats["structureless_wl_disc"] += 1
                wl_rounds_structureless.append(rounds)
                # Save counterexample
                if len(counterexamples) < 5:
                    counterexamples.append(table.copy())
            else:
                stats["structured_wl_disc"] += 1
                wl_rounds_structured.append(rounds)
        else:
            stats["wl_fail"] += 1
            if is_structureless:
                stats["structureless_wl_fail"] += 1
                wl_colors_structureless_fail.append(num_colors)
            else:
                stats["structured_wl_fail"] += 1
                wl_colors_structured_fail.append(num_colors)

        # Progress
        if count % 10000 == 0:
            elapsed = time.time() - t0
            rate = count / elapsed
            eta = (target - count) / rate
            print(
                f"  [{count:,}/{target:,}] "
                f"{elapsed:.1f}s elapsed, ~{eta:.0f}s remaining",
                flush=True,
            )

    elapsed = time.time() - t0

    # Compute averages
    avg_rounds = {
        "structured": (
            sum(wl_rounds_structured) / len(wl_rounds_structured)
            if wl_rounds_structured
            else 0
        ),
        "structureless": (
            sum(wl_rounds_structureless) / len(wl_rounds_structureless)
            if wl_rounds_structureless
            else 0
        ),
    }
    avg_colors_fail = {
        "structured": (
            sum(wl_colors_structured_fail) / len(wl_colors_structured_fail)
            if wl_colors_structured_fail
            else 0
        ),
        "structureless": (
            sum(wl_colors_structureless_fail)
            / len(wl_colors_structureless_fail)
            if wl_colors_structureless_fail
            else 0
        ),
    }

    return label, stats, elapsed, avg_rounds, avg_colors_fail, counterexamples


def print_wl_census(label, stats, elapsed, avg_rounds, avg_colors_fail, counterexamples, n):
    total = stats["total"]
    rigid = stats["rigid"]
    print(f"\n{label}  ({elapsed:.1f}s)")
    print(f"  Total:     {total:,}")
    print(f"  Rigid:     {rigid:,} ({100*rigid/total:.1f}%)")

    if rigid == 0:
        print("  (no rigid magmas found)")
        return

    structured = stats["structured"]
    structureless = stats["structureless"]

    print(f"  Of rigid:")

    # Structured
    s_disc = stats["structured_wl_disc"]
    s_fail = stats["structured_wl_fail"]
    print(f"    Structured:            {structured:>8,} ({100*structured/rigid:5.1f}%)")
    if structured > 0:
        r_str = f"  avg rounds: {avg_rounds['structured']:.1f}" if s_disc > 0 else ""
        print(f"      WL-1 discriminated:  {s_disc:>8,} ({100*s_disc/structured:5.1f}%){r_str}")
        c_str = f"  avg colors: {avg_colors_fail['structured']:.1f}/{n}" if s_fail > 0 else ""
        print(f"      WL-1 failed:         {s_fail:>8,} ({100*s_fail/structured:5.1f}%){c_str}")

    # Structureless
    sl_disc = stats["structureless_wl_disc"]
    sl_fail = stats["structureless_wl_fail"]
    print(f"    Structureless:         {structureless:>8,} ({100*structureless/rigid:5.1f}%)")
    if structureless > 0:
        r_str = f"  avg rounds: {avg_rounds['structureless']:.1f}" if sl_disc > 0 else ""
        marker = "  <-- COUNTEREXAMPLES" if sl_disc > 0 else ""
        print(f"      WL-1 discriminated:  {sl_disc:>8,} ({100*sl_disc/structureless:5.1f}%){r_str}{marker}")
        c_str = f"  avg colors: {avg_colors_fail['structureless']:.1f}/{n}" if sl_fail > 0 else ""
        print(f"      WL-1 failed:         {sl_fail:>8,} ({100*sl_fail/structureless:5.1f}%){c_str}")

    if counterexamples:
        print(f"\n  COUNTEREXAMPLE CANDIDATES: {sl_disc:,} structureless + WL-discriminated")
        # Save first few
        ce_dir = os.path.join(os.path.dirname(__file__) or ".", "counterexamples")
        os.makedirs(ce_dir, exist_ok=True)
        for idx, ce in enumerate(counterexamples):
            path = os.path.join(ce_dir, f"ce_n{n}_{idx}.npy")
            np.save(path, ce)
        print(f"  First {len(counterexamples)} saved to counterexamples/ce_n{n}_*.npy")
        print(f"\n  Example counterexample (first):")
        print_cayley(counterexamples[0], n)


def print_cayley(table, n):
    """Print a small Cayley table."""
    header = "    · | " + " ".join(f"{j}" for j in range(n))
    print(f"    {'-' * len(header)}")
    print(f"  {header}")
    print(f"    {'-' * len(header)}")
    for i in range(n):
        row = " ".join(f"{table[i, j]}" for j in range(n))
        print(f"    {i} | {row}")


# ── Kamea Baseline ────────────────────────────────────────────


def run_kamea_baseline():
    """Run WL-1 on the Kamea's 66x66 Cayley table."""
    print("=" * 60)
    print("  Kamea Baseline (n=66)")
    print("=" * 60)

    # Import kamea
    sys.path.insert(0, os.path.dirname(__file__) or ".")
    try:
        from kamea import ALL_NAMES, ALL_ATOMS, atom_dot
    except ImportError:
        print("  ERROR: Could not import kamea.py")
        return

    n = len(ALL_ATOMS)
    print(f"  Building {n}x{n} Cayley table...", flush=True)

    # Build Cayley table: map atom names to indices
    name_to_idx = {name: i for i, name in enumerate(ALL_NAMES)}
    table = np.zeros((n, n), dtype=np.int64)
    for i, x in enumerate(ALL_ATOMS):
        for j, y in enumerate(ALL_ATOMS):
            result = atom_dot(x, y)
            table[i, j] = name_to_idx.get(result.name, -1)

    print(f"  Running WL-1 refinement...", flush=True)
    t0 = time.time()
    num_colors, rounds, colors = wl_refine(table, n)
    elapsed = time.time() - t0

    print(f"  WL-1 colors: {num_colors}/{n} {'(full discrimination)' if num_colors == n else '(PARTIAL)'}")
    print(f"  WL-1 rounds: {rounds}")
    print(f"  Time: {elapsed:.2f}s")

    if num_colors == n:
        print(f"  Conclusion: Kamea is WL-1 discriminable in {rounds} rounds")
    else:
        # Show which atoms share colors
        from collections import Counter
        color_counts = Counter(int(c) for c in colors)
        collisions = {c: cnt for c, cnt in color_counts.items() if cnt > 1}
        print(f"  WARNING: {len(collisions)} color classes have >1 element")
        for c, cnt in sorted(collisions.items(), key=lambda x: -x[1])[:10]:
            members = [ALL_NAMES[i] for i in range(n) if colors[i] == c]
            print(f"    Color {c}: {cnt} atoms — {', '.join(members[:8])}{'...' if cnt > 8 else ''}")


# ── SAT Mode ──────────────────────────────────────────────────


def run_sat_search(n: int, max_solutions: int = 100):
    """Search for structureless rigid WL-discriminable magmas via SAT."""
    print("=" * 60)
    print(f"  SAT Counterexample Search (n={n})")
    print("=" * 60)

    try:
        from pysat.solvers import Glucose4
        from pysat.card import CardEnc, EncType
    except ImportError:
        print("  ERROR: python-sat not installed.")
        print("  Install with: uv add python-sat")
        print("  Or: pip install python-sat")
        return

    print(f"  Encoding constraints for n={n}...", flush=True)
    t0 = time.time()

    # Variables: for each cell (i,j) and value v, a Boolean variable
    # var(i, j, v) = i*n*n + j*n + v + 1  (1-indexed for SAT)
    def var(i, j, v):
        return i * n * n + j * n + v + 1

    num_vars = n * n * n
    clauses = []

    # Exactly-one constraints for each cell
    for i in range(n):
        for j in range(n):
            cell_vars = [var(i, j, v) for v in range(n)]
            # At least one
            clauses.append(cell_vars)
            # At most one (pairwise)
            for a in range(n):
                for b in range(a + 1, n):
                    clauses.append([-var(i, j, a), -var(i, j, b)])

    # No left absorber: for each e, ∃x such that T[e][x] ≠ e
    for e in range(n):
        # At least one x where T[e][x] != e → at least one x where var(e,x,e) is false
        # Equivalently: NOT (all var(e,x,e) for all x)
        # → at least one -var(e,x,e)
        clauses.append([-var(e, x, e) for x in range(n)])

    # No right absorber: for each e, ∃x such that T[x][e] ≠ e
    for e in range(n):
        clauses.append([-var(x, e, e) for x in range(n)])

    # No left identity: for each e, ∃x such that T[e][x] ≠ x
    for e in range(n):
        clauses.append([-var(e, x, x) for x in range(n)])

    # No right identity: for each e, ∃x such that T[x][e] ≠ x
    for e in range(n):
        clauses.append([-var(x, e, x) for x in range(n)])

    # No non-trivial sub-magma: for each subset S of size 2..n-1,
    # ∃ a,b ∈ S such that T[a][b] ∉ S
    for size in range(2, n):
        for subset in itertools.combinations(range(n), size):
            s = set(subset)
            complement = [v for v in range(n) if v not in s]
            if not complement:
                continue
            # For this subset to NOT be a sub-magma:
            # at least one (a,b) in S×S maps outside S
            # i.e., OR over (a,b) in S×S, v not in S: var(a,b,v)
            clause = []
            for a in subset:
                for b in subset:
                    for v in complement:
                        clause.append(var(a, b, v))
            clauses.append(clause)

    encode_time = time.time() - t0
    print(f"  Clauses: {len(clauses):,}  Variables: {num_vars}")
    print(f"  Encoding time: {encode_time:.1f}s")

    # Solve
    print(f"  Searching (max {max_solutions} solutions)...", flush=True)
    t0 = time.time()
    found = 0
    checked = 0
    counterexamples = []

    solver = Glucose4()
    for clause in clauses:
        solver.add_clause(clause)

    while found < max_solutions:
        if not solver.solve():
            break
        checked += 1

        model = solver.get_model()

        # Decode table
        table = np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            for j in range(n):
                for v in range(n):
                    if model[var(i, j, v) - 1] > 0:
                        table[i, j] = v
                        break

        # Check WL discrimination (also implies rigidity)
        num_colors, rounds, _ = wl_refine(table, n)

        if num_colors == n:
            # WL-discriminated → rigid + efficiently recoverable
            found += 1
            counterexamples.append((table.copy(), rounds))
            if found <= 3:
                print(f"    Found #{found}: WL rounds={rounds}")
                print_cayley(table, n)
                print()

        # Block this solution
        block = [-lit for lit in model]
        solver.add_clause(block)

        if checked % 1000 == 0:
            elapsed = time.time() - t0
            print(
                f"    Checked {checked:,} solutions, found {found} counterexamples "
                f"({elapsed:.1f}s)",
                flush=True,
            )

    solver.delete()
    elapsed = time.time() - t0

    print(f"\n  SAT search complete ({elapsed:.1f}s)")
    print(f"  Solutions checked: {checked:,}")
    print(f"  Counterexamples (structureless + WL-discriminated): {found}")

    if counterexamples:
        ce_dir = os.path.join(os.path.dirname(__file__) or ".", "counterexamples")
        os.makedirs(ce_dir, exist_ok=True)
        for idx, (ce, r) in enumerate(counterexamples[:10]):
            path = os.path.join(ce_dir, f"ce_sat_n{n}_{idx}.npy")
            np.save(path, ce)
        print(f"  Saved to counterexamples/ce_sat_n{n}_*.npy")


# ── Main ──────────────────────────────────────────────────────


def main():
    parser = argparse.ArgumentParser(
        description="Counterexample search: structureless rigid magmas + WL discrimination"
    )
    subparsers = parser.add_subparsers(dest="mode", help="Run mode")

    # Census
    census_p = subparsers.add_parser(
        "census", help="WL discrimination census on random magmas"
    )
    census_p.add_argument(
        "--max-n", type=int, default=6, help="Largest n to test (default: 6)"
    )
    census_p.add_argument(
        "--samples", type=int, default=100_000, help="Samples per n (default: 100000)"
    )

    # Kamea
    subparsers.add_parser("kamea", help="WL baseline on Kamea (n=66)")

    # SAT
    sat_p = subparsers.add_parser(
        "sat", help="SAT-based counterexample search"
    )
    sat_p.add_argument("--n", type=int, default=8, help="Order n (default: 8)")
    sat_p.add_argument(
        "--max-solutions", type=int, default=100, help="Max solutions to check"
    )

    args = parser.parse_args()

    if args.mode == "census":
        print("=" * 60)
        print("  Counterexample Search: WL Discrimination Census")
        print("=" * 60)

        for n in range(3, args.max_n + 1):
            exhaustive = n <= 3
            label, stats, elapsed, avg_rounds, avg_colors_fail, counterexamples = (
                run_wl_census(n, args.samples, exhaustive=exhaustive)
            )
            print_wl_census(
                label, stats, elapsed, avg_rounds, avg_colors_fail, counterexamples, n
            )

        print("\n" + "=" * 60)
        print("  Done.")
        print("=" * 60)

    elif args.mode == "kamea":
        run_kamea_baseline()

    elif args.mode == "sat":
        run_sat_search(args.n, args.max_solutions)

    else:
        parser.print_help()


if __name__ == "__main__":
    main()

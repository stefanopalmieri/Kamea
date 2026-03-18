#!/usr/bin/env python3
"""
Reflection Distinctness Test

Tests whether the reflective tower (meta-circular evaluator + reification +
branch swap) forces any of the 10 expressiveness-only distinctness pairs.

Methodology (Option B): Take the Ψ₁₆ᶠ Cayley table, merge two roles by
replacing all occurrences of element B with element A throughout the table,
then run the reflective tower on the merged table.

This is a semantic merge: the table still has 16 elements but two are now
behaviorally identical (same row, same column behavior).

Usage:
  uv run python -m ds_search.reflection_distinctness_test
"""

import sys
import os
import copy
import time
import signal
import subprocess
import textwrap
from pathlib import Path

# ═══════════════════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════════════════

ROOT = Path(__file__).parent.parent

# Ψ₁₆ᶠ Cayley table (from psi_star.py)
TABLE = [
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    [5,1,13,7,11,5,6,8,2,5,11,9,4,14,3,15],
    [0,1,0,0,0,0,1,1,1,0,1,1,0,0,1,1],
    [0,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11],
    [0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,0],
    [15,0,5,9,3,15,14,14,2,12,8,14,12,4,12,8],
    [0,1,8,4,13,2,11,2,14,3,15,12,14,15,6,5],
    [12,1,13,7,11,5,12,11,4,12,5,14,15,7,11,12],
    [1,6,14,14,14,14,9,8,3,15,5,7,13,11,12,4],
    [13,1,4,3,12,11,2,11,5,3,8,14,9,7,11,11],
    [14,1,9,10,11,13,12,7,5,6,8,2,14,12,10,4],
    [0,1,1,0,1,1,0,1,1,1,0,0,0,0,0,1],
    [3,0,14,4,14,6,11,12,7,3,15,10,14,2,6,8],
    [14,0,5,4,3,2,12,5,11,14,3,14,12,2,6,3],
    [1,3,13,15,3,7,14,8,15,4,11,6,7,14,12,10],
]

# Element constants (from psi_star.py)
ELEMENTS = {
    "⊤": 0, "⊥": 1, "f": 2, "τ": 3, "g": 4,
    "Q": 6, "E": 7, "ρ": 8, "η": 9, "Y": 10,
}

# The 10 expressiveness-only pairs
PAIRS = [
    ("⊤", "⊥"), ("Q", "ρ"), ("Q", "Y"), ("E", "ρ"), ("E", "Y"),
    ("E", "f"), ("f", "ρ"), ("f", "Y"), ("ρ", "Y"), ("η", "Y"),
]

TIMEOUT_SECONDS = 60


# ═══════════════════════════════════════════════════════════════════════
# Table merge
# ═══════════════════════════════════════════════════════════════════════

def merge_table(table, idx_a, idx_b):
    """
    Merge element B into element A in the Cayley table.

    1. In every cell, replace idx_b with idx_a.
    2. Row idx_b becomes a copy of row idx_a.

    Returns a new table (deep copy).
    """
    n = len(table)
    merged = [row[:] for row in table]

    # Replace all occurrences of B with A in every cell
    for i in range(n):
        for j in range(n):
            if merged[i][j] == idx_b:
                merged[i][j] = idx_a

    # Row B becomes a copy of row A
    merged[idx_b] = merged[idx_a][:]

    return merged


# ═══════════════════════════════════════════════════════════════════════
# Tower runner (subprocess with monkeypatched table)
# ═══════════════════════════════════════════════════════════════════════

def run_tower_with_table(merged_table):
    """
    Run the reflective tower with a custom Cayley table.

    Spawns a subprocess that monkeypatches psi_star.TABLE before
    importing psi_lisp, then runs the two tower files.

    Returns (stdout, stderr, returncode, timed_out).
    """
    # Build inline script that patches TABLE before running
    table_repr = repr(merged_table)
    script = textwrap.dedent(f"""\
        import sys
        sys.setrecursionlimit(50000)
        sys.path.insert(0, {str(ROOT)!r})

        # Patch psi_star.TABLE before psi_lisp imports it
        import psi_star
        psi_star.TABLE = {table_repr}

        import psi_lisp
        from psi_lisp import run_file, builtin_env, display

        # psi_lisp imported TABLE from psi_star at import time.
        # Since we patched psi_star.TABLE before importing psi_lisp,
        # psi_lisp.TABLE should already be the merged table.
        # But patch it explicitly to be safe:
        psi_lisp.TABLE = psi_star.TABLE

        _VOID = psi_lisp._VOID

        env = builtin_env()
        for path in ["examples/psi_metacircular.lisp",
                      "examples/psi_reflective_tower.lisp"]:
            try:
                results = run_file(path, env)
                for r in results:
                    if r is not _VOID:
                        try:
                            print(display(r))
                        except Exception:
                            pass
            except Exception as e:
                print(f"TOWER_ERROR: {{e}}")
                break
    """)

    try:
        result = subprocess.run(
            [sys.executable, "-c", script],
            capture_output=True, text=True,
            timeout=TIMEOUT_SECONDS,
            cwd=str(ROOT),
        )
        return result.stdout, result.stderr, result.returncode, False
    except subprocess.TimeoutExpired:
        return "", "", -1, True


def check_tower_output(stdout):
    """
    Check tower output against 5 checkpoints.
    Returns dict of checkpoint -> (passed, detail).
    """
    checks = {}

    # 1. Basic computation
    fib_ok = "fib(8)... 21" in stdout
    fact_ok = "fact(10)... 3628800" in stdout
    checks["comp"] = (fib_ok and fact_ok,
                      f"fib={fib_ok}, fact={fact_ok}")

    # 2. Table invariants
    inv_ok = "ALL INVARIANTS HOLD" in stdout
    checks["invariants"] = (inv_ok, "")

    # 3. Reification
    reify_ok = "Chain depth: 3" in stdout
    checks["reify"] = (reify_ok, "")

    # 4. Frame tags
    bind_ok = "Frame 0 tag = k-let-bind? YES" in stdout
    body_ok = "Frame 1 tag = k-let-body? YES" in stdout
    kid_ok = "Frame 2 tag = k-id? YES" in stdout
    checks["tags"] = (bind_ok and body_ok and kid_ok,
                      f"bind={bind_ok}, body={body_ok}, id={kid_ok}")

    # 5. Branch swap
    swap_ok = "With branch swap: (if 1 42 99)" in stdout and "99" in stdout
    confirmed_ok = "CONFIRMED: Program rewrote its own if-branches" in stdout
    checks["swap"] = (swap_ok and confirmed_ok, "")

    return checks


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("=" * 70)
    print("REFLECTION DISTINCTNESS TEST")
    print("Does the reflective tower force any of the 10 expressiveness-only pairs?")
    print("=" * 70)

    # Verify baseline first
    print("\nBaseline (unmerged table)...")
    t0 = time.time()
    stdout, stderr, rc, timed_out = run_tower_with_table(TABLE)
    elapsed = time.time() - t0

    if timed_out:
        print(f"  BASELINE TIMED OUT after {TIMEOUT_SECONDS}s — cannot proceed")
        sys.exit(1)

    baseline_checks = check_tower_output(stdout)
    all_pass = all(v[0] for v in baseline_checks.values())

    if not all_pass:
        print(f"  BASELINE FAILED — cannot proceed")
        for name, (passed, detail) in baseline_checks.items():
            mark = "OK" if passed else "FAIL"
            extra = f" ({detail})" if detail else ""
            print(f"    {name}: {mark}{extra}")
        if stderr:
            print(f"  stderr: {stderr[:500]}")
        sys.exit(1)

    print(f"  All 5 checkpoints pass ({elapsed:.1f}s)")

    # Test each pair
    print(f"\n{'─'*70}")
    results = {}

    for role_a, role_b in PAIRS:
        idx_a = ELEMENTS[role_a]
        idx_b = ELEMENTS[role_b]
        label = f"{role_a}={role_b}"

        print(f"\n  {label} (merge {idx_b}→{idx_a})...")
        merged = merge_table(TABLE, idx_a, idx_b)

        t0 = time.time()
        stdout, stderr, rc, timed_out = run_tower_with_table(merged)
        elapsed = time.time() - t0

        if timed_out:
            print(f"    TIMEOUT ({TIMEOUT_SECONDS}s) — likely infinite loop")
            results[label] = {
                "comp": (False, "timeout"),
                "invariants": (False, "timeout"),
                "reify": (False, "timeout"),
                "tags": (False, "timeout"),
                "swap": (False, "timeout"),
                "timed_out": True,
                "error": None,
            }
            # Save merged table
            save_merged_table(merged, role_a, role_b)
            continue

        # Check for crash
        error = None
        if "TOWER_ERROR:" in stdout:
            error = stdout.split("TOWER_ERROR:")[1].strip().split("\n")[0]

        checks = check_tower_output(stdout)
        checks["timed_out"] = False
        checks["error"] = error
        results[label] = checks

        any_fail = not all(v[0] for k, v in checks.items()
                          if k not in ("timed_out", "error"))

        if any_fail:
            save_merged_table(merged, role_a, role_b)

        status_parts = []
        for name in ["comp", "invariants", "reify", "tags", "swap"]:
            passed, detail = checks[name]
            status_parts.append("OK" if passed else "FAIL")
        status_str = " | ".join(status_parts)

        if error:
            print(f"    Error: {error[:100]}")
        print(f"    [{status_str}] ({elapsed:.1f}s)")

    # ── Report ────────────────────────────────────────────────────────
    print(f"\n{'='*70}")
    print("RESULTS")
    print(f"{'='*70}")

    header = f"| {'Pair':>6s} | {'Comp':>4s} | {'Inv':>3s} | {'Reify':>5s} | {'Tags':>4s} | {'Swap':>4s} | {'Status':>20s} |"
    sep = f"|{'-'*8}|{'-'*6}|{'-'*5}|{'-'*7}|{'-'*6}|{'-'*6}|{'-'*22}|"
    print(header)
    print(sep)

    killed = 0
    for role_a, role_b in PAIRS:
        label = f"{role_a}={role_b}"
        r = results[label]

        if r.get("timed_out"):
            cols = ["TOUT"] * 5
            status = "KILLED (timeout)"
            killed += 1
        else:
            cols = []
            any_fail = False
            for name in ["comp", "invariants", "reify", "tags", "swap"]:
                passed, _ = r[name]
                cols.append("OK" if passed else "FAIL")
                if not passed:
                    any_fail = True
            if any_fail:
                status = "KILLED (tower fails)"
                killed += 1
            else:
                status = "survives"

        print(f"| {label:>6s} | {cols[0]:>4s} | {cols[1]:>3s} | {cols[2]:>5s} | {cols[3]:>4s} | {cols[4]:>4s} | {status:>20s} |")

    print(f"\n{killed}/10 pairs killed by the reflective tower")

    if killed > 0:
        print(f"\nNew accounting: 32 categorical + 3 TC + {killed} reflection "
              f"+ {10-killed} expressiveness = 45")
    else:
        print("\nAll 10 survive even the tower. They are the nontriviality axiom of Kamea.")


def save_merged_table(merged, role_a, role_b):
    """Save a merged table as evidence."""
    out_dir = ROOT / "ds_search" / "merged_tables"
    out_dir.mkdir(exist_ok=True)
    fname = f"merged_{role_a}_{role_b}.txt"
    with open(out_dir / fname, "w") as f:
        f.write(f"# Merged table: {role_a} = {role_b}\n")
        f.write(f"# Element {ELEMENTS[role_b]} replaced by {ELEMENTS[role_a]}\n")
        for row in merged:
            f.write(str(row) + "\n")


if __name__ == "__main__":
    main()

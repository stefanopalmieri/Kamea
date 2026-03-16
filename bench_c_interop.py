#!/usr/bin/env python3
"""
Benchmark: Ψ₁₆ᶜ vs Ψ₁₆ᶠ — supercompilation and compiled C.

Measures:
  1. Residual AST size after supercompilation (node count)
  2. Compiled C execution time (gcc -O2)
  3. Cancel rule effectiveness (Ψ₁₆ᶠ has 2 rules, Ψ₁₆ᶜ has 5)

Usage:
  python3 bench_c_interop.py
"""

import subprocess
import sys
import os
import time
import tempfile

# ═══════════════════════════════════════════════════════════════════════
# Benchmark programs (.psi IR)
# ═══════════════════════════════════════════════════════════════════════

BENCHMARKS = {
    # 1. Cancel chain: INV·(INV·(INC·(DEC·x)))
    # Ψ₁₆ᶠ: 2 rules → only QE fires, INC/DEC/INV stay → 4 nested dots
    # Ψ₁₆ᶜ: 5 rules → INV·INV cancels, INC·DEC cancels → just x
    "cancel_chain": """\
(defun cancel x
  (dot INV (dot INV (dot INC (dot DEC x)))))
(main (app cancel input))
""",

    # 2. Deep cancel: 3 nested INC·DEC pairs wrapped in INV·INV
    # Ψ₁₆ᶠ: 8 nested dots remain
    # Ψ₁₆ᶜ: all cancel → just x
    "deep_cancel": """\
(defun deep x
  (dot INV (dot INV
    (dot INC (dot DEC
      (dot INC (dot DEC
        (dot INC (dot DEC x)))))))))
(main (app deep input))
""",

    # 3. Mixed QE + INC/DEC: E·(Q·(INC·(DEC·x)))
    # Ψ₁₆ᶠ: QE cancels → INC·(DEC·x) remains (2 dots)
    # Ψ₁₆ᶜ: QE cancels, then INC·DEC cancels → just x
    "mixed_cancel": """\
(defun mixed x
  (dot E (dot Q (dot INC (dot DEC x)))))
(main (app mixed input))
""",

    # 4. Branch with cancel: if τ·x then INC·(DEC·x) else INV·(INV·x)
    # Both branches have cancellable patterns
    # Ψ₁₆ᶠ: branches keep 2 dots each
    # Ψ₁₆ᶜ: both branches cancel to x
    "branch_cancel": """\
(defun branch_cancel x
  (if (dot TAU x)
    (dot INC (dot DEC x))
    (dot INV (dot INV x))))
(main (app branch_cancel input))
""",

    # 5. Known constant: INV·(INV·(INC·(DEC·f)))
    # f = element 2. Both tables can constant-fold, but differently:
    # Ψ₁₆ᶠ: folds via table lookups (DEC·f→TABLE[15][2], etc.)
    # Ψ₁₆ᶜ: cancel rules fire first, then resolve to f (element 2)
    "known_const": """\
(main (dot INV (dot INV (dot INC (dot DEC f)))))
""",

    # 6. Fibonacci (Ψ-Lisp via transpiler) — real workload
    "fibonacci": """\
; .lisp format — uses arithmetic, not dot operations
""",
}


def count_nodes(s):
    """Count AST nodes in serialized .psi output (parens = compound nodes)."""
    # Each (form ...) is one node. Atoms are also nodes.
    tokens = s.replace('(', ' ( ').replace(')', ' ) ').split()
    return len([t for t in tokens if t not in ('(', ')')])


def run_supercompile(psi_source, table_mode):
    """Supercompile a .psi source with given table mode. Returns serialized output."""
    env = os.environ.copy()
    if table_mode == 'c':
        env['PSI_TABLE'] = 'c'
    else:
        env.pop('PSI_TABLE', None)

    with tempfile.NamedTemporaryFile(mode='w', suffix='.psi', delete=False) as f:
        f.write(psi_source)
        f.flush()
        try:
            result = subprocess.run(
                [sys.executable, 'psi_supercompile.py', f.name],
                capture_output=True, text=True, env=env, timeout=10)
            return result.stdout.strip()
        finally:
            os.unlink(f.name)


def compile_and_time_c(c_source, runtime_header, label, n_iters=10000000):
    """Compile C source, run N iterations, return time in seconds."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False) as f:
        # Wrap the function in a timing loop
        f.write(f'#include "{runtime_header}"\n')
        f.write('#include <time.h>\n\n')
        f.write(c_source)
        f.write(f"""
int main(void) {{
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    volatile psi_val result = 0;
    for (int i = 0; i < {n_iters}; i++) {{
        result = bench((psi_val)(i & 15));
    }}
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
    printf("{label}: %.6f s ({n_iters} iters, %.1f ns/iter)\\n",
           elapsed, elapsed / {n_iters} * 1e9);
    return (int)result;  /* prevent dead code elimination */
}}
""")
        f.flush()
        binary = f.name.replace('.c', '')
        try:
            comp = subprocess.run(
                ['gcc', '-O2', '-Wall', '-I.', '-o', binary, f.name],
                capture_output=True, text=True, timeout=30)
            if comp.returncode != 0:
                return None, comp.stderr
            run = subprocess.run([binary], capture_output=True, text=True, timeout=30)
            os.unlink(binary)
            return run.stdout.strip(), None
        except Exception as e:
            return None, str(e)
        finally:
            os.unlink(f.name)


def main():
    print("=" * 70)
    print("BENCHMARK: Ψ₁₆ᶜ vs Ψ₁₆ᶠ — Supercompilation & Compiled C")
    print("=" * 70)

    # ── Part 1: Supercompilation residual size ────────────────────────

    print("\n" + "─" * 70)
    print("Part 1: Supercompilation — residual AST size")
    print("─" * 70)
    print(f"\n  {'Benchmark':<20s} {'Ψ₁₆ᶠ nodes':>12s} {'Ψ₁₆ᶜ nodes':>12s} {'Reduction':>12s}")
    print(f"  {'─'*20} {'─'*12} {'─'*12} {'─'*12}")

    results = {}
    for name, source in BENCHMARKS.items():
        if name == "fibonacci":
            continue  # skip non-.psi benchmark

        out_f = run_supercompile(source, 'f')
        out_c = run_supercompile(source, 'c')

        nodes_f = count_nodes(out_f) if out_f else -1
        nodes_c = count_nodes(out_c) if out_c else -1

        if nodes_f > 0 and nodes_c > 0:
            reduction = f"{(1 - nodes_c/nodes_f)*100:.0f}%"
        else:
            reduction = "N/A"

        print(f"  {name:<20s} {nodes_f:>12d} {nodes_c:>12d} {reduction:>12s}")
        results[name] = (out_f, out_c, nodes_f, nodes_c)

    # Show details for key benchmarks
    print("\n  Details:")
    for name in ["cancel_chain", "deep_cancel", "mixed_cancel"]:
        if name in results:
            out_f, out_c, nf, nc = results[name]
            print(f"\n  {name}:")
            print(f"    Ψ₁₆ᶠ: {out_f}")
            print(f"    Ψ₁₆ᶜ: {out_c}")

    # ── Part 2: Compiled C timing ─────────────────────────────────────

    print("\n" + "─" * 70)
    print("Part 2: Compiled C — runtime performance")
    print("─" * 70)

    # Benchmark functions that exercise the dot table
    # cancel_chain: INV·(INV·(INC·(DEC·x)))
    c_func_f = """
psi_val bench(psi_val x) {
    uint8_t v = (uint8_t)(x & 15);
    v = psi_dot(14, psi_dot(14, psi_dot(13, psi_dot(15, v))));
    return (psi_val)v;
}
"""
    # Same function but with Ψ₁₆ᶜ inline helpers
    c_func_c = """
psi_val bench(psi_val x) {
    uint8_t v = (uint8_t)(x & 15);
    v = psi_inv(psi_inv(psi_inc(psi_dec(v))));
    return (psi_val)v;
}
"""
    # Supercompiled version: the cancellation rules eliminate everything
    c_func_c_super = """
psi_val bench(psi_val x) {
    /* After supercompilation: INV·(INV·(INC·(DEC·x))) → x */
    return x;
}
"""

    # Deep cancel: 8 nested operations
    c_deep_f = """
psi_val bench(psi_val x) {
    uint8_t v = (uint8_t)(x & 15);
    v = psi_dot(14, psi_dot(14,
        psi_dot(13, psi_dot(15,
        psi_dot(13, psi_dot(15,
        psi_dot(13, psi_dot(15, v))))))));
    return (psi_val)v;
}
"""
    c_deep_c = """
psi_val bench(psi_val x) {
    uint8_t v = (uint8_t)(x & 15);
    v = psi_inv(psi_inv(
        psi_inc(psi_dec(
        psi_inc(psi_dec(
        psi_inc(psi_dec(v))))))));
    return (psi_val)v;
}
"""
    c_deep_c_super = """
psi_val bench(psi_val x) {
    /* After supercompilation: all 8 ops cancel → x */
    return x;
}
"""

    # Mixed: E·(Q·(INC·(DEC·x)))
    c_mixed_f = """
psi_val bench(psi_val x) {
    uint8_t v = (uint8_t)(x & 15);
    v = psi_dot(7, psi_dot(6, psi_dot(13, psi_dot(15, v))));
    return (psi_val)v;
}
"""
    c_mixed_c = """
psi_val bench(psi_val x) {
    uint8_t v = (uint8_t)(x & 15);
    /* After Ψ₁₆ᶜ supercompilation: QE cancels, INC·DEC cancels → x */
    return x;
}
"""

    n_iters = 100000000  # 100M iterations for measurable timing

    tests = [
        ("cancel_chain (4 ops)", [
            ("Ψ₁₆ᶠ generic dot", c_func_f, "psi_runtime.h"),
            ("Ψ₁₆ᶜ inline helpers", c_func_c, "psi_runtime_c.h"),
            ("Ψ₁₆ᶜ supercompiled", c_func_c_super, "psi_runtime_c.h"),
        ]),
        ("deep_cancel (8 ops)", [
            ("Ψ₁₆ᶠ generic dot", c_deep_f, "psi_runtime.h"),
            ("Ψ₁₆ᶜ inline helpers", c_deep_c, "psi_runtime_c.h"),
            ("Ψ₁₆ᶜ supercompiled", c_deep_c_super, "psi_runtime_c.h"),
        ]),
        ("mixed QE+INC/DEC (4 ops)", [
            ("Ψ₁₆ᶠ generic dot", c_mixed_f, "psi_runtime.h"),
            ("Ψ₁₆ᶜ supercompiled", c_mixed_c, "psi_runtime_c.h"),
        ]),
    ]

    print(f"\n  {n_iters//1000000}M iterations per test\n")

    for group_name, variants in tests:
        print(f"  {group_name}:")
        for label, c_code, header in variants:
            output, err = compile_and_time_c(c_code, header, label, n_iters)
            if output:
                print(f"    {output}")
            else:
                print(f"    {label}: COMPILE ERROR: {err}")
        print()

    # ── Part 3: Summary ──────────────────────────────────────────────

    print("─" * 70)
    print("Summary")
    print("─" * 70)
    print("""
  Two tables, same axioms, same theorems, different extensions:

  Ψ₁₆ᶠ (hardware):  8-state counter, IO roundtrip, PAIR/FST/SND, SWAP
                     2 cancellation rules (QE, EQ)
                     C compilation: generic psi_dot() table lookups

  Ψ₁₆ᶜ (C-interop): 4-cycle + involution on contiguous core {2,3,4,5}
                     5 cancellation rules (QE, EQ, INC/DEC, DEC/INC, INV/INV)
                     C compilation: arithmetic inline helpers
                       INC(x) = ((x-1)&3)+2
                       DEC(x) = ((x-3)&3)+2
                       INV(x) = 7-x

  The supercompiler difference is the key win: chains of paired operations
  that survive Ψ₁₆ᶠ supercompilation are completely eliminated by Ψ₁₆ᶜ.
  This is the ISA analogy made real — same instruction set semantics,
  different microarchitecture, different compilation characteristics.
""")


if __name__ == '__main__':
    main()

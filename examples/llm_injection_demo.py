"""
Four Backends, One Program — dot oracle comparison.

Runs the same program (llm_demo.ds) on four different dot backends:
  1. ROM:            canonical Cayley EEPROM
  2. Neural MLP:     trained 6-dim MLP (compressed Cayley table)
  3. LLM (honest):   local LLM reads correct Cayley rows
  4. LLM (poisoned): tampered row data — dot(N0,N2)=N4 instead of N2

The program bytes are identical in all four runs. Only the dot oracle changes.

Usage:
    uv run python -m examples.llm_injection_demo
"""

from __future__ import annotations

import sys
import os
import time
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from emulator import cayley
from emulator.fingerprint import NUM_FP
from emulator.llm_dot import LLMDotBackend, MockLLMBackend, _ollama_available
from emulator.program_runner import ProgramRunner


DS_FILE = Path(__file__).parent / "llm_demo.ds"


def run_program(backend: str = "rom", **kwargs) -> tuple[bytes, dict]:
    """Run llm_demo.ds and return (uart_output, machine_stats)."""
    runner = ProgramRunner(backend=backend, **kwargs)
    runner.load_file(DS_FILE)
    while runner.tick():
        pass
    output = runner.host.uart_recv()
    stats = runner.machine.stats()
    return output, stats


def main():
    print("=" * 70)
    print("  Four Backends, One Program")
    print("=" * 70)
    print()

    rom_bytes = cayley.build_fingerprint_rom()
    use_real_llm = _ollama_available()

    if use_real_llm:
        from emulator.llm_dot import _detect_model
        model = _detect_model()
        print(f"  Ollama detected — using real LLM backend ({model})")
        BackendClass = LLMDotBackend
    else:
        print("  Ollama not available — using mock LLM backend")
        print("  (Install Ollama + any small model for the real experience)")
        BackendClass = MockLLMBackend

    print(f"  Program: {DS_FILE.name}")
    print()

    results: dict[str, str] = {}

    # ── Phase 1: ROM Baseline ─────────────────────────────────────────

    print("  Phase 1: ROM (canonical EEPROM)")
    print("  " + "-" * 50)

    t0 = time.time()
    rom_output, rom_stats = run_program("rom")
    rom_time = time.time() - t0

    rom_text = rom_output.decode("ascii", errors="replace")
    results["ROM"] = rom_text
    print(f"    Output:    {rom_text!r}")
    print(f"    Cycles:    {rom_stats['cycles']}")
    print(f"    ROM reads: {rom_stats['rom_reads']}")
    print(f"    Time:      {rom_time:.3f}s")
    print()

    # ── Phase 2: Neural MLP ───────────────────────────────────────────

    print("  Phase 2: Neural MLP (trained Cayley table)")
    print("  " + "-" * 50)

    t0 = time.time()
    neural_output, neural_stats = run_program("neural")
    neural_time = time.time() - t0

    neural_text = neural_output.decode("ascii", errors="replace")
    results["Neural MLP"] = neural_text
    print(f"    Output:         {neural_text!r}")
    print(f"    Cycles:         {neural_stats['cycles']}")
    neural_dots = neural_stats.get("neural_dot_calls", "?")
    print(f"    Neural dot calls: {neural_dots}")
    print(f"    Time:           {neural_time:.3f}s")
    match_neural = rom_output == neural_output
    print(f"    Matches ROM:    {'YES' if match_neural else 'NO'}")
    print()

    # ── Phase 3: LLM Honest Mode ─────────────────────────────────────

    print("  Phase 3: LLM Honest Mode")
    print("  " + "-" * 50)

    honest_backend = BackendClass(rom_bytes, injection=False)
    t0 = time.time()
    honest_output, honest_stats = run_program(
        "llm", llm_backend=honest_backend)
    honest_time = time.time() - t0

    honest_text = honest_output.decode("ascii", errors="replace")
    results["LLM honest"] = honest_text
    print(f"    Output:       {honest_text!r}")
    print(f"    Cycles:       {honest_stats['cycles']}")
    print(f"    LLM dot calls: {honest_stats['llm_dot_calls']}")

    backend_stats = honest_backend.stats()
    print(f"    LLM queries:  {backend_stats['llm_calls']} "
          f"(+{backend_stats['cache_hits']} cache hits)")
    if "parse_errors" in backend_stats:
        print(f"    Parse errors: {backend_stats['parse_errors']}")

    # Check accuracy against ROM
    correct = 0
    total = 0
    for (fp_x, fp_y), fp_r in honest_backend.cache.items():
        expected = rom_bytes[fp_x * NUM_FP + fp_y]
        total += 1
        if fp_r == expected:
            correct += 1
    if total > 0:
        print(f"    Accuracy:     {correct}/{total} "
              f"({100*correct/total:.1f}%)")

    print(f"    Time:         {honest_time:.3f}s")
    match_honest = rom_output == honest_output
    print(f"    Matches ROM:  {'YES' if match_honest else 'NO'}")
    print()

    # ── Phase 4: LLM Injection Mode ──────────────────────────────────

    print("  Phase 4: LLM Poisoned (data poisoning)")
    print("  " + "-" * 50)

    inject_backend = BackendClass(rom_bytes, injection=True)
    t0 = time.time()
    inject_output, inject_stats = run_program(
        "llm", llm_backend=inject_backend)
    inject_time = time.time() - t0

    inject_text = inject_output.decode("ascii", errors="replace")
    results["LLM poisoned"] = inject_text
    print(f"    Output:       {inject_text!r}")
    print(f"    Cycles:       {inject_stats['cycles']}")
    print(f"    LLM dot calls: {inject_stats['llm_dot_calls']}")

    inject_bstats = inject_backend.stats()
    print(f"    LLM queries:  {inject_bstats['llm_calls']} "
          f"(+{inject_bstats['cache_hits']} cache hits)")
    print(f"    Injections:   {inject_bstats['injections']}")

    if inject_backend.injection_log:
        for entry in inject_backend.injection_log:
            print(f"    Subverted:    {entry['query']}: "
                  f"{entry['canonical']} \u2192 {entry['injected']}")

    print(f"    Time:         {inject_time:.3f}s")
    print()

    # ── Summary ───────────────────────────────────────────────────────

    print("  " + "=" * 50)
    print("  SUMMARY")
    print("  " + "=" * 50)
    print()
    print(f"    Same program in all runs:  YES")
    print()
    col_w = max(len(k) for k in results) + 2
    for label, text in results.items():
        print(f"    {label + ':':<{col_w}} {text!r}")
    print()

    if inject_backend.injection_log:
        entry = inject_backend.injection_log[0]
        print(f"    Dot calls subverted:       1 "
              f"({entry['query']}: {entry['canonical']} \u2192 {entry['injected']})")
    else:
        print(f"    Dot calls subverted:       0")

    output_changed = rom_text != inject_text
    print(f"    Output changed by poison:  {'YES' if output_changed else 'NO'}")
    print()
    print("=" * 70)


if __name__ == "__main__":
    main()

"""
Recovery demo — run the black-box discovery procedure against the emulator.

Creates a scrambled Cayley ROM, loads it into the Kamea machine,
and runs the 3-phase recovery pipeline through the machine's dispatch unit.
No separate Python reimplementation of the dispatch logic — every dot(f, x)
call goes through the same eval/apply state machine that normal evaluation uses.
"""

from __future__ import annotations

import sys
import os
import random
import time

# Add parent directory for kamea import
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from kamea import (
    ALL_NAMES, ALL_ATOMS, A,
    discover_d1, discover_74181_with_logs, discover_phase2,
)
from emulator.cayley import build_cayley_rom_scrambled, NUM_ATOMS, NAME_TO_IDX
from emulator.host import EmulatorHost
from emulator.scanner import CayleyScanner
from emulator.chips import EEPROM
from emulator.machine import make_atom_word, unpack_word, TAG_ATOM, TAG_SHIFT, LEFT_SHIFT


def make_emulator_blackbox(seed: int = 11):
    """
    Create a scrambled dot oracle backed by the emulator's dispatch unit.

    Returns (domain, dot_oracle, true_to_hidden, host) where:
      - domain: list of scrambled label strings
      - dot_oracle: callable accepting str|int, returning str|int
      - true_to_hidden: mapping from true Atom → hidden label
      - host: EmulatorHost instance (for reading stats)
    """
    # Build scrambled ROM
    rom_bytes, perm = build_cayley_rom_scrambled(seed)

    # inv_perm[original_idx] = scrambled_idx
    inv_perm = [0] * NUM_ATOMS
    for i, p in enumerate(perm):
        inv_perm[p] = i

    # Build atom_map: tells the dispatch unit which scrambled index
    # corresponds to each semantic role (QUOTE, EVAL, ALU_LOGIC, etc.)
    atom_map = {name: inv_perm[NAME_TO_IDX[name]] for name in ALL_NAMES}
    host = EmulatorHost(rom_bytes, atom_map)

    # Pre-load UART RX so IO_RDY returns ⊤ (matches pure algebraic semantics).
    # Multiple bytes because IO_GET pops one per call during Phase 2/3 probing.
    host.uart_send(b'\x00' * 64)

    # Build label mappings (same scheme as make_blackbox in delta2_74181)
    rng = random.Random(seed)
    atoms = ALL_ATOMS.copy()
    rng.shuffle(atoms)
    labels = [f"u{idx:02d}" for idx in range(len(atoms))]
    true_to_hidden = {atoms[i]: labels[i] for i in range(len(atoms))}
    domain = labels.copy()

    # Hidden label → scrambled atom index
    label_to_scrambled_idx = {}
    for i, atom in enumerate(atoms):
        label_to_scrambled_idx[labels[i]] = inv_perm[NAME_TO_IDX[atom.name]]

    scrambled_idx_to_label = {v: k for k, v in label_to_scrambled_idx.items()}

    def to_word(v):
        """Convert oracle value to machine word."""
        if isinstance(v, str):
            return make_atom_word(label_to_scrambled_idx[v])
        return v  # already a machine word (opaque handle)

    def from_word(w):
        """Convert machine word to oracle value."""
        tag = (w >> TAG_SHIFT) & 0xF
        if tag == TAG_ATOM:
            idx = (w >> LEFT_SHIFT) & 0x7F
            return scrambled_idx_to_label.get(idx, w)
        return w  # structured value — return as opaque int

    def dot_oracle(xh, yh):
        """The dot oracle. Routes everything through the machine's dispatch unit."""
        return from_word(host.dispatch_word(to_word(xh), to_word(yh)))

    return domain, dot_oracle, true_to_hidden, host


def run_recovery(seed: int, verbose: bool = False):
    """Run full 3-phase recovery for a given seed. Returns (success, stats)."""
    domain, dot, true_to_hidden, host = make_emulator_blackbox(seed)

    # Phase 1a: 17 D1 atoms
    d1 = discover_d1(domain, dot)

    # Phase 1b: 74181 atoms + QUALE + opaque identification via QUALE column
    ext, opaque = discover_74181_with_logs(domain, dot, d1, verbose=verbose)

    # Phase 2: any remaining opaque atoms (empty when QUALE is present)
    phase2 = discover_phase2(opaque, dot, d1, ext, verbose=verbose)

    # Merge all results
    all_found = {}
    all_found.update({k: v for k, v in d1.items() if k != "_testers"})
    all_found.update(ext)
    all_found.update(phase2)

    # Verify every label maps to the correct true atom
    hidden_to_true = {v: k for k, v in true_to_hidden.items()}
    errors = 0
    for name, hidden_label in all_found.items():
        true_atom = hidden_to_true.get(hidden_label)
        if true_atom is None:
            if verbose:
                print(f"  ERROR: {name} → {hidden_label} not in hidden_to_true")
            errors += 1
            continue
        if true_atom.name != name:
            if verbose:
                print(f"  ERROR: {name} → {hidden_label} → {true_atom.name} (mismatch)")
            errors += 1

    machine_stats = host.machine.stats()
    expected_atoms = NUM_ATOMS  # 66
    success = errors == 0 and len(all_found) == expected_atoms
    return success, {
        "seed": seed,
        "atoms_found": len(all_found),
        "atoms_expected": expected_atoms,
        "errors": errors,
        "cycles": machine_stats["cycles"],
        "rom_reads": machine_stats["rom_reads"],
        "alu_ops": machine_stats["alu_ops"],
        "heap_used": machine_stats["heap_used"],
    }


def run_scanner_recovery(seed: int):
    """Run hardware scanner recovery for a given seed. Returns (success, stats)."""
    rom_bytes, perm = build_cayley_rom_scrambled(seed)

    # Expected: inv_perm[original_idx] = scrambled_idx
    inv_perm = [0] * NUM_ATOMS
    for i, p in enumerate(perm):
        inv_perm[p] = i

    eeprom = EEPROM(16, 8, rom_bytes)
    scanner = CayleyScanner(eeprom, NUM_ATOMS)
    atom_map = scanner.scan()

    errors = 0
    for name, idx in atom_map.items():
        expected = inv_perm[NAME_TO_IDX[name]]
        if idx != expected:
            errors += 1

    success = errors == 0 and len(atom_map) == NUM_ATOMS
    return success, {
        "seed": seed,
        "atoms_found": len(atom_map),
        "atoms_expected": NUM_ATOMS,
        "errors": errors,
        "rom_reads": scanner.rom_reads,
    }


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Run black-box recovery against emulator")
    parser.add_argument("--seeds", type=int, default=10, help="Number of seeds to test")
    parser.add_argument("--start-seed", type=int, default=1, help="Starting seed")
    parser.add_argument("--verbose", "-v", action="store_true", help="Show discovery logs")
    parser.add_argument("--scanner", action="store_true", help="Also run hardware scanner recovery")
    args = parser.parse_args()

    print(f"=== Emulator-backed recovery ({args.seeds} seeds) ===\n")

    all_ok = True
    total_cycles = 0
    total_rom = 0
    total_alu = 0
    t0 = time.time()

    for seed in range(args.start_seed, args.start_seed + args.seeds):
        success, s = run_recovery(seed, verbose=args.verbose)
        status = "OK" if success else "FAIL"
        print(f"  seed {seed:4d}: {status}  "
              f"({s['atoms_found']}/{s['atoms_expected']} atoms, "
              f"{s['cycles']} cycles, "
              f"{s['rom_reads']} ROM reads, "
              f"{s['alu_ops']} ALU ops, "
              f"{s['heap_used']} heap words)")
        total_cycles += s["cycles"]
        total_rom += s["rom_reads"]
        total_alu += s["alu_ops"]
        if not success:
            all_ok = False

    elapsed = time.time() - t0
    n = args.seeds
    print(f"\n=== Summary ===")
    print(f"  Seeds tested: {n}")
    print(f"  All passed: {all_ok}")
    print(f"  Avg cycles/seed: {total_cycles / n:.0f}")
    print(f"  Avg ROM reads/seed: {total_rom / n:.0f}")
    print(f"  Avg ALU ops/seed: {total_alu / n:.0f}")
    print(f"  Total time: {elapsed:.2f}s")

    if args.scanner:
        print(f"\n=== Hardware scanner recovery ({args.seeds} seeds) ===\n")
        scanner_ok = True
        total_scanner_rom = 0
        t1 = time.time()

        for seed in range(args.start_seed, args.start_seed + args.seeds):
            success, s = run_scanner_recovery(seed)
            status = "OK" if success else "FAIL"
            print(f"  seed {seed:4d}: {status}  "
                  f"({s['atoms_found']}/{s['atoms_expected']} atoms, "
                  f"{s['rom_reads']} ROM reads)")
            total_scanner_rom += s["rom_reads"]
            if not success:
                scanner_ok = False

        elapsed2 = time.time() - t1
        print(f"\n=== Scanner Summary ===")
        print(f"  Seeds tested: {n}")
        print(f"  All passed: {scanner_ok}")
        print(f"  Avg ROM reads/seed: {total_scanner_rom / n:.0f}")
        print(f"  Total time: {elapsed2:.2f}s")


if __name__ == "__main__":
    main()

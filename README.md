<p align="center">
  <img src="https://upload.wikimedia.org/wikipedia/commons/thumb/7/7a/Albrecht_D%C3%BCrer_-_Melencolia_I_-_Google_Art_Project_%28_AGDdr3EHmNGyA%29.jpg/1280px-Albrecht_D%C3%BCrer_-_Melencolia_I_-_Google_Art_Project_%28_AGDdr3EHmNGyA%29.jpg" width="250" alt="Albrecht Dürer — Melencolia I (1514)" />
</p>

# Kamea

**Axiom-driven search for self-describing finite algebras, with machine-checked proofs in Lean 4.**

<p align="center"><sub>In loving memory of Boba</sub></p>

---

## The Ψ Framework

What is the simplest finite structure that can identify its own components through its own operation?

The Ψ framework answers this by stacking axioms on a finite magma (N-element set with binary operation `dot`) until the structure contains its own quote/eval pair, branch/compose/Y combinators, IO channels, an 8-state counter, and a 2×2 product space — all in a single 16×16 Cayley table.

The canonical result is **Ψ₁₆ᶠ**: a 16-element algebra with **83 machine-checked Lean theorems** covering every operational constraint simultaneously. All proofs compile with **zero `sorry`** on Lean 4.28.0 / Mathlib v4.28.0.

Claim status is tracked in [`CLAIMS.md`](CLAIMS.md) (`Lean-proved`, `Empirical`, `Conjecture/Open`).

---

## Key Results

### Ψ₁₆ᶠ: Full Operational Saturation (83 Lean Theorems)

A single 16×16 Cayley table satisfying all axioms simultaneously:

- **Structural**: L0–L8, Kleene (C), Inert Propagation (D), Power-Associativity (PA), Inert Self-Application (VV)
- **Reflective**: Quote/Eval inverse pair (QE), E-transparency, 1-inert
- **Computational**: Branch, Compose, Y-combinator, Selection (η·ρ = τ)
- **Arithmetic**: 8-state counter (INC + DEC), 4-state sub-counter (INC2)
- **IO**: PUT/GET roundtrip on core, SEQ sequencer
- **Data**: PAIR/FST/SND (curried 2×2 product), SWAP involution on core

Properties:
- **WL-1 discrete** (rigid): all 16 elements distinguishable after 1 Weisfeiler-Leman refinement
- **Fully producible**: every element appears as some `a·b`
- **{⊤,⊥,Q,E} generates all 16** elements in ≤4 steps (Lean-verified)
- **Only 2 idempotents**: {⊤, ⊥}
- **No associative sub-magma of size ≥ 4**

### Multi-Duty Architecture

Elements serve up to 4 roles each:

| Element | Roles |
|---------|-------|
| 14 | GET / FST / SWAP / s1 (4 roles) |
| 6 (Q) | Q / SND / s2 / p01 (4 roles) |
| 7 (E) | E / INC2 / s7 (3 roles) |
| 15 | DEC / PUT / s5 (3 roles) |
| 11 | PAIR / s3 / p11 (3 roles) |
| 9 (η) | η / p10 (2 roles) |
| 12 | s0 / p00 (2 roles) |
| 8 (ρ) | ρ / s6 (2 roles) |
| 10 (Y) | Y / s4 (2 roles) |
| 13 (INC) | INC only (1 role) |

### Actuality Irreducibility

The tester row is **completely free**: at N=16, all 14 core tester cells can independently flip between ⊤ and ⊥ (SAT-verified with push/pop). The distinction the tester draws is a genuine choice, not determined by the structural axioms.

---

## The Axiom System

### Structural Ladder (L0–L8)

| Level | Name | What It Forces |
|-------|------|----------------|
| L0 | Absorber ⊤ | `∀x: 0·x = 0` |
| L1 | Absorber ⊥ | `∀x: 1·x = 1` |
| L2 | Extensionality | All rows distinct |
| L3 | Tester exists | At least one non-absorber has boolean outputs |
| L4 | Encoder exists | At least one element synthesizes (≥2 distinct non-boolean outputs) |
| L5 | No extra absorbers | Only ⊤ and ⊥ are absorbers |
| L6 | No extra testers | At most 2 testers among non-absorbers |
| L7 | Inert exists | At least one "substrate" element |
| L8 | Encoder separation | ≥2 encoders with distinct output sets |

### Additional Axioms

| Axiom | What It Forces |
|-------|----------------|
| **C (Kleene)** | Only testers can produce boolean outputs on non-absorbers |
| **D (Inert Propagation)** | Inert elements preserve non-absorber status |
| **PA (Power-Associativity)** | `(x·x)·x = x·(x·x)` for all x |
| **VV (Inert Self-Application)** | Inert self-application yields a tester or encoder |
| **QE (Quote/Eval)** | `E·(Q·x) = x` and `Q·(E·x) = x` on core — mutual inverses |
| **1-Inert** | Exactly 1 inert element |
| **E-Transparency** | `E·⊤ = ⊤` and `E·⊥ = ⊥` |
| **Branch** | `ρ·x = f·x` if `τ·x = ⊤`, else `ρ·x = g·x` — tester-mediated conditional |
| **Compose** | `η·x = ρ·(g·x)` — function composition through branch |
| **Y-Combinator** | `Y·ρ = ρ·(Y·ρ)`, with `Y·ρ ≥ 2` — fixed-point combinator |
| **Selection** | `η·ρ = τ` — composing then branching yields a judgment |

### Minimum N by Feature

| Feature | Min N |
|---------|-------|
| L8 (full ladder) | 6 |
| + QE pair | 8 |
| + Branch/Compose/Y | 12 |
| + IO + 8-state counter + Selection | 16 |

---

## Element Assignments (Ψ₁₆ᶠ)

| Index | Symbol | Role | Computational | Counter | IO | Product |
|-------|--------|------|---------------|---------|----|---------|
| 0 | ⊤ | absorber | top/true | — | — | — |
| 1 | ⊥ | absorber | bottom/false | — | — | — |
| 2 | f | encoder | branch-if (f path) | — | — | — |
| 3 | τ | tester | branch tester | — | — | — |
| 4 | g | inert | branch-else (g path) | — | — | — |
| 5 | SEQ | tester | — | — | SEQ | — |
| 6 | Q | encoder | quote | s2 | — | SND/p01 |
| 7 | E | encoder | eval | s7 | — | INC2 |
| 8 | ρ | encoder | branch element | s6 | — | — |
| 9 | η | encoder | compose element | — | — | p10 |
| 10 | Y | encoder | Y-combinator | s4 | — | — |
| 11 | PAIR | encoder | — | s3 | — | PAIR/p11 |
| 12 | s0 | tester | — | s0 (zero) | — | p00 |
| 13 | INC | encoder | increment | — | — | — |
| 14 | — | encoder | — | s1 | GET/FST | SWAP |
| 15 | — | encoder | decrement | s5 | PUT/DEC | — |

### 8-State Counter

```
s0(12) →INC→ s1(14) →INC→ s2(Q=6) →INC→ s3(11) →INC→
s4(Y=10) →INC→ s5(15) →INC→ s6(ρ=8) →INC→ s7(E=7) →INC→ s0(12)
```

DEC reverses this cycle exactly. Zero test: `τ·s0 = ⊤`, `τ·sₖ = ⊥` for k≠0.

### IO Roundtrip

`GET·(PUT·x) = x` on core {2,3,4,5}, with PUT=15, GET=14.

### 2×2 Product

| Pair | State | Element | FST | SND |
|------|-------|---------|-----|-----|
| (s0,s0) | p00 | 12 (=s0) | s0 | s0 |
| (s0,s1) | p01 | 6 (=Q) | s0 | s1 |
| (s1,s0) | p10 | 9 (=η) | s1 | s0 |
| (s1,s1) | p11 | 11 (=PAIR) | s1 | s1 |

### Black-Box Recovery

All 16 elements can be identified from a shuffled, opaque dot oracle — no ground truth, no labels. Three methods (`psi_blackbox.py`), all 100% on 1000 seeds:

| Method | Mean dot calls | Strategy |
|--------|---------------|----------|
| **Behavioral** | 755 | 12-step axiom-driven probing (full row reads) |
| **Generation** | 658 | Steps 1–7, then depth-2 generation from {⊤,⊥,Q,E} |
| **Adaptive** | **62** | Absorber-probe signatures + Kleene/QE targeting + generation |

The adaptive method never reads a full row. The 2-probe signature `(x·⊤, x·⊥)` partitions all non-absorbers into 5 classes, uniquely locating g (orients ⊤), E (Kleene separates it from testers), and Q (QE round-trip on E). Then 12 generation calls produce all remaining elements.

```bash
uv run python psi_blackbox.py --method adaptive              # single demo
uv run python psi_blackbox.py --method adaptive --seeds 1000  # batch
uv run python psi_blackbox.py --seeds 1000 --compare          # cost comparison
```

---

## Emulator: Kamea Machine

A cycle-accurate emulator of the hardware architecture: Cayley ROM, IC74181 ALU, SRAM heap, hardware stack, UART FIFOs, and a microcode-driven eval/apply state machine. The emulator implements the full 66-atom Kamea algebra (the original Δ-based extension with ALU, IO, W32, MUL, and QUALE atoms).

```bash
# Run "Hello, world!" in the TUI debugger
uv run python -m emulator.debugger examples/hello_world.ds

# Run emulator tests (4356 atom pairs + ALU + IO + W32 + MUL)
uv run python -m emulator.test_machine

# Run with neural backend (MLP instead of ROM)
uv run python -m emulator.debugger --neural examples/hello_world.ds

# Run with LLM backend (Ollama)
uv run python -m emulator.debugger --llm examples/llm_demo.ds

# REPL: ALU 7 + 5 = 12
uv run ds_repl.py -e '(((ALU_ARITH :N9) :N7) :N5)'
```

---

## Repository Structure

```
├── DistinctionStructures/
│   ├── Basic.lean                    # Abstract DS definitions and axioms
│   ├── BaseAxiomDerivation.lean      # Base axioms imply only card ≥ 2 (tight)
│   ├── BasePlusA7Derivation.lean     # Adding generic A7′ still doesn't force card ≥ 17
│   ├── OntologicalSchema.lean        # Abstract four-lift schema theorem
│   ├── Psi16.lean                    # Ψ₁₆ with selection axiom (42 theorems)
│   └── Psi16Full.lean               # Ψ₁₆ᶠ full operations (83 theorems)
├── emulator/                         # Cycle-accurate Kamea machine emulator
│   ├── chips.py                      # Hardware primitives (EEPROM, IC74181, SRAM)
│   ├── cayley.py                     # Cayley ROM builder
│   ├── machine.py                    # Eval/apply state machine
│   ├── host.py                       # High-level interface (ROM, neural, LLM)
│   ├── fingerprint.py                # WL-derived structural fingerprints
│   ├── wl_fingerprint.py             # WL-1 color refinement
│   ├── coordinate_free.py            # Coordinate-free program construction
│   ├── neural_dot.py                 # Neural Cayley table (MLP)
│   ├── llm_dot.py                    # LLM dot backend (Ollama)
│   ├── debugger.py                   # Textual TUI debugger
│   └── test_*.py                     # Test suites
├── examples/                         # Emulator demos (.ds programs, Python scripts)
├── ds_search/
│   ├── axiom_explorer.py             # Core encoder: encode_level(), classify_elements()
│   ├── stacking_analysis.py          # All Ψ analysis functions (~17k lines)
│   └── substrate_analysis.py         # Substrate/stacking analysis
├── docs/
│   ├── psi_framework_summary.md      # Comprehensive Ψ framework reference
│   └── minimal_model.md              # Minimal model notes
├── kamea.py                          # Core 66-atom algebra (Python)
├── psi_blackbox.py                   # Ψ₁₆ᶠ black-box recovery (3 methods)
├── ds_repl.py                        # Interactive REPL
├── rigid_census.py                   # Small rigid magma census
├── counterexample_search.py          # WL-1 discrimination tests
├── CLAIMS.md                         # Claim status registry
└── README.md
```

## Building

```bash
# Lean (requires Lean 4.28.0 / Mathlib v4.28.0)
lake build

# Python (requires uv)
uv run python -m emulator.test_machine
```

All Lean theorems are checked by `decide` or `native_decide`, appropriate and complete for finite carrier types with decidable equality. Zero sorry.

---

## What Is Not Proved

- **Cell-by-cell freedom at N=16.** The push/pop analysis has been done at N=12 (117/144 free cells, 18.8% determination) and N=8 (46/64 free, 28.1%). The N=16 analysis remains open.
- **Uniqueness of Ψ₁₆ᶠ.** The Cayley table is ONE model from the solution space. The axioms constrain roles and relationships but leave many cells free (demonstrated at N=12).
- **Minimality from base axioms.** Abstract axiom limitation theorems show base DirectedDS axioms imply only `card ≥ 2` (tight). What forcing conditions derive the full structure from first principles remains open.
- **Symmetric impossibility.** The symmetric synthesis barrier is demonstrated by construction but not proved as a general impossibility theorem.
- **Necessity of self-modeling.** Empirical evidence (`counterexample_search.py`) strongly suggests self-modeling is not required for efficient scramble-resilience — nearly all structureless rigid magmas are WL-1 discriminable. Self-modeling provides interpretability, not computational necessity.

---

## Why It Matters

The Ψ framework shows that a remarkably small structure — 16 elements, one binary operation — can simultaneously contain:

1. **Self-description**: quote/eval inverse pair on core
2. **Branching**: tester-mediated conditional dispatch
3. **Composition**: function composition through branch
4. **Recursion**: Y-combinator with non-trivial fixed point
5. **Arithmetic**: bidirectional 8-state counter with zero-test
6. **IO**: PUT/GET roundtrip on core
7. **Data structures**: curried 2×2 product with projections
8. **Termination**: selection axiom (η·ρ = τ)

The axioms determine the skeleton — roles, absorbers, functional relationships on core — but leave the flesh open. The determination question (how much of the table does self-description actually force?) reveals a fundamental tension: self-description is a *relational* property, constraining how cells relate to each other, not what individual cells contain.

---

## License

MIT

## Citation

If you use this work, please cite:

```bibtex
@software{palmieri2025kamea,
  author = {Palmieri, Stefano},
  title = {Kamea: Axiom-Driven Self-Describing Finite Algebras with Machine-Checked Proofs},
  year = {2025},
  url = {https://github.com/stefanopalmieri/Kamea}
}
```

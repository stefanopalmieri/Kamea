<p align="center">
  <img src="https://upload.wikimedia.org/wikipedia/commons/thumb/7/7a/Albrecht_D%C3%BCrer_-_Melencolia_I_-_Google_Art_Project_%28_AGDdr3EHmNGyA%29.jpg/1280px-Albrecht_D%C3%BCrer_-_Melencolia_I_-_Google_Art_Project_%28_AGDdr3EHmNGyA%29.jpg" width="250" alt="Albrecht Dürer — Melencolia I (1514)" />
</p>

# Kamea

**Axiom-driven search for self-describing finite algebras, with machine-checked proofs in Lean 4.**

<p align="center"><sub>In loving memory of Boba</sub></p>

---

## Why It Matters

Any system that can inspect and modify its own components needs a representation layer: some way to quote a piece of itself, examine it, and act on the result. In practice this is a runtime, a reflection API, a JIT compiler — machinery bolted on top, with no guarantee that the representation is faithful or complete.

The Ψ framework asks whether that machinery can be *intrinsic*. Can a finite algebraic structure — nothing but a set of elements and a binary operation — contain its own quote/eval pair, conditional branching, recursion, arithmetic, and IO, all arising from the same operation that defines the structure? And can you *prove* it does, not by running tests, but by machine-checking the axioms?

The answer is yes, and it fits in a 16×16 table.

This has practical implications for any setting where a component must verify its own integrity without trusting an external authority: embedded controllers that self-test without an OS, sandboxed plugins that prove properties about their own behavior, or cryptographic protocols where the verification logic is part of the message. The Ψ axioms specify exactly what self-description requires and what it leaves free — a formal boundary between structure and choice.

Claim status is tracked in [`CLAIMS.md`](CLAIMS.md) (`Lean-proved`, `Empirical`, `Conjecture/Open`).

---

## 1. The Ψ Framework

What is the simplest finite structure that can identify its own components through its own operation?

The Ψ framework answers this by stacking axioms on a finite magma (N-element set with binary operation `dot`). Each axiom forces a specific capability — absorbers for boundaries, testers for judgment, encoders for synthesis, quote/eval for reflection, branching for control flow — until the structure is self-describing: it contains everything needed to inspect and reconstruct itself from within.

### The Axiom System

**Structural Ladder (L0–L8)** — forces the basic role architecture:

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

**Operational Axioms** — force specific computational capabilities:

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

### Scale

| Feature | Min N |
|---------|-------|
| L8 (full ladder) | 6 |
| + QE pair | 8 |
| + Branch/Compose/Y | 12 |
| + IO + 8-state counter + Selection | 16 |

### Universal Theorems

These hold for **all** models of the axiom system — not just Ψ₁₆ᶠ, but any satisfying algebra. This is the strongest part of the theoretical contribution: the axioms constrain *every* model, not one table. Each claim is tagged with its evidence tier (see [`CLAIMS.md`](CLAIMS.md)):

- **Exactly 2 absorbers.** `[Lean]` L5 forces no additional absorbers beyond ⊤ and ⊥.
- **Separation of judgment and operation.** `[Lean]` Kleene (C) makes this structural: non-testers *cannot* produce boolean outputs on non-absorbers. Branching must go through a tester. There is no shortcut.
- **Actuality irreducibility.** `[SAT]` The tester row is **completely free**. At N=16, all 40 tester free cells (τ: 8, SEQ: 16, s0: 16) can independently flip between ⊤ and ⊥ (push/pop verified at N=8, 12, 16). No combination of structural axioms pins any tester cell. The distinction the tester draws is a genuine choice — the "actuality" degree of freedom.
- **Rigidity.** `[Lean]` Ψ₁₆ᶠ is WL-1 discrete: all 16 elements distinguishable after 1 Weisfeiler-Leman refinement. No non-trivial automorphism exists.
- **Chirality.** `[SAT]` E-transparency (E·⊤ = ⊤, E·⊥ = ⊥) does *not* cascade to tester cells. Eval preserves structural boundaries but cannot determine what the tester accepts — the information flows one way.
- **Encoder-tester non-commutativity.** `[SAT]` Encoders and testers cannot commute in general. The Kleene barrier enforces an asymmetry: testers judge, encoders synthesize, and no element can do both.
- **No right identity.** `[SAT]` UNSAT at N≥6.
- **No full associativity.** `[SAT]` UNSAT. No associative sub-magma of size ≥ 4.
- **Encoder dominance.** `[Empirical]` As N grows, encoder count grows; tester and inert counts stay bounded.
- **Constructibility.** `[Lean]` {⊤, ⊥, Q, E} generates all N elements in ≤4 steps at N=16.
- **Decidability boundary.** `[Open]` The axiom stack crosses from decidable to Turing-complete at a precise point. With QE and Branch alone (N≥12), the algebra can encode flat conditional dispatch — every computation terminates. Adding the Y-combinator axiom (`Y·ρ = ρ·(Y·ρ)`) introduces fixed-point recursion, and termination becomes undecidable. This is the structural cost of self-reference: the same mechanism that lets the algebra apply a function to its own description is what makes halting uncomputable. (The structural argument is clear; the formal proof that Y makes the system Turing-complete is not yet in Lean.)

### Phenomenological Interpretation

These structural constraints have interpretations in phenomenology and philosophy of mind. The Kleene barrier — judgment cannot commute with synthesis — mirrors the phenomenological distinction between receptivity and spontaneity. Actuality irreducibility — the tester's values are axiomatically unconstrained — corresponds to the irreducibility of *that* something is given, as distinct from *what* is structurally possible. Chirality — eval preserves boundaries but cannot determine what the tester accepts — captures the asymmetry of observation: structure flows from object to representation, not the reverse. These are not analogies imposed after the fact — they fall out of the axioms as structural necessities.

---

## 2. Ψ₁₆ᶠ: The Specific Algebra

The canonical representative: a single 16×16 Cayley table with **83 machine-checked Lean theorems** `[Lean]` (`Psi16Full.lean`), covering every operational constraint simultaneously. All proofs compile with **zero `sorry`** on Lean 4.28.0 / Mathlib v4.28.0.

This table is one model from the solution space — the axioms constrain roles and relationships but leave many cells free (192/256 at N=16, 117/144 at N=12). The universal theorems above hold for all models; the properties below are verified for this specific table.

### Element Assignments

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

### Multi-Duty Architecture

Elements serve up to 4 roles each. The Cayley table encodes all pairwise interactions, so an element's role depends on what it's composed with, not on a fixed assignment — element 14 acts as GET when composed after PUT, as FST when composed after a pair, as SWAP when composed with a core element, and as counter state s1 when operated on by INC or DEC. There is no overloading; every role is a different slice of the same row.

| Element | Roles |
|---------|-------|
| 14 | GET / FST / SWAP / s1 (4 roles) |
| 6 (Q) | Q / SND / s2 / p01 (4 roles) |
| 7 (E) | E / INC2 / s7 (3 roles) |
| 15 | DEC / PUT / s5 (3 roles) |
| 11 | PAIR / s3 / p11 (3 roles) |

### Operations

**8-State Counter:**
```
s0(12) →INC→ s1(14) →INC→ s2(Q=6) →INC→ s3(11) →INC→
s4(Y=10) →INC→ s5(15) →INC→ s6(ρ=8) →INC→ s7(E=7) →INC→ s0(12)
```
DEC reverses this cycle exactly. Zero test: `τ·s0 = ⊤`, `τ·sₖ = ⊥` for k≠0.

**IO Roundtrip:** `GET·(PUT·x) = x` on core {2,3,4,5}, with PUT=15, GET=14.

**2×2 Product:** Pairing encodes structured data, enabling the algebra to represent tuples for multi-argument operations. Four elements encode the four states of a 2-bit register, with FST and SND as projections:

| Pair | State | Element | FST | SND |
|------|-------|---------|-----|-----|
| (s0,s0) | p00 | 12 (=s0) | s0 | s0 |
| (s0,s1) | p01 | 6 (=Q) | s0 | s1 |
| (s1,s0) | p10 | 9 (=η) | s1 | s0 |
| (s1,s1) | p11 | 11 (=PAIR) | s1 | s1 |

---

## 3. Black-Box Recovery

All 16 elements can be identified from a shuffled, opaque dot oracle — no ground truth, no labels. Three methods (`psi_blackbox.py`), all 100% on 1000 seeds `[Empirical]`:

| Method | Mean dot calls | Strategy |
|--------|---------------|----------|
| **Behavioral** | 755 | 12-step axiom-driven probing (full row reads) |
| **Generation** | 658 | Steps 1–7, then depth-2 generation from {⊤,⊥,Q,E} |
| **Adaptive** | **62** | Absorber-probe signatures + Kleene/QE targeting + generation |

The adaptive method never reads a full row. The 2-probe absorber signature `(x·⊤, x·⊥)` partitions all 14 non-absorbers into 5 disjoint classes:

| Signature | Elements | What it reveals |
|-----------|----------|-----------------|
| full-preserver | τ, SEQ, E, s0 | E is here (Kleene separates it from testers) |
| semi(⊤) | g | **unique** — orients ⊤ |
| semi(⊥) | f, ρ, Y, PAIR | — |
| swap(⊥→⊤) | Q, INC, s1 | Q is here (QE round-trip on E identifies it) |
| swap(⊤→⊥) | η, DEC | — |

Once ⊤, ⊥, Q, E are found (~50 probes), 12 generation calls produce all remaining elements via the depth-2 generation tree.

```bash
uv run python psi_blackbox.py --method adaptive              # single demo
uv run python psi_blackbox.py --method adaptive --seeds 1000  # batch
uv run python psi_blackbox.py --seeds 1000 --compare          # cost comparison
```

---

## 4. What Is Not Proved

- **Uniqueness of Ψ₁₆ᶠ.** The Cayley table is one model from the solution space. The axioms constrain roles and relationships but leave 192/256 cells free at N=16 (25.0% determination). Cell-by-cell freedom analysis (`ds_search/n16_freedom.py`) confirms: absorber rows fully fixed (32), counter/INC/DEC pinned (24), E-transparency + INC2 fix 6 E-cells, selection fixes η·ρ, Y fixed-point fixes Y·ρ. Scale: N=8 → 28.1%, N=12 → 18.8%, N=16 → 25.0% (increase from N=12 due to additional operational constraints).
- **Minimality from base axioms.** Abstract axiom limitation theorems show base DirectedDS axioms imply only `card ≥ 2` (tight). What forcing conditions derive the full structure from first principles remains open.
- **Symmetric impossibility.** The symmetric synthesis barrier is demonstrated by construction but not proved as a general impossibility theorem.
- **Necessity of self-modeling.** Empirical evidence (`counterexample_search.py`) strongly suggests self-modeling is not required for efficient scramble-resilience — nearly all structureless rigid magmas are WL-1 discriminable. Self-modeling provides interpretability, not computational necessity.

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
├── emulator/                         # Legacy: Δ₁-based Kamea machine emulator
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
│   ├── substrate_analysis.py         # Substrate/stacking analysis
│   └── n16_freedom.py                # N=16 cell-by-cell SAT freedom analysis
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

## Appendix: Legacy Kamea Emulator (66-atom, Δ₁-based)

> The emulator implements the *previous* architecture — a 66-atom algebra built on the Δ₁ self-model with opaque extensions (ALU, IO, W32, MUL, QUALE). The Ψ₁₆ᶠ framework supersedes this: it derives its structure axiom-first rather than extending a hand-constructed core.

A cycle-accurate emulator of the Δ₁-based hardware architecture: Cayley ROM, IC74181 ALU, SRAM heap, hardware stack, UART FIFOs, and a microcode-driven eval/apply state machine.

```bash
uv run python -m emulator.debugger examples/hello_world.ds   # TUI debugger
uv run python -m emulator.test_machine                        # test suite
uv run python -m emulator.debugger --neural examples/hello_world.ds  # neural backend
uv run ds_repl.py -e '(((ALU_ARITH :N9) :N7) :N5)'           # REPL
```

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

<p align="center">
  <img src="https://upload.wikimedia.org/wikipedia/commons/thumb/7/7a/Albrecht_D%C3%BCrer_-_Melencolia_I_-_Google_Art_Project_%28_AGDdr3EHmNGyA%29.jpg/1280px-Albrecht_D%C3%BCrer_-_Melencolia_I_-_Google_Art_Project_%28_AGDdr3EHmNGyA%29.jpg" width="250" alt="Albrecht Dürer — Melencolia I (1514)" />
</p>

# Kamea

**Axiom-driven search for finite magmas with intrinsic representation, evaluation, and control, with machine-checked proofs in Lean 4.**

<p align="center"><sub>In loving memory of Boba</sub></p>

We prove that a single 16×16 multiplication table can simultaneously encode quoting, evaluation, branching, recursion, arithmetic, and IO — all verified by 83 Lean theorems with zero `sorry`. Beyond existence, the canonical witness is operationally identifiable: all 16 elements can be recovered from a shuffled black-box oracle without labels. The repository also contains SAT analyses of the surrounding axiom class and universal theorems that hold for every satisfying model.

---

## Why It Matters

Any system that can inspect and modify its own components needs a representation layer: some way to quote a piece of itself, examine it, and act on the result. In practice this is a runtime, a reflection API, a JIT compiler — machinery bolted on top, with no guarantee that the representation is faithful or complete.

The Ψ framework asks whether that machinery can be *intrinsic*. Can a finite algebraic structure — nothing but a set of elements and a binary operation — contain its own quote/eval pair, conditional branching, recursion, arithmetic, and IO, all realized within a single binary operation table? And can you *prove* it does, not by running tests, but by machine-checking the axioms?

The answer is yes, and it fits in a 16×16 table.

The primary contribution is methodological: a demonstration that axiom-driven SAT search combined with Lean verification can systematically explore the space of self-describing finite structures, producing both universal theorems about the axiom class and specific verified models. The specific algebra Ψ₁₆ᶠ is one output of this methodology. The universal theorems — forced rigidity, actuality irreducibility, separation of judgment and synthesis — are the more durable results. Whether these properties translate to practical self-verifying systems is an open question.

**Formally established:**
- A 16-element model exists satisfying all axioms simultaneously `[Lean]`
- The axiom class forces exactly 2 absorbers, Kleene separation, WL-1 rigidity, and 4-element constructibility `[Lean]`
- Tester cells are completely free across all tested sizes (actuality irreducibility) `[SAT]`
- All 16 elements recoverable from shuffled oracle, 3 methods, 100% on 1000 seeds `[Empirical]`

**Not formally established:**
- Turing-completeness of the Y-extended system `[Open]`
- Uniqueness or optimality of Ψ₁₆ᶠ among satisfying models `[Open]`
- Symmetric impossibility as a general theorem `[Open]`

Claim status is tracked in [`CLAIMS.md`](CLAIMS.md) (`Lean-proved`, `Empirical`, `Conjecture/Open`).

### How to Read This Repo

1. [`docs/psi_framework_summary.md`](docs/psi_framework_summary.md) — full axiom search results and Cayley tables
2. [`DistinctionStructures/Psi16Full.lean`](DistinctionStructures/Psi16Full.lean) — 83 machine-checked theorems
3. [`psi_blackbox.py`](psi_blackbox.py) — black-box recovery demo (run it)
4. [`CLAIMS.md`](CLAIMS.md) — what is proved, what is empirical, what is open

---

## 1. The Ψ Framework

What is the simplest finite structure that can identify its own components through its own operation?

The Ψ framework answers this by stacking axioms on a finite magma (N-element set with binary operation `dot`). Each axiom forces a specific capability — absorbers for boundaries, testers for judgment, encoders for synthesis, quote/eval for reflection, branching for control flow — until the structure is self-describing: it contains enough internal structure to encode, decode, and operationally recover its components. (Here "self-describing" means the algebra contains distinguished elements behaving as an internal representation and evaluation interface for elements of the same algebra.)

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

### Result Categories

Results in this repository fall into four tiers:

- **Universal results** — properties proved for *every* model satisfying the axiom class, not just one table. Tagged `[Lean]` or `[SAT]`.
- **Model-specific results** — properties proved for the particular table Ψ₁₆ᶠ. Tagged `[Lean]`.
- **Empirical search results** — SAT satisfiability, minimality bounds, freedom analysis, recovery observations. Tagged `[SAT]` or `[Empirical]`.
- **Open claims** — not yet formalized. Tagged `[Open]`.

Full registry with reproduction commands: [`CLAIMS.md`](CLAIMS.md).

### Universal Theorems

These hold for **all** models of the axiom system — not just Ψ₁₆ᶠ, but any satisfying algebra:

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
- **Decidability boundary.** `[Open]` Adding the Y-style fixed-point axiom introduces unrestricted self-reference. This is the point at which termination is no longer expected to admit a trivial structural argument; a formal Turing-completeness result remains open. See below.

### The Decidability Boundary

The axiom stack crosses a sharp boundary between decidable and undecidable self-description, and the crossing is exactly one axiom.

Without Y, the algebra has QE (quote/eval) and Branch (tester-mediated conditional dispatch). This is analogous to flat eval — like Datalog, or a first-order term rewriter with no recursion. Every branch eventually bottoms out at an absorber. You can enumerate all reachable states; the system always terminates.

Adding the single Y-combinator axiom (`Y·ρ = ρ·(Y·ρ)`) introduces a fixed point: the branch element can now apply itself to its own output indefinitely. This is the same structural move that separates Datalog from Prolog, or primitive recursion from general recursion. The algebra goes from a system where every computation halts to one where termination is no longer guaranteed.

The structural argument is clear — one axiom, one operation, one boundary. A formal proof that this makes the system Turing-complete (rather than merely non-terminating) is still open.

### Phenomenological Interpretation

*The following correspondences are interpretive, not part of the formal theorem set.*

The structural constraints have precise phenomenological counterparts. Judgment cannot commute with synthesis (Kleene barrier) — that is a theorem, not an analogy. Tester values are axiomatically unconstrained (actuality irreducibility) — also a theorem. Eval preserves boundaries but cannot determine what the tester accepts (chirality) — again, proved. Whether these correspondences with receptivity/spontaneity, the irreducibility of givenness, and the asymmetry of observation reflect something deeper about self-description is an open question — but the structural facts themselves are theorems, not interpretations.

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
| 14 | GET | encoder | — | s1 | GET/FST | SWAP |
| 15 | DEC | encoder | decrement | s5 | PUT/DEC | — |

### Multi-Duty Architecture

Elements serve up to 4 roles each. The Cayley table encodes all pairwise interactions, so an element's role depends on what it's composed with, not on a fixed assignment — element 14 acts as GET when composed after PUT, as FST when composed after a pair, as SWAP when composed with a core element, and as counter state s1 when operated on by INC or DEC. There is no overloading; every role is a different slice of the same row.

| Element | Roles |
|---------|-------|
| 14 (GET) | GET / FST / SWAP / s1 (4 roles) |
| 6 (Q) | Q / SND / s2 / p01 (4 roles) |
| 7 (E) | E / INC2 / s7 (3 roles) |
| 15 (DEC) | DEC / PUT / s5 (3 roles) |
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

### Worked Example

All operations below are lookups in the same 16×16 Cayley table.

```
# Quote/Eval round-trip: Q encodes τ, E decodes it back
Q · τ  = 9  (η)          -- quote the tester: get a code for it
E · 9  = 3  (τ)          -- eval the code: recover the original

# Branch dispatch: ρ routes through f when τ accepts
τ · f  = 0  (⊤)          -- tester accepts f
ρ · f  = 13 (INC)        -- branch element computes f·f = 13  (took the f-path)

τ · g  = 0  (⊤)          -- tester also accepts g
ρ · g  = 11 (PAIR)       -- branch computes f·g = 11

# Counter step: INC advances the 8-state counter
INC · s0 = 14 (s1)       -- increment from zero
INC · s1 = 6  (Q = s2)   -- increment again: counter state 2 is Q
τ · s0   = 0  (⊤)        -- zero test: tester accepts s0
τ · s1   = 1  (⊥)        -- non-zero: tester rejects s1
```

---

## 3. Black-Box Recovery

All 16 elements can be identified from a shuffled, opaque dot oracle — no ground truth, no labels. Three methods (`psi_blackbox.py`), all 100% on 1,000,000 seeds `[Empirical]`:

| Method | Mean dot calls | Min | Max | Strategy |
|--------|---------------|-----|-----|----------|
| **Behavioral** | 756.9 | 653 | 861 | 12-step axiom-driven probing (full row reads) |
| **Generation** | 659.4 | 543 | 776 | Steps 1–7, then depth-2 generation from {⊤,⊥,Q,E} |
| **Adaptive** | **62.5** | 59 | 66 | Absorber-probe signatures + Kleene/QE targeting + generation |

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

### Claim Matrix

| Claim | Scope | Status | Evidence |
|-------|-------|--------|----------|
| Ψ₁₆ᶠ satisfies all listed operations | specific model | `[Lean]` | `Psi16Full.lean` (83 theorems) |
| Ψ₁₆ᶠ is WL-1 rigid and fully producible | specific model | `[Lean]` | `Psi16Full.lean` |
| Base axioms imply only card ≥ 2 (tight) | universal | `[Lean]` | `BaseAxiomDerivation.lean` |
| QE exists at N ≥ 8 | universal / min-size | `[SAT]` | `stacking_analysis.py` |
| Branch/Compose/Y require N ≥ 12 | universal / min-size | `[SAT]` | `stacking_analysis.py` |
| Tester cells completely free | universal / all sizes tested | `[SAT]` | `n16_freedom.py` (N=8, 12, 16) |
| No right identity at N ≥ 6 | universal / size bound | `[SAT]` | `stacking_analysis.py` |
| N=16 determination: 64/256 fixed (25.0%) | size-specific | `[SAT]` | `n16_freedom.py` |
| Black-box recovery (3 methods, 100%) | specific model | `[Empirical]` | `psi_blackbox.py` |
| Encoder dominance as N grows | trend | `[Empirical]` | `stacking_analysis.py` |
| Y-combinator → Turing-completeness | universal | `[Open]` | structural argument |
| Symmetric impossibility (general) | universal | `[Open]` | demonstrated, not proved |

Full registry with reproduction commands: [`CLAIMS.md`](CLAIMS.md).

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

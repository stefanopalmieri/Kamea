# Kamea

**Three walls. Seven roles. One table that knows itself. Zero `sorry`.**

*Judgment cannot merge with computation. Substrate cannot merge with anything active. Among all rigid algebras satisfying these walls, maximal expressiveness selects seven roles — the same seven McCarthy needed for Lisp.*

<p align="center">
  <img src="melencolia.png" width="250" alt="Albrecht Dürer — Melencolia I (1514)" />
</p>
<p align="center"><sub>In loving memory of Boba</sub></p>

## Quick Start

```bash
git clone https://github.com/stefanopalmieri/Kamea.git && cd Kamea

python3 psi_lisp.py examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp
# or: kamea-rs/target/release/kamea run examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp
```

```
=== PSI REFLECTIVE TOWER (Defunctionalized CPS) ===
Layer 3: User programs (fib, fact)
Layer 2: CPS meta-circular evaluator (psi_metacircular.lisp)
Layer 1: Base evaluator (psi_lisp.py)
Layer 0: Cayley table (256 bytes)

--- Level 0: Computation (meta-evaluated) ---
Defining fib and computing fib(8)... 21
Defining fact and computing fact(10)... 3628800

--- Level 1: Ground Verification (Cayley table probes) ---
Absorber laws (TOP/BOT): ALL HOLD
Table health: ALL INVARIANTS HOLD

--- Level 2b: Continuation Chain Inspection ---
Reify inside (let ((x (reify))) x):
  Chain depth: 3
  Frame 0 tag = k-let-bind? YES
  Frame 1 tag = k-let-body? YES
  Frame 2 tag = k-id? YES

--- Level 2c: Continuation Modification (rewriting the future) ---
K-IF BRANCH SWAP — the definitive 3-Lisp demo:
  Without modification: (if 1 42 99) → 42
  With branch swap: (if 1 42 99) → 99
  CONFIRMED: Program rewrote its own if-branches.
```

A program that can inspect its own continuation, where the continuation is data built from algebraically verified atoms, running on a table whose rigidity, discoverability, and actuality irreducibility are Lean-proved, implementing a Lisp whose five role categories are axiom-forced, whose seven specialized roles maximize compositional expressiveness among tested collapses, and whose term algebra is Turing complete.

Smith's 3-Lisp (1984) had the reflective tower but no ground. The levels went down forever — interpreter interpreting interpreter interpreting interpreter. There was no bottom. Each level's meaning depended on the level below, and there was no foundation. Here, the tower terminates at a 16×16 Cayley table — 256 bytes whose algebraic properties are machine-checked. The program verifies the table before trusting the evaluator. There is nothing beneath the table to worry about. It IS the algebra, not an implementation of it.

The demo: a defunctionalized CPS meta-circular evaluator — Ψ-Lisp interpreting itself with inspectable continuations — computes fibonacci, verifies the Cayley table it runs on, then reifies its own continuation as walkable data, navigates to a pending `k-if` frame, swaps the then/else branches, reflects, and takes the opposite branch from what the source code says. The program rewrites its own future. Everything below — axioms, theorems, phenomenology — is context for understanding what you just saw.

```bash
python3 psi_repl.py                                        # interactive REPL
python3 examples/psi16_corrupted_host_demo.py               # watch one wizard heal another
cd kamea-rs && cargo run --release -- repl                   # Rust REPL (~25x faster)
cd kamea-rs && cargo run --release -- run \                  # Rust reflective tower
  examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp
```

### Compile to Native

```bash
# C backend
python3 psi_supercompile.py examples/psi_counter_known.psi > /tmp/opt.psi
python3 psi_transpile.py /tmp/opt.psi > /tmp/counter.c
gcc -O2 -I. -o /tmp/counter /tmp/counter.c
/tmp/counter                                               # native speed, zero table lookups

# Rust backend (self-hosted transpiler — works with either interpreter)
python3 psi_lisp.py --table=c examples/psi_transpile_test.lisp | sed '1d;$d' > /tmp/out.rs
# or: kamea-rs/target/release/kamea run examples/psi_transpile_test.lisp | sed '1d;$d' > /tmp/out.rs
cp psi_runtime.rs /tmp/
rustc -O -o /tmp/out /tmp/out.rs && /tmp/out               # 3 42 99 3 5 5
```

The transpiler handles computational programs (arithmetic, recursion, branching, list operations). It does not yet handle metaprograms — programs that construct and manipulate source code as data. The reflective tower is exactly such a program: a meta-circular evaluator that builds S-expressions as cons-cell data structures using quoted symbols. Extending the transpiler to handle quoted symbol encoding would enable compiling the reflective tower to native code, producing a compiled interpreter with native-speed dispatch and MMTk-managed continuations. This is architecturally straightforward (a symbol-to-integer table at transpile time) but not yet implemented. See [`docs/transpiler_gaps.md`](docs/transpiler_gaps.md) for the full gap analysis.

---

## The Seven Roles

| Ψ | Lisp | Role |
|---|------|------|
| ⊤ | NIL | Empty / base case |
| Q | QUOTE | Freeze a term (constructor) |
| E | EVAL | Unwrap / interpret (destructor) |
| g | CONS | Build a pair |
| f | CAR | First projection |
| η | CDR | Second projection |
| ρ | COND | Conditional branch |

The correspondence is structural (same role inventory) rather than semantic (the domains differ: Ψ operates on magma elements, Lisp on symbolic lists). That two systems designed for self-manipulation — one axiom-driven, one engineering-driven — converge on the same seven-role architecture is a noteworthy observation, not a proof of necessity.

The Ψ axioms force five behavioral categories with hard walls between them (32/45 role pairs UNSAT at N=12). All instantiations — from 5 role-bearing elements to 7+ — produce rigid discoverable algebras. Among tested collapses, full specialization to seven roles maximizes compositional expressiveness (49 vs 16 1-step cells). Four roles are forced by axioms alone; three are selected by the expressiveness principle. Full argument: [`docs/forced_roles_theorem.md`](docs/forced_roles_theorem.md).

## Why It Matters

Any system that can inspect and modify its own components needs a representation layer: some way to quote a piece of itself, examine it, and act on the result. In practice this is a runtime, a reflection API, a JIT compiler — machinery bolted on top, with no guarantee that the representation is faithful or complete.

The Ψ framework asks whether that machinery can be *intrinsic*. Can a finite algebraic structure — nothing but a set of elements and a binary operation — contain its own quote/eval pair, conditional branching, recursion, arithmetic, and IO, all realized within a single binary operation table? And can the language that emerges from this table interpret itself — can a program written in it verify the table, capture its own continuation, and modify its own future, all within the same algebra?

The answer is yes, and it fits in a 16×16 table.

## Key Results

- Rigidity: every injective endomorphism is the identity `[Lean]`
- Discoverability: 4 probes identify all 16 elements `[Lean]`
- Actuality irreducibility: twin models agree on structure, disagree on tester assignment `[Lean]`
- No right identity in any model; card ≥ 4 from role axioms (tight) `[Lean]`
- Kleene wall: judgment cannot merge with computation (32/45 role pairs UNSAT) `[SAT]`
- Turing completeness: 7 axiom-forced elements simulate 2CM `[Empirical]`
- Reflective tower: 3 levels, branch swap, grounded continuations `[Empirical]`
- Compilation: within 4x of native Rust via supercompile → C/Rust `[Empirical]`
- GC: 10M allocations in 4MB via MMTk `[Empirical]`
- Futamura: all 3 projections demonstrated, fixed-point verified `[Empirical]`
- Extension profiles: Ψ₁₆ᶠ (hardware) and Ψ₁₆ᶜ (software), same core theorems `[Empirical]`

Full claim matrix with 43 entries and reproduction commands: [`CLAIMS.md`](CLAIMS.md). Full technical details: [`docs/technical_overview.md`](docs/technical_overview.md).

---

## The Axiom System

What is the simplest finite structure that can identify its own components through its own operation?

The Ψ framework answers this by stacking axioms on a finite magma (N-element set with binary operation `dot`). Each axiom forces a specific capability — absorbers for boundaries, testers for judgment, encoders for synthesis, quote/eval for reflection, branching for control flow — until the structure is self-describing.

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

| Feature | Min N |
|---------|-------|
| L8 (full ladder) | 6 |
| + QE pair | 8 |
| + Branch/Compose/Y | 12 |
| + IO + 8-state counter + Selection | 16 |

The axiom stack admits models of size 12 supporting quote/eval, branching, and fixed points — enough for Turing completeness. The specific model Ψ₁₆ᶠ adds efficient counters, IO, product encodings, and a Y-combinator at size 16. The computational core is 7 axiom-forced elements; the rest is infrastructure. Full details: [`docs/technical_overview.md`](docs/technical_overview.md).

Results fall into four tiers:

- **Universal results** — properties proved for *every* model satisfying the axiom class. Tagged `[Lean]` or `[SAT]`.
- **Model-specific results** — properties proved for the particular table Ψ₁₆ᶠ. Tagged `[Lean]`.
- **Empirical search results** — SAT satisfiability, minimality bounds, freedom analysis, recovery observations. Tagged `[SAT]` or `[Empirical]`.
- **Open claims** — not yet formalized. Tagged `[Open]`.

Full registry with reproduction commands: [`CLAIMS.md`](CLAIMS.md).

### How to Read This Repo

1. [`psi_repl.py`](psi_repl.py) — Interactive Ψ-Lisp REPL
2. [`examples/psi_metacircular.lisp`](examples/psi_metacircular.lisp) — Defunctionalized CPS meta-circular evaluator with inspectable continuations
3. [`examples/psi_reflective_tower.lisp`](examples/psi_reflective_tower.lisp) — Three-level reflective tower: compute → verify table → inspect/modify continuations → branch swap
4. [`examples/psi_recovery_spell.lisp`](examples/psi_recovery_spell.lisp) — Black-box recovery as pure Ψ-Lisp (the "spell" cast by the wizard)
5. [`examples/psi16_corrupted_host_demo.py`](examples/psi16_corrupted_host_demo.py) — Animated TUI: watch one wizard heal another using the spell
6. [`psi_star.py`](psi_star.py) — Turing-completeness proof: 2CM simulation via 7 axiom-forced elements (run it)
7. [`psi_lisp.py`](psi_lisp.py) — Mini-Lisp → Ψ∗ transpiler (McCarthy 1960 conventions)
8. [`kamea-rs/`](kamea-rs/) — Rust emulator + WASM browser debugger (~25x faster than Python)
9. [`docs/psi_framework_summary.md`](docs/psi_framework_summary.md) — full axiom search results and Cayley tables
10. [`DistinctionStructures/Psi16Full.lean`](DistinctionStructures/Psi16Full.lean) — 83 operational theorems + rigidity/discoverability/irreducibility proofs
11. [`psi_blackbox.py`](psi_blackbox.py) — Black-box recovery (3 methods, 100% on 1M seeds)
12. [`CLAIMS.md`](CLAIMS.md) — what is proved, what is empirical, what is open
13. [`psi_supercompile.py`](psi_supercompile.py) — Partial evaluator: constant folding + QE cancellation + branch elimination + let propagation + lambda inlining
14. [`psi_transpile.py`](psi_transpile.py) — Supercompiled Ψ∗ → C transpiler
15. [`psi_runtime.h`](psi_runtime.h) — C runtime: 256-byte Cayley table + inline dot function
16. [`examples/psi_futamura.psi`](examples/psi_futamura.psi) — Futamura projection demo: interpreter specialization = direct compilation (10 test cases)
17. [`examples/psi_specialize.lisp`](examples/psi_specialize.lisp) — Ψ-Lisp specializer: Futamura projections 1 & 2 on tagged-pair IR
18. [`examples/psi_transpile.lisp`](examples/psi_transpile.lisp) — Self-hosted transpiler: Ψ-Lisp → Rust (Futamura projection 3 fixed point)
19. [`psi_runtime.rs`](psi_runtime.rs) — Rust runtime: Cayley table + Arena bump allocator

---

## What Is Not Proved

- **Uniqueness of Ψ₁₆ᶠ.** The Cayley table is one model from the solution space. The axioms constrain roles and relationships but leave 192/256 cells free at N=16 (25.0% determination). Cell-by-cell freedom analysis (`ds_search/n16_freedom.py`) confirms: absorber rows fully fixed (32), counter/INC/DEC pinned (24), E-transparency + INC2 fix 6 E-cells, selection fixes η·ρ, Y fixed-point fixes Y·ρ. Scale: N=8 → 28.1%, N=12 → 18.8%, N=16 → 25.0% (increase from N=12 due to additional operational constraints).
- **Minimality from base axioms.** Abstract axiom limitation theorems show base DirectedDS axioms imply only `card ≥ 2` (tight). What forcing conditions derive the full structure from first principles remains open.
- **Symmetric impossibility.** The symmetric synthesis barrier is demonstrated by construction but not proved as a general impossibility theorem.
- **Necessity of self-modeling.** Empirical evidence (`ds_search/counterexample_search.py`) strongly suggests self-modeling is not required for efficient scramble-resilience — nearly all structureless rigid magmas are WL-1 discriminable. Self-modeling provides interpretability, not computational necessity.
- **Extension profile optimality.** Ψ₁₆ᶠ and Ψ₁₆ᶜ are two points in the extension design space. Whether either is optimal for its target — or whether better profiles exist — is unexplored. The methodology (SAT search with target-specific constraints) can find other profiles, but the space has not been systematically enumerated.

---

## Performance

| Implementation | Single invocation | Amortized/iter | vs Ψ-Lisp Python |
|----------------|------------------|---------------|-----------------|
| **Ψ-Lisp (Python interpreter)** | ~2,000 ms | — | 1x |
| **Ψ-Lisp (Rust interpreter)** | ~200 ms | — | 10x |
| **Native Python** | ~30 ms (startup), 5 µs compute | 5 µs | 400,000x |
| **Compiled Ψ-Lisp** (both profiles, gcc -O2) | ~2.4 ms (startup) | 0.01 µs | 200,000,000x |
| **Native Rust** (LLVM -O) | ~1 ms (startup) | 0.003 µs | ~700,000,000x |

The compiled output is within **4x of hand-written Rust compiled with LLVM** — and faster than native Python. The entire compilation pipeline is ~1,100 lines: a 312-line supercompiler, a 640-line transpiler, and a 121-line C runtime whose core is a 256-byte array. Full performance analysis and extension profile comparison: [`docs/technical_overview.md#10-performance`](docs/technical_overview.md#10-performance).

---

## Repository Structure

```
├── DistinctionStructures/
│   ├── Basic.lean                    # Abstract DS definitions and axioms
│   ├── BaseAxiomDerivation.lean      # Base axioms imply only card ≥ 2 (tight)
│   ├── BasePlusA7Derivation.lean     # Adding generic A7′ still doesn't force card ≥ 17
│   ├── OntologicalSchema.lean        # Abstract four-lift schema theorem
│   ├── Psi16.lean                    # Ψ₁₆ with selection axiom (42 theorems)
│   ├── Psi16C.lean                  # Ψ₁₆ᶜ C-interop table (INC/DEC/INV cancellations)
│   ├── Psi16Full.lean               # Ψ₁₆ᶠ full operations (83 theorems)
│   ├── Psi16Discoverable.lean       # Behavioral discoverability (4-probe injectivity)
│   ├── Psi16Rigidity.lean           # Automorphism rigidity (Aut = {id})
│   ├── Psi16ActualityIrreducibility.lean  # Twin-model actuality irreducibility
│   ├── PsiStructure.lean               # Abstract Ψ role axioms (L0–L3)
│   ├── PsiUniversalBounds.lean          # No right identity + card ≥ 4 (algebraic)
│   └── PsiCountermodels.lean            # Tight 4-element countermodel
├── kamea-rs/                             # Rust emulator + WASM browser debugger
│   ├── crates/
│   │   ├── psi-core/                     # The algebra — #![no_std], zero deps
│   │   │   └── src/
│   │   │       ├── table.rs              # 16×16 Cayley table as const array
│   │   │       ├── term.rs               # Term enum + arena allocator
│   │   │       └── eval.rs               # Explicit-stack Ψ∗ evaluator
│   │   ├── psi-runtime/                  # The machine — heap, IO, Mini-Lisp
│   │   │   └── src/
│   │   │       ├── machine.rs            # Lisp evaluator, builtins, environment
│   │   │       ├── lisp.rs               # S-expression parser
│   │   │       └── io.rs                 # IO channel abstraction
│   │   ├── psi-cli/                      # Native CLI — runner, REPL, benchmark
│   │   │   └── src/main.rs
│   │   ├── psi-web/                      # WASM target + browser debugger
│   │   │   ├── src/lib.rs                # wasm-bindgen exports
│   │   │   └── www/
│   │   │       ├── index.html            # Debugger UI
│   │   │       ├── debugger.js           # UI logic (computation in Web Worker)
│   │   │       ├── worker.js             # WASM Web Worker
│   │   │       └── style.css
│   │   ├── wispy-gc/                     # MMTk garbage collector integration
│   │   │   └── src/
│   │   │       ├── lib.rs                # WispyVal type, tag helpers, public API
│   │   │       ├── vm.rs                 # VMBinding impl, WispySlot, Collection, Scanning
│   │   │       ├── object.rs             # 24-byte cons cell ObjectModel (header + car + cdr)
│   │   │       ├── roots.rs              # Shadow stack for GC root scanning
│   │   │       └── alloc.rs              # wispy_cons/car/cdr — allocation through MMTk
│   │   └── wispy-stress/                 # GC stress test (10M allocs in 4MB heap)
│   │       └── src/main.rs
│   └── examples/
│       └── psi_*.lisp                    # Lisp test programs (copied from examples/)
├── examples/
│   ├── psi16_corrupted_host_demo.py  # Animated TUI: dual-wizard corrupted-host bootstrap
│   ├── psi16_bijection_designer.py   # Interactive bijection designer for wiz2 sprite
│   ├── psi16_wizard_sprites.py       # Sprite rendering utilities
│   ├── wiz2.json                     # Hand-designed bijective sprite mapping
│   ├── psi_metacircular.lisp         # Defunctionalized CPS evaluator (~350 lines, 14 continuation types)
│   ├── psi_reflective_tower.lisp     # Three-level reflective tower + branch swap demo
│   ├── psi_recovery_spell.lisp       # Black-box recovery as pure Ψ-Lisp
│   ├── psi_hello_world.lisp          # Ψ-Lisp hello world example
│   ├── psi_counter_known.psi          # Supercompiler test: known-base counter increments
│   ├── psi_counter_free.psi           # Supercompiler test: free-variable counter
│   ├── psi_branch_test.psi            # Supercompiler test: branch elimination
│   ├── psi_fold_constants.lisp        # Supercompiler test: constant folding
│   ├── psi_futamura.psi              # Futamura projection demo (10 test cases, Ψ₁₆ᶜ)
│   ├── psi_specialize.lisp           # Ψ-Lisp specializer: Futamura projections 1 & 2
│   ├── psi_transpile.lisp            # Self-hosted transpiler: Ψ-Lisp IR → Rust code
│   ├── psi_transpile_test.lisp       # Transpiler test harness (6 expression types)
│   └── psi_*.lisp                    # Mini-Lisp test programs (fibonacci, recursion, etc.)
├── ds_search/
│   ├── axiom_explorer.py             # Core encoder: encode_level(), classify_elements()
│   ├── stacking_analysis.py          # All Ψ analysis functions (~17k lines)
│   ├── substrate_analysis.py         # Substrate/stacking analysis
│   ├── n16_freedom.py                # Ψ₁₆ᶠ cell-by-cell SAT freedom analysis
│   ├── n16_c_interop.py              # Ψ₁₆ᶜ SAT search + freedom analysis
│   ├── forced_roles_test.py           # Layer 1: 45 pairwise role-aliasing tests (forced categories)
│   ├── collapse_rigidity_test.py     # Layer 2: rigidity at 6 collapse levels (universal rigidity)
│   ├── compositional_expressiveness.py # Layer 3: compositional cell/value counts (variational selection)
│   ├── collapse_model_count.py       # Model diversity at maximal collapse (20+ models, all rigid)
│   ├── tc_merge_test.py              # DEPRECATED: tests Ext, not role forcing (see forced_roles_test.py)
│   ├── counterexample_search.py      # WL-1 discrimination tests
│   ├── rigid_census.py               # Small rigid magma census
│   └── counterexamples/              # Saved counterexample tables (.npy)
├── docs/
│   ├── technical_overview.md          # Full technical details (moved from README)
│   ├── forced_roles_theorem.md        # The Forced Roles Theorem (core theoretical result)
│   ├── forced_roles.md               # Forced categories: raw SAT data + necessity analysis
│   ├── psi_framework_summary.md      # Comprehensive Ψ framework reference
│   ├── extension_profiles.md         # Ψ₁₆ᶠ vs Ψ₁₆ᶜ: modular extension architecture
│   ├── transpiler_gaps.md            # Transpiler gap analysis for reflective tower compilation
│   ├── continuation_protocol.md      # Continuation protocol documentation
│   └── minimal_model.md              # Minimal model notes
├── psi_star.py                       # Ψ∗ TC proof: 2CM simulation via 7 axiom-forced elements
├── psi_star_c.py                     # Ψ∗ term algebra over Ψ₁₆ᶜ (C-interop table)
├── psi_lisp.py                       # Mini-Lisp → Ψ∗ transpiler (McCarthy 1960 conventions)
├── psi_supercompile.py               # Partial evaluator: 2–5 pass supercompiler (table-dependent)
├── psi_transpile.py                  # Ψ-Lisp → C/Rust transpiler (--target c|rust)
├── psi_runtime.h                     # C runtime for Ψ₁₆ᶠ: 256-byte table + inline dot
├── psi_runtime_c.h                   # C runtime for Ψ₁₆ᶜ: table + arithmetic helpers
├── psi_runtime.rs                    # Rust runtime for Ψ₁₆ᶜ: table + Arena (bump allocator)
├── bench_c_interop.py                # Benchmark: Ψ₁₆ᶜ vs Ψ₁₆ᶠ comparison
├── psi_blackbox.py                   # Ψ₁₆ᶠ black-box recovery (3 methods)
├── psi_repl.py                       # Interactive Ψ-Lisp REPL
├── CLAIMS.md                         # Claim status registry
└── README.md
```

## Building

```bash
# Lean (requires Lean 4.28.0 / Mathlib v4.28.0)
lake build

# Python (requires uv)
uv run python psi_lisp.py examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp  # reflective tower
uv run python psi_repl.py                                     # interactive REPL
uv run python examples/psi16_corrupted_host_demo.py           # TUI demo
uv run python examples/psi16_corrupted_host_demo.py --plain   # plain narrative
python3 psi_repl.py --algebraic                              # Q-chain number representation
python3 psi_lisp.py --algebraic examples/psi_fibonacci.lisp  # verify: same results, algebraic encoding

# Rust interpreter (requires rustup — https://rustup.rs)
cd kamea-rs
cargo test                                                     # run all tests (40 total)
cargo run --release -- run examples/psi_fibonacci.lisp         # run a Lisp program (~25x faster)
cargo run --release -- --table=c run examples/psi_specialize.lisp  # Ψ₁₆ᶜ table
cargo run --release -- repl                                    # interactive REPL
cargo run --release -- bench examples/psi_fibonacci.lisp       # benchmark with timing

# Compiled Ψ-Lisp (C and Rust backends)
python3 psi_transpile.py examples/psi_fibonacci.lisp > /tmp/fib.c    # C (default)
gcc -O2 -I. -o /tmp/fib /tmp/fib.c && /tmp/fib

python3 psi_transpile.py --target rust examples/psi_fibonacci.lisp > /tmp/fib.rs  # Rust
cp psi_runtime.rs /tmp/
rustc -O -o /tmp/fib /tmp/fib.rs && /tmp/fib

# MMTk garbage collection stress test
cd kamea-rs
HEAP_MB=4 cargo run -p wispy-stress --release                  # 10M allocs in 4MB heap

# WASM browser debugger (requires wasm-pack — https://rustwasm.github.io/wasm-pack/)
cd kamea-rs/crates/psi-web
wasm-pack build --target web                                   # build WASM (124KB)
python3 -m http.server 8080 --directory www                    # serve debugger UI
# → open http://localhost:8080
```

All Lean theorems are checked by `decide` or `native_decide`, appropriate and complete for finite carrier types with decidable equality. Zero sorry.

All Mini-Lisp test programs produce identical output across Python, compiled C, compiled Rust, Rust interpreter, and WASM.

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

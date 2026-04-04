# Kamea

A 16-element algebra whose Cayley table is a complete computational system: a Lisp that fits in 256 bytes, compiles to native code matching hand-written C, and whose reflective tower (meta-circular evaluator, continuation reification, branch swap) compiles to a single binary in 2.2 ms.

<p align="center">
  <img src="melencolia.png" width="250" alt="Albrecht Dürer — Melencolia I (1514)" />
</p>
<p align="center"><sub>In loving memory of Boba</sub></p>

The 16×16 operation table contains seven elements that correspond to Lisp's primitives (quote, eval, cons, car, cdr, cond, nil). Not by encoding, but because the algebraic constraints that make reflection possible force those roles to exist. The algebra is Turing-complete via these seven elements alone. The remaining nine elements are I/O and counter machinery.

Behind the artifact is a structural decomposition: self-representation (encoding/decoding), self-description (classification), and self-execution (internal composition) are three independent capabilities of reflective computation. No capability implies any other, all six non-implications Lean-proved. The theory, paper, and proofs are in a separate repository: **[finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence)** (93 theorems, 12 Lean files, zero `sorry`).

### Why a finite magma?

A meta-circular evaluator applies functions to arguments. Strip away syntax, types, and environment, keeping only `apply(f, x)`, and what remains is a set with a binary operation: a magma. The Cayley table *is* the complete specification. Extensionality (distinct rows) gives the operation its discriminating power. The two absorbers (⊤, ⊥) are the constant functions. The retraction pair (Q, E) is Gödel numbering. Everything else is structure that the operation forces.

This is not a claim that magmas *are* evaluators. It is a claim that the algebraic structure of `apply` (the constraints that extensionality, encoding, classification, and composition impose on a finite operation table) is the right level of abstraction to separate reflective capabilities. The separation is invisible in richer settings (lambda calculus, typed systems) where the capabilities are entangled by construction.

### Why the engineering artifacts work

The Cayley table is a 256-byte array. Every operation in the algebra, including the operations that *implement the evaluator*, is a table lookup. This has three consequences:

1. **The table is transparent to optimizers.** A supercompiler can constant-fold through any chain of table lookups, because the table is static data. There is no interpretive overhead that can't be compiled away. The "interpreter" is just indexing into an array.

2. **The reflective tower has a fixed point.** In an infinite tower (3-Lisp, Black), each level is interpreted by the one below, and compilation requires cutting the chain. In a grounded tower, the bottom level *is* the table. The compiler doesn't need to cut anything; it bottoms out at 256 bytes of constant data. That's why the meta-circular evaluator compiles to a native binary: the tower terminates at data, not at another interpreter.

3. **Allocation is trivial.** Cons cells are pairs of table indices (integers). The runtime is a bump allocator: allocation is a pointer increment, no GC, no free lists. This is why compiled Ψ-Lisp matches hand-written C on cons-heavy workloads: there is no runtime system to get in the way.

## The Three Capabilities

| Capability | Categorical property | Finite-algebra instantiation | Independence |
|------------|---------------------|------------------------------|--------------|
| **Self-representing (S)** | Section-retraction pair | Q/E with mutual inverse on core | `[Lean]` `SelfSimulation.lean` |
| **Self-describing (D)** | Decidable subobject classifier | Classifier dichotomy: every non-zero is all-boolean or all-non-boolean on core | `[Lean]` `Countermodel.lean`, `Countermodels10.lean` |
| **Self-execution (H)** | Partial internal composition | Some element's row on core factors non-trivially as c ∘ b with b core-preserving | `[Lean]` `Countermodels10.lean` |

Each can be present or absent independently. Whether the axioms for each capability are *minimal* remains open.

| Enrichment | What it adds |
|------------|-------------|
| **Branch** | Classifier-controlled dispatch: ρ·x = f·x if τ·x = ⊤, else g·x. Bridges D and H. |
| **Y** | Fixed-point combinator: Y·ρ = ρ·(Y·ρ), Y·ρ non-absorber. Crosses the decidability boundary. |

Branch and Y are not independent capabilities. They connect the three capabilities and add power. Both are irredundant for the full evaluator (SAT-proved).

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

The demo exercises the 16-element coexistence witness: computation on the algebra (S), verification of the Cayley table's invariants (D), and continuation reification + branch swap within a meta-circular evaluator (H). The independence theorem is proved by the six separate counterexamples in the Lean files. See [`docs/artifact.md`](docs/artifact.md) for additional demos.

### Compiled Grounded Reflective Tower

```bash
python3 psi_transpile.py --target rust \
  examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp > /tmp/tower.rs
cp psi_runtime_f.rs /tmp/
rustc -O -o /tmp/tower /tmp/tower.rs
/tmp/tower    # 2.2 ms — same output, 20,000x faster
```

The reflective tower (fibonacci, factorial, table verification, continuation reification, frame walking, branch swap) compiles to a single native binary. An ungrounded (infinite) tower cannot be compiled because each level depends on the one below. A grounded tower can: the compiler bottoms out at the verified Cayley table.

### Compile to Native

```bash
# C backend
python3 psi_supercompile.py examples/psi_counter_known.psi > /tmp/opt.psi
python3 psi_transpile.py /tmp/opt.psi > /tmp/counter.c
gcc -O2 -I. -o /tmp/counter /tmp/counter.c

# Rust backend (self-hosted transpiler, works with either interpreter)
python3 psi_lisp.py --table=c examples/psi_transpile_test.lisp | sed '1d;$d' > /tmp/out.rs
cp psi_runtime.rs /tmp/
rustc -O -o /tmp/out /tmp/out.rs && /tmp/out               # 3 42 99 3 5 5

# Compiled reflective tower
python3 psi_transpile.py --target rust \
  examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp > /tmp/tower.rs
cp psi_runtime_f.rs /tmp/
rustc -O -o /tmp/tower /tmp/tower.rs && /tmp/tower
```

The transpiler handles both computational programs and metaprograms (continuation reification, branch swap). A compile-time symbol table maps each quoted symbol to a stable integer constant. See [`docs/transpiler_gaps.md`](docs/transpiler_gaps.md) for implementation details.

---

## Why It Matters

Kamea is not a new model of computation. It is a structural decomposition of reflective computation into independent capabilities, using finite algebra as a microscope.

**Did you just encode Lisp in a lookup table?** No. We found the *space* of reflective axiom systems, and Lisp is a distinguished point in it. The three capabilities (S, D, H) are irredundant, each corresponding to a standard categorical structure. The specific axiom forms are not unique: composition admits ≥6 variants. But in 4 of 5 alternatives, computational elements cross the classifier wall and become classifiers. The McCarthy realization is the unique form that minimizes the classifier count: it keeps the maximum number of elements in the computational stratum. It is "natural" not by uniqueness proof but by parsimony: don't judge when you can compute.

**Are the axioms natural or engineered?** The *capabilities* are natural, corresponding to standard categorical concepts (section-retraction pair, decidable subobject classifier, partial internal composition). The *specific axiom forms* are conventional; each capability admits multiple presentations. The enrichments (Branch, Y) are the deliberate choices that connect D to H and cross the decidability boundary.

**What's the contribution?** (1) A full independence theorem: R, D, and H are pairwise independent, four of six bounds provably tight. (2) A working artifact: a compiled reflective tower (2.2 ms native) demonstrating all three capabilities plus both enrichments in a single 16-element algebra. (3) Turing completeness via 7 axiom-forced elements, compilation to native code matching hand-written C, and a meta-circular CPS evaluator with continuation reification.

## The Seven Roles

| Ψ | Lisp | Role | Source |
|---|------|------|--------|
| ⊤ | NIL | Empty / base case | S (retraction pair) |
| Q | QUOTE | Freeze a term (constructor) | S (retraction pair) |
| E | EVAL | Unwrap / interpret (destructor) | S (retraction pair) |
| g | CONS | Build a pair (core-preserving) | H (internal composition: storage) |
| f | CAR | First projection | Branch enrichment |
| η | CDR | Second projection | H (internal composition: composite) |
| ρ | COND | Conditional branch | H (internal composition: dispatch) + Branch enrichment |

The correspondence is structural (same role inventory) rather than semantic (Ψ operates on magma elements, Lisp on symbolic lists). The structure is necessarily non-commutative: any magma with two distinct left-absorbers cannot be commutative ([`NoCommutativity.lean`](Kamea/NoCommutativity.lean)).

**What is proved vs. what is convergent.** The *architecture* (three categories: absorbers, classifiers, non-classifiers, with hard walls between them) is a universal theorem: every finite dichotomic retract magma decomposes the same way (112 non-isomorphic models at N=4 all share it). The *specific seven roles* are convergently natural: three independently motivated axiom systems (category-theoretic, game-theoretic, categorical topos), none referencing Lisp, recover the identical 2-1-8-1 distribution. A fourth (information-theoretic) recovers 2-1-9-0, missing inert because it lacks a substrate axiom. The architecture is a theorem; the instantiation is convergent evidence, not a uniqueness proof.

Of the 45 pairwise distinctness requirements, **35 are derived** (32 from categorical axioms + 3 from TC). The remaining **10 are the nontriviality axiom**, analogous to 0 ≠ 1 in a nontrivial ring. Full analysis: [`docs/forced_roles_theorem.md`](docs/forced_roles_theorem.md). Canonicity: [`docs/categorical_canonicity.md`](docs/categorical_canonicity.md).

## Key Results

### Lean-Proved (model-specific, Ψ₁₆ᶠ)

- Rigidity: every injective endomorphism is the identity
- Discoverability: 4 probes identify all 16 elements
- Actuality irreducibility: twin models agree on structure, disagree on classifier assignment
- 35/45 role pairs forced distinct: 32 by categorical axioms + 3 by TC
- 83 operational theorems on the 16×16 table

**What actuality irreducibility means.** Two Cayley tables can agree on every cell except the classifier's response to one element. Both satisfy all structural axioms. Structure does not determine classification: the classifier assignment is independent and not derivable from anything else in the structure.

### SAT and Empirical Results

- Classifier wall: judgment cannot merge with any other role (τ: 9/9 UNSAT) `[SAT]`
- Substrate wall: inert cannot merge with any other role (g: 9/9 UNSAT) `[SAT]`
- TC forces 3 distinctions: Q≠E, Q≠f, f≠η `[Empirical]`
- Reflective tower and composition closure force 0 additional distinctions `[Empirical]`
- 10/45 distinctness pairs are independent of all tested derivation sources `[Empirical]`
- Turing completeness: 7 axiom-forced elements simulate 2CM `[Empirical]`
- Reflective tower: 3 levels, branch swap, grounded continuations `[Empirical]`
- Compilation: compiled Ψ-Lisp matches hand-written C on N-Queens(8) `[Empirical]`
- Compiled reflective tower: 2.2 ms native (20,000x over interpreted) `[Empirical]`
- GC: 10M allocations in 4MB via MMTk `[Empirical]`
- Futamura: all 3 projections demonstrated, fixed-point verified `[Empirical]`
- Extension profiles: Ψ₁₆ᶠ (hardware) and Ψ₁₆ᶜ (software), same core theorems `[Empirical]`
- Self-simulation: universal self-simulator verified on both tables (512/512 cells) `[Empirical]`
- Full axiom stack requires N=12 `[SAT]`

Full claim matrix with reproduction commands: [`CLAIMS.md`](CLAIMS.md). Full technical details: [`docs/technical_overview.md`](docs/technical_overview.md).

---

## The Axiom System

What is the simplest finite structure that can identify its own components through its own operation?

**Structural Ladder (L0–L8)**, forcing the basic role architecture:

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

**Operational Axioms**, forcing specific computational capabilities:

| Axiom | What It Forces |
|-------|----------------|
| **C (Classifier dichotomy)** | Only testers can produce boolean outputs on non-absorbers |
| **D (Inert Propagation)** | Inert elements preserve non-absorber status |
| **PA (Power-Associativity)** | `(x·x)·x = x·(x·x)` for all x |
| **VV (Inert Self-Application)** | Inert self-application yields a tester or encoder |
| **QE (Quote/Eval)** | `E·(Q·x) = x` and `Q·(E·x) = x` on core (mutual inverses) |
| **1-Inert** | Exactly 1 inert element |
| **E-Transparency** | `E·⊤ = ⊤` and `E·⊥ = ⊥` |
| **Branch** | `ρ·x = f·x` if `τ·x = ⊤`, else `ρ·x = g·x` (tester-mediated conditional) |
| **Compose** | `η·x = ρ·(g·x)` (function composition through branch) |
| **Y-Combinator** | `Y·ρ = ρ·(Y·ρ)`, with `Y·ρ ≥ 2` (fixed-point combinator) |
| **Selection** | `η·ρ = τ` (composing then branching yields a judgment) |

**Minimum sizes:**

| What | Min N | What it gives |
|------|-------|---------------|
| S+D+H (three capabilities alone) | **5** | Encoding, classification, evaluation; optimal (ICP needs 3 core elements) |
| S+D+H with sec ≠ ret | **6** | Non-degenerate retraction pair, non-trivial ICP factorization |
| + all roles distinct | **10** | Separated roles |
| + structural ladder + PA + Selection | **12** | Clean 2-1-8-1 architecture, McCarthy correspondence |
| + IO + 8-state counter | **16** | The specific Ψ₁₆ᶠ witness |

The axioms have an equivalent categorical formulation using standard vocabulary: zero morphisms, retraction pairs, subobject classifiers, and the classifier dichotomy. See [`CatKripkeWallMinimal.lean`](Kamea/CatKripkeWallMinimal.lean), [`NoCommutativity.lean`](Kamea/NoCommutativity.lean), and [`CategoricalFoundation.lean`](Kamea/CategoricalFoundation.lean).

The axioms operate at three layers: the **capability layer** (S, D, H) provides the three independent computational capabilities; the **enrichment layer** (Branch, Y) connects them; the **organizational layer** (L3–L8, PA, Selection, 1-Inert) forces the clean role architecture that produces the McCarthy correspondence. Full inevitability analysis: [`docs/inevitability_summary.md`](docs/inevitability_summary.md). H characterization: [`docs/h_characterization.md`](docs/h_characterization.md).

Results fall into four tiers: **Universal** (every model of the axiom class, `[Lean]`/`[SAT]`), **Model-specific** (Ψ₁₆ᶠ only, `[Lean]`), **Empirical** (`[SAT]`/`[Empirical]`), and **Open** (`[Open]`). Full registry: [`CLAIMS.md`](CLAIMS.md).

### How to Read This Repo

**The independence theorem:** [finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence) (separate repo, self-contained)

**The artifact** (this repo: the 16-element witness and its consequences)
- [`psi_repl.py`](psi_repl.py) — Interactive Ψ-Lisp REPL
- [`examples/psi_reflective_tower.lisp`](examples/psi_reflective_tower.lisp) — Three-level reflective tower
- [`Kamea/Psi16Full.lean`](Kamea/Psi16Full.lean) — 83 operational theorems + rigidity/discoverability/irreducibility
- [`psi_star.py`](psi_star.py) — Turing-completeness: 2CM simulation via 7 axiom-forced elements
- [`psi_lisp.py`](psi_lisp.py) — Ψ-Lisp → Ψ∗ transpiler (McCarthy 1960 conventions)
- [`examples/psi_metacircular.lisp`](examples/psi_metacircular.lisp) — Defunctionalized CPS meta-circular evaluator
- [`kamea-rs/`](kamea-rs/) — Rust emulator + WASM browser debugger (~25x faster)
- [`examples/psi16_corrupted_host_demo.py`](examples/psi16_corrupted_host_demo.py) — Animated TUI: watch one wizard heal another
- [`docs/psi_framework_summary.md`](docs/psi_framework_summary.md) — Full axiom search results and Cayley tables

**Compilation and performance**
- [`psi_supercompile.py`](psi_supercompile.py) — Partial evaluator: constant folding + QE cancellation + branch elimination
- [`psi_transpile.py`](psi_transpile.py) — Supercompiled Ψ∗ → C/Rust transpiler
- [`examples/psi_futamura.psi`](examples/psi_futamura.psi) — Futamura projection demo (all 3 projections, fixed point verified)
- [`examples/psi_transpile.lisp`](examples/psi_transpile.lisp) — Self-hosted transpiler: Ψ-Lisp → Rust
- [`psi_blackbox.py`](psi_blackbox.py) — Black-box recovery (3 methods, 100% on 1M seeds)

---

## What Is Not Proved

- **Uniqueness of Ψ₁₆ᶠ.** The Cayley table is one model. The axioms constrain roles and relationships but leave 192/256 cells free at N=16 (25.0% determination). Cell-by-cell freedom analysis: `ds_search/n16_freedom.py`.
- **Role uniqueness (resolved: not unique, but selected by classifier minimality).** Compose admits ≥6 variants. In 4 of 5 alternatives, computational elements cross the classifier wall. The McCarthy realization (η = ρ∘g) is the unique form that minimizes classifier count. Whether classifier minimality is equivalent to a known categorical property is open.
- **Minimality from base axioms.** Abstract axiom limitation theorems show base DirectedDS axioms imply only `card ≥ 2` (tight). What forcing conditions derive the full structure from first principles remains open.
- **Self-modeling vs discriminability.** Nearly all rigid magmas are WL-1 discriminable without self-modeling. Self-modeling adds interpretability: elements have roles (classifier, transformer, substrate), not just unique fingerprints. Whether interpretability is necessary for reflective computation is open.
- **Extension profile optimality.** Ψ₁₆ᶠ and Ψ₁₆ᶜ are two points in the extension design space. Whether either is optimal is unexplored.
- **Distinctness: 78% derived, 22% axiomatic.** Of 45 distinctness requirements, 35 are derived (32 categorical + 3 TC). The remaining 10 have been exhaustively tested against categorical axioms, TC, composition closure, and the full reflective tower. All 10 survive; they are the nontriviality axiom.
- **No canonical object.** Ψ₁₆ᶠ is not initial, terminal, or otherwise universal in the category of dichotomic retract magmas (112 non-isomorphic models exist at N=4). The canonicity lies at the theory level: the three-class decomposition is a proved functorial invariant ([`Functoriality.lean`](Kamea/Functoriality.lean)). See [`docs/categorical_canonicity.md`](docs/categorical_canonicity.md).

---

## Related Work

Boba's Tower sits at one end of an architectural fork in reflective language design.

Smith's 3-Lisp (1984) introduced the reflective tower — an infinite chain of meta-interpreters, each interpreting the one below. Subsequent implementations (Black, Brown, Blond) added live meta-modification: `(set! base-eval ...)` changes how the running interpreter works. Amin and Rompf (POPL 2018) showed how to compile user programs *through* the tower via stage polymorphism, collapsing multiple interpretation levels into efficient generated code.

All of these systems use higher-order continuations — opaque closures that can be invoked and composed but not inspected. Boba's Tower uses defunctionalized continuations — tagged data structures that can be walked, inspected frame by frame, and modified field by field. This is the architectural fork, and it is forced by whether the tower terminates.

An infinite tower cannot be defunctionalized — there are infinitely many continuation types. A grounded tower must be — there is no closure to hide behind; the bottom is data. Therefore: grounded → finite continuation types → defunctionalization → transparency → the branch swap. And symmetrically: infinite → closures → opacity → live meta-modification. The transparency of our continuations and the opacity of theirs are consequences of the same design choice.

| System | Tower | Continuations | Headline result |
|--------|-------|---------------|-----------------|
| Smith (1984) | Infinite | — | Reflective tower concept |
| Black/Brown/Blond | Infinite | Opaque closures | Live `set! base-eval` |
| Amin & Rompf (POPL 2018) | Collapsible | Opaque closures | Compile through the tower |
| **Boba's Tower** (ours) | **Grounded (256 bytes)** | **Tagged data** | **Compile the tower itself** |

What they have that we don't: live meta-interpreter modification (`set! base-eval`), infinite tower levels, compilation under modified semantics. What we have that none of them do: walkable continuations (the branch swap), a compiled tower (2.2 ms native), formal verification (106+ Lean theorems, zero `sorry`), and runtime substrate verification. See [`docs/related_work.md`](docs/related_work.md) for the full comparison.

**Algebraic models of computation.** The tradition of studying computation through finite algebraic structures includes Minsky's register machines, Shepherdson and Sturgis's work on computability via algebraic operations, and the algebraic approach to CSP (constraint satisfaction problems) pioneered by Jeavons, Bulatov, and others. Our magmas are not register machines — they are closer to the action of a monoid on itself via left-multiplication. The connection is that the Cayley table of a finite magma *is* the complete specification of the operation, and the structural properties of that table (retraction pairs, classifier dichotomy, internal composition) determine which computational capabilities the algebra supports. The algebraic CSP program studies which algebraic structures make constraint problems tractable; our program studies which algebraic structures make reflective computation possible.

**Self-execution and Futamura projections.** Our capability H (self-execution) is related to the Futamura projections: specializing an interpreter with respect to a program yields a compiled program (projection 1), specializing a specializer with respect to an interpreter yields a compiler (projection 2), and specializing a specializer with respect to itself yields a compiler generator (projection 3). The compiled reflective tower in the artifact is projection 1 applied to the meta-circular evaluator. The connection to H is that self-execution is the algebraic precondition for these projections: without internal composition, the algebra cannot represent the specialization step, and the projections require an external machine. With H, the algebra provides its own evaluator, and compilation becomes possible.

---

## Performance

Primary benchmark: N-Queens(8), backtracking search with cons-cell lists (92 solutions). This stresses allocation, recursion, and branching, and cannot be constant-folded.

**N-Queens(8)** (backtracking with cons/car/cdr, per call):

| Implementation | Time/call | vs C baseline |
|----------------|----------|---------------|
| **C** (gcc -O2, bump allocator) | 98 µs | 1x |
| **Compiled Ψ-Lisp → C** (gcc -O2, bump) | 86 µs | **0.9x** |
| **Compiled Ψ-Lisp → Rust** (LLVM -O, bump) | 114 µs | 1.2x |
| **Rust + MMTk Immix** (32 MB heap) | 184 µs | 1.9x |
| **Rust + MMTk Immix** (4 MB heap) | 186 µs | 1.9x |
| **LuaJIT** | 220 µs | 2.2x |
| **SBCL** (native Common Lisp) | 432 µs | 4.4x |
| **Native Python** | 5.9 ms | 60x |
| **Ψ-Lisp (Rust interpreter)** | 4.1 s | 42,000x |
| **Ψ-Lisp (Python interpreter)** | 301 s | 3,100,000x |

Compiled Ψ-Lisp with the bump allocator matches hand-written C. With MMTk Immix (a real mark-region garbage collector), it beats LuaJIT. The bump allocator advantage is ~2x: the difference between a pointer increment and Immix's alloc path + side metadata. The 4 MB and 32 MB heaps perform identically because nqueens has a small live set (the placed-queens list is at most 8 cells deep), so collection pressure is negligible. The entire compilation pipeline is ~1,100 lines: a 312-line supercompiler, a 640-line transpiler, and a 121-line C runtime whose core is a 256-byte array.

**Counter arithmetic** (fib(8) + fib-iter(30) + fact(10) + power(2,10) + gcd(100,75), runtime inputs via argv):

| Implementation | Time/iter | vs C baseline |
|----------------|----------|---------------|
| **Rust** (native, LLVM -O) | 0.002 µs | 0.1x |
| **C** (gcc -O2) | 0.016 µs | 1x |
| **LuaJIT** | 0.17 µs | 10x |
| **SBCL** | 0.20 µs | 13x |

This workload involves no allocation, so the GC/bump distinction is irrelevant. The compiled Ψ-Lisp transpiler emits literal constants in `main()`, so gcc constant-folds the entire computation (~0.01 µs). The table above uses runtime inputs (argv) for a fair comparison. Full performance analysis: [`docs/technical_overview.md#10-performance`](docs/technical_overview.md#10-performance).

**Grounded reflective tower** (meta-circular evaluator: fib(8) + fact(10) + table verification + reify/reflect + branch swap):

| Implementation | Time | vs Compiled |
|----------------|------|-------------|
| **Compiled tower** (rustc -O) | 2.2 ms | 1x |
| **Ψ-Lisp (Python interpreter)** | ~43 s | ~20,000x |

The compiled tower is not about benchmark speed. It's about having the meta-circular evaluator as compiled Rust with continuations as data, the Cayley table verified at runtime, and branch swap via continuation modification, all in a single native binary.

---

## Repository Structure

```
├── Kamea/
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
│   ├── PsiCountermodels.lean            # Tight 4-element countermodel
│   ├── SelfSimulation.lean              # Self-simulation: partial application injectivity (4 universal theorems)
│   ├── CategoricalFoundation.lean       # CatEndoMagma: categorical vocabulary for full N=16
│   ├── CatKripkeWall.lean               # Abstract classifier wall + dichotomy theorems
│   ├── CatKripkeWallMinimal.lean        # FaithfulRetractMagma + DichotomicRetractMagma: N=4/5 witnesses + 16 universal theorems
│   ├── NoCommutativity.lean             # Asymmetry: two left-absorbers ⇒ non-commutative (3-line proof)
│   ├── CatWitness.lean                  # N=16 witness as CatEndoMagma (satisfiability)
│   ├── CatForcedDistinctness.lean       # 32 forced-distinct pairs on N=16 witness
│   ├── CatRigidity.lean                 # Rigidity of N=16 categorical witness
│   ├── CatDiscoverable.lean             # 4-probe discoverability of N=16 witness
│   ├── CatActualityIrreducibility.lean  # Twin-model actuality irreducibility
│   ├── E2PM.lean                        # Ext2PointedMagma: D⊬S (N=5), H⊬S (N=6), structural S⊬H (N=6)
│   ├── ICP.lean                         # Internal Composition Property: ICP ↔ Compose+Inert (universal)
│   ├── Countermodels10.lean             # D⊬H, H⊬D: N=10 counterexamples
│   ├── Witness5.lean                    # Optimal S+D+H coexistence at N=5 + no ICP at N=4
│   ├── Witness6.lean                    # S+D+H coexistence at N=6 with sec≠ret
│   ├── Witness10.lean                   # S+D+H at N=10 with all roles distinct
│   ├── SelfSim5.lean                    # Self-simulation at N=5 (sim term = classifier)
│   ├── SelfSim6.lean                    # Self-simulation at N=6 (sim term = retraction)
│   ├── SelfSimulation.lean              # Universal: partial application injectivity
│   └── legacy/                          # Historical Δ₁/Δ₂/Δ₃ proofs (superseded by Ψ₁₆)
├── kamea-rs/                             # Rust emulator + WASM browser debugger
│   ├── crates/
│   │   ├── psi-core/                     # The algebra — #![no_std], zero deps
│   │   │   └── src/
│   │   │       ├── table.rs              # 16×16 Cayley table as const array
│   │   │       ├── term.rs               # Term enum + arena allocator
│   │   │       └── eval.rs               # Explicit-stack Ψ∗ evaluator
│   │   ├── psi-runtime/                  # The machine — heap, IO, Ψ-Lisp
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
│   │   ├── wispy-stress/                 # GC stress test (10M allocs in 4MB heap)
│   │   │   └── src/main.rs
│   │   └── wispy-bench/                  # N-Queens + counter arithmetic with MMTk GC
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
│   ├── psi_self_simulator.lisp       # Self-simulators: brute-force (256 cells) + role-aware (60/256 algebraic)
│   ├── psi_hello_world.lisp          # Ψ-Lisp hello world example
│   ├── psi_counter_known.psi          # Supercompiler test: known-base counter increments
│   ├── psi_counter_free.psi           # Supercompiler test: free-variable counter
│   ├── psi_branch_test.psi            # Supercompiler test: branch elimination
│   ├── psi_fold_constants.lisp        # Supercompiler test: constant folding
│   ├── psi_futamura.psi              # Futamura projection demo (10 test cases, Ψ₁₆ᶜ)
│   ├── psi_specialize.lisp           # Ψ-Lisp specializer: Futamura projections 1 & 2
│   ├── psi_transpile.lisp            # Self-hosted transpiler: Ψ-Lisp IR → Rust code
│   ├── psi_transpile_test.lisp       # Transpiler test harness (6 expression types)
│   └── psi_*.lisp                    # Ψ-Lisp test programs (fibonacci, recursion, etc.)
├── ds_search/
│   ├── axiom_explorer.py             # Core encoder: encode_level(), classify_elements()
│   ├── stacking_analysis.py          # All Ψ analysis functions (~17k lines)
│   ├── substrate_analysis.py         # Substrate/stacking analysis
│   ├── n16_freedom.py                # Ψ₁₆ᶠ cell-by-cell SAT freedom analysis
│   ├── n16_c_interop.py              # Ψ₁₆ᶜ SAT search + freedom analysis
│   ├── forced_roles_test.py           # Layer 1: 45 pairwise role-aliasing tests (forced categories)
│   ├── collapse_rigidity_test.py     # Layer 2: rigidity at 6 collapse levels (universal rigidity)
│   ├── distinctness_test.py            # Distinctness axiom: 32 forced + 13 added, SAT at N=12/16
│   ├── compositional_expressiveness.py # Expressiveness justification for distinctness (monotone)
│   ├── collapse_model_count.py       # Model diversity at maximal collapse (20+ models, all rigid)
│   ├── axiom_archaeology.py          # Axiom removal + new axiom candidates (Direction 1 & 3)
│   ├── axiom_archaeology_deep.py     # Composition wall detail, redundancy, max removable set
│   ├── alternative_axioms.py         # Alternative axiom systems (Direction 2)
│   ├── categorical_topos.py          # Genuine categorical endomorphism magma axioms
│   ├── inert_expressiveness.py       # Substrate expressiveness analysis (inert count vs discoverability)
│   ├── n16c_expressiveness_search.py # Ψ₁₆ᶜ table search (maximally expressive model)
│   ├── tc_merge_test.py              # DEPRECATED: tests Ext, not role forcing (see forced_roles_test.py)
│   ├── n5_rdh_unsat.py               # N=5 R+D+H SAT verification + algebraic analysis
│   ├── n5_rdh_check.py               # N=5 R+D+H Z3 SAT check
│   ├── counterexample_search.py      # WL-1 discrimination tests
│   ├── composition_closure_test.py    # Composition closure: compatible but kills 0/10 pairs
│   ├── reflection_distinctness_test.py # Reflective tower test on 10 nontriviality pairs (0/10 killed)
│   ├── kripke_canonicity.py           # DRMag enumeration + homomorphism search (112 iso classes at N=4)
│   ├── rigid_census.py               # Small rigid magma census
│   └── counterexamples/              # Saved counterexample tables (.npy)
├── paper/
│   ├── main-lics.tex                  # LICS submission (double-blind)
│   └── arxiv-preprint/
│       ├── main.tex                   # arXiv preprint (de-anonymized)
│       └── main.pdf                   # Rendered 10-page PDF
├── docs/
│   ├── technical_overview.md          # Full technical details (moved from README)
│   ├── forced_roles_theorem.md        # The Forced Roles Theorem (core theoretical result)
│   ├── inevitability_summary.md      # Three-layer inevitability argument (definitive synthesis)
│   ├── axiom_inevitability.md        # Detailed evidence for inevitability layers
│   ├── axiom_archaeology_results.md  # Raw axiom removal/alternative system data
│   ├── forced_roles.md               # Forced categories: raw SAT data + necessity analysis
│   ├── psi_framework_summary.md      # Comprehensive Ψ framework reference
│   ├── extension_profiles.md         # Ψ₁₆ᶠ vs Ψ₁₆ᶜ: modular extension architecture
│   ├── transpiler_gaps.md            # Transpiler implementation: symbol encoding, arena threading, compiled tower
│   ├── categorical_canonicity.md      # Canonicity analysis: no canonical object, canonical theory
│   ├── self_simulation_necessity.md  # Self-simulation derivation: which axioms are necessary?
│   ├── h_characterization.md         # H as factorable action: ICP characterization + 250-model validation
│   ├── related_work.md               # Grounded tower vs Smith/Black/Blond/LMS-Black: the architectural fork
│   ├── continuation_protocol.md      # Continuation protocol documentation
│   └── minimal_model.md              # Minimal model notes
├── h_characterization_final.py       # H characterization: ICP validation across 250 models
├── universal_self_simulator.py       # Universal self-simulator: one program, any Ψ model
├── self_simulation_investigation.py  # 4-phase self-simulation necessity investigation
├── psi_star.py                       # Ψ∗ TC proof: 2CM simulation via 7 axiom-forced elements
├── psi_star_c.py                     # Ψ∗ term algebra over Ψ₁₆ᶜ (C-interop table)
├── psi_lisp.py                       # Ψ-Lisp → Ψ∗ transpiler (McCarthy 1960 conventions)
├── psi_supercompile.py               # Partial evaluator: 2–5 pass supercompiler (table-dependent)
├── psi_transpile.py                  # Ψ-Lisp → C/Rust transpiler (--target c|rust)
├── psi_runtime.h                     # C runtime for Ψ₁₆ᶠ: 256-byte table + inline dot
├── psi_runtime_c.h                   # C runtime for Ψ₁₆ᶜ: table + arithmetic helpers
├── psi_runtime.rs                    # Rust runtime for Ψ₁₆ᶜ: table + Arena (bump allocator)
├── psi_runtime_f.rs                  # Rust runtime for Ψ₁₆ᶠ: table + Arena (default for transpiler)
├── bench_c_interop.py                # Benchmark: Ψ₁₆ᶜ vs Ψ₁₆ᶠ comparison
├── psi_blackbox.py                   # Ψ₁₆ᶠ black-box recovery (3 methods)
├── psi_repl.py                       # Interactive Ψ-Lisp REPL
├── CLAIMS.md                         # Claim status registry
└── README.md
```

## Building

`lake build` compiles all Lean files: the independence structure (90 theorems across 13 files) and the Ψ-specific operational proofs (130+ theorems on the 16-element table in `Psi16*.lean`). Zero `decide` on universal theorems. Zero `sorry` across all files.

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

# Rust interpreter (requires rustup: https://rustup.rs)
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

# WASM browser debugger (requires wasm-pack: https://rustwasm.github.io/wasm-pack/)
cd kamea-rs/crates/psi-web
wasm-pack build --target web                                   # build WASM (124KB)
python3 -m http.server 8080 --directory www                    # serve debugger UI
# → open http://localhost:8080
```

Lean proofs use two techniques: universal theorems (`CatKripkeWallMinimal.lean`, `PsiUniversalBounds.lean`) use pure algebraic reasoning with no `decide` or `native_decide`. Model-specific theorems (`Psi16*.lean`, `Cat*.lean`) use `decide` or `native_decide`, appropriate and complete for finite carrier types with decidable equality. Zero `sorry` across all files.

All Ψ-Lisp test programs produce identical output across Python, compiled C, compiled Rust, Rust interpreter, and WASM.

---


## License

MIT

## Citation

If you use this work, please cite:

```bibtex
@software{palmieri2025kamea,
  author = {Palmieri, Stefano},
  title = {Kamea: A Compiled Reflective Tower from a 256-Byte Cayley Table},
  year = {2025},
  url = {https://github.com/stefanopalmieri/Kamea}
}
```

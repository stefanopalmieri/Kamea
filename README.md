# Kamea

A structural decomposition of reflective computation into independent capabilities, witnessed by finite algebras and proved by universal theorems over algebraic varieties.

**Three capabilities. Three walls. Seven roles. Zero `sorry`.**

*A finite algebra can simulate itself without describing itself. It can describe itself without internalizing its evaluator. It can internalize its evaluator without describing itself. No capability implies any other.*

### For Reviewers

1. **Definitions**: S (self-simulation) = retraction pair; D (self-description) = classifier dichotomy; H (evaluator internalization) = factorable action (Internal Composition Property)
2. **Independence theorem**: S ⊬ D, D ⊬ H, H ⊬ D, S ⊬ H — all four non-trivial directions Lean-proved (`Countermodel.lean`, `Countermodels10.lean`). The two remaining directions (D → S, H → S) are trivial: the Lean formalization builds D and H on top of FRM, so both include a retraction pair by construction.
3. **Tight bound**: N=10 is necessary (counting) and sufficient (Lean witness in `Witness10.lean`)
4. **Decomposition invariance**: three-category decomposition preserved by homomorphisms (`Functoriality.lean`)
5. **Proof inventory**: 7 files, 55 theorems, zero `sorry` — verify with `lake build`

<p align="center">
  <img src="melencolia.png" width="250" alt="Albrecht Dürer — Melencolia I (1514)" />
</p>
<p align="center"><sub>In loving memory of Boba</sub></p>

Kamea separates three independent capabilities of reflective computation — self-simulation, self-description, and evaluator internalization — and shows that no capability implies any other (proved by concrete counterexamples). The core theorem is witnessed minimally at N=10. A richer 16×16 table supports the artifact: a reflective tower, compilation, and operational demos.

## The Three Capabilities

Self-simulation, self-description, and evaluator internalization are three independent capabilities. No capability implies any other — proved by concrete finite counterexamples at every boundary and every diagonal. Each can be present or absent independently. Whether the axioms for each capability are *minimal* (whether fewer or different axioms could achieve the same structural effect) remains open.

| Capability | Presentation-independent definition | Witnesses (one presentation) | Independence |
|------------|-------------------------------------|------------------------------|--------------|
| **Self-simulating (S)** | Retraction pair on core | Q (section), E (retraction) | `[Lean]` `SelfSimulation.lean` |
| **Self-describing (D)** | Classifier dichotomy — every non-zero is all-boolean or all-non-boolean on core | τ (classifier), Kripke wall | `[Lean]` `Countermodel.lean`, `Countermodels10.lean` |
| **Evaluator internalization (H)** | Factorable action — some element's row on core factors non-trivially as c ∘ b with b core-preserving | η (composite), g (storage), ρ (dispatch) | `[Lean]` `Countermodels10.lean` |

All three are single-concept definitions. None references specific element names. The witnesses (Q/E, τ, η/g/ρ) are one presentation; each capability admits multiple axiom forms.

| Enrichment | What it adds | Bridges |
|------------|-------------|---------|
| **Branch** | Classifier-controlled dispatch: ρ·x = f·x if τ·x = ⊤, else g·x | Connects D (classification) to H (evaluation) |
| **Y** | Fixed-point combinator: Y·ρ = ρ·(Y·ρ), Y·ρ non-absorber | Crosses the decidability boundary (bounded → unbounded recursion) |

Branch and Y are not independent capabilities — they are enrichments that connect the three capabilities and add power. Branch bridges D and H: the classifier's judgment controls the evaluator's dispatch. Y crosses the decidability boundary: without it, evaluation is bounded (finite case analysis suffices); with it, the algebra supports unbounded recursion. Both are irredundant for the full evaluator (SAT-proved) and necessary for the reflective tower artifact.

**Full independence.** No capability implies any other. Four non-trivial directions (D and H both include S by construction, so D→S and H→S are definitional):

| | S ⊬ D | D ⊬ H | H ⊬ D | S ⊬ H |
|---|---|---|---|---|
| **Counterexample** | N=8 (the Countermodel) | N=10 (no factorable action) | N=10 (diagonal) | N=4 (`kripke4`) |
| **What it shows** | Self-simulates, no clean roles | Has dichotomy, no composition factors | Has factorable action, no dichotomy | Has retraction pair, too small for H |
| **Proof** | `[Lean]` | `[Lean]` | `[Lean]` | `[Lean]` (trivial: H needs N≥10) |

The classifier wall is not forced by computation — an N=8 counterexample self-simulates without it, and an N=10 counterexample has a factorable action (the evaluation core) without it. An algebra can *evaluate* without *understanding itself as evaluating*.

(The classifier dichotomy is analogous in spirit to a grounded/ungrounded separation [Kripke 1975], but here it is a total finite algebraic condition rather than a partial transfinite construction. See [`docs/categorical_reconstruction.md`](docs/categorical_reconstruction.md) for the categorical analysis.)

The Ψ₁₆ᶠ table has all three capabilities at once. The demo below exercises all of them: the table computes itself (S), the classifier wall gives elements interpretable roles (D), and the meta-circular evaluator runs within the algebra with no external machine (H).

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

The demo exercises all three capabilities: computation on the algebra (S), verification of the Cayley table's invariants (D), and continuation reification + branch swap within a meta-circular evaluator (H). The reflective stack is grounded in a 16×16 verified Cayley table — the table is not an implementation of the algebra, it is the algebra. See [`docs/artifact.md`](docs/artifact.md) for the full artifact description and additional demos.

### Compiled Boba's Tower

```bash
python3 psi_transpile.py --target rust \
  examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp > /tmp/tower.rs
cp psi_runtime_f.rs /tmp/
rustc -O -o /tmp/tower /tmp/tower.rs
/tmp/tower    # 2.2 ms — same output, 20,000x faster
```

Boba's Tower — fibonacci, factorial, table verification, continuation reification, frame walking, branch swap — compiles to a single native binary. 2.2 ms compiled vs ~43 s interpreted. The 256-byte Cayley table is embedded in the binary and verified at runtime. An ungrounded tower cannot be compiled because each level depends on the one below. A grounded tower can — the compiler bottoms out at the verified Cayley table.

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

# Compile the reflective tower to native (meta-circular evaluator as compiled Rust)
python3 psi_transpile.py --target rust \
  examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp > /tmp/tower.rs
cp psi_runtime_f.rs /tmp/
rustc -O -o /tmp/tower /tmp/tower.rs && /tmp/tower
```

The transpiler handles both computational programs (arithmetic, recursion, branching, list operations) and metaprograms (programs that construct and manipulate source code as data). The reflective tower — a meta-circular evaluator that builds S-expressions, reifies continuations, and modifies its own control flow — compiles to a single native binary via `psi_transpile.py --target rust`. The compiled tower produces identical output to the interpreted tower in 2.2 ms (vs ~43 s interpreted), a ~20,000x speedup. The 256-byte Cayley table is embedded in the binary and verified at runtime. A compile-time symbol table maps each quoted symbol to a stable integer constant, matching the interpreter's `_symbol_to_term` encoding. See [`docs/transpiler_gaps.md`](docs/transpiler_gaps.md) for the implementation details.

---

## Why It Matters

Kamea is not a new model of computation. It is a structural decomposition of reflective computation into independent capabilities, using finite algebra as a microscope — not proposing it as a replacement for lambda calculus.

Many reflective systems combine mechanisms that this framework separates into three capabilities and two enrichments. The framework shows what each costs: a retraction pair (naming), the classifier dichotomy (judging), and a factorable action (evaluating) — plus two enrichments that connect them: Branch (classifier-controlled dispatch) and Y (unbounded recursion). All three capabilities have single-concept, presentation-independent definitions; all three are proved independent. The three-category architecture (zeros, classifiers, non-classifiers) and the walls between categories are proved universal. The specific seven roles are one realization within an equivalence class — each capability admits multiple axiom forms (≥6, ≥4, ≥3), and the McCarthy realization is the unique form that minimizes the classifier count. Full analysis: [`docs/inevitability_summary.md`](docs/inevitability_summary.md), [`docs/categorical_reconstruction.md`](docs/categorical_reconstruction.md), [`docs/h_characterization.md`](docs/h_characterization.md).

The 16×16 table, the compiled tower, Turing completeness, and performance benchmarks are the *artifact* — a witness demonstrating that all three capabilities can coexist. The artifact demonstrates feasibility; the independence theorem is the primary contribution.

### Frequently Asked Questions

**Did you just encode Lisp in a lookup table?** No. We found the *space* of reflective axiom systems, and Lisp is a distinguished point in it. The three capabilities (S, D, H) are irredundant — each is a single abstract property (retraction pair, classifier dichotomy, factorable action). The two enrichments (Branch, Y) connect them. The specific axiom forms are not unique: composition admits ≥6 variants. But the variants are not equal: in 4 of 5 alternatives, computational elements cross the classifier wall and become classifiers. The McCarthy realization is the unique form that minimizes the classifier count — it keeps the maximum number of elements in the computational stratum. It is "natural" not by uniqueness proof but by a parsimony principle: don't judge when you can compute.

**Are the axioms natural or engineered?** The *capabilities* are natural — they correspond to standard categorical concepts (section-retraction, decidable subobject classifier, partial internal composition). Each has a presentation-independent definition: S is a retraction pair, D is the classifier dichotomy, H is a non-trivial factorable action — the existence of an element whose row on core factors as the composition of two other elements' actions, one core-preserving. The *specific axiom forms* are conventional — each capability admits multiple presentations. Even Compose admits 6 equivalent forms; the choice η·x = ρ·(g·x) is the one that minimizes the classifier count. The enrichments (Branch, Y) are the deliberate choices that connect D to H and cross the decidability boundary.

**What's the contribution?** (1) An independence theorem: self-simulation, self-description, and evaluator internalization are three independent capabilities of reflective computation — no capability implies any other, proved by Lean-verified finite counterexamples (N=8, N=10). All three have single-concept, presentation-independent definitions. (2) A tight coexistence bound: N=10 is both necessary and sufficient for all three capabilities, proved from both directions. (3) Thirty universal algebraic theorems (zero `decide`, zero `sorry`) establishing the decomposition, its invariance under homomorphisms, asymmetry, and self-simulation injectivity. (4) A working artifact: a compiled reflective tower (2.2 ms native) demonstrating all three capabilities plus both enrichments in a single 16-element algebra.

## The Seven Roles

| Ψ | Lisp | Role | Source |
|---|------|------|--------|
| ⊤ | NIL | Empty / base case | S (retraction pair) |
| Q | QUOTE | Freeze a term (constructor) | S (retraction pair) |
| E | EVAL | Unwrap / interpret (destructor) | S (retraction pair) |
| g | CONS | Build a pair (core-preserving) | H (factorable action: storage) |
| f | CAR | First projection | Branch enrichment |
| η | CDR | Second projection | H (factorable action: composite) |
| ρ | COND | Conditional branch | H (factorable action: dispatch) + Branch enrichment |

The correspondence is structural (same role inventory) rather than semantic (the domains differ: Ψ operates on magma elements, Lisp on symbolic lists). S gives quote/eval. H gives the factorable action — g stores, ρ dispatches, η composes — enabling pair construction and sequential evaluation. The Branch enrichment connects D's classifier to H's dispatcher, giving ρ its conditional behavior. The roles fall out of the capabilities and enrichments.

The structure is necessarily non-commutative: any magma with two distinct left-absorbers cannot be commutative (three-line Lean proof in [`NoCommutativity.lean`](Kamea/NoCommutativity.lean)).

**What is proved vs. what is convergent.** The *architecture* — three categories (absorbers, classifiers, non-classifiers) with hard walls between them — is a universal theorem: every finite dichotomic retract magma decomposes the same way (112 non-isomorphic models at N=4 all share the decomposition). The *specific seven roles* within that architecture are not proved to be the unique decomposition. They are, however, convergently natural: three independently motivated axiom systems (category-theoretic, game-theoretic, categorical topos) — none referencing Lisp or McCarthy — recover the identical 2-1-8-1 category distribution (2 absorbers, 1 tester, 8 encoders, 1 inert). A fourth system (information-theoretic) recovers the same categories and walls but a 2-1-9-0 distribution, missing inert because it lacks an axiom forcing substrate. Whether an alternative axiom set could produce a different functional decomposition within the same three categories — say, different primitives that are not quote/eval/cons/car/cdr/cond but achieve the same computational power — is open. The architecture is a theorem; the specific instantiation is convergent evidence, not a uniqueness proof.

Of the 45 pairwise distinctness requirements among the ten role-bearing elements, **35 are derived theorems** (32 from categorical axioms + 3 from Turing completeness). The remaining **10 are the nontriviality axiom** — as 0 ≠ 1 in a nontrivial ring. Full analysis: [`docs/forced_roles_theorem.md`](docs/forced_roles_theorem.md). Canonicity: [`docs/categorical_canonicity.md`](docs/categorical_canonicity.md).

## Key Results

### Paper 1: The Independence Structure (self-contained)

55 theorems across 7 Lean files. Zero `sorry`. A reviewer does not need to look at the 16-element table, the Lisp implementation, or the reflective tower to evaluate the core claim. Those are supporting material and motivation, not load-bearing walls.

**The decomposition exists** ([`CatKripkeWallMinimal.lean`](Kamea/CatKripkeWallMinimal.lean), [`NoCommutativity.lean`](Kamea/NoCommutativity.lean)):
- Three-category decomposition: every element is a zero morphism, classifier, or non-classifier `[Lean, universal]`
- classifier wall: classifier ∩ non-classifier = ∅ `[Lean, universal]`
- Retraction pair members are non-classifiers `[Lean, universal]`
- No right identity in any model `[Lean, universal]`
- Card ≥ 4 (tight); card ≥ 5 when sec ≠ ret (tight) `[Lean, universal]`
- Asymmetry: two distinct left-absorbers ⇒ non-commutative `[Lean, universal]`

**It's invariant** ([`Functoriality.lean`](Kamea/Functoriality.lean)):
- DRM isomorphisms preserve zeros, classifiers, and non-classifiers `[Lean, algebraic, no decide]`
- Combined: the three-category decomposition is a proved algebraic invariant `[Lean, algebraic]`

**Self-simulation forces injectivity** ([`SelfSimulation.lean`](Kamea/SelfSimulation.lean)):
- Partial application injectivity: the self-simulator cannot compress the encoding `[Lean, universal]`
- Encoding injectivity: Q-depth encoding is injective `[Lean, universal]`
- Row determination: equal partial applications ⇒ identical rows `[Lean, universal]`

**The three capabilities are independent** ([`Countermodel.lean`](Kamea/Countermodel.lean), [`Countermodels10.lean`](Kamea/Countermodels10.lean)):
- S ⊬ D: N=8 FRM with classifier that violates classifier dichotomy `[Lean, by decide]`
- D ⊬ H: N=10 DRM satisfying classifier dichotomy where no non-trivial factorable action exists `[Lean, by native_decide]`
- H ⊬ D: N=10 FRM with factorable action (Compose+Inert+Branch+Y) that violates classifier dichotomy `[Lean, by native_decide]`
- S ⊬ H: N=4 DRM (trivial — H needs N ≥ 10) `[Lean, by decide]`

**Tight bound** ([`Witness10.lean`](Kamea/Witness10.lean)):
- S+D+H coexist at N=10: concrete witness is a DRM with factorable action + Branch + Y `[Lean, by native_decide]`
- N=10 is optimal: 10 distinct distinguished elements need N ≥ 10 (counting) `[trivial]`

**Partial minimality** (`axiom_irredundancy_test.py`):
- Each capability's axiom set is irredundant — no axiom is derivable from the others `[SAT]`
- S = {retraction pair, E-transparency}: both irredundant
- D = {classifier dichotomy}: single axiom
- H = {Compose, Inert}: the factorable action core (2 axioms, equivalent to the Internal Composition Property)
- Enrichments = {Branch, Y}: both irredundant over S+D+H
- Total: 5 capability axioms + 2 enrichment axioms = 7 irredundant axioms

### Paper 2: The Artifact (supporting material)

Proved for the specific 16-element table by `decide`/`native_decide`. These are properties of one model, not universal theorems — they motivate the independence structure but are not load-bearing for the core claim.

- Rigidity: every injective endomorphism is the identity `[Lean]`
- Discoverability: 4 probes identify all 16 elements `[Lean]`
- Actuality irreducibility: twin models agree on structure, disagree on classifier assignment `[Lean]`

  **What actuality irreducibility means.** Two Cayley tables can agree on every cell except the classifier's response to one element. Both satisfy all structural axioms. Both are valid models. But they disagree on judgment — one classifies a given element as "true," the other classifies it as "false."

  The theorem says: structure does not determine classification. Three ways to read this:

  - *Philosophically*: the table's structure is phenomenal; the classifier assignment is noumenal. What counts as "actual" is not recoverable from observed structure.
  - *Computationally*: a well-typed program can produce different runtime behavior depending on which twin model it runs on. The type system underdetermines execution.
  - *Informationally*: the table is a channel; the classifier is a message. The channel doesn't determine the message. Additional information is irreducible.

  The classifier isn't arbitrary — both twins satisfy the axioms. It's *independent*: not derivable from anything else in the structure.

- 35/45 role pairs forced distinct: 32 by categorical axioms + 3 by TC `[Lean + Empirical]`
- 83 operational theorems on the 16×16 table `[Lean]`

### SAT and Empirical Results

- classifier wall: judgment cannot merge with any other role (τ: 9/9 UNSAT) `[SAT]`
- Substrate wall: inert cannot merge with any other role (g: 9/9 UNSAT) `[SAT]`
- TC forces 3 distinctions: Q≠E (lazy/eager), Q≠f (lazy/eager), f≠η (projection uniqueness) `[Empirical]`
- Reflective tower forces 0 additional distinctions: all 10 nontriviality pairs survive full tower `[Empirical]`
- Composition closure forces 0 additional distinctions: all 10 survive sub-magma requirement `[Empirical]`
- 10/45 distinctness pairs are independent of all tested derivation sources (nontriviality axiom), exhaustively characterized `[Empirical]`
- Turing completeness: 7 axiom-forced elements simulate 2CM `[Empirical]`
- Reflective tower: 3 levels, branch swap, grounded continuations `[Empirical]`
- Compilation: within 4x of native Rust via supercompile → C/Rust; compiled reflective tower in 2.2 ms (20,000x over interpreted) `[Empirical]`
- Compiled reflective tower: meta-circular evaluator + continuation reification + branch swap in a single native binary `[Empirical]`
- GC: 10M allocations in 4MB via MMTk `[Empirical]`
- Futamura: all 3 projections demonstrated, fixed-point verified `[Empirical]`
- Extension profiles: Ψ₁₆ᶠ (hardware) and Ψ₁₆ᶜ (software), same core theorems `[Empirical]`
- Self-simulation: universal self-simulator verified on both Ψ₁₆ᶠ and Ψ₁₆ᶜ (512/512 cells, same code) `[Empirical]`
- Self-simulation: role-aware self-simulator computes 60/256 cells from algebraic rules alone `[Empirical]`
- S ⊬ D: N=8 non-dichotomic retraction magma (the Countermodel) `[Lean: Countermodel.lean]`
- D ⊬ H: N=10 DRM without factorable action (no Compose) `[Lean: Countermodels10.lean]`; N=10 DRM without Inert `[SAT]`
- H ⊬ D: N=10 FRM with factorable action + Branch + Y but 4 mixed elements violating classifier dichotomy `[Lean: Countermodels10.lean]`
- Tight bound: S+D+H coexist at N=10 (minimum possible) `[Lean: Witness10.lean]`; full axiom stack requires N=12 `[SAT]`

Full claim matrix with reproduction commands: [`CLAIMS.md`](CLAIMS.md). Full technical details: [`docs/technical_overview.md`](docs/technical_overview.md).

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
| **C (Classifier dichotomy)** | Only testers can produce boolean outputs on non-absorbers |
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

**Minimum sizes.** The axioms operate at two layers: the three capabilities (S, D, H) provide the computational primitives; the structural ladder (L3–L8) and coherence axioms (PA, Selection, VV, 1-Inert) organize those primitives into a clean role architecture.

| What | Min N | What it gives |
|------|-------|---------------|
| S+D+H (three capabilities alone) | **10** | Encoding, classification, evaluation — computationally complete but role structure unconstrained |
| + structural ladder (L3–L8) + PA + Selection | **12** | Clean 2-1-8-1 role architecture, seven separated roles, McCarthy correspondence |
| + IO + 8-state counter | **16** | Efficient counters, product encodings, the specific Ψ₁₆ᶠ witness |

The computational primitives of Lisp — quote/eval, conditional, cons/car/cdr, recursion — fall out of the three capability axioms alone at N=10. The clean seven-role architecture that makes those primitives look like McCarthy's specific design requires the additional organizational axioms and pushes the minimum to N=12. The gap between N=10 and N=12 is the cost of *legibility*: going from an algebra that works to one whose roles are cleanly separated and interpretable. Full details: [`docs/technical_overview.md`](docs/technical_overview.md).

The axioms have an equivalent categorical formulation using standard vocabulary: zero morphisms, retraction pairs, subobject classifiers, and the classifier dichotomy. The categorical formulation and its universal theorems are in [`CatKripkeWallMinimal.lean`](Kamea/CatKripkeWallMinimal.lean) (minimal 5-element witness + 16 universal algebraic theorems), [`NoCommutativity.lean`](Kamea/NoCommutativity.lean) (asymmetry — 3 universal theorems), and [`CategoricalFoundation.lean`](Kamea/CategoricalFoundation.lean) (full 16-element structure with products, copairing, and fixed-point combinator). All use only standard algebraic concepts — no Ψ-specific vocabulary.

The axioms operate at three layers. The **capability layer** (retraction pair, classifier dichotomy, factorable action) provides the three independent computational capabilities (S, D, H) — no capability implies any other (counterexamples at N=8 and N=10), and all three coexist at N=10. The **enrichment layer** (Branch, Y) connects the capabilities: Branch bridges D and H (the classifier controls the dispatcher), and Y crosses the decidability boundary (bounded → unbounded recursion). The **organizational layer** (structural ladder L3–L8, PA, Selection, 1-Inert) forces the clean role architecture (2-1-8-1 distribution, seven separated roles) that produces the McCarthy correspondence — this pushes the minimum to N=12. Full inevitability analysis: [`docs/inevitability_summary.md`](docs/inevitability_summary.md). Categorical reconstruction: [`docs/categorical_reconstruction.md`](docs/categorical_reconstruction.md). H characterization: [`docs/h_characterization.md`](docs/h_characterization.md).

Results fall into four tiers:

- **Universal results** — properties proved for *every* model satisfying the axiom class. Tagged `[Lean]` or `[SAT]`.
- **Model-specific results** — properties proved for the particular table Ψ₁₆ᶠ. Tagged `[Lean]`.
- **Empirical search results** — SAT satisfiability, minimality bounds, freedom analysis, recovery observations. Tagged `[SAT]` or `[Empirical]`.
- **Open claims** — not yet formalized. Tagged `[Open]`.

Full registry with reproduction commands: [`CLAIMS.md`](CLAIMS.md).

### How to Read This Repo

**Paper 1: The independence structure** (self-contained, no artifact needed)
- [`Kamea/CatKripkeWallMinimal.lean`](Kamea/CatKripkeWallMinimal.lean) — **Start here**: FaithfulRetractMagma + DichotomicRetractMagma, minimal witnesses, 19 universal theorems
- [`Kamea/Functoriality.lean`](Kamea/Functoriality.lean) — DRM isomorphisms preserve the Z/C/N decomposition (algebraic proof)
- [`Kamea/NoCommutativity.lean`](Kamea/NoCommutativity.lean) — Asymmetry: two left-absorbers ⇒ non-commutative
- [`Kamea/SelfSimulation.lean`](Kamea/SelfSimulation.lean) — Self-simulation forces encoding injectivity (4 universal theorems)
- [`Kamea/Countermodel.lean`](Kamea/Countermodel.lean) — S ⊬ D: N=8 FRM violating classifier dichotomy
- [`Kamea/Countermodels10.lean`](Kamea/Countermodels10.lean) — D ⊬ H and H ⊬ D: N=10 counterexamples
- [`Kamea/Witness10.lean`](Kamea/Witness10.lean) — Tight bound: S+D+H coexist at N=10
- [`independence_results.py`](independence_results.py) — Generate, verify, and freeze all counterexamples
- [`docs/categorical_reconstruction.md`](docs/categorical_reconstruction.md) — Standard categorical vocabulary translation
- [`docs/h_characterization.md`](docs/h_characterization.md) — H as factorable action: presentation-independent characterization
- [`CLAIMS.md`](CLAIMS.md) — what is proved, what is empirical, what is open

**Paper 2: The artifact** (the 16-element witness and its consequences)
- [`psi_repl.py`](psi_repl.py) — Interactive Ψ-Lisp REPL
- [`examples/psi_reflective_tower.lisp`](examples/psi_reflective_tower.lisp) — Three-level reflective tower: compute → verify → inspect/modify continuations → branch swap
- [`Kamea/Psi16Full.lean`](Kamea/Psi16Full.lean) — 83 operational theorems + rigidity/discoverability/irreducibility
- [`psi_star.py`](psi_star.py) — Turing-completeness: 2CM simulation via 7 axiom-forced elements
- [`psi_lisp.py`](psi_lisp.py) — Ψ-Lisp → Ψ∗ transpiler (McCarthy 1960 conventions)
- [`examples/psi_metacircular.lisp`](examples/psi_metacircular.lisp) — Defunctionalized CPS meta-circular evaluator
- [`kamea-rs/`](kamea-rs/) — Rust emulator + WASM browser debugger (~25x faster)
- [`examples/psi16_corrupted_host_demo.py`](examples/psi16_corrupted_host_demo.py) — Animated TUI: watch one wizard heal another
- [`docs/psi_framework_summary.md`](docs/psi_framework_summary.md) — Full axiom search results and Cayley tables

**Compilation and performance**
- [`psi_supercompile.py`](psi_supercompile.py) — Partial evaluator: constant folding + QE cancellation + branch elimination + let propagation + lambda inlining
- [`psi_transpile.py`](psi_transpile.py) — Supercompiled Ψ∗ → C/Rust transpiler
- [`examples/psi_futamura.psi`](examples/psi_futamura.psi) — Futamura projection demo: interpreter specialization = direct compilation (10 test cases). All 3 projections demonstrated; projection 3 fixed point verified. The compiled reflective tower is projection 1 applied to the meta-circular evaluator
- [`examples/psi_transpile.lisp`](examples/psi_transpile.lisp) — Self-hosted transpiler: Ψ-Lisp → Rust (Futamura projection 3 fixed point)
- [`psi_blackbox.py`](psi_blackbox.py) — Black-box recovery (3 methods, 100% on 1M seeds)

---

## What Is Not Proved

- **Uniqueness of Ψ₁₆ᶠ.** The Cayley table is one model from the solution space. The axioms constrain roles and relationships but leave 192/256 cells free at N=16 (25.0% determination). Cell-by-cell freedom analysis (`ds_search/n16_freedom.py`) confirms: absorber rows fully fixed (32), counter/INC/DEC pinned (24), E-transparency + INC2 fix 6 E-cells, selection fixes η·ρ, Y fixed-point fixes Y·ρ. Scale: N=8 → 28.1%, N=12 → 18.8%, N=16 → 25.0% (increase from N=12 due to additional operational constraints).
- **Role uniqueness (resolved: not unique, but selected by classifier minimality).** The *capabilities* are irredundant — you need some composition, some branching, some recursion. The *specific axiom forms* are not unique: Compose admits ≥6 variants. But the variants are not structurally equal. In 4 of 5 alternative Compose forms, elements that should be computational (f, η) cross the classifier wall and become classifiers — the algebra confuses doing with judging. The McCarthy realization (η = ρ∘g) is the **unique** form that minimizes the classifier count: 1 tester (the minimum for conditional dispatch), everything else computational. This is a parsimony principle intrinsic to the framework's own architectural axiom: don't judge when you can compute. The criterion is well-defined, selects a unique answer, and uses the classifier wall (already an axiom) to grade the alternatives. Whether classifier minimality is equivalent to a known categorical property (smallest subobject classifier lattice, most free encoder subcategory) is open.
- **Minimality from base axioms.** Abstract axiom limitation theorems show base DirectedDS axioms imply only `card ≥ 2` (tight). What forcing conditions derive the full structure from first principles remains open.
- **Self-modeling vs discriminability.** Empirical search shows nearly all rigid magmas are WL-1 discriminable without self-modeling — unique structural fingerprints suffice for identification. Self-modeling adds interpretability: elements don't just have unique fingerprints, they have roles (classifier, transformer, substrate) that make the algebra a computational system rather than a mere barcode. Whether interpretability is necessary for reflective computation, or merely convenient, is open.
- **Extension profile optimality.** Ψ₁₆ᶠ and Ψ₁₆ᶜ are two points in the extension design space. Whether either is optimal for its target — or whether better profiles exist — is unexplored. The methodology (SAT search with target-specific constraints) can find other profiles, but the space has not been systematically enumerated.
- **Distinctness: 78% derived, 22% axiomatic (fully characterized).** Of 45 pairwise distinctness requirements, 35 are derived: 32 from categorical axioms (Lean-proved on the witness, SAT-verified universally at N=12) and 3 from Turing completeness (lazy/eager and projection conflicts — no evaluator can resolve them). The remaining 10 (⊤=⊥, Q=ρ, Q=Y, E=f, E=ρ, E=Y, f=ρ, f=Y, ρ=Y, η=Y) have been exhaustively tested against categorical axioms, Turing completeness, composition closure, and the full reflective tower including continuation reification and branch swap. All 10 survive all tests. They are the nontriviality axiom — the analog of 0 ≠ 1 in a nontrivial ring. Merged-role algebras satisfying all other axioms exist, compute, and reflect; they are expressively but not computationally degenerate.
- **Capability independence (resolved, Lean-proved).** All three capabilities are fully independent — no capability implies any other. Four Lean-verified counterexamples: S ⊬ D (N=8, `Countermodel.lean`), D ⊬ H (N=10, `Countermodels10.lean`), H ⊬ D (N=10, `Countermodels10.lean`), S ⊬ H (N=4, trivial). The classifier wall is epistemic, not computational: evaluation machinery does not force clean roles. Tight bound: S+D+H coexist at N=10 (`Witness10.lean`). Whether the axioms for each capability are *minimal* remains open. See [`docs/categorical_reconstruction.md`](docs/categorical_reconstruction.md).
- **No canonical object.** Ψ₁₆ᶠ is not initial, terminal, or otherwise universal in the category of Kripke magmas — 112 non-isomorphic models exist at N=4. The canonicity lies at the theory level: the three-class decomposition is a **proved functorial invariant** — DRM isomorphisms preserve Z, C, N (algebraic proof in [`Functoriality.lean`](Kamea/Functoriality.lean), no `decide`). Whether a natural universal property characterizes Ψ₁₆ᶠ within DRMag⁺ remains open. See [`docs/categorical_canonicity.md`](docs/categorical_canonicity.md).
- **Evaluator internalization characterization (resolved).** H now has a presentation-independent definition on par with S and D: the *Internal Composition Property* (ICP). An algebra satisfies ICP when there exist pairwise distinct non-absorber elements a, b, c such that b preserves the core, a · x = c · (b · x) on core, and a takes ≥2 distinct values — "some element's action on core factors non-trivially through two others, one core-preserving." ICP is empirically equivalent to Compose + Inert across 250 SAT-generated retraction magmas and the 3 Lean-proved N=10 counterexamples (250/250 agreement). The equivalence is not yet a Lean theorem. Two degeneracies motivate the conditions: Q² = E requires b ≠ c (pairwise distinct), and classifier-then-inert → constant-absorber requires non-triviality (≥2 values). Branch and Y are enrichments on top of ICP: Branch bridges D to H (the classifier controls the dispatcher), Y crosses the decidability boundary (bounded → unbounded recursion). Full analysis: [`docs/h_characterization.md`](docs/h_characterization.md).
- **Categorical formalization (mostly complete for paper 1).** The paper-1 proof inventory covers: universal decomposition theorems (19), functoriality (4), self-simulation injectivity (4), full independence (14 countermodel theorems), and tight bound (7) — 55 theorems across 7 Lean files, zero `sorry`. What remains for Lean: the intermediate distinctness layer (proving 13 non-forced pairs are independently justified by expressiveness) is supported by SAT analysis, not Lean. See [`docs/inevitability_summary.md`](docs/inevitability_summary.md).

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
| **Boba's Tower (Kamea)** | **Grounded (256 bytes)** | **Tagged data** | **Compile the tower itself** |

What they have that we don't: live meta-interpreter modification (`set! base-eval`), infinite tower levels, compilation under modified semantics. What we have that none of them do: walkable continuations (the branch swap), a compiled tower (2.2 ms native), formal verification (106+ Lean theorems, zero `sorry`), and runtime substrate verification. See [`docs/related_work.md`](docs/related_work.md) for the full comparison.

---

## Performance

Two benchmarks: counter arithmetic (fib + fact + power + gcd, all inputs known at call time) and N-Queens(8) (backtracking search with cons-cell lists, 92 solutions). Counter arithmetic is pure compute; nqueens stresses allocation and recursion.

**Counter arithmetic** (fib(8) + fib-iter(30) + fact(10) + power(2,10) + gcd(100,75), amortized per iteration):

| Implementation | Time/iter | vs Native Rust |
|----------------|----------|---------------|
| **Native Rust** (LLVM -O) | 0.003 µs | 1x |
| **Compiled Ψ-Lisp → C** (gcc -O2) | 0.01 µs | **~4x** |
| **Native Python** | 5 µs | ~1,700x |
| **Ψ-Lisp (Rust interpreter)** | ~200 ms | ~70,000,000x |
| **Ψ-Lisp (Python interpreter)** | ~2,000 ms | ~700,000,000x |

**N-Queens(8)** (backtracking with cons/car/cdr, per call):

| Implementation | Time/call | vs Native Rust |
|----------------|----------|---------------|
| **Native Rust** (LLVM -O) | 47 µs | 1x |
| **Compiled Ψ-Lisp → C** (gcc -O2) | 86 µs | **1.8x** |
| **Compiled Ψ-Lisp → Rust** (LLVM -O) | 114 µs | **2.4x** |
| **Native Python** | 5.9 ms | 125x |
| **Ψ-Lisp (Rust interpreter)** | 4.1 s | 87,000x |
| **Ψ-Lisp (Python interpreter)** | 301 s | 6,400,000x |

Compiled Ψ-Lisp is within **4x of native Rust** on pure arithmetic and within **2x on nqueens(8)** — faster than native Python in both cases. The nqueens gap is smaller because the cons-cell arena (bump allocator, no GC) is competitive with Rust's `Vec` push/pop. The entire compilation pipeline is ~1,100 lines: a 312-line supercompiler, a 640-line transpiler, and a 121-line C runtime whose core is a 256-byte array. Full performance analysis and extension profile comparison: [`docs/technical_overview.md#10-performance`](docs/technical_overview.md#10-performance).

**Boba's Tower** (meta-circular evaluator: fib(8) + fact(10) + table verification + reify/reflect + branch swap):

| Implementation | Time | vs Compiled |
|----------------|------|-------------|
| **Compiled tower** (rustc -O) | 2.2 ms | 1x |
| **Ψ-Lisp (Python interpreter)** | ~43 s | ~20,000x |

The compiled tower is not about benchmark speed — it's about having the meta-circular evaluator as compiled Rust with continuations as data, the Cayley table verified at runtime, and branch swap via continuation modification, all in a single native binary.

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
│   ├── counterexample_search.py      # WL-1 discrimination tests
│   ├── composition_closure_test.py    # Composition closure: compatible but kills 0/10 pairs
│   ├── reflection_distinctness_test.py # Reflective tower test on 10 nontriviality pairs (0/10 killed)
│   ├── kripke_canonicity.py           # DRMag enumeration + homomorphism search (112 iso classes at N=4)
│   ├── rigid_census.py               # Small rigid magma census
│   └── counterexamples/              # Saved counterexample tables (.npy)
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
│   ├── related_work.md               # Boba's Tower vs Smith/Black/Blond/LMS-Black: the architectural fork
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

`lake build` compiles all Lean files — the categorical foundation (19 universal theorems from axioms in `CatKripkeWallMinimal.lean` + `NoCommutativity.lean`), the self-simulation foundation (4 universal theorems from definition in `SelfSimulation.lean`), and the Ψ-specific operational proofs (130+ theorems on the 16-element table in `Psi16*.lean`). Zero `decide` on universal theorems. Zero `sorry` across all files.

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

Lean proofs use two techniques: universal theorems (`CatKripkeWallMinimal.lean`, `PsiUniversalBounds.lean`) use pure algebraic reasoning — no `decide`, no `native_decide`. Model-specific theorems (`Psi16*.lean`, `Cat*.lean`) use `decide` or `native_decide`, appropriate and complete for finite carrier types with decidable equality. Zero `sorry` across all files.

All Ψ-Lisp test programs produce identical output across Python, compiled C, compiled Rust, Rust interpreter, and WASM.

---


## License

MIT

## Citation

If you use this work, please cite:

```bibtex
@software{palmieri2025kamea,
  author = {Palmieri, Stefano},
  title = {Kamea: Three Independent Capabilities of Reflective Computation in Finite Algebras},
  year = {2025},
  url = {https://github.com/stefanopalmieri/Kamea}
}
```

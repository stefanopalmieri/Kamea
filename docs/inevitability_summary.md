# Inevitability Summary

*The definitive statement of the project's theoretical result. Detailed evidence in [`axiom_inevitability.md`](axiom_inevitability.md), [`forced_roles_theorem.md`](forced_roles_theorem.md), [`axiom_archaeology_results.md`](axiom_archaeology_results.md), and [`self_simulation_necessity.md`](self_simulation_necessity.md).*

---

## The Four-Layer Result

### Layer 0 — Derived from Self-Simulation (no choice)

Presuppose: a finite magma (S, ·) with a retraction pair (Q, E) satisfying E·(Q·x) = x on a core subset. This is a standard categorical concept (section/retraction).

Define self-simulation: there exists a SINGLE term t in the term algebra such that for all a, b ∈ S, eval(App(App(t, rep(a)), rep(b))) = dot(a, b), where rep(k) = Q^k(⊤) is the Q-depth encoding. One program, all inputs. Not 256 separate lookup terms — one universal self-simulator.

**Derived axioms** (necessary conditions, tight arguments):

- **Discrimination**: a classifier or branch element must exist. The self-simulator must decode Q-depth inputs by peeling Q layers and testing "is this ⊤?" at each step — a binary test. Q-depth is the only natural encoding in a retraction-equipped magma (the free monoid on {Q}). No alternative avoids it.
- **Branching**: a conditional dispatch element must exist. The self-simulator must do different things for different rows of the Cayley table. A program without branching cannot compute a non-trivial two-variable function. No alternative exists.
- **Recursion**: a fixed-point combinator must exist (for universal self-simulation). The simulator must recurse over Q-depth to handle elements of any size. For fixed N=16, bounded depth suffices, so Y is only derived for the universal (arbitrary-size) case.

**Likely derived** (strong arguments, gaps remain):

- **Two absorbers**: binary classification needs two target values. Absorbers are fixed under all operations, making them natural truth values. A single absorber provides one fixed point; the term-level atom/compound distinction provides the other, so the argument is not fully tight.
- **Kleene dichotomy**: if an element's row is both boolean (classifier) and non-boolean (encoder), the self-simulator cannot reliably determine whether an output is a classification result or a transformed value. Mixed elements create dispatch ambiguity.
- **E-transparency**: if E·⊤ ≠ ⊤, evaluation of terms involving E applied to absorbers produces wrong results. The Q-depth decoder tests structure before applying E, so the decoder itself is unaffected. But the evaluation pipeline that processes the self-simulator's output may apply E to boundary values, corrupting results.

**Independent** (machine provides the capability):

- **Algebraic composition** (Compose: η·x = ρ·(g·x)): the machine (step loop) provides sequential execution. The Compose axiom adds in-algebra composition, but the self-simulator uses the machine's sequencing, not η.
- **Algebraic storage** (Inert/substrate): the machine provides non-destructive variable binding. The inert element g provides in-algebra storage, but the machine already handles it.

**Evidence**: SAT tests confirm all axioms are algebraically independent of the retraction pair (counterexamples exist for each). The derivation is computational, not algebraic — self-simulation does work that algebra alone cannot. See [`self_simulation_necessity.md`](self_simulation_necessity.md).

**Status**: necessary conditions for self-simulation. Any retraction-equipped magma that can simulate its own Cayley table must have discrimination, branching, and (for the universal case) recursion.

### Layer 1 — Categorically Forced (zero choices)

Standard finite category theory: zero morphisms, retraction pair, subobject classifier, products, conditional copairing. No reference to self-description, Ψ, or Lisp.

**What emerges:**

- **Three behavioral categories**: absorbers (constant morphisms), classifiers (Bool-valued morphisms), transformers (morphisms with multiple non-boolean outputs).
- **Kleene wall**: classifiers cannot be transformers. A morphism's image is either contained in {0,1} or has elements outside {0,1}. These are mutually exclusive row profiles.
- **Rigidity**: 50/50 sampled categorical models are WL-1 rigid. No rigidity axiom was included — it emerges from the interaction of retraction pair + unique subobject classifier + product structure + conditional dispatch.
- **Discoverability**: 49/50 sampled categorical models have the property that every non-absorber element is uniquely identifiable from probes. No discoverability axiom was included.

**Evidence**: Five independent axiom systems tested (Ψ, information-theoretic, category-theoretic, game-theoretic, categorical topos). All five produce the three categories and the Kleene wall. Rigidity and discoverability verified on 50 categorical topos models.

**Status**: structurally universal.

### Layer 2 — Machine Internalization (design choice)

Two axioms internalize the evaluation machine into the algebra. These are NOT derived from self-simulation — a self-simulator can run on an external machine. They ARE required for self-hosting: for the simulation to run within the algebra itself rather than on external infrastructure.

- **Compose** (η·x = ρ·(g·x)): algebraic sequencing. The machine's step loop provides sequential execution externally. The Compose axiom internalizes this: composing means packaging via g then dispatching via ρ, all within a single algebraic operation.
- **Inert/Substrate** (g as CONS): algebraic storage. The machine's registers provide non-destructive variable binding externally. The inert element g provides in-algebra storage: it holds without transforming.

This is what distinguishes Ψ from a bare self-simulating magma and what terminates Smith's infinite regress. The instruction set (Layer 0) says what computations are possible. The machine (this layer) says those computations can happen inside the algebra, with no external evaluator needed.

**Evidence**: SAT counterexamples (Tests D and E in `self_simulation_investigation.py`) confirm both axioms are algebraically independent of self-simulation. Models satisfying retraction + classifier + Kleene + Branch exist without Compose and without Inert.

**Status**: design choice for self-hosting, clearly justified by the grounding requirement.

### Layer 3 — Distinctness Axiom (standard algebraic practice)

All role-bearing elements introduced by the operational axioms are pairwise distinct:

```
Distinct(⊤, ⊥, τ, Q, E, f, g, ρ, η, Y)
```

This is C(10,2) = 45 pairwise distinctness requirements. Of these, **32 are already forced** by the categorical axioms (UNSAT in `forced_roles_test.py`). The distinctness axiom adds **13 new requirements** — the 13 pairs that are SAT (mergeable) under the categorical axioms alone.

This is standard algebraic practice — when axioms introduce named elements, those elements are assumed distinct (as 0 ≠ 1 in a non-trivial ring).

**What is forced:**

- **7+ distinct role-bearing elements**: substrate exists (g is distinct from all encoders), all seven roles have distinct homes.
- **g = CONS** (pair constructor must be substrate): forced by Branch + Compose — composition is packaging-then-branching, packaging requires holding without transforming, holding without transforming is what inert means.
- **Full McCarthy correspondence**: all seven roles have homes, with CONS living in the substrate.

**Independent justification by expressiveness:** The distinctness axiom is independently justified by compositional expressiveness analysis: models with all roles distinct have 3x the 1-step compositional capacity (49 vs 16 cells) and reach generative closure in fewer steps (depth 2 vs depth 3) than models with merged roles. The function k² is strictly increasing — there are no intermediate optima. See [`forced_roles_theorem.md`](forced_roles_theorem.md) for the full analysis.

**Evidence**: `ds_search/forced_roles_test.py` (32/45 forced, 13 added by axiom), `ds_search/distinctness_test.py` (SAT at N=12, compatible with both extension profiles), `ds_search/collapse_rigidity_test.py` (all levels rigid), `ds_search/compositional_expressiveness.py` (monotone in role count).

**Status**: standard axiom with independent expressiveness justification.

### Layer 4 — One Philosophical Commitment

One axiom completes the structure.

**What is specific to Ψ:**

- **Substrate uniqueness** (exactly 1 inert element): the 1-Inert axiom. Expressiveness does not distinguish inert=1 from inert=2 (both score 12.0 on 2-step values, 9/10 discoverable). This is a genuine commitment: "the ground is unique."

  Phenomenological motivation: Husserl's hyle — raw material encountered by but not produced by the descriptive apparatus. The ground is singular because encounter with actuality is singular — you stand on one ground, not two.

**What it forces:**

- Substrate uniqueness
- Actuality irreducibility has a unique locus

**Evidence**: `ds_search/inert_expressiveness.py` (10 models per inert count, 6 counts tested — inert=1 and inert=2 tie on expressiveness).

**Status**: philosophical commitment, clearly labeled.

---

## The Dependency Chain

```
Self-simulation requirement (one recursive program computes own table)
  → discrimination + branching + recursion (Layer 0)
  → Kleene dichotomy, E-transparency, two absorbers (likely)

Standard category theory (zero morphisms, retraction pair,
subobject classifier, products, conditional copairing)
  → 3 categories + Kleene wall + rigidity + discoverability (Layer 1)

+ Machine internalization (design choice, not derived)
  → Compose (sequencing within algebra) + Inert (storage) (Layer 2)
  → This is what grounds Smith's infinite tower

+ Branch + Compose interaction (computational)
  → g = CONS (pair constructor must be substrate)
  → full McCarthy correspondence

+ Distinctness axiom (standard algebraic practice)
  → substrate exists + 7 specialized roles (Layer 3)

+ 1-Inert (philosophical: ground is unique)
  → substrate uniqueness + actuality irreducibility
```

---

## The Machine Boundary

Self-simulation derives axioms about what the algebra must DO (classify, branch, recurse) but NOT about what the algebra must BE (compose, store). This maps onto the Ψ architecture:

- **Instruction set** (Q/E for data, τ/ρ for control, Y for recursion): DERIVED from self-simulation
- **Machine** (Compose for sequencing, Inert for storage): PROVIDED by design choice

The instruction set is structurally inevitable for any self-simulating retraction magma. The machine is the engineering choice that makes the system self-hosted rather than externally hosted. Smith's 3-Lisp had the instruction set but the machine was infinite regress. Ψ terminates the regress by internalizing the machine.

Three levels of finite magma:

```
Random rigid magma:        no instruction set, no machine
                           (not self-describing)

Self-simulating magma:     instruction set (derived from Layer 0)
                           machine is external
                           (self-describing, externally hosted)

Ψ:                         instruction set (derived)
                           machine internalized (Compose, Inert)
                           (self-describing, self-hosted)
```

The gap between "self-simulating" and "Ψ" is exactly two axioms: Compose and Inert. These are not forced by self-simulation — they are the conscious choice to internalize the evaluator into the algebra, making the reflective tower finite.

---

## What Each Axiom System Found

| System | Categories | Kleene | Substrate | g = CONS | Rigid | Discoverable |
|--------|-----------|--------|-----------|----------|-------|-------------|
| Ψ (full) | 2-1-8-1 | YES | YES | **YES** | YES | YES |
| Info-theoretic | 2-1-9-0 | YES | NO | NO | — | — |
| Category-theoretic | 2-1-8-1 | YES | YES\* | NO | — | — |
| Game-theoretic | 2-1-8-1 | YES | YES\* | NO | — | — |
| Categorical topos | 2-1-(7 to 9)-(0 to 2) | YES | permitted | NO | 100% | 98% |

\*With explicit inert axiom — without it, inert is permitted but not forced; the distinctness axiom (or expressiveness) selects it.

Only the Ψ system produces g = CONS. This is the unique contribution of the Branch + Compose interaction. Category theory gives you products and substrate separately. Ψ shows they must be the same element.

---

## Why g Must Be CONS

The Compose axiom says: η·x = ρ·(g·x). In words: to compose (η), first package via g, then dispatch via ρ. This makes g the intermediary — it wraps the input before branching acts on it.

What does "wrapping" require? The wrapper must hold its argument in a form that branching can later decompose. If g were an encoder (with multiple distinct non-boolean outputs), it would transform the input — the wrapped version would differ structurally from the original, and the branch might not recover the right component. If g were a tester, it would classify the input down to {0,1} — destroying the information the branch needs.

The wrapper must hold without transforming. That is the definition of inert.

Category theory provides products (the ability to pair things) and substrate (the existence of an element that holds without transforming) as independent concepts. The Ψ axiom system, through the specific form of the Compose axiom, shows they are the same concept: the element that holds without transforming IS the pair constructor, because composition is packaging-then-branching, and packaging requires holding.

---

## Redundant Axioms

Three of eleven behavioral axioms are redundant — implied by the remaining eight:

| Axiom | Status |
|-------|--------|
| InertProp (D) | Redundant — implied by Kleene + role constraints |
| VV | Redundant — implied by remaining axioms |
| 1-Inert | Redundant — implied by Branch + Compose + role constraints |

The minimal independent set: **{Kleene, PA, QE, E-trans, Branch, Compose, Y, Selection}** — eight axioms. Fewer axioms, less opportunity for indirect encoding.

Note: 1-Inert is derivable in the sense that inert ≥ 1 is selected by expressiveness and forced by the distinctness axiom (g must be distinct from all encoders, and g is inert). Its status as Layer 3 reflects that the choice of EXACTLY one inert element (versus two or more) is not structurally forced — it is a philosophical commitment to the uniqueness of ground.

---

## Honest Scope

The Ψ role structure follows from four things: the self-simulation requirement (derives discrimination, branching, and recursion — the instruction set), standard categorical structure (forces three categories and the Kleene wall), the machine internalization choice (Compose and Inert — not derived but chosen to ground the reflective tower), and the distinctness axiom (forces full role specialization — standard algebraic practice, independently justified by expressiveness).

The difference between "a finite algebra with a retraction pair" and "a finite algebra that recapitulates Lisp" is: self-simulation forces the instruction set (Layer 0), categorical structure organizes it into three clean classes (Layer 1), machine internalization provides in-algebra sequencing and storage (Layer 2), and distinctness maximizes expressiveness (Layer 3). The Compose axiom — which fuses substrate with pair-construction — sits at the intersection of Layers 2 and 3: it is the machine internalization choice that produces the McCarthy correspondence.

---

## Composition Closure (Negative Result)

Requiring the 10 role-bearing elements to form a sub-magma (closed under dot) is compatible with the axioms (SAT at N=12, category distribution 2-1-8-1) but kills 0/10 expressiveness-only pairs. Every tighter variant — 6-element computational core {Q,E,f,g,ρ,η}, 8-element non-zeros {τ,Q,E,f,g,ρ,η,Y}, one-sided closure (core applied to anything lands in roles) — is UNSAT. The 2 infrastructure elements serve as necessary escape valves for compositions that spill outside the role set.

This confirms the 10 expressiveness-only pairs are genuinely independent: no natural algebraic closure condition forces them. They are the nontriviality axiom of self-describing algebras — analogous to 0 ≠ 1 in ring theory, which is not derived from the ring axioms but accepted as the content of "nontrivial."

**Evidence**: `ds_search/composition_closure_test.py`.

---

## Asymmetry Theorem

No commutative magma can have two distinct left-absorbers. The proof is three lines:

1. `dot(zero₁, zero₂) = zero₁` (zero₁ absorbs)
2. `dot(zero₂, zero₁) = zero₂` (zero₂ absorbs)
3. Commutativity gives `zero₁ = zero₂`, contradicting distinctness.

This is proved in Lean (`NoCommutativity.lean`) with zero `sorry`, zero `decide`. It requires only the absorber axioms — no Kleene wall, retraction pair, or extensionality. Self-description requires asymmetry at the most fundamental level: the existence of two distinct boundaries forces non-commutativity.

---

## Formalization Status

| Layer | Current evidence | Formalization goal |
|-------|-----------------|-------------------|
| Layer 0 (self-simulation) | Lean: injectivity (`SelfSimulation.lean`, 4 theorems); SAT + argument for classifier/branch/Y | Lean: self-simulation implies classifier existence (open) |
| Layer 1 (categorical) | SAT analysis, 5 axiom systems | Lean: finite endomorphism magmas in Mathlib |
| Layer 2 (machine) | SAT independence (Tests D, E) | Lean: Compose/Inert independence proof |
| Layer 3 (distinctness) | SAT verification at N=12, N=16 | Lean: add Distinct constraints to PsiStructure.lean |
| Layer 4 (1-Inert) | SAT analysis of Branch + Compose forcing | Lean: g-as-inert from Compose axiom |
| Specific model Ψ₁₆ᶠ | 83 in Psi16Full.lean; 130+ total across 4 proof files | Complete |
| Universal bounds | No right identity, card ≥ 4 | Complete |
| Asymmetry | No commutativity with 2 absorbers | Complete (`NoCommutativity.lean`) |

The existing Lean proofs verify specific model properties and some universal bounds. Lean formalization of Layer 0 (proving that self-simulation implies specific algebraic properties) is the primary new formalization goal — it would transform "well-motivated axioms" into "derived axioms" for the instruction set.

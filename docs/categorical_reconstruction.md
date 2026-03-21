# Categorical Reconstruction of the Three Capabilities

## Summary

The three capabilities — self-simulation (S), self-description (D), self-hosting (H) — correspond to three standard categorical enrichment steps applied to finite extensional magmas. No capability implies any other (proved by counterexample at N=8 and N=10). All three coexist at N=10.

| Capability | Categorical Structure | What's Internalized | Standard Analog |
|---|---|---|---|
| **S** (self-simulating) | Faithful magma + section-retraction pair | Naming | Gödel numbering; representability |
| **D** (self-describing) | + Subobject classifier + dichotomy | Judging | Subobject classifier (topos) |
| **H** (self-hosting) | + Internal composition + substrate + fixpoint | Evaluating | Internal hom (closed category) |

## Definitions

**Setting.** A *faithful magma* is (S, ·) where the left-regular representation a ↦ Lₐ is injective. Equivalently: if a · x = b · x for all x, then a = b (extensionality). A *2-pointed faithful magma* has exactly two left-absorbers z₁, z₂ ∈ S. The *core* is S \ {z₁, z₂}.

**Capability S.** A *Faithful Retract Magma* (FRM) is a 2-pointed faithful magma with a retraction pair: elements s, r ∈ core(S) satisfying r · (s · x) = x and s · (r · x) = x for all x in core. In categorical terms: s is a section, r a retraction of the identity on core. This provides encoding infrastructure — elements can name each other via Q-depth encoding.

**Capability D.** A *Dichotomic Retract Magma* (DRM) extends FRM with:
- A classifier c ∈ core where c · x ∈ {z₁, z₂} for all x
- The Kripke dichotomy: every non-zero element is either entirely {z₁, z₂}-valued on core (classifier) or entirely non-{z₁, z₂}-valued on core (non-classifier)

This is the finite analog of a subobject classifier with decidability: the partition of morphisms into characteristic (Ω-valued) and non-characteristic is exhaustive and disjoint on the core. No element can be partially classifying.

**Capability H.** A *Compositional FRM* extends FRM (not necessarily DRM) with:
- Conditional copairing ρ: dispatches based on a classifier element
- Substrate g: maps core away from absorbers (data construction)
- Internal composition η: satisfies η · x = ρ · (g · x) on core
- Fixed-point combinator Y: satisfies Y · ρ = ρ · (Y · ρ) with Y · ρ in core

The Compose axiom η · x = ρ · (g · x) is a fragment of internal hom: η represents the composite Lρ ∘ Lg as a single element. This is the critical fragment sufficient for Turing-complete evaluation.

## Independence Results

**Theorem (S ⊬ D).** There exists an 8-element FRM with a classifier that violates the Kripke dichotomy. Element 5 has both boolean and non-boolean outputs on core. [Lean-proved: `Countermodel.lean`, `countermodel8_violates_dichotomy`]

**Theorem (D ⊬ H).** There exists a 10-element DRM satisfying the Kripke dichotomy where (a) no element satisfies the Compose axiom, and (b) no inert element exists. [SAT: `independence_results.py`, Tests D and E]

**Theorem (H ⊬ D).** There exists a 10-element FRM with Branch, Compose, Y fixed-point, and substrate — all H machinery — but 4 mixed elements violating the Kripke dichotomy. Internal evaluation does not force clean roles. [SAT: `independence_results.py`, diagonal test]

**Corollary.** No capability implies any other. The independence is full:

|  | S ⊬ D | D ⊬ H | H ⊬ D |
|---|---|---|---|
| Counterexample | N=8 (Lean) | N=10 (Lean) | N=10 (Lean) |

**Theorem (Coexistence).** The three capability axioms are simultaneously satisfiable at N=10, the minimum possible size (10 distinguished elements). The full axiom system (capabilities + organizational ladder L3–L8 + PA + Selection) has minimum satisfying size N=12. [SAT: `minimal_sdh_test.py`]

## Categorical Vocabulary Translation

| Ψ Concept | Categorical Translation | Standard? |
|---|---|---|
| Left-absorber | Zero morphism (constant endomorphism) | Yes |
| Extensionality | Faithfulness of left-regular representation | Yes |
| Retraction pair (Q/E) | Section-retraction pair | Yes |
| Classifier (τ) | Subobject classifier restricted to 2-valued | Yes |
| Kripke dichotomy | Decidability of the classifier partition | Novel (finite analog) |
| Three-category decomposition (Z/C/N) | Zero / classifier-orbit / complement | Standard components |
| Kripke wall (C ∩ N = ∅) | Partition completeness of classifier action | Novel (finite analog) |
| Conditional copairing (ρ) | Coproduct structure / case analysis | Yes |
| Substrate (g) | Ground object / constant constructor | Yes |
| Internal composition (η) | Fragment of internal hom | Yes (weaker than full) |
| Fixed-point combinator (Y) | Fixed-point operator | Yes |

The novel elements are the Kripke dichotomy and the three-category decomposition as a universal invariant. Everything else translates to standard categorical vocabulary.

## Lean Proof Inventory (Paper 1, self-contained)

48 theorems across 6 files. Zero `sorry`. A reviewer does not need the 16-element table, the Lisp implementation, or the reflective tower.

**The decomposition exists** (`CatKripkeWallMinimal.lean`, `NoCommutativity.lean`):
1. Three-category decomposition: S = Z ⊔ C ⊔ N. Exhaustive and pairwise disjoint.
2. Kripke wall: C ∩ N = ∅.
3. Retraction pair placement: s, r ∈ N.
4. No right identity.
5. Cardinality: |S| ≥ 4 (tight); |S| ≥ 5 when s ≠ r (tight).
6. Asymmetry: two distinct left-absorbers ⇒ non-commutative.

**It's invariant** (`Functoriality.lean`):
7. DRM isomorphisms preserve Z, C, and N. Algebraic proof, no `decide`.

**Self-simulation forces injectivity** (`SelfSimulation.lean`):
8. Partial application injectivity.
9. Encoding injectivity.
10. Row determination.

**The capabilities are independent** (`Countermodel.lean`, `Countermodels10.lean`):
11. S ⊬ D: N=8 FRM with classifier violating Kripke. `[decide]`
12. D ⊬ H: N=10 DRM without Compose. `[native_decide]`
13. H ⊬ D: N=10 FRM with Branch+Compose+Y violating Kripke. `[native_decide]`
14. S ⊬ H: N=4 DRM, trivially too small for H. `[decide]`

## The Two-Layer Structure

The axiom system operates at two layers:

**Capability layer** (N=10): Three independent axiom groups provide the computational primitives — retraction pair (encoding), Kripke dichotomy (classification), and internal composition + substrate + fixpoint (evaluation). These are the ingredients.

**Organizational layer** (N=12): The structural ladder (L3–L8) forces specific role counts (2-1-8-1 distribution). Coherence axioms (PA, Selection, 1-Inert) tie the capabilities together. These produce the clean seven-role architecture and the McCarthy correspondence. This is the recipe.

The computational primitives of Lisp fall out of the capability layer alone at N=10. The clean separation into seven interpretable roles requires the organizational layer and pushes the minimum to N=12. The gap is the cost of legibility.

## Realization Freedom

Each capability admits multiple inequivalent axiom forms (`axiom_mutation_test.py`):

| Capability | Axiom | Alternatives tested | Result |
|---|---|---|---|
| H | Compose: η·x = ρ·(g·x) | 5 variants (reversed, f∘g, ρ∘f, f∘ρ, g∘f) | All 6 SAT |
| H | Y: Y·ρ = ρ·(Y·ρ) | 3 variants (general, g-fixpt, idempotent) | All 4 SAT |
| H | Branch: τ→f, else→g | 2 variants (swapped, three-way) | All 3 SAT |

The capabilities are the invariants; the axiom forms are presentations of those capabilities. Different presentations produce different role assignments within the same three-category architecture. The McCarthy role inventory (quote, eval, cons, car, cdr, cond, nil) is one realization — a canonical point within an equivalence class.

This is analogous to the relationship between groups and group presentations, or between λ-calculus and combinatory logic: the algebraic structure is fixed, but the specific generators and relations are a choice.

## Conjectures

**Conjecture 1 (Cross-Formalism Universality).** The three capabilities (naming, judging, evaluating) are three independent design choices for any finite reflective system. The specific axioms may vary across formalisms, but the independence of the three capabilities persists.

**Conjecture 2 (Kripke–Subobject Correspondence).** The Kripke dichotomy is the finite analog of decidability of the subobject classifier in a topos. A formal functor from the category of DRMs to Set, sending each DRM to its three-category decomposition (Z, C, N), is natural.

**Conjecture 3 (Realization Equivalence).** The set of axiom systems realizing each capability forms an equivalence class under a natural notion of "same capability, different presentation." The McCarthy realization and its 12+ tested alternatives are all equivalent in this sense.

## What Is Proved vs. What Is Open

55 Lean theorems, 7 files, zero `sorry`.

| Claim | Status | File |
|---|---|---|
| Three-category decomposition universal | Lean-proved | `CatKripkeWallMinimal.lean` |
| Kripke wall (C ∩ N = ∅) | Lean-proved | `CatKripkeWallMinimal.lean` |
| Asymmetry (non-commutative) | Lean-proved | `NoCommutativity.lean` |
| Decomposition is algebraic invariant | Lean-proved | `Functoriality.lean` |
| Self-simulation → encoding injectivity | Lean-proved | `SelfSimulation.lean` |
| S ⊬ D (N=8 Countermodel) | Lean-proved | `Countermodel.lean` |
| D ⊬ H (N=10, no Compose) | Lean-proved | `Countermodels10.lean` |
| H ⊬ D (N=10, diagonal) | Lean-proved | `Countermodels10.lean` |
| S+D+H coexist at N=10 (tight bound) | Lean-proved | `Witness10.lean` |
| Kripke wall is epistemic, not computational | Proved (H⊬D) | `Countermodels10.lean` |
| Full axiom stack requires N=12 | SAT-verified | `minimal_sdh_test.py` |
| Each capability's axioms irredundant (partial minimality) | SAT-verified | `axiom_irredundancy_test.py` |
| Cross-formalism universality | Conjectured | — |
| Kripke ↔ subobject classifier decidability | Conjectured | — |
| Role uniqueness (McCarthy correspondence) | Open | — |

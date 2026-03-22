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
- The classifier dichotomy: every non-zero element is either entirely {z₁, z₂}-valued on core (classifier) or entirely non-{z₁, z₂}-valued on core (non-classifier)

This is the finite analog of a subobject classifier with decidability: the partition of morphisms into characteristic (Ω-valued) and non-characteristic is exhaustive and disjoint on the core. No element can be partially classifying.

**Capability H.** A *Compositional FRM* extends FRM (not necessarily DRM) with:
- Conditional copairing ρ: dispatches based on a classifier element
- Substrate g: maps core away from absorbers (data construction)
- Internal composition η: satisfies η · x = ρ · (g · x) on core
- Fixed-point combinator Y: satisfies Y · ρ = ρ · (Y · ρ) with Y · ρ in core

The Compose axiom η · x = ρ · (g · x) is a fragment of internal hom: η represents the composite Lρ ∘ Lg as a single element. This is the critical fragment sufficient for Turing-complete evaluation.

## Independence Results

**Theorem (S ⊬ D).** There exists an 8-element FRM with a classifier that violates the classifier dichotomy. Element 5 has both boolean and non-boolean outputs on core. [Lean-proved: `Countermodel.lean`, `countermodel8_violates_dichotomy`]

**Theorem (D ⊬ H).** There exists a 10-element DRM satisfying the classifier dichotomy where (a) no element satisfies the Compose axiom, and (b) no inert element exists. [SAT: `independence_results.py`, Tests D and E]

**Theorem (H ⊬ D).** There exists a 10-element FRM with Branch, Compose, Y fixed-point, and substrate — all H machinery — but 4 mixed elements violating the classifier dichotomy. Internal evaluation does not force clean roles. [SAT: `independence_results.py`, diagonal test]

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
| classifier dichotomy | Decidability of the classifier partition | Novel (finite analog) |
| Three-category decomposition (Z/C/N) | Zero / classifier-orbit / complement | Standard components |
| classifier wall (C ∩ N = ∅) | Partition completeness of classifier action | Novel (finite analog) |
| Conditional copairing (ρ) | Coproduct structure / case analysis | Yes |
| Substrate (g) | Ground object / constant constructor | Yes |
| Internal composition (η) | Fragment of internal hom | Yes (weaker than full) |
| Fixed-point combinator (Y) | Fixed-point operator | Yes |

The novel elements are the classifier dichotomy and the three-category decomposition as a universal invariant. Everything else translates to standard categorical vocabulary.

## Lean Proof Inventory (Paper 1, self-contained)

48 theorems across 6 files. Zero `sorry`. A reviewer does not need the 16-element table, the Lisp implementation, or the reflective tower.

**The decomposition exists** (`Catclassifier dichotomyWallMinimal.lean`, `NoCommutativity.lean`):
1. Three-category decomposition: S = Z ⊔ C ⊔ N. Exhaustive and pairwise disjoint.
2. classifier wall: C ∩ N = ∅.
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
11. S ⊬ D: N=8 FRM with classifier violating classifier dichotomy. `[decide]`
12. D ⊬ H: N=10 DRM without Compose. `[native_decide]`
13. H ⊬ D: N=10 FRM with Branch+Compose+Y violating classifier dichotomy. `[native_decide]`
14. S ⊬ H: N=4 DRM, trivially too small for H. `[decide]`

## The Two-Layer Structure

The axiom system operates at two layers:

**Capability layer** (N=10): Three independent axiom groups provide the computational primitives — retraction pair (encoding), classifier dichotomy (classification), and internal composition + substrate + fixpoint (evaluation). These are the ingredients.

**Organizational layer** (N=12): The structural ladder (L3–L8) forces specific role counts (2-1-8-1 distribution). Coherence axioms (PA, Selection, 1-Inert) tie the capabilities together. These produce the clean seven-role architecture and the McCarthy correspondence. This is the recipe.

The computational primitives of Lisp fall out of the capability layer alone at N=10. The clean separation into seven interpretable roles requires the organizational layer and pushes the minimum to N=12. The gap is the cost of legibility.

## Realization Freedom

Each capability admits multiple inequivalent axiom forms (`axiom_mutation_test.py`):

| Capability | Axiom | Alternatives tested | Result |
|---|---|---|---|
| H | Compose: η·x = ρ·(g·x) | 5 variants (reversed, f∘g, ρ∘f, f∘ρ, g∘f) | All 6 SAT |
| H | Y: Y·ρ = ρ·(Y·ρ) | 3 variants (general, g-fixpt, idempotent) | All 4 SAT |
| H | Branch: τ→f, else→g | 2 variants (swapped, three-way) | All 3 SAT |

The capabilities are the invariants; the axiom forms are presentations. But the presentations are not all equal: they differ in how many elements they push across the classifier wall.

**Classifier minimality.** The 6 Compose variants produce different role structures:

| Compose form | Classifiers | η category | f category |
|---|---|---|---|
| **η = ρ∘g [McCarthy]** | **1** | **N (encoder)** | **N (encoder)** |
| η = g∘ρ | 2 | N (encoder) | C (classifier) |
| η = f∘g | 3 | C (classifier) | C (classifier) |
| η = ρ∘f | 3 | C (classifier) | C (classifier) |
| η = f∘ρ | 3 | C (classifier) | C (classifier) |
| η = g∘f | 3 | C (classifier) | C (classifier) |

The McCarthy realization is the **unique** form that minimizes the classifier count: 1 tester, everything else computational. In all alternatives, either f or η (or both) cross the classifier wall — projection becomes judgment, or composition becomes classification. The McCarthy form is the one where the wall is maximally respected.

This is a parsimony principle intrinsic to the framework: the classifier wall separates judgment from computation; the McCarthy realization is the presentation that keeps the most elements on the computation side. It is "natural" not by universal property but by minimality over the wall the axioms already require.

## Conjectures

**Conjecture 1 (Cross-Formalism Universality).** The three capabilities (naming, judging, evaluating) are three independent design choices for any finite reflective system. The specific axioms may vary across formalisms, but the independence of the three capabilities persists.

**Conjecture 2 (Subobject Classifier Correspondence).** The classifier dichotomy is the finite analog of decidability of the subobject classifier in a topos. A formal functor from the category of DRMs to Set, sending each DRM to its three-category decomposition (Z, C, N), is natural.

**Conjecture 3 (Classifier Minimality as Categorical Property).** The McCarthy realization is the unique Compose variant with |C|=1 (classifier count minimized). The initial hypothesis — that this corresponds to core-faithfulness of the non-classifier stratum — is **refuted**: SAT counterexamples show |C|=1 DRMs with non-faithful N (N=6,8,10) and |C|>1 DRMs with faithful N (N=8,10). The correlation in the Compose variants is specific to those models, not a structural law.

Classifier minimality remains a well-defined selection criterion that uniquely picks the McCarthy form from the space of Compose variants. Whether it corresponds to any known categorical property (beyond the combinatorial fact of having the fewest classifiers) is open. Candidate connections: two-valuedness of the subobject classifier action, maximality of the encoder sub-representation, minimal logical complexity of the internal observation structure.

## What Is Proved vs. What Is Open

55 Lean theorems, 7 files, zero `sorry`.

| Claim | Status | File |
|---|---|---|
| Three-category decomposition universal | Lean-proved | `Catclassifier dichotomyWallMinimal.lean` |
| classifier wall (C ∩ N = ∅) | Lean-proved | `Catclassifier dichotomyWallMinimal.lean` |
| Asymmetry (non-commutative) | Lean-proved | `NoCommutativity.lean` |
| Decomposition is algebraic invariant | Lean-proved | `Functoriality.lean` |
| Self-simulation → encoding injectivity | Lean-proved | `SelfSimulation.lean` |
| S ⊬ D (N=8 Countermodel) | Lean-proved | `Countermodel.lean` |
| D ⊬ H (N=10, no Compose) | Lean-proved | `Countermodels10.lean` |
| H ⊬ D (N=10, diagonal) | Lean-proved | `Countermodels10.lean` |
| S+D+H coexist at N=10 (tight bound) | Lean-proved | `Witness10.lean` |
| classifier wall is epistemic, not computational | Proved (H⊬D) | `Countermodels10.lean` |
| Full axiom stack requires N=12 | SAT-verified | `minimal_sdh_test.py` |
| Each capability's axioms irredundant (partial minimality) | SAT-verified | `axiom_irredundancy_test.py` |
| Cross-formalism universality | Conjectured | — |
| Classifier dichotomy ↔ subobject classifier decidability | Conjectured | — |
| McCarthy realization minimizes classifier count | SAT-verified |
| Classifier minimality ↔ core-faithfulness of N | **Refuted** (SAT counterexamples both directions) |
| Classifier minimality as categorical property | Open | — |

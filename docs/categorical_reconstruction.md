# Categorical Reconstruction of the Three-Level Hierarchy

The Kamea project identifies three independent levels of reflective capability in finite algebras: self-simulation, self-description, and self-hosting. The independence is proved by finite counterexamples (N=8, N=10). This document reconstructs the three levels using standard categorical vocabulary and identifies the precise connections to topos theory and enriched category theory.

The goal is to show that the three levels are not Ψ-specific constructions but instances of three progressively richer categorical enrichment steps — and that the independence results are statements about these standard categorical structures, not artifacts of a particular formalism.

## 1. The Setting: Faithful Magma Actions

A *magma* is a set S with a binary operation · : S × S → S. We view (S, ·) through its **left-regular representation**: each element a ∈ S defines a map Lₐ : S → S by Lₐ(x) = a · x. The operation · is then the *action* of S on itself.

**Extensionality** (faithfulness): The left-regular representation S → End(S), a ↦ Lₐ, is injective. Equivalently: if a · x = b · x for all x, then a = b. Every element is determined by its action. This is the finite analog of *faithful representation* in algebra and *faithfulness* in category theory.

**Zero morphisms**: An element z ∈ S is a *left-absorber* (zero morphism) if z · x = z for all x. In the left-regular representation, Lz is a constant map. We require exactly two: z₁, z₂ with z₁ ≠ z₂. This gives S a **2-pointed set structure** — the two truth values that will serve as the image of classification.

The **core** of S is the set S \ {z₁, z₂} — the non-zero elements.

## 2. Level 1: Faithful Retract Magma (Self-Simulation)

**Definition.** A *Faithful Retract Magma* (FRM) is (S, ·, z₁, z₂, s, r) where:
- (S, ·) is an extensional magma with exactly two left-absorbers z₁, z₂
- s, r ∈ core(S) form a **retraction pair**: r · (s · x) = x and s · (r · x) = x for all x in core(S)

In categorical terms: s is a *section* and r is a *retraction* of the identity on the core. The composite Ls ∘ Lr is a retraction (idempotent endomorphism) on End(S).

**What this gives.** The retraction pair provides **encoding infrastructure**. An element a ∈ S can be encoded as the term s^k(z₁) for its index k (Q-depth encoding). The retraction r peels off one layer: r · (s · x) = x. This is the finite analog of Gödel numbering — the algebra can *name* its own elements.

**Self-simulation** (defined on top of FRM): There exists a term t in the free term algebra over S such that evaluating t on the encodings of any a, b returns the atom a · b. The key Lean theorem: self-simulation forces **partial application injectivity** — the encoding cannot compress distinct elements (`SelfSimulation.lean`, 4 universal theorems).

**Standard categorical context.** Section-retraction pairs are among the most basic categorical constructions. Every retraction pair gives rise to a splitting of an idempotent. In the category of endomorphisms on S, the pair (Ls, Lr) splits the idempotent Lr ∘ Ls.

**Lean formalization.** `FaithfulRetractMagma n` in `CatKripkeWallMinimal.lean`.

## 3. Level 2: Dichotomic Retract Magma (Self-Description)

**Definition.** A *Dichotomic Retract Magma* (DRM) is an FRM (S, ·, z₁, z₂, s, r) together with:
- A **classifier** c ∈ core(S) such that c · x ∈ {z₁, z₂} for all x ∈ S
- The **Kripke dichotomy**: for every non-zero a ∈ S, either
  - a · x ∈ {z₁, z₂} for all x in core(S) — a is a **classifier**, or
  - a · x ∉ {z₁, z₂} for all x in core(S) — a is a **non-classifier**
- **Non-degeneracy**: at least one non-classifier exists

**The three-category decomposition** (universal theorem):

Every element of S falls into exactly one of three classes:
- **Z** (zeros): the left-absorbers {z₁, z₂}
- **C** (classifiers): non-zero elements whose action on core is entirely {z₁, z₂}-valued
- **N** (non-classifiers): non-zero elements whose action on core is entirely non-{z₁, z₂}-valued

The **Kripke wall** is: C ∩ N = ∅. No element can be partially classifying and partially computational. This is a theorem, not an axiom — it follows from the dichotomy.

**What this gives.** The algebra can now **classify its own elements** into coherent behavioral categories. Classification (judgment) is cleanly separated from computation. The algebra has roles, not just actions.

### Connection to subobject classifiers

In a topos, the **subobject classifier** Ω is the object representing the subobject functor: Sub(X) ≅ Hom(X, Ω). A morphism χ : X → Ω "classifies" a subobject of X by indicating membership.

The classifier c in a DRM is the finite magma analog:
- The map Lc : S → {z₁, z₂} classifies every element as z₁ ("true") or z₂ ("false")
- This classifies the partition of S into "c-positive" and "c-negative" elements
- The 2-pointed set {z₁, z₂} plays the role of Ω

The Kripke dichotomy is the finite analog of **decidability of the subobject classifier**: not only does c classify, but every non-zero element is *either* a classifying map (like c — all outputs in {z₁, z₂}) *or* a computational map (no outputs in {z₁, z₂} on core). There are no "partially decidable" elements. In topos-theoretic terms: the characteristic morphisms and the non-characteristic morphisms form a complete partition of the non-zero morphism space, with no mixing.

This goes beyond having a subobject classifier — it constrains the *entire morphism space* relative to the classifier. In a general topos, morphisms can map partially into Ω. The dichotomy forbids this: every morphism is either entirely Ω-valued or entirely non-Ω-valued on the core. This is a strong structural property specific to the finite self-describing setting.

### Why the dichotomy is independent of Level 1

The N=8 counterexample (`self_simulation_investigation.py`, Test B): a faithful retract magma with 8 elements that self-simulates perfectly (64/64 cells correct) but contains elements with *mixed* rows — some core outputs in {z₁, z₂}, others not. The dichotomy fails. Classification and computation are entangled. The algebra can compute its own table but cannot organize its elements into coherent roles.

In categorical terms: the FRM has a 2-pointed set structure and a retraction pair, but the morphism space does not partition cleanly relative to the 2-pointed set. Having a section-retraction pair does not force a subobject classifier with dichotomy.

**Lean formalization.** `DichotomicRetractMagma n` in `CatKripkeWallMinimal.lean`. Key theorems: `three_categories`, `classifier_not_non_classifier`, `ret_is_non_classifier`, `sec_is_non_classifier`, `no_right_identity`, `card_ge_four`.

## 4. Level 3: Compositional Dichotomic Retract Magma (Self-Hosting)

**Definition.** A *Compositional DRM* (CDRM) is a DRM (S, ·, z₁, z₂, s, r, c) together with:
- **Conditional copairing** ρ ∈ N: a non-classifier element that dispatches based on classification:
  - ρ · x = p₁ · x when c · x = z₁ (classifier says "true" → take first branch)
  - ρ · x = g · x when c · x = z₂ (classifier says "false" → take second branch)
  where p₁ ∈ N is a projection and g ∈ S is a substrate element
- **Substrate** (inert element) g: an element whose action preserves the non-zero stratum (g · x ∉ {z₁, z₂} for x in core)
- **Internal composition** η ∈ N: a non-classifier satisfying η · x = ρ · (g · x) for x in core — the action of η is the composite "first apply g, then apply ρ"
- **Fixed-point combinator** Y ∈ N: an element satisfying Y · ρ = ρ · (Y · ρ) with Y · ρ in core

**What this gives.** The algebra can now **evaluate its own terms internally**. The conditional copairing ρ provides control flow (if-then-else). The substrate g provides data construction (pair/cons). The internal composition η provides sequencing (do g then do ρ). The fixed-point combinator Y provides recursion. Together, these internalize the evaluator — no external machine is required. Smith's infinite tower terminates.

### Connection to internal hom / closed categories

In a **closed category**, there is an internal hom functor [−, −] with a natural bijection Hom(A ⊗ B, C) ≅ Hom(A, [B, C]). The internal hom represents "the space of morphisms from B to C" as an object in the category itself.

The Compose axiom η · x = ρ · (g · x) is a fragment of internal hom: the element η ∈ S *represents* the composite Lρ ∘ Lg as a single element of S. The algebra contains an element whose action *is* the composition of two other elements' actions. This is the beginning of internalization — the algebra can represent composites of its own operations as first-class elements.

A full internal hom would require: for any two elements a, b ∈ S, there exists an element [a, b] ∈ S whose action represents "apply a then apply b." The Compose axiom provides one specific instance (η represents "g then ρ"). This is not a full internal hom, but it is the critical fragment that suffices for Turing-complete evaluation — because ρ provides branching, g provides data, and η provides sequencing, which together with Y (recursion) form a universal basis.

The substrate g plays the role of a **ground object** or **constant object**: it provides the raw material (data construction) that the computational elements (ρ, η, Y) operate on. In categorical terms, g is analogous to a terminal-like object in the computational stratum — the thing from which data structures are built.

### Why internal composition is independent of Level 2

The N=10 counterexamples (`self_simulation_investigation.py`, Tests D and E):
- **Test D** (no Compose): A DRM with 10 elements satisfying the Kripke dichotomy. The three-category decomposition holds. But no element η ∈ S can satisfy η · x = ρ · (g · x) — there is no internal representation of composition.
- **Test E** (no Inert): A DRM with 10 elements satisfying the Kripke dichotomy. Every non-zero element is either a classifier or an encoder — no substrate element exists. The algebra has judgment and computation but no ground.

In categorical terms: having a subobject classifier with dichotomy (Level 2) does not force the existence of an internal composition operator or a ground object. The morphism space can be cleanly partitioned (classifiers vs non-classifiers) without any element representing a composite of two others.

**Lean formalization.** `CatEndoMagma n` in `CategoricalFoundation.lean` provides the full structure. Conditional copairing: `copair_true`, `copair_false`. Internal composition: `compose`. Fixed point: `fixpt_eq`, `fixpt_nontrivial`.

## 5. The Three Levels as Categorical Enrichment

The three levels correspond to three progressively richer categorical structures:

| Level | Ψ Structure | Categorical Structure | What's Internalized | Standard Analog |
|-------|-------------|----------------------|--------------------|----|
| 1 | FaithfulRetractMagma | Faithful magma + section-retraction pair | **Naming**: elements can encode themselves | Gödel numbering; representability |
| 2 | DichotomicRetractMagma | + Subobject classifier + dichotomy | **Judging**: elements classify themselves into roles | Subobject classifier; topos structure |
| 3 | CatEndoMagma | + Internal composition + substrate + fixpoint | **Evaluating**: elements compose and evaluate themselves | Internal hom; closed category |

Each step internalizes a capability that previously required external infrastructure:
- Level 1 internalizes *encoding* (the retraction pair lets elements name each other)
- Level 2 internalizes *classification* (the classifier lets elements judge each other)
- Level 3 internalizes *evaluation* (internal composition lets elements compute with each other)

And each step is independent of the previous — proved by concrete finite models that have the earlier structure but lack the later one.

### The hierarchy as progressive closure

Another way to see the three levels: each one *closes* a previously open operation.

1. **FRM**: The algebra acts on itself (left multiplication), but the action is just raw data — there is no internal organization of the action space. The algebra can compute, but it cannot reflect on what it computes.

2. **DRM**: The action space is now *organized* — every morphism is either truth-valued or computation-valued, with no mixing. The algebra has an internal type system (classifier vs non-classifier). But computation is still *external* — you need a machine outside the algebra to evaluate compound expressions.

3. **CDRM**: Computation is *internal* — the algebra contains elements that represent composites of its own operations. The external machine is eliminated. The reflective tower terminates.

This is analogous to the progression in category theory:
1. **Category**: objects and morphisms, but composition is metalinguistic
2. **Category with subobject classifier**: internal truth values, but function spaces are external
3. **Closed category**: internal hom, function spaces are first-class objects

The analogy is not exact — a CDRM is not a topos, and the Compose axiom is not a full internal hom. But the *pattern* is the same: progressive internalization of metalinguistic operations.

## 6. What Survives Translation

The following results are stated in standard categorical vocabulary and do not depend on Ψ-specific concepts:

**Theorem (Three-Category Decomposition).** In any DRM, the set S decomposes as S = Z ⊔ C ⊔ N where Z = {left-absorbers}, C = {elements with entirely {z₁, z₂}-valued action on core}, N = {elements with entirely non-{z₁, z₂}-valued action on core}. The decomposition is exhaustive and the classes are pairwise disjoint. [Lean-proved, universal]

**Theorem (Kripke Wall).** C ∩ N = ∅ — no element is partially classifying and partially computational. [Lean-proved, universal]

**Theorem (Retraction Pair Placement).** The section and retraction are both non-classifiers: s, r ∈ N. [Lean-proved, universal]

**Theorem (Asymmetry).** No extensional magma with two distinct left-absorbers is commutative. [Lean-proved, universal]

**Theorem (Cardinality Bounds).** |S| ≥ 4 for any DRM; |S| ≥ 5 when s ≠ r. Both bounds are tight. [Lean-proved, universal]

**Theorem (No Right Identity).** No DRM has a right identity element. [Lean-proved, universal]

**Theorem (Partial Application Injectivity).** If an FRM self-simulates, the partial application map a ↦ eval(App(t, rep(a))) is injective. [Lean-proved, universal]

**Independence Result 1.** FRM ⊬ Kripke dichotomy. Counterexample: N=8 FRM with mixed elements that self-simulates (64/64 cells). [SAT]

**Independence Result 2.** DRM ⊬ internal composition. Counterexample: N=10 DRM satisfying Kripke dichotomy where no element satisfies the Compose axiom. [SAT]

**Independence Result 3.** DRM ⊬ substrate existence. Counterexample: N=10 DRM satisfying Kripke dichotomy with no inert element. [SAT]

**Independence Result 4 (new).** CDRM machinery ⊬ Kripke dichotomy. Counterexample: N=10 FRM with retraction pair, classifier, Branch, Compose, Y fixed-point — all Level 3 evaluation machinery — but 4 mixed elements violating the Kripke dichotomy. The algebra can evaluate (Branch + Compose + Y all hold) but cannot classify coherently (rows mix boolean and non-boolean outputs on core). [SAT, `composition_forces_kripke_test.py`]

This is the **diagonal independence result**: Level 3 does not imply Level 2. Internal composition does not force the Kripke wall. A system can evaluate without organizing its elements into coherent roles. The wall is an architectural choice about *interpretability* — making the algebra's elements legible as classifiers vs transformers — not a consequence of *computational power*.

Combined with Independence Results 1–3, the full independence picture is:

```
         Level 1 (FRM)    Level 2 (DRM)    Level 3 (CDRM)
Level 1    —               ⊬ (N=8)          ⊬ (N=10, Result 4)
Level 2    trivial          —               ⊬ (N=10, Results 2–3)
Level 3    trivial          ⊬ (N=10, R4)     —
```

No level implies any other. The three enrichment steps are fully independent.

## 7. What Does Not Survive (Yet)

The following claims require further work to establish in general categorical terms:

**Self-simulation → classification (open).** The informal argument: any system that can compute its own multiplication table must be able to distinguish different behavioral types (classifiers vs non-classifiers) to dispatch correctly. The formal gap: `SelfSimulation.lean` proves injectivity consequences but does not derive the Kripke dichotomy. The N=8 counterexample shows that self-simulation does NOT force the dichotomy. So the correct statement is: self-simulation forces *naming* but not *judging*. Judging is an independent architectural requirement.

**Generalization beyond finite magmas (open).** The three-category decomposition is proved for finite extensional magmas. Whether an analogous decomposition holds in:
- Infinite algebras (countable or uncountable magmas)
- Typed settings (simply-typed λ-calculus, System F)
- Higher-categorical settings (2-categories, ∞-categories)

is open. The conjecture: the dichotomy (clean separation of classifiers and non-classifiers) is a *finiteness* phenomenon — in infinite settings, partially classifying elements may exist, and the wall may soften to a spectrum. Whether the three-*level* separation (naming/judging/evaluating) persists regardless of whether the wall is hard or soft is the deeper question.

**Internal hom completeness (open).** The Compose axiom η · x = ρ · (g · x) provides one specific internal composite. A full internal hom would require arbitrary composition to be representable. Whether the CDRM axioms imply a richer internal composition structure, or whether they provide exactly the fragment needed for Turing-complete evaluation and no more, is open.

**Functorial naturality (open).** The three-category decomposition should be a functor from the category of DRMs (with structure-preserving morphisms) to the category of 3-partitioned sets. This functor should be natural. The ingredients are clear (the decomposition is defined uniformly for all DRMs), but the formal verification requires:
1. Defining the category DRM with appropriate morphisms
2. Proving the decomposition is preserved by morphisms
3. Formalizing this in Lean

This has not been done. The decomposition is proved for each individual DRM but not as a functorial construction.

## 8. The Honest Assessment

**What the categorical reconstruction establishes:**
- The three levels correspond to three standard categorical enrichment steps: retraction pair → subobject classifier → internal composition
- The independence results are facts about these standard structures, not artifacts of Ψ-specific vocabulary
- The three-category decomposition and the Kripke wall are universal theorems that hold for all models, stated in standard vocabulary (zero morphisms, subobject classifier, faithful representation)

**What remains open:**
- Whether the three-level separation reappears in categorically different settings (λ-calculus, typed systems, infinite algebras)
- Whether the Kripke dichotomy is an instance of a known categorical property (it resembles decidability of the subobject classifier, but the precise relationship is not formalized)
- Whether the specific role inventory (the seven roles, the McCarthy correspondence) is unique or one of several equivalent bases within the three categories
- Whether the internal composition fragment (Compose axiom) admits characterization as a universal property

**The categorical vocabulary translation:**

| Ψ Concept | Categorical Translation | Standard? |
|-----------|------------------------|-----------|
| Left-absorber | Zero morphism (constant endomorphism) | Yes |
| Extensionality | Faithfulness of left-regular representation | Yes |
| Retraction pair (Q/E) | Section-retraction pair | Yes |
| Classifier (τ) | Subobject classifier restricted to 2-valued | Yes |
| Kripke dichotomy | Decidability of the classifier partition | Novel (finite analog) |
| Three-category decomposition | Zero / classifier-orbit / complement | Standard components, novel combination |
| Kripke wall (C ∩ N = ∅) | Partition completeness of classifier action | Novel (finite analog) |
| Conditional copairing (ρ) | Conditional morphism / case analysis | Yes (coproduct structure) |
| Substrate (g) | Ground object / constant constructor | Yes (analogous to terminal object in stratum) |
| Internal composition (η) | Fragment of internal hom | Yes (weaker than full internal hom) |
| Fixed-point combinator (Y) | Fixed-point operator | Yes (standard in domain theory) |

The novel elements are the Kripke dichotomy (a strong finiteness-dependent partition property) and the three-category decomposition as a universal invariant. Everything else translates directly to standard categorical vocabulary.

## 9. The Conjecture (Revised)

The three levels — naming (retraction pair), judging (subobject classifier + dichotomy), evaluating (internal composition) — are three independent internalization steps. The independence is now proved in **both directions**: no level implies any other (Independence Results 1–4). The universality across formalisms is conjectured.

The strongest form of the original conjecture — **any finite extensional algebra that can internally evaluate must contain a subobject classifier satisfying the dichotomy** — is **refuted** by Independence Result 4. The N=10 counterexample has all Level 3 evaluation machinery (Branch, Compose, Y) but violates the Kripke dichotomy. Internal evaluation does not force clean roles. You can compute without classifying coherently.

**The revised conjecture:** The three levels are three independent *design choices* for finite reflective systems:
1. **Naming** (retraction pair): enables self-simulation — the algebra can encode and decode its own elements
2. **Organization** (Kripke dichotomy): enables self-description — the algebra's elements have coherent, interpretable roles
3. **Internalization** (internal composition): enables self-hosting — the algebra can evaluate without external help

Any finite reflective system must make choice (1). Choices (2) and (3) are independent of each other and of (1). A system can evaluate without organized roles (Independence Result 4). A system can have organized roles without internal evaluation (Independence Results 2–3). A system can self-simulate without either (Independence Result 1). The Ψ₁₆ᶠ table makes all three choices.

The significance of the Kripke wall is therefore not computational but **epistemic**: it is the axiom that makes the algebra's structure *legible*. A system without the wall can compute but cannot coherently classify its own elements into behavioral categories. The wall is the difference between a system that works and a system that *understands itself as working*.

Evidence for the revised conjecture: convergence of four independent axiom systems on the same three-category architecture (when the dichotomy is present). Evidence for full independence: concrete finite counterexamples at every boundary and every diagonal (N=8, N=10).

The architecture (three categories, walls) is a theorem for systems that choose the dichotomy. The independence of the three choices is a theorem. The specific role inventory (seven roles, McCarthy correspondence) is convergent evidence. The cross-formalism universality of the three *choices* is conjectured.

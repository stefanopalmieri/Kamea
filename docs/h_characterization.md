# Presentation-Independent Characterization of H

*The self-execution capability corresponds to a standard categorical structure: partial internal composition.*

---

## The Problem

S corresponds to a section-retraction pair (the algebra can name its own elements). D corresponds to a decidable subobject classifier (classification and transformation don't mix). H was a bundle of operational axioms — Compose (η·x = ρ·(g·x)), Inert (g maps core to core), Branch (ρ dispatches on τ), and Y (fixed-point combinator). The goal: find a single categorical property that captures what H IS, with the axioms as witnesses rather than definition.

## The Result

**Categorical property:** Partial internal composition — the left-regular representation contains a non-trivially composed element.

**Finite-algebra instantiation (Internal Composition Property / ICP):**

> *There exist pairwise distinct elements a, b, c ∈ S \ {⊤, ⊥} such that b preserves the core, the composite function c ∘ b on core equals a's row on core, and a takes at least two distinct values on core.*

Formally: ∃ a, b, c ∈ S \ {z₁, z₂}, pairwise distinct, such that:

1. **Core-preservation:** b · x ∉ {z₁, z₂} for all x ∈ core(S)
2. **Factorization:** a · x = c · (b · x) for all x ∈ core(S)
3. **Non-triviality:** |{a · x : x ∈ core(S)}| ≥ 2

In one sentence: **"The left-regular representation admits a non-trivial factorization L_a = L_c ∘ L_b on core, with L_b core-preserving."**

This is one concept — *partial internal composition* — not a list of four capabilities. "Factorable action" is the concrete finite-algebra term for the same property.

## Equivalence

ICP is **empirically equivalent** to the current H axioms (Compose + Inert with non-trivial composite) across:

- **3 Lean-proved N=10 counterexamples:** D⊬H (ICP fails ✓), H⊬D (ICP holds ✓), S+D+H (ICP holds ✓)
- **250 diverse SAT-generated retraction magmas** at N=10: 250/250 agreement (100%)
  - 50 models forced to satisfy H → all satisfy ICP
  - 50 models forced to violate Compose (at g=6, ρ=7) → ICP holds iff H holds with other element assignments
  - 50 models with Kripke dichotomy but no Compose → none satisfy ICP
  - 100 unconstrained FRM models → ICP matches H on every model

**ICP ↔ H_nontrivial: PERFECT EQUIVALENCE** across all tested models.

## Why Each Condition Is Needed

Three degeneracies were identified and eliminated during the investigation:

| Degeneracy | Example | Fix |
|---|---|---|
| Self-composition: Q ∘ Q = E (retraction inverse as power) | b = c = Q, a = E | Pairwise distinct (b ≠ c) |
| Trivial collapse: classifier ∘ inert → constant absorber row | ρ=classifier, g=inert, η→all-zero | Non-triviality (≥ 2 distinct values) |
| Over-restriction: requiring a to map core to core | Fails on H⊬D counterexample where η has mixed outputs | Allow a to have absorber outputs |

Each condition has a specific role:
- **Pairwise distinct** eliminates algebraic tautologies (Q² = Q⁻¹ = E)
- **Core-preservation of b** is the inertness requirement: the "storage" step must not collapse data to boundary values
- **Factorization** is the composition requirement: one evaluation step decomposes as storage-then-processing
- **Non-triviality** ensures the composition carries information, not just annihilates it

## What ICP Captures and What It Doesn't

ICP captures the **core** of H: Compose + Inert. It does NOT capture the enrichments:

| H Component | Captured by ICP? | Status |
|---|---|---|
| **Compose** (η = ρ ∘ g) | YES — this IS the factorization condition | Core |
| **Inert** (g maps core to core) | YES — this IS the core-preservation condition | Core |
| **Branch** (ρ dispatches on τ) | NO — ICP doesn't require conditional routing | Enrichment |
| **Y** (fixed-point combinator) | NO — ICP doesn't require recursion | Enrichment |

This aligns with the existing framework structure. The inevitability summary already identifies Compose + Inert as the core of Layer 2 (machine internalization), with Branch and Y as enrichments that enable specific computational patterns. ICP formalizes exactly the core.

## Categorical Interpretation

ICP has a natural categorical reading: **the endomorphism magma admits a partial internal composition**.

In a monoidal closed category, the internal hom [B, C] is an object representing Hom(B, C). A category is *closed* if all internal homs exist. ICP says: the left-regular representation of the magma contains at least one composed morphism. Specifically:

- The left-multiplication maps {L_a : a ∈ S} form a subset of End(core(S))
- ICP says: ∃ a, b, c such that L_a = L_c ∘ L_b (a represents the composite of c after b)
- With the constraint that L_b(core) ⊆ core (the inner morphism doesn't escape)

This is a fragment of monoidal closure: not every composite is representable, but at least one is. Full closure ({L_a} closed under composition) is **far too strong** — it fails for all tested models, including those with H. The algebra represents exactly the evaluation-relevant composite, nothing more.

**H = the algebra has a minimal internal hom fragment.**

## The Three Capabilities Restated

| Capability | Categorical property | Finite-algebra definition |
|---|---|---|
| **S** (self-representing) | Section-retraction pair | Retraction pair on core |
| **D** (self-describing) | Decidable subobject classifier | Every non-absorber is all-boolean or all-non-boolean on core |
| **H** (self-hosting) | Partial internal composition | Some element's action on core factors non-trivially through two others, one core-preserving |

All three correspond to standard categorical structures. The finite-algebra definitions reference no specific element names or operational axioms.

## What Was Tested and What Was Ruled Out

### Route 1: Full Compositional Representability (CR)

**Tested:** For all a, b ∈ S, ∃ c such that c · x = a · (b · x) on core.

**Result:** WRONG DIRECTION. The D⊬H model has MORE representable compositions (62%) than H models (31%). Full CR correlates inversely with H because models with fewer distinct rows have more accidental row-collisions.

| Model | Full CR | Core CR | Has H? |
|---|---|---|---|
| D⊬H | 62/100 (62%) | 32/64 (50%) | NO |
| H⊬D | 31/100 (31%) | 4/64 (6%) | YES |
| S+D+H | 31/100 (31%) | 5/64 (8%) | YES |

Full CR is not a viable characterization. The algebra doesn't need ALL compositions to be internal — just the evaluation-relevant one.

### Route 2: Internal Action (program/data closure)

**Tested:** Programs applied to data stay in the data domain (P · X ⊆ X ∪ ABS).

**Result:** DOES NOT DISCRIMINATE. Closure rates are 79%, 70%, and 50% for D⊬H, H⊬D, and S+D+H respectively. The best H model has the WORST closure. The Q-depth data domain is too small (2-5 elements) to give meaningful results at N=10.

The internal action property captures something about the SEMANTICS of the term algebra, not the STRUCTURE of the magma. It requires knowledge of which elements are "programs" and which are "data" — information that depends on the evaluation semantics, not just the Cayley table.

### Route 3: Evaluation Closure (depth-k representability)

**Tested:** What fraction of depth-k compositions are representable?

**Result:** DOES NOT DISCRIMINATE. Depth-2 representability is 61%, 12%, and 15% for D⊬H, H⊬D, and S+D+H. Again inverted — the model without H has the most representable deep compositions.

### Route 4: Factorization Variants

Multiple variants tested:

- **Evaluator Absorption** (compositions involving eval-relevant elements): 56%, 25%, 27%. Does not discriminate.
- **Essential CR** (specific element properties): Correctly discriminates but is essentially a restatement of the current axioms.
- **ICP with various non-triviality conditions**: ICP_v1 (≥2 distinct values) and ICP_v2 (+c has non-absorber outputs) both give PERFECT EQUIVALENCE. ICP_v3 (+a maps core to core) is TOO STRONG — fails on H⊬D.

## Why H Resists Full Abstraction

The investigation reveals why H is harder to abstract than S or D:

1. **S is global:** the retraction pair acts on ALL of core. It's a property of the whole algebra.
2. **D is global:** the Kripke dichotomy constrains EVERY non-absorber element. It's a partition of the entire algebra.
3. **H is local:** ICP only requires ONE factored element. It's the existence of a single algebraic witness.

This locality is inherent. The evaluator needs exactly one composition step (store-then-dispatch). It doesn't need all compositions to be internal, or most, or even many. It needs exactly one. This makes H intrinsically existential rather than universal, which is why it felt like a bundle of operational axioms — each axiom was witnessing a different aspect of the same existential statement.

ICP shows that the "bundle" is actually a single existential: ∃ a non-trivial internal composite. Compose, Inert, Branch, and Y are four witnesses of this one fact, not four independent requirements. (Branch and Y are enrichments that go beyond what ICP captures, but ICP captures the core.)

## What ICP Does NOT Solve

1. **Branch and Y are still enrichments.** ICP captures Compose + Inert but not Branch (conditional dispatch) or Y (recursion). A fuller characterization might say: "ICP + conditional dispatch + fixed-point existence." Whether these can be unified into a single property remains open.

2. **The characterization is empirical, not proved.** The equivalence ICP ↔ H holds across 250+ tested models but is not a theorem. A Lean proof of the equivalence (or a counterexample) would strengthen the result.

3. **The non-triviality condition feels ad hoc.** Conditions (1) and (2) of ICP are natural — pairwise distinct, core-preserving, factored. Condition (3) (≥2 distinct values) patches a specific degeneracy. A more elegant formulation might subsume this.

## Artifacts

- `h_characterization_investigation.py` — Route 1-4 testing on Lean counterexamples
- `h_characterization_sat.py` — SAT validation across 100 random FRM models
- `h_characterization_targeted.py` — Targeted SAT with degeneracy discovery
- `h_characterization_final.py` — Final validation: 250 models, all variants, perfect equivalence

## Reproduction

```bash
python3 h_characterization_final.py    # full validation (requires z3-solver)
```

---

## Summary

H = **partial internal composition** — the left-regular representation admits a non-trivial factorization on core.

One categorical concept, one sentence, no element names. In finite algebras, this instantiates as the Internal Composition Property (ICP). The current axioms (Compose + Inert) are witnesses. Branch and Y are enrichments that provide conditional dispatch and recursion on top of the basic composition.

| Capability | Categorical property | Finite-algebra instantiation | Witnesses |
|---|---|---|---|
| S | Section-retraction pair | Retraction pair on core | Q, E |
| D | Decidable subobject classifier | Dichotomic partition of non-absorbers | τ, Kripke wall |
| H | Partial internal composition | Non-trivial factorable action on core | η, g, ρ |

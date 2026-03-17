# Axiom Archaeology Results

*Raw data for [`axiom_inevitability.md`](axiom_inevitability.md), which presents the refined three-layer interpretation.*

**Date**: 2026-03-17
**Script**: `ds_search/axiom_archaeology.py`
**N**: 12 (minimum size where all axioms are SAT)

## Summary of Findings

### Phase 1: Single Axiom Removal

**Result: Removing ANY single axiom keeps the system SAT with identical category counts.**

| Removed | Status | Abs | Tst | Enc | Inr | Change |
|---------|--------|-----|-----|-----|-----|--------|
| Baseline | SAT | 2 | 1 | 8 | 1 | — |
| Kleene | SAT | 2 | 1 | 8 | 1 | SAME |
| InertProp | SAT | 2 | 1 | 8 | 1 | SAME |
| PA | SAT | 2 | 1 | 8 | 1 | SAME |
| VV | SAT | 2 | 1 | 8 | 1 | SAME |
| QE | SAT | 2 | 1 | 8 | 1 | SAME |
| E-trans | SAT | 2 | 1 | 8 | 1 | SAME |
| 1-Inert | SAT | 2 | 1 | 8 | 1 | SAME |
| Branch | SAT | 2 | 1 | 8 | 1 | SAME |
| Compose | SAT | 2 | 1 | 8 | 1 | SAME |
| Y | SAT | 2 | 1 | 8 | 1 | SAME |
| Selection | SAT | 2 | 1 | 8 | 1 | SAME |

**Interpretation**: No single axiom is necessary for SAT or for the 5-category structure. The role constraints (tester/encoder/inert type-forcing) plus L0 (absorbers + extensionality) are doing the heavy lifting for category formation.

### Phase 2: Wall Survival Under Axiom Removal

| Removed | Kleene Wall (τ) | Substrate Wall (g) | Composition Wall (η) |
|---------|----------------|-------------------|---------------------|
| Kleene | HOLDS | HOLDS | **1/3 BROKE** |
| InertProp | HOLDS | HOLDS | HOLDS |
| PA | HOLDS | HOLDS | **1/3 BROKE** |
| VV | HOLDS | HOLDS | HOLDS |
| QE | HOLDS | HOLDS | **2/3 BROKE** |
| E-trans | HOLDS | HOLDS | HOLDS |
| 1-Inert | HOLDS | HOLDS | HOLDS |
| Branch | HOLDS | HOLDS | HOLDS |
| Compose | HOLDS | HOLDS | **2/3 BROKE** |
| Y | HOLDS | HOLDS | HOLDS |
| Selection | HOLDS | HOLDS | **1/3 BROKE** |

**Key findings**:
- **Kleene wall (τ isolated)**: Completely robust — survives removal of ANY axiom
- **Substrate wall (g isolated)**: Completely robust — survives removal of ANY axiom
- **Composition wall (η partial)**: Fragile — breaks under removal of Kleene, PA, QE, Compose, or Selection
  - QE and Compose are most critical (2/3 UNSAT pairs become SAT)
  - The η isolation depends on a web of interacting axioms, not a single one

**Interpretation**: The first two walls (τ and g isolation) are structurally inevitable — they follow from the Roles constraints alone. The third wall (η partial isolation) is the genuinely axiom-dependent structure, requiring the interplay of multiple behavioral axioms.

#### Composition Wall — Detailed Breakdown

| Removed | η=Q | η=E | η=ρ | η=f | η=Y |
|---------|-----|-----|-----|-----|-----|
| Baseline | UNSAT | UNSAT | UNSAT | SAT | SAT |
| -Kleene | UNSAT | UNSAT | **→SAT** | SAT | SAT |
| -PA | UNSAT | UNSAT | **→SAT** | SAT | SAT |
| -QE | **→SAT** | **→SAT** | UNSAT | SAT | SAT |
| -Compose | **→SAT** | **→SAT** | UNSAT | SAT | SAT |
| -Selection | UNSAT | UNSAT | **→SAT** | SAT | SAT |

**Pattern**: Two distinct failure modes:
- **QE, Compose removal** → η can merge with Q or E (but NOT ρ)
- **Kleene, PA, Selection removal** → η can merge with ρ (but NOT Q or E)

This reveals that the Composition wall has two independent sub-walls defended by different axiom subsets.

### Phase 2b: Axiom Redundancy Check

| Axiom | Status |
|-------|--------|
| Kleene | **INDEPENDENT** (violated in model without it) |
| InertProp | **REDUNDANT** (implied by other axioms) |
| PA | **INDEPENDENT** |
| VV | **REDUNDANT** (implied by other axioms) |
| QE | **INDEPENDENT** |
| E-trans | **INDEPENDENT** |
| 1-Inert | **REDUNDANT** (implied by other axioms) |
| Branch | **INDEPENDENT** |
| Compose | **INDEPENDENT** |
| Y | **INDEPENDENT** |
| Selection | **INDEPENDENT** |

**Three redundant axioms**: InertProp, VV, and 1-Inert are implied by the rest. The minimal independent set has 8 axioms: {Kleene, PA, QE, E-trans, Branch, Compose, Y, Selection}.

### Phase 3: Maximum Removable Set

**Result: ALL 11 behavioral axioms can be removed while keeping SAT + 5 categories.**

| Axioms Removed | Kept | Categories |
|---|---|---|
| 4 | {1-Inert, Branch, Compose, E-trans, QE, Selection, Y} | 2-1-8-1 |
| 5 | {1-Inert, Branch, Compose, E-trans, Selection, Y} | 2-1-8-1 |
| 6 | {1-Inert, Branch, Compose, Selection, Y} | 2-1-8-1 |
| 7 | {Branch, Compose, Selection, Y} | 2-1-8-1 |
| 8 | {Compose, Selection, Y} | 2-1-8-1 |
| 9 | {Selection, Y} | 2-1-8-1 |
| 10 | {Selection} | 2-1-8-1 |
| **11** | **{} (NONE)** | **2-1-8-1** |

**The 5-category structure with 2-1-8-1 distribution requires ZERO behavioral axioms.** L0 (absorbers + extensionality) plus Roles (type-forcing tester/encoder/inert on specific indices) is sufficient.

### Phase 3b: Wall Survival With Zero Behavioral Axioms

| Wall | Result |
|------|--------|
| Kleene: τ vs non-absorber roles (7 pairs) | **ALL HOLD** (7/7 UNSAT) |
| Kleene: τ vs absorbers (2 pairs) | BROKE (τ=⊤, τ=⊥ now SAT) |
| Substrate: g vs non-absorber roles (6 pairs) | **ALL HOLD** (6/6 UNSAT) |
| Substrate: g vs absorbers (2 pairs) | BROKE (g=⊤, g=⊥ now SAT) |
| Composition: η vs all roles (5 pairs) | **ALL BROKE** (5/5 SAT) |

**Key insight**: With zero behavioral axioms:
- Kleene wall: 7/9 pairs still UNSAT (only absorber merges break)
- Substrate wall: 6/8 pairs still UNSAT (only absorber merges break)
- Composition wall: completely gone (0/5 UNSAT)

The absorber merges (τ=⊤, g=⊤) break because without behavioral axioms, nothing prevents a tester or inert row from also being absorbing. The behavioral axioms (especially Kleene) close this gap.

### Phase 4: Candidate New Axioms (Direction 3)

| Candidate | Status | Notes |
|-----------|--------|-------|
| QE associativity: Q·(E·x) = (Q·E)·x on core | **SAT** | Compatible; doesn't change categories |
| Encoder associativity: a·(b·c) = (a·b)·c for all encoders | **UNSAT** | **New universal theorem!** |
| ∃ absorption pair: a·(b·a) = a | **SAT** | Witness: a=encoder, b=encoder |
| ∃ idempotent x≥2: x·x = x | **SAT** | Witness: encoder can be idempotent |
| ∃ left-distributive element a≥2 | **SAT** | Witness: a=inert (g) is left-distributive |
| Column distinctness (right-extensionality) | **SAT** | Compatible; categories unchanged |

**New theorems discovered**:
1. **Encoder associativity is UNSAT**: No model of the full axiom system can have all 6 encoder elements satisfy `a·(b·c) = (a·b)·c`. This is a new universal prohibition — encoders necessarily form a non-associative sub-structure.

**Compatible extensions**:
1. **QE associativity** can be added without conflict — it constrains Q·E interactions further
2. **Column distinctness** (right-extensionality) is compatible — can require all columns to be distinct
3. **The inert element can be left-distributive** — `g·(b·c) = (g·b)·(g·c)` is SAT. This is surprising and gives the substrate a ring-like flavor.

## Architectural Implications

### What the Roles axiom is really doing

The Roles constraints (forcing specific indices to be tester/encoder/inert types) are doing almost ALL the structural work. The behavioral axioms (QE, Branch, Compose, etc.) primarily serve to:

1. **Partially isolate η** (Composition wall) — this is the only wall that depends on behavioral axioms
2. **Further constrain the model space** — reducing freedom but not changing the category structure

### Minimal axiom set for 5 categories + 2 walls

**L0 + Roles** alone is sufficient for:
- 5 categories (absorber, tester, encoder, inert)
- Kleene wall (τ isolated)
- Substrate wall (g isolated)

The behavioral axioms are needed ONLY for the Composition wall and for the specific functional relationships (quote/eval, branch, compose, Y-combinator) that give the algebra its computational character.

### The honest picture

The five categories and two major walls are **structural inevitabilities** — they follow from the mere *existence* of elements with tester/encoder/inert row profiles plus extensionality. The behavioral axioms add computational structure *within* the already-determined categorical framework. They don't create the framework; they furnish it.

This is evidence that the role structure is NOT axiom-dependent — it would emerge from any reasonable axiom system that requires elements with these distinct row profiles. The specific *content* of the roles (what Q does vs what E does) is axiom-dependent, but the *existence* of the role categories is not.

---

## Direction 2: Alternative Axiom Systems

**Script**: `ds_search/alternative_axioms.py`

### Approach A: Information-Theoretic

Axioms based on information flow (constant/injective/surjective rows + inverse pair + discoverability), with NO reference to Ψ roles.

| Result | Value |
|--------|-------|
| Status | **SAT** |
| Absorbers | 2 |
| Testers | 1 |
| Encoders | 9 |
| **Inert** | **0** |
| 5 categories | **NO** — missing inert |

**Key finding**: The information-theoretic approach produces 4 categories, not 5. The "lossy" row property (non-injective, non-boolean) maps to encoders, not to a separate inert category. Without an explicit axiom forcing an inert element, the optimizer avoids creating one.

The injective row requirement is SAT — element 7 was injective on non-absorber inputs (10/10 unique outputs). This shows injective encoders exist in the model space.

### Approach B: Category-Theoretic

Axioms: retraction pair (section/retraction = QE analog), classifier morphism (tester), inert morphism, conditional dispatch (branch analog).

| Result | Value |
|--------|-------|
| Status | **SAT** (26.4s — hardest of the three) |
| Absorbers | 2 |
| Testers | 1 |
| Encoders | 8 |
| Inert | 1 |
| 5 categories | **YES** |

**Key finding**: Category-theoretic axioms produce the same 5-category structure. The 2-1-8-1 distribution (abs-tst-enc-inr) matches the Ψ baseline exactly. This approach converged despite being formulated in terms of retractions, classifiers, and conditional morphisms rather than quote/eval/branch.

### Approach C: Game-Theoretic (Discoverability-First)

Axioms: discoverability as PRIMARY requirement, plus classifiers, transformers, neutral strategies, and strategic diversity (inverse pair).

| Result | Value |
|--------|-------|
| Status | **SAT** (0.2s — fastest) |
| Absorbers | 2 |
| Testers | 1 |
| Encoders | 8 |
| Inert | 1 |
| 5 categories | **YES** |
| All elements discoverable | **YES** |

**Key finding**: Starting from discoverability as the primary axiom (not a consequence) also converges to the same 5-category structure. The game-theoretic framing — dominant strategies (absorbers), classifiers (testers), transformers (encoders), neutral strategies (inert) — produces 2-1-8-1 distribution.

### Cross-Approach Comparison

| Approach | 5 Categories | Distribution | Missing |
|----------|-------------|-------------|---------|
| Ψ axioms (baseline) | YES | 2-1-8-1 | — |
| A: Information-theoretic | **NO** | 2-1-9-0 | Inert |
| B: Category-theoretic | YES | 2-1-8-1 | — |
| C: Game-theoretic | YES | 2-1-8-1 | — |

**Convergence result**: 2 out of 3 alternative axiom systems converge to exactly the same category distribution as the Ψ axioms. The information-theoretic approach misses inert because it has no axiom forcing a "lossy but minimal" element — its definition of "lossy" (non-injective, non-boolean) maps onto the encoder category.

**Implication**: The 5-category structure with the specific 2-1-8-1 distribution is robust across fundamentally different axiom vocabularies. It emerges from category theory and game theory just as it does from the Ψ framework. The inert category specifically requires some axiom that forces a "ground/substrate" element — without it, the optimizer fills all slots with encoders.

---

## Critical Experiment: What Forces What?

### The "Did We Encode Lisp?" Test

The central question from AXIOM_PROMPT.md: are the roles forced by self-description, or by the particular axiom vocabulary?

**Experiment**: Strip away different layers to isolate what forces the 5 categories.

| Configuration | Abs | Tst | Enc | Inr | 5 cats? |
|---|---|---|---|---|---|
| Full (behavioral + Roles) | 2 | 1 | 8 | 1 | YES |
| Behavioral only (no Roles) | 2 | 1 | 8 | 1 | **YES** |
| Behavioral except 1-Inert (no Roles) | 2 | 1 | 9 | 0 | NO (no inert) |
| Minimal comp core only (QE+Branch+Compose+Y+Selection, no Roles) | 2 | 0 | 10 | 0 | NO (no tester, no inert) |
| L0 only (no behavioral, no Roles) | 2 | 0 | 9 | 1 | NO (no tester) |
| Roles only (no behavioral) | 2 | 1 | 8 | 1 | YES |

### What this reveals:

**The 5-category structure has TWO independent sufficient conditions:**

1. **Roles alone** (no behavioral axioms) → 2-1-8-1 ✓
2. **Full behavioral axioms alone** (no Roles) → 2-1-8-1 ✓

But they achieve this through DIFFERENT mechanisms:

- **Roles** directly type-forces specific indices as tester/encoder/inert. This is definitional — it encodes the answer.
- **Behavioral axioms** produce 5 categories through the interaction of 1-Inert (forces inert existence), Kleene (forces tester/encoder separation), and the named-role axioms (Branch uses τ as a tester, forcing it to have boolean outputs). **Without 1-Inert, the inert category vanishes.** Without Branch (which references τ as a tester), nothing forces a tester to exist.

### The honest answer to "did we encode Lisp?"

**Partially yes, partially no.**

The named-role axioms (Branch references τ, QE references Q/E, Compose references η/g) implicitly constrain these elements to have specific row profiles. Branch forces τ to act as a tester. QE forces Q and E to be encoders (they must be bijective on a core). Compose forces η to be an encoder. The 1-Inert axiom explicitly forces an inert element to exist.

These constraints are SUFFICIENT to produce 5 categories even without explicit type-forcing. But they are not *accidentally* producing the categories — they are *computationally* producing them. The axioms describe computational operations (quote/eval, branch, compose, fixed-point) that inherently require elements with these row profiles.

**The categories are not forced by self-description in the abstract.** They are forced by the specific computational operations that self-description requires. A different formalization of self-description (e.g., without branch/compose) might produce different categories. The alternative axiom experiments (Direction 2) confirm this: systems without explicit inert-forcing (Approach A) miss the inert category.

## Overall Conclusions

1. **The 5-category structure has two independent sufficient conditions**: Roles alone (type-forcing) OR full behavioral axioms alone. Both produce 2-1-8-1. But the Roles path is definitional; the behavioral path is computational.

2. **The behavioral axioms produce categories through computational necessity**: Branch forces τ to be a tester (it must classify). QE forces Q/E to be encoders (they must biject). 1-Inert forces an inert element. Remove 1-Inert → inert vanishes. Remove Branch → tester vanishes from named roles.

3. **The Kleene and Substrate walls follow from row-profile typing** — they hold with zero behavioral axioms for non-absorber merges (7/9 and 6/8 pairs). They are structural consequences of the tester/encoder/inert definitions.

4. **The Composition wall is genuinely axiom-dependent** with two independent sub-walls:
   - η vs Q/E: defended by QE and Compose
   - η vs ρ: defended by Kleene, PA, and Selection
   - With zero behavioral axioms, the wall vanishes entirely.

5. **Three axioms are redundant**: InertProp, VV, and 1-Inert are implied by the remaining 8. The minimal independent set is {Kleene, PA, QE, E-trans, Branch, Compose, Y, Selection}.

6. **Encoder non-associativity theorem (refined)**: Full encoder associativity is UNSAT. The minimal obstruction is the **{ρ, η} pair** — branch and compose cannot be mutually associative. This follows from the Compose axiom (η·x = ρ·(g·x)) which creates a non-associative dependency. All 14 other encoder pairs CAN be associative. Every triple containing both ρ and η is UNSAT.

7. **Surprise findings**:
   - The inert element can be left-distributive: g·(b·c) = (g·b)·(g·c)
   - Idempotent non-absorbers exist (x·x = x for some encoder)
   - Column distinctness (right-extensionality) is compatible

8. **Cross-axiom convergence**: 2/3 alternative axiom systems (category-theoretic, game-theoretic) converge to 2-1-8-1. The information-theoretic approach misses inert, confirming that inert requires explicit forcing.

9. **The honest answer to "did we encode Lisp?"**: The categories are forced by the *computational operations* the axioms describe (quote/eval, branch, compose), not by self-description in the abstract. A different computational vocabulary might produce different categories. The structure is computationally inevitable, not ontologically inevitable.

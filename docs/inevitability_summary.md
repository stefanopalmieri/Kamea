# Inevitability Summary

*The definitive statement of the project's theoretical result. Detailed evidence in [`axiom_inevitability.md`](axiom_inevitability.md), [`forced_roles_theorem.md`](forced_roles_theorem.md), and [`axiom_archaeology_results.md`](axiom_archaeology_results.md).*

---

## The Three-Layer Result

### Layer 1 — Categorically Forced (zero choices)

Standard finite category theory: zero morphisms, retraction pair, subobject classifier, products, conditional copairing. No reference to self-description, Ψ, or Lisp.

**What emerges:**

- **Three behavioral categories**: absorbers (constant morphisms), classifiers (Bool-valued morphisms), transformers (morphisms with multiple non-boolean outputs).
- **Kleene wall**: classifiers cannot be transformers. A morphism's image is either contained in {0,1} or has elements outside {0,1}. These are mutually exclusive row profiles.
- **Rigidity**: 50/50 sampled categorical models are WL-1 rigid. No rigidity axiom was included — it emerges from the interaction of retraction pair + unique subobject classifier + product structure + conditional dispatch.
- **Discoverability**: 49/50 sampled categorical models have the property that every non-absorber element is uniquely identifiable from probes. No discoverability axiom was included.

**Evidence**: Five independent axiom systems tested (Ψ, information-theoretic, category-theoretic, game-theoretic, categorical topos). All five produce the three categories and the Kleene wall. Rigidity and discoverability verified on 50 categorical topos models.

**Status**: structurally universal.

### Layer 2 — Distinctness Axiom (standard algebraic practice)

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

### Layer 3 — One Philosophical Commitment

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
Standard category theory (zero morphisms, retraction pair,
subobject classifier, products, conditional copairing)
  → 3 categories + Kleene wall + rigidity + discoverability

+ Distinctness axiom (standard algebraic practice)
  → substrate exists + 7 specialized roles

+ Branch + Compose interaction (computational)
  → g = CONS (pair constructor must be substrate)
  → full McCarthy correspondence

+ 1-Inert (philosophical: ground is unique)
  → substrate uniqueness + actuality irreducibility
```

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

The Ψ role structure follows from three things: standard categorical structure (forces three categories and the Kleene wall), the distinctness axiom (forces full role specialization and substrate existence — standard algebraic practice, independently justified by expressiveness analysis), and one philosophical commitment (the ground is unique). The fusion of substrate with pair-constructor is forced by the interaction of Branch and Compose, and is what produces the full McCarthy correspondence.

The difference between "a finite algebra with classification and transformation" and "a finite algebra that recapitulates Lisp" is two things: the distinctness axiom (which selects substrate and role specialization) and the Compose axiom (which fuses substrate with pair-construction). Everything else is category theory.

---

## Formalization Status

| Layer | Current evidence | Formalization goal |
|-------|-----------------|-------------------|
| Layer 1 (categorical) | SAT analysis, 5 axiom systems | Lean: finite endomorphism monoids in Mathlib |
| Layer 2 (distinctness) | SAT verification at N=12, N=16 | Lean: add Distinct constraints to PsiStructure.lean |
| Layer 3 (Ψ-specific) | SAT analysis of Branch + Compose forcing | Lean: g-as-inert from Compose axiom |
| Specific model Ψ₁₆ᶠ | 83 in Psi16Full.lean; 130+ total across 4 proof files | Complete |
| Universal bounds | No right identity, card ≥ 4 | Complete |

The existing Lean proofs verify specific model properties and some universal bounds. Lean formalization of the categorical foundation (three-layer inevitability argument) is the primary formalization goal. Adding `Distinct` constraints to `PsiStructure.lean` is straightforward.

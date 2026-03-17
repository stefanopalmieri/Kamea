# Inevitability Summary

*The definitive statement of the project's theoretical result. Detailed evidence in [`axiom_inevitability.md`](axiom_inevitability.md), [`forced_roles_theorem.md`](forced_roles_theorem.md), and [`axiom_archaeology_results.md`](axiom_archaeology_results.md).*

---

## The Three-Layer Result

### Layer 1 — Categorically Forced

Standard finite category theory: zero morphisms, retraction pair, subobject classifier, products, conditional copairing. No reference to self-description, Ψ, or Lisp.

**What emerges:**

- **Three behavioral categories**: absorbers (constant morphisms), classifiers (Bool-valued morphisms), transformers (morphisms with multiple non-boolean outputs).
- **Kleene wall**: classifiers cannot be transformers. A morphism's image is either contained in {0,1} or has elements outside {0,1}. These are mutually exclusive row profiles.
- **Rigidity**: 50/50 sampled categorical models are WL-1 rigid. No rigidity axiom was included — it emerges from the interaction of retraction pair + unique subobject classifier + product structure + conditional dispatch.
- **Discoverability**: 49/50 sampled categorical models have the property that every non-absorber element is uniquely identifiable from probes. No discoverability axiom was included.

**Evidence**: Five independent axiom systems tested (Ψ, information-theoretic, category-theoretic, game-theoretic, categorical topos). All five produce the three categories and the Kleene wall. Rigidity and discoverability verified on 50 categorical topos models.

**Status**: structurally universal.

### Layer 2 — Selected by Expressiveness

The categorical axioms permit 0 to 5+ inert (substrate) elements. The expressiveness principle selects a specific region of this space.

**What is selected:**

- **Substrate exists (inert ≥ 1)**: without substrate, 2-step compositional expressiveness drops from 12.0 to 11.5 average values, and discoverability collapses from 9/10 to 1/10. The pair-constructor role is shoehorned into the classifier — a degenerate arrangement.
- **Full role specialization**: among tested collapse levels, 7 distinct role-bearing elements maximize compositional expressiveness (49 vs 16 1-step cells, depth-2 vs depth-3 reachability).

**What is NOT selected:**

- **Substrate uniqueness**: inert=1 and inert=2 tie on 2-step expressiveness (12.0) and discoverability (9/10). The expressiveness principle selects "at least one" but does not distinguish 1 from 2.

**Evidence**: `ds_search/inert_expressiveness.py` (10 models per inert count, 6 counts tested), `ds_search/compositional_expressiveness.py` (6 collapse levels).

**Status**: structurally selected (not axiomatized, not arbitrary).

### Layer 3 — Ψ-Specific

One axiom and one interaction complete the McCarthy correspondence.

**What is specific to Ψ:**

- **Substrate uniqueness** (exactly 1 inert element): the 1-Inert axiom. Expressiveness does not distinguish inert=1 from inert=2. This is a genuine commitment: "the ground is unique."

- **g = CONS** (substrate as pair constructor): forced by the interaction of Branch and Compose. The Compose axiom defines η·x = ρ·(g·x) — composition is packaging (g) then dispatching (ρ). Packaging means holding the input without transforming it. Holding without transforming is what inert means. Therefore the pair constructor must be the inert element.

  This is a logical chain, not a coincidence:
  1. Compose says: to compose, first package via g, then branch via ρ.
  2. Packaging means g holds its argument without altering it.
  3. "Holds without altering" is the definition of inert.
  4. Therefore g must be inert.
  5. Therefore CONS lives in the substrate.

  In categorical models without Branch + Compose, the pair constructor lives in an encoder (10/10 models at inert=1). Only the Ψ axioms force CONS into the substrate.

- **Full McCarthy correspondence**: all seven roles have homes, with CONS living in the substrate. This is the unique contribution of the Ψ axiom system.

**Evidence**: `ds_search/inert_expressiveness.py` (pair constructor analysis), `ds_search/forced_roles_test.py` (role-forcing), SAT verification of Branch + Compose forcing g-as-inert.

**Status**: Ψ-specific, but with a clean logical explanation.

---

## The Dependency Chain

```
Standard category theory (zero morphisms, retraction pair,
subobject classifier, products, conditional copairing)
  → 3 categories + Kleene wall + rigidity + discoverability

+ Expressiveness principle (maximal compositional capacity)
  → substrate exists + roles specialize to 7

+ 1-Inert axiom (philosophical: the ground is unique)
+ Branch + Compose interaction (computational: composition = package then branch)
  → g = CONS + full McCarthy correspondence
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

\*With explicit inert axiom — without it, inert is permitted but not forced; expressiveness selects it.

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

---

## Honest Scope

The Ψ role structure is computationally inevitable given representation (retraction pair), classification (subobject classifier), pairing (products), and dispatch (conditional copairing). Three of five categories and the Kleene wall are categorically universal. Substrate existence is expressiveness-selected. Substrate uniqueness is a philosophical commitment. The fusion of substrate with pair-constructor is Ψ-specific, forced by the interaction of Branch and Compose, and is what produces the full McCarthy correspondence.

The difference between "a finite algebra with classification and transformation" and "a finite algebra that recapitulates Lisp" is two things: the expressiveness principle (which selects substrate and role specialization) and the Compose axiom (which fuses substrate with pair-construction). Everything else is category theory.

---

## Formalization Status

| Layer | Current evidence | Formalization goal |
|-------|-----------------|-------------------|
| Layer 1 (categorical) | SAT analysis, 5 axiom systems | Lean: finite endomorphism monoids in Mathlib |
| Layer 2 (expressiveness) | SAT sampling, 6 inert counts × 10 models | Lean: monotonicity of cell count |
| Layer 3 (Ψ-specific) | SAT analysis of Branch + Compose forcing | Lean: g-as-inert from Compose axiom |
| Specific model Ψ₁₆ᶠ | 83 Lean theorems | Complete |
| Universal bounds | No right identity, card ≥ 4 | Complete |

The existing Lean proofs verify specific model properties and some universal bounds. Lean formalization of the categorical foundation (three-layer inevitability argument) is the primary formalization goal.

# Axiom Inevitability

*Companion to [`forced_roles_theorem.md`](forced_roles_theorem.md). The forced roles theorem says **what** the axioms force. This document says **why** — which parts are structurally universal and which are choices.*

Evidence: `ds_search/axiom_archaeology.py`, `ds_search/alternative_axioms.py`, `ds_search/axiom_archaeology_deep.py`. Raw data: [`axiom_archaeology_results.md`](axiom_archaeology_results.md).

---

## The Three-Layer Picture

### Layer 1: Universal

Emerged from all four independent axiom systems tested (phenomenological, information-theoretic, category-theoretic, game-theoretic).

- **Absorbers** (boundaries/ground). Two constant rows. Present in every system with extensionality.
- **Testers** (judgment/classification). Boolean rows that partition elements into two classes.
- **Encoders** (synthesis/transformation). Rows with multiple distinct non-boolean outputs.
- **Kleene wall**: judgment cannot merge with computation. A row cannot be simultaneously all-boolean and have multiple non-boolean outputs. This is a definitional impossibility, not an axiom — it follows from the definitions of tester and encoder.

### Layer 2: Computationally Inevitable

Present in 3/4 systems. Requires computational structure (QE + Branch + Compose or categorical equivalents).

- **Inert element** (substrate). A row that is neither tester nor encoder — it has non-boolean outputs but not enough diversity to qualify as an encoder.
- **Substrate wall**: substrate cannot merge with any active element. The inert row profile is incompatible with both tester and encoder profiles.
- **Five categories total** (absorber, tester, encoder, inert, plus the Composition sub-wall partially isolating η among encoders).
- **Seven roles under maximal expressiveness** = McCarthy's primitives.

### Layer 3: Philosophically Contingent

Specific to axiom systems that include a substrate commitment.

- **Actuality irreducibility**. The tester row is completely free — which elements the tester maps to ⊤ vs ⊥ is undetermined by structural axioms.
- **The axiom that self-description must encounter something outside its own descriptive machinery.** Formalized as 1-Inert: exactly one element whose row is neither classifying nor synthesizing.

---

## The Four Axiom Systems Tested

| System | Motivation | Distribution | Kleene Wall | Substrate Wall |
|--------|-----------|-------------|-------------|----------------|
| Ψ (phenomenological) | self-description | 2-1-8-1 | YES | YES |
| Info-theoretic (A) | information flow | 2-1-9-0 | YES | NO (no inert) |
| Category-theoretic (B) | retractions + products | 2-1-8-1 | YES | YES |
| Game-theoretic (C) | strategic diversity | 2-1-8-1 | YES | YES |

### Ψ — Phenomenological

Axiom vocabulary: absorbers, extensionality, Kleene separation, QE inverse pair, Branch dispatch, Compose, Y-combinator, Selection, 1-Inert. Motivated by self-description: a structure that identifies its own components through its own operation.

Result: 2 absorbers, 1 tester, 8 encoders, 1 inert. Both walls hold.

### Approach A — Information-Theoretic

Axiom vocabulary: constant rows (information-destroying), binary classifiers (information-partitioning), injective rows (information-preserving), non-injective non-boolean rows (lossy), inverse pair on a core, full discoverability. No reference to Ψ roles.

Result: 2 absorbers, 1 tester, 9 encoders, **0 inert**. Kleene wall holds. Substrate wall absent.

### Approach B — Category-Theoretic

Axiom vocabulary: retraction pair (section + retraction = QE analog), classifier morphism (tester), inert morphism, conditional dispatch (branch analog). Motivated by standard categorical concepts: retractions, products, classifiers.

Result: 2 absorbers, 1 tester, 8 encoders, 1 inert. Both walls hold.

### Approach C — Game-Theoretic (Discoverability-First)

Axiom vocabulary: dominant strategies (absorbers), classification strategies (testers), transformation strategies (encoders), neutral strategies (inert), strategic diversity (inverse pair), full discoverability as primary axiom.

Result: 2 absorbers, 1 tester, 8 encoders, 1 inert. Both walls hold. All non-absorber elements discoverable.

---

## The Information-Theoretic Divergence

Approach A produced no inert element. This is the structurally important divergence.

The information-theoretic vocabulary classifies rows by their information properties: constant (absorber), binary classifier (tester), injective (information-preserving encoder), lossy (non-injective encoder). There is no information-theoretic category for "inert" — a row that has some non-boolean output but not enough diversity to count as an encoder. In information-theoretic terms, such a row is simply a degenerate lossy function. The axioms provide no reason to distinguish it from other lossy functions, so the optimizer fills all non-absorber, non-tester slots with encoders.

The inert element does not emerge from information flow. It requires a commitment: the claim that self-description encounters something outside its own descriptive machinery. This commitment has phenomenological motivation. Husserl's concept of *hyle* — raw sensory matter not yet formed by intentional acts — corresponds precisely to the inert element: something consciousness encounters but that is not itself an act of judgment or synthesis. The Ψ axiom 1-Inert formalizes this philosophical claim. The category-theoretic and game-theoretic systems include analogous commitments (an inert morphism, a neutral strategy) and recover the inert element. The information-theoretic system, which has no such commitment, does not.

This is interpretive context, not part of the formal claim. The formal claim is: the inert category requires an axiom that forces a substrate element. Without such an axiom, the optimizer produces only encoders.

---

## Dependency Chain for the McCarthy Correspondence

| Role | McCarthy | Forced by | Layer |
|------|----------|-----------|-------|
| ⊤ | NIL | L0 (absorber) | Universal |
| τ | — | Kleene (tester/encoder incompatibility) | Universal |
| Q | QUOTE | QE axiom | Computationally inevitable |
| E | EVAL | QE axiom | Computationally inevitable |
| f | CAR | Branch (if-path) | Computationally inevitable |
| η | CDR | Compose | Computationally inevitable |
| ρ | COND | Branch (conditional) | Computationally inevitable |
| g | CONS | 1-Inert + Branch | Philosophically contingent |

g (CONS) is the only role that depends on the philosophically contingent layer. Without the inert element, the pair-constructor role has no natural home — there is no element whose row profile is compatible with serving as substrate for pairing. The difference between "a system that can classify and transform" and "a system that can do Lisp" is one axiom about substrate.

---

## Redundant Axioms

Three of the eleven behavioral axioms are redundant — implied by the remaining eight:

| Axiom | Status | Explanation |
|-------|--------|-------------|
| InertProp (D) | Redundant | Implied by Kleene + role constraints |
| VV | Redundant | Implied by remaining axioms |
| 1-Inert | Redundant | Implied by Branch + Compose + role constraints |

The minimal independent behavioral axiom set is: **{Kleene, PA, QE, E-trans, Branch, Compose, Y, Selection}** — eight axioms.

This strengthens the non-circularity argument. Fewer axioms means less opportunity for indirect encoding. The eight independent axioms each have clear, distinct motivations: Kleene enforces judgment/computation separation, PA ensures power-associativity, QE provides representation, E-trans makes eval transparent to absorbers, Branch provides conditional dispatch, Compose provides function composition, Y provides recursion, Selection connects composition to judgment.

---

## The Composition Wall Requires Deep Axiom Interaction

The Composition wall (η cannot merge with Q, E, or ρ) is the only wall that depends on behavioral axioms. How many axioms does it need?

| Axiom subset size | Sufficient for full wall? |
|---|---|
| 1 (any single axiom) | NO — all 11 singletons fail |
| 2 (any pair) | NO — all 55 pairs fail |
| 3 (any triple) | NO — all 165 triples fail |
| 4 (any 4-tuple) | NO — all 330 4-tuples fail |

The Composition wall requires **at least 5 of 11 behavioral axioms** working in concert. No small axiom subset reproduces it. This makes the Composition wall a genuinely emergent property of the axiom system — it arises from the interaction of multiple independent constraints, not from any single axiom or small group.

Recall from the detailed breakdown that the wall has two independent sub-walls (η vs Q/E defended by QE + Compose; η vs ρ defended by Kleene + PA + Selection). Even these sub-walls individually require their respective axiom groups plus the Roles constraints — neither sub-wall can be sustained by fewer than its required axioms.

---

## Encoder Non-Associativity Obstruction

Full associativity restricted to all six encoders {Q, E, f, ρ, η, Y} is UNSAT — encoders necessarily form a non-associative sub-structure.

The minimal obstruction is the pair **{ρ, η}**. Branch and compose cannot be mutually associative. This follows from the Compose axiom (η·x = ρ·(g·x) on core), which creates a non-associative dependency between the two elements.

| Subset | Associative? |
|--------|-------------|
| Any pair not containing both ρ and η | SAT (14/15 pairs) |
| {ρ, η} | **UNSAT** |
| Any triple containing both ρ and η | UNSAT (4/20 triples) |
| All 6 encoders | UNSAT |

All 14 encoder pairs that do not include both ρ and η can be associative. The non-associativity is localized to the branch-compose interaction.

---

## Honest Scope Statement

The Ψ role structure is computationally inevitable given QE + Branch + Compose, and three of its five categories are structurally universal. The fourth category (inert/substrate) is a philosophical commitment — well-motivated but not forced by computation or information theory alone. Whether this commitment is the correct formalization of self-description's encounter with actuality, or whether alternative formalizations exist that achieve the same structural effect without an explicit substrate axiom, remains the central open question.

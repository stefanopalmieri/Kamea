# Distinction Structures

### A Minimal Self-Modeling Framework for Relational Description

---

## What This Document Is

This document presents a framework built on a simple question: *what are the minimum concepts needed to describe any situation where things are distinguished from each other?*

The answer we found is four: Distinction, Context, Actuality, and Synthesis. We formalized these as a mathematical structure, proved the axioms consistent, and proved something surprising — the structure can contain a working behavioral model of itself. Not a label or a name, but a functioning internal replica: elements that, when operated on by the structure's own composition operation, reproduce the behavior of the structure's own components.

We then asked whether the structure could *reveal* this self-model to an outside observer — whether someone examining the structure with no prior knowledge could discover the self-description purely by probing. This led to a second surprise: symmetric composition (where the order of inputs doesn't matter) supports self-modeling but not self-announcement. To make the self-model discoverable, we needed directed composition (where order matters). The cost of this upgrade turned out to be remarkably small: one additional element and the switch from unordered to ordered inputs.

The document tells this story from start to finish. Part I introduces the four concepts in plain language. Part II formalizes them as mathematics. Part III proves the self-modeling result with a fully explicit construction. Part IV develops the category-theoretic perspective. Part V attempts discoverable reflexivity, hits a wall, and proves the wall is structural. Part VI crosses the wall with directed synthesis and constructs the discoverable model. Part VII draws out the implications and honestly assesses what is proven, what is conjectured, and what was tried and retracted.

Every proof is included in full. Every element earns its place.

---

## Part I: The Framework

### 1. Four Concepts

The framework rests on four interrelated concepts. They are not independent axioms but mutually defining aspects of a single structural situation: *something is distinguished, somewhere, actually, as part of a whole.*

#### 1.1 Distinction

A Distinction is the most primitive element of the framework: *that two things are not the same*. It does not presuppose what the things are, what properties they have, or what substrate supports them. It is pure non-identity.

A Distinction is always relative to a Context (see below). There is no Distinction "in itself," floating free. This is the framework's central commitment: **distinction is contextual and relational, as far as we can determine.**

This does not rule out context-independent units of distinction. It observes that none have been identified: every candidate (bits, qubits, Planck-scale quantities) is defined relative to measurement contexts. The framework treats contextuality as the working assumption while remaining open to revision.

#### 1.2 Context

A Context is the *locus at which Distinctions are sustained*. It is not a container, not a boundary between inside and outside, and not a subject. It is, minimally, whatever must be the case for a Distinction to be drawn rather than not drawn.

To prevent vacuity, we require: a Context is any situation in which at least one Distinction is sustained — in which non-identity is maintained rather than collapsing.

Examples include: a perceptual field, a measurement apparatus, a formal system, a biological membrane. What these share is not substrate but structure: each sustains at least one non-identity.

A key insight, revealed by the category-theoretic formalization (Part IV), is that **a Context is constituted by the Distinctions it sustains**. There is no hidden Context-essence behind the pattern of Distinctions. Strip away the Distinctions and there is no residual Context left over. A Context *is* its pattern of Distinctions. This is the structural content of Yoneda's Lemma applied to the framework.

The Context does not imply a knower on one side and a world on the other. A thermostat sustains a Distinction (above/below threshold) without cognition. The concept is more general than "experience" or "observation," though it includes both.

#### 1.3 Actuality

Actuality is the *selection of which Distinctions obtain* — the fact that some Distinctions are drawn rather than merely possible.

In any Context, indefinitely many Distinctions are possible (you could attend to the exact hue of each pixel in your visual field), but only some are actual at any moment (you notice the red of the traffic light against the grey sky). Actuality captures this difference: not *what* is distinguished, but *that* it is distinguished, here and now.

Is Actuality itself just another Distinction — the Distinction between "drawn" and "not drawn"? We hold that it is not. It plays a different structural role. Distinction describes *what*; Actuality describes *that*. The formal results make this precise: Actuality is a different mathematical type from Distinction. No operation converts one into the other. And the formalization revealed that Actuality is the *irreducible* component — the one not derivable from the other three.

#### 1.4 Synthesis

Synthesis is the capacity to treat multiple Distinctions as a unity — to compose a new, higher-order Distinction from lower-order ones. "Red," "round," and "sweet" synthesize into "apple." Pixel-level color Distinctions synthesize into "a face."

Synthesis gives the framework its scalability. Without it, we have only atomic Distinctions in a Context. With it, we can describe hierarchy, abstraction, and the emergence of composite entities.

A critical question is whether Synthesis merely groups for convenience or tracks real structural joints. We distinguish two modes. *Pragmatic synthesis* groups for convenience — the grouped Distinctions retain individual character and the grouping could be drawn differently (example: constellations). *Structural synthesis* tracks a real pattern — the composite participates in Distinctions that its components do not (example: a water molecule participates in Distinctions like liquidity that individual atoms do not). The framework provides vocabulary for asking which mode is operative in any given case.

### 2. The Central Claims

**Distinctions are contextual and relational, as far as we can determine.** The evidence is negative but robust: every candidate for a fundamental, context-independent unit of Distinction turns out to be defined relative to a framework of measurement or formalism.

**Four concepts suffice for relational description.** Any situation where distinctions are drawn can be described using Distinction, Context, Actuality, and Synthesis. This is a claim about sufficiency, not necessity — the necessity claim (that four is the minimum) is a conjecture, not yet proven.

**The framework describes itself.** The four concepts can be applied to the framework itself: each concept is distinguished from the others (Distinction), the framework is a locus where these Distinctions are sustained (Context), these specific Distinctions are actual within the framework (Actuality), and the four compose into a unity with properties none individually possess (Synthesis). The formal proof shows this self-description is behavioral, not merely verbal.

**Scope declaration.** The framework describes relational structure — what can be said once distinction is operative. It does not claim to describe what, if anything, is prior to relation. This boundary cannot appear as a concept within the framework, because any concept within it would already be relational. A framework that claimed to capture both the relational and the pre-relational would be incoherent.

### 3. Key Properties

**Parsimony.** Four concepts. No hidden assumptions about substance, causation, or subjectivity.

**Universality without vacuity.** The framework applies broadly, but the Context concept is constrained (requires sustained Distinction), preventing the trivial result that "everything is a Distinction Structure."

**Non-dualism.** The Context is a structural locus, not a mind or subject. Perceptual experience and physical measurement are described in the same terms without assuming one reduces to the other.

**Relational ontology.** Properties and entities are patterns of Distinction in a Context. "Red" is a Distinction, not an intrinsic quality. "Electron" is a pattern of Distinctions sustained in the Context of experimental physics.

**Epistemic modesty.** The framework does not claim that reality *is* Distinctions. It claims Distinctions are the minimal vocabulary for describing what we can know about relational structure.

---

## Part II: Formalization

### 4. Set-Theoretic Foundation

To move from philosophy to mathematics, we define a Distinction Structure as a precise mathematical object.

**Definition 4.1.** A *Distinction Structure* is a quadruple Δ = ⟨𝐈, D, M, {Σ_I}⟩ where:

- **𝐈** is a non-empty collection of Contexts
- **D** assigns to each I ∈ 𝐈 a set of Distinctions D(I)
- **M** assigns to each I ∈ 𝐈 a subset M(I) ⊆ D(I) of actual Distinctions
- **Σ_I** is a total function from finite non-empty subsets of D(I) to D(I), for each I

In plain language: there are Contexts, each Context has Distinctions, some Distinctions are actual, and there is a Synthesis operation that takes collections of Distinctions and produces new Distinctions.

### 5. Axioms

**A1 (Existence):** 𝐈 ≠ ∅. There is at least one Context.

**A2 (Sustenance):** For every Context I: M(I) ≠ ∅. Every Context sustains at least one actual Distinction.

**A3 (Containment):** For every Context I: M(I) ⊆ D(I). Actuality selects from what is available.

**A4 (Contextuality):** For distinct Contexts I ≠ J: D(I) ∩ D(J) = ∅. Distinctions are indexed to their Context.

**A5 (Selectivity):** There exists some Context I where M(I) ⊊ D(I). Actuality is a genuine selection — not everything possible is actual.

**A6 (Total synthesis):** Each Σ_I is total on Fin*(D(I)) — it is defined for every finite non-empty subset.

**A7′ (Structural novelty):** There exist I ∈ 𝐈 and S ⊆ M(I) with |S| ≥ 2 such that δ* = Σ_I(S) satisfies: (N1) δ* ∉ S, and (N2) there exists a test element t ∈ D(I) with Σ_I({δ*, t}) ≠ Σ_I({δ, t}) for all δ ∈ S. Synthesis can produce genuinely new Distinctions — ones with interaction profiles that none of their components have.

**Ext (Behavioral separability):** For every Context I and all x ≠ x′ in D(I), there exists y in D(I) such that Σ_I({x, y}) ≠ Σ_I({x′, y}). Distinct Distinctions are distinguishable by some interaction under Synthesis. This gives the principle "meaning is behavior" mathematical content.

### 6. What the Axioms Say in Plain Language

A1–A3 say: there are Contexts, they have Distinctions, and some of those Distinctions actually obtain. This is the minimal setup — a place where things are distinguished, with some distinctions being real.

A4 says Distinctions belong to their Context. The "red" of a traffic light and the "red" of a sunset are different Distinctions even if we use the same word, because they are sustained in different Contexts.

A5 says Actuality is selective — not everything that *could* be distinguished *is* distinguished. This prevents a degenerate framework where "actual" just means "possible."

A6 says Synthesis always produces a result. You can always compose Distinctions; the composition may be trivial (it might just return a default), but it is always defined.

A7′ says Synthesis can produce something genuinely new — an element whose behavior is different from any of its components. This is what makes Synthesis more than mere grouping.

Ext says that if two Distinctions are different, there must be some way to tell them apart by how they interact with other Distinctions. Distinctions that behave identically in all interactions are the same Distinction.

---

## Part III: The Self-Modeling Proof

### 7. The Problem: Nominal vs. Behavioral Encoding

The philosophical claim is that the framework describes itself. But can we prove this formally? A first attempt might define four elements in a Distinction Structure, label them "Distinction," "Context," "Actuality," and "Synthesis," and declare victory.

This doesn't work. External review (GPT 5.3) correctly identified it as *nominal* — the elements were labeled but didn't *behave* as components. Any four elements in any structure could be labeled the same way. You could label four rocks "Distinction," "Context," "Actuality," "Synthesis" — that doesn't make the rocks a self-model.

### 8. The Solution: Behavioral Self-Modeling

The resolution (contributed by Gemini): make the Synthesis operation act as an internal evaluator. The encoding elements don't just *stand for* components — they *compute like* them. When you synthesize the element representing D with the element representing a Context K, you get the element representing D(K). The element *proves what it is by what it does*.

**Definition 8.1 (Encoding map).** An *encoding map* for Δ at Context ι is an injective function ρ from the structure's macro-entities (its four components, each Context, each D(K) and M(K), and the whole Δ) into D(ι).

**Definition 8.2 (Homomorphism conditions).** An encoding is *homomorphic* if Σ_ι simulates D, M, and Σ:

- **H1:** For every Context K: Σ_ι({e_D, e_K}) = ρ(D(K)). Synthesizing the D-encoder with a Context-encoder yields the encoding of that Context's Distinctions.
- **H2:** For every Context K: Σ_ι({e_M, e_K}) = ρ(M(K)). Synthesizing the M-encoder with a Context-encoder yields the encoding of that Context's Actualities.
- **H3:** For the component set S₀ = {e_𝐈, e_D, e_M, e_Σ}: Σ_ι({e_Σ, ρ(S₀)}) = ρ(Σ_ι(S₀)). The Synthesis-encoder, applied to a coded input, yields the coded output.

Note on H3: this condition is mildly self-referential — Σ appears on both sides, as the operation being simulated and the operation doing the simulating. In the explicit construction this resolves cleanly, but the self-referential character bears on the open question of whether behavioral self-modeling is genuinely distinct from syntactic self-reference.

**Definition 8.3 (Intrinsic reflexivity).** Δ is *intrinsically reflexive* if there exists a Context ι and a homomorphic encoding ρ at ι satisfying:

- **(IR1) Presence:** The component encoders are pairwise distinct in D(ι)
- **(IR2) Actuality:** All encoding elements are in M(ι) — the self-model is actual, not merely possible
- **(IR3) Homomorphism:** H1, H2, H3 hold
- **(IR4) Closure:** Σ_ι({e_𝐈, e_D, e_M, e_Σ}) = e_Δ — the four components synthesize into the whole
- **(IR5) Non-exhaustion:** D(ι) contains elements not in the range of ρ — the self-Context is richer than the self-model

### 9. Existence Theorem

**Theorem 9.1.** *Intrinsically reflexive Distinction Structures exist.*

**Proof.** We construct an explicit model Δ₀ = ⟨𝐈, D, M, {Σ_I}⟩.

**Contexts:** 𝐈 = {ι, κ}.

**Distinctions:** D(ι) has 14 elements: four component encoders (e_𝐈, e_D, e_M, e_Σ), two Context encoders (e_ι, e_κ), four set encoders (r_Dι, r_Dκ, r_Mι, r_Mκ), one whole-structure encoder (e_Δ), one component-set encoder (r_S), and two surplus elements (p, q). D(κ) = {α, β}, disjoint from D(ι).

| Element | Encodes |
|---|---|
| e_𝐈 | 𝐈 (the Context class) |
| e_D | D (the Distinction assignment) |
| e_M | M (the Actuality selection) |
| e_Σ | Σ (the Synthesis operation) |
| e_ι, e_κ | ι and κ (the two Contexts) |
| r_Dι, r_Dκ | D(ι) and D(κ) |
| r_Mι, r_Mκ | M(ι) and M(κ) |
| e_Δ | Δ (the whole structure) |
| r_S | {e_𝐈, e_D, e_M, e_Σ} (the component set) |
| p, q | (surplus — no encoding) |

**Actuality:** M(ι) = all 12 encoding elements (p and q are merely possible). M(κ) = {α}.

**Synthesis Σ_ι** (by priority):

| # | Input | Output | Purpose |
|---|-------|--------|---------|
| 1 | {x} (singleton) | x | Identity |
| 2 | {e_D, e_ι} | r_Dι | H1 for ι |
| 3 | {e_D, e_κ} | r_Dκ | H1 for κ |
| 4 | {e_M, e_ι} | r_Mι | H2 for ι |
| 5 | {e_M, e_κ} | r_Mκ | H2 for κ |
| 6 | {e_Σ, r_S} | e_Δ | H3 |
| 7 | {e_𝐈, e_D, e_M, e_Σ} | e_Δ | IR4 (closure) |
| 8 | {e_Δ, e_D} | r_Dι | A7′ witness |
| 9 | {x, q} (non-special x) | x | Ext discriminator |
| 10 | All other S | p | Default |

**Synthesis Σ_κ:** {α} ↦ α, {β} ↦ β, {α,β} ↦ α.

**Axiom verification:**

A1: 𝐈 = {ι, κ} ≠ ∅. ✓

A2: M(ι) = 12 elements ≠ ∅. M(κ) = {α} ≠ ∅. ✓

A3: M(ι) ⊆ D(ι). M(κ) ⊆ D(κ). ✓

A4: D(ι) ∩ D(κ) = ∅ by construction. ✓

A5: M(ι) = 12 ⊊ D(ι) = 14. M(κ) = 1 ⊊ D(κ) = 2. ✓

A6: Σ_ι total (Rule 10 catches all remaining). Σ_κ total on three subsets. ✓

A7′: S = {e_𝐈, e_D, e_M, e_Σ}, δ* = Σ_ι(S) = e_Δ (Rule 7). e_Δ ∉ S (N1 ✓). Test t = e_D: e_Δ · e_D = r_Dι, but e_D · e_D = e_D, e_𝐈 · e_D = p, e_M · e_D = p, e_Σ · e_D = p. All differ from r_Dι (N2 ✓). ✓

Ext: For any a ≠ b in D(ι), choose y = q. Rule 9 gives Σ_ι({a,q}) = a and Σ_ι({b,q}) = b, so they differ. ✓

**Reflexivity verification:**

IR1: e_𝐈, e_D, e_M, e_Σ, e_ι are pairwise distinct. ✓

IR2: All encoding elements are in M(ι). ✓

IR3: H1 for ι: Σ_ι({e_D, e_ι}) = r_Dι = ρ(D(ι)). ✓
H1 for κ: Σ_ι({e_D, e_κ}) = r_Dκ = ρ(D(κ)). ✓
H2 for ι: Σ_ι({e_M, e_ι}) = r_Mι = ρ(M(ι)). ✓
H2 for κ: Σ_ι({e_M, e_κ}) = r_Mκ = ρ(M(κ)). ✓
H3: Σ_ι({e_Σ, r_S}) = e_Δ = ρ(Δ). ✓

IR4: Σ_ι({e_𝐈, e_D, e_M, e_Σ}) = e_Δ, and e_Δ ∉ {e_𝐈, e_D, e_M, e_Σ}. ✓

IR5: p, q ∈ D(ι) are not in the range of ρ. ✓

All axioms and intrinsic reflexivity conditions are satisfied. ∎

*Machine verification.* All claims in this proof are verified in Lean 4 (`Delta0.lean`). Every axiom, homomorphism condition, and reflexivity property is checked computationally via `decide` or `native_decide` over the finite carrier type. The Lean development also verifies Δ₁ (`Delta1.lean`) and the recovery procedure (`Discoverable.lean`). No `sorry` appears in any file.

### 10. What Intrinsic Reflexivity Means

In non-technical terms: we built a small mathematical world with 16 elements and a single operation. Inside that world, 12 elements form a working model of the world itself. Not a picture, not a label — a model. You can "run" it: synthesize e_D with e_κ and get r_Dκ, which encodes D(κ) = {α, β}. Synthesize e_M with e_κ and get r_Mκ, which encodes M(κ) = {α}. The internal model gives the same answers as the external structure.

The encoding elements prove what they are by what they do. e_D *behaves like* D: when you synthesize it with a Context-encoding, you get the encoding of that Context's Distinctions. This is the difference between calling a rock "Distinction" and building an element that, when combined with other elements via the structure's own operation, reproduces the behavior of Distinction.

The Synthesis operation acts as a universal evaluator — an operation that can simulate any of the structure's own components when given the right encoded arguments. This is structurally analogous to a universal Turing machine or a Lisp evaluator, but achieved without computation, time, or sequence. Just elements and a single operation.

---

## Part IV: The Category-Theoretic Perspective

### 11. Building Contexts from Distinctions

The set-theoretic formalization works but quietly betrays the philosophy. It defines Contexts first and assigns Distinctions to them. The philosophy says Contexts are *constituted by* their Distinctions. Category theory resolves this.

Begin with a *pre-distinction graph* G = (V, E): V is a collection of Distinctions, and an edge between δ and ε records that they are *co-contextual* — sustained together somewhere. The edges are symmetric (if δ is distinguished from ε, then ε is distinguished from δ) and irreflexive (nothing is distinguished from itself).

A **Context** emerges as a maximal clique in G — a largest collection of Distinctions that are all pairwise co-contextual. Contexts are derived, not primitive. Two Contexts are the same if and only if they contain the same Distinctions. There is no hidden Context-identity beyond the pattern.

This is the structural content of Yoneda's Lemma: an object is completely determined by its relationships. Applied here: a Context is completely determined by the Distinctions it sustains.

### 12. Contextuality as Theorem

In the set-theoretic formulation, contextuality (Distinctions have different profiles in different Contexts) is an axiom (A4). In the categorical formulation, it becomes a consequence. If Contexts are maximal cliques and two Contexts I ≠ J have D(I) ≠ D(J), then any Distinction δ belonging to both has a different profile in each — because its neighbors differ. The framework's central thesis is a *theorem*.

### 13. The Irreducibility of Actuality

The categorical perspective reveals a striking asymmetry. Three of the four roles are derivable from the distinction category 𝒟: Distinctions are objects, Contexts are maximal cliques, and Synthesis corresponds to colimits (universal compositions). But Actuality is not determined by 𝒟. Two identical distinction categories can have different Actuality selections. M adds information the category structure does not contain.

This is the formal content of Kant's claim that "existence is not a predicate." Actuality is not a structural property. It is a different mathematical type — a sub-presheaf vs. objects/morphisms/colimits — and no categorical operation converts one into the other.

This claim is now machine-verified as a concrete independence result (`ActualityIrreducibility.lean`). Two directed Distinction Structures Δ₁ and Δ₁′ are constructed on the same 18-element carrier. Their operation tables are identical except at the actuality tester m_I: Δ₁ has M = D \ {p} (m_I rejects p), while Δ₁′ has M′ = D \ {q} (m_I rejects q). Both models independently satisfy Ext, H1–H3, and all reflexivity conditions. The key lemmas: `∀ x ≠ m_I, dot1 x y = dot1' x y` (the operation tables agree outside the m_I row) and `∀ x ≠ m_I, dot1 x p = dot1' x q` (the non-actual elements are right-indistinguishable by all non-m_I elements). A Lean proof (`no_universal_actuality_predicate`) verifies that no single predicate on the carrier can simultaneously agree with both actuality assignments. The compositional structure does not determine actuality. The only way to determine which elements are actual is to query the actuality tester directly.

### 14. The Four Categorical Types

| Concept | Set-Theoretic Type | Categorical Type |
|---|---|---|
| Distinction | Class element | Object |
| Context | Class | Representable presheaf |
| Actuality | Selection function | Sub-presheaf |
| Synthesis | Operation | Colimit |

These are four fundamentally different categorical entities. No categorical operation transforms one type into another. This type-distinctness is the deepest reason the framework has four concepts, not fewer: the roles live in different categorical strata.

### 15. Categorical Status

The full categorical formalization remains a program rather than a completed proof. Free categories lack non-trivial colimits; a finitely presented category is needed. And A4 (disjointness) is too strong categorically — the correct result is profile-contextuality (A4′): profiles differ across Contexts even when Distinctions belong to multiple Contexts.

The existence proof (Theorem 9.1) uses A4 because it simplifies construction, but does not depend on it. The homomorphism conditions operate entirely within a single Context ι. Under A4′, the self-model at ι still works.

---

## Part V: The Discoverability Problem

### 16. Three Levels of Reflexivity

The project revealed three progressively stronger forms of self-description:

**Level 1 — Encoding reflexivity.** The structure contains elements formally mapped to its components via external bijections. Valid but nominal — any four elements could be labeled the same way. *(Proven but superseded.)*

**Level 2 — Intrinsic reflexivity.** The encoding elements *behave like* the components under Σ. Meaning is demonstrated by interaction, not declared by labeling. *(Proven. Theorem 9.1.)*

**Level 3 — Discoverable reflexivity.** The encoding is recoverable from Σ-behavior alone. An observer with no prior knowledge can identify the component encoders purely by probing. The structure doesn't just model itself — it *reveals* its model. *(Achieved via directed synthesis. See Part VI.)*

### 17. The Discoverability Architecture

For Level 3, an architecture was proposed: embed an internal "type system" in Σ-behavior using booleans (absorbing elements), set-codes (boolean-valued membership testers), and context-codes (maximal Σ-closed subsets). An observer could find the booleans, then the set-codes, then the context-codes, then the component encoders — all by probing.

The architecture is sound. But its implementation on set-based (symmetric) Σ revealed a fundamental obstacle.

### 18. The Symmetric Synthesis Barrier

**The core problem.** Σ operates on *sets* — unordered collections. When two elements with operational behavior are paired, their rules collide. The pairing {x, y} = {y, x} gives no way to determine which element is "acting on" which.

**The boolean contradiction.** Two absorbing booleans ⊤ and ⊥ require Σ({⊤, x}) = ⊤ for all x, and Σ({⊥, x}) = ⊥ for all x. But {⊤, ⊥} = {⊥, ⊤}, so we need Σ({⊤, ⊥}) = ⊤ AND Σ({⊤, ⊥}) = ⊥. Contradiction.

**The operator/operand conflict.** Even if booleans are patched (via priority), set-codes and component encoders conflict. If c is a set-code (returning booleans) and e_D is an encoder (returning structural tokens), the pair {c, e_D} cannot satisfy both rules — the set-code wants to return a boolean, the encoder wants to return a structural token, and the pair is the same regardless of who is "acting."

**The structural finding.** These aren't implementation bugs. They are consequences of a mathematical fact:

> *In set-based synthesis, every element has exactly one behavior per pairing. An element cannot be both operator and operand, because the pairing is unordered.*

In a lambda calculus, (f x) ≠ (x f). Function and argument have distinct roles. In set-based Σ, there is no function/argument distinction. The symmetric synthesis barrier is a theorem about the expressiveness of symmetric composition:

> **Symmetric synthesis supports self-modeling but not self-announcement.**

### 19. The Gap Between Self-Knowledge and Communication

This finding was not anticipated. It says something about the relationship between knowing yourself and making yourself known.

A structure with set-based Σ can contain a working behavioral model of itself — Theorem 9.1 proves this. But it cannot *reveal* that model to an observer without introducing an asymmetry that its symmetric operation cannot natively express. To be self-announcing, the structure needs ordered application — a way to say "this element is the operator and that element is the data."

This is the function/argument distinction that Frege argued was irreducible. You cannot have a complete logical language without it. The framework rediscovered Frege's point from within: symmetric composition suffices for self-knowledge but not for communication.

### 20. Two Interpretations

This finding admits two interpretations, useful in different contexts:

**Philosophical: the limitation is the point.** Self-knowledge is internal and symmetric. Communication is external and asymmetric. The framework can describe itself but cannot *present* itself without an encounter that introduces asymmetry from outside. This is another instance of the framework's recurring finding: it is complete for what it *is* but incomplete for how it *relates to what is outside it*.

**Practical: Synthesis has expressive modes.** For systems that need to not just model themselves but teach their own interpretation, Synthesis can be extended with directed application. This gives three modes of composition: pragmatic (mere aggregation), structural (producing novelty), and expressive (carrying enough structure to teach its own interpretation). The extension preserves the four-concept architecture while enriching what Synthesis means.

---

## Part VI: Directed Synthesis and Discoverable Reflexivity

### 21. Directed Distinction Structures

A *directed Distinction Structure* replaces the symmetric Σ with an ordered binary operation:

$$\cdot_I : D(I) \times D(I) \to D(I)$$

where x ·_I y ≠ y ·_I x in general. The left element acts on the right element. This introduces the function/argument asymmetry that symmetric Σ lacked.

The philosophical cost is real: symmetric Σ expressed the idea that composition treats its inputs equally. Directed synthesis introduces a hierarchy — operator and operand. But the discoverability results show this cost buys something specific: the ability for the structure to announce its own interpretation.

### 22. Construction of Δ₁

We construct a directed Distinction Structure with 17 elements that is *discoverably reflexive* — an observer with no prior knowledge can recover the self-model purely by probing.

**Contexts:** 𝐈 = {ι, κ}.

**Distinctions in ι (17 elements):**

| Element | Role |
|---------|------|
| ⊤, ⊥ | Booleans — discoverable truth values |
| i, k | Context tokens — encode ι and κ |
| a, b | κ-element encodings — encode α and β |
| e_I | Context tester — identifies context tokens |
| e_D | Distinction encoder — maps contexts to domain codes |
| e_M | Actuality encoder — maps contexts to actuality codes |
| e_Σ | Synthesis encoder |
| e_Δ | Whole-structure token |
| d_I | Domain code for ι (nominal — a token, not a membership tester) |
| d_K | Domain code for κ (extensional — a membership tester for {a,b}) |
| m_I | Actuality code for ι (extensional — tests membership in M(ι)) |
| m_K | Actuality code for κ (extensional — tests membership in M(κ)) |
| s_C | Component-set token |
| p | Surplus/default — non-actual |

Note on d_I: this element is a nominal token (it represents D(ι) but does not test membership in D(ι)). Making it extensional would require 17 additional rules. This is a deliberate minimality trade, not an error. d_K, m_I, and m_K are all genuine membership testers.

**Distinctions in κ:** D(κ) = {α, β}, disjoint from D(ι).

**Actuality:** M(ι) = D(ι) \ {p} (16 of 17). M(κ) = {α}.

### 23. The Operation Table

For x, y ∈ D(ι), define x ·_ι y by the first matching rule:

**Block A — Boolean absorption:**

| # | Pattern | Output |
|---|---------|--------|
| 1 | ⊤ · y | ⊤ |
| 2 | ⊥ · y | ⊥ |

**Block B — Testers (boolean-valued left-actions):**

| # | Pattern | Output |
|---|---------|--------|
| 3 | e_I · i | ⊤ |
| 4 | e_I · k | ⊤ |
| 5 | e_I · y (other) | ⊥ |
| 6 | d_K · a | ⊤ |
| 7 | d_K · b | ⊤ |
| 8 | d_K · y (other) | ⊥ |
| 9 | m_K · a | ⊤ |
| 10 | m_K · y (y ≠ a) | ⊥ |
| 11 | m_I · p | ⊥ |
| 12 | m_I · y (y ≠ p) | ⊤ |

**Block C — Structural encoders:**

| # | Pattern | Output |
|---|---------|--------|
| 13 | e_D · i | d_I |
| 14 | e_D · k | d_K |
| 15 | e_M · i | m_I |
| 16 | e_M · k | m_K |
| 17 | e_Σ · s_C | e_Δ |
| 18 | e_Δ · e_D | d_I |

**Block D — Absorption breaker:**

| # | Pattern | Output |
|---|---------|--------|
| 19 | p · ⊤ | ⊤ |

Without this rule, p would be a third left-absorber (p · y = p for all y via the default), breaking boolean uniqueness.

**Block E — Passive self-identification:**

| # | Pattern | Output |
|---|---------|--------|
| 20 | i · ⊤ | i |
| 21 | k · ⊤ | k |
| 22 | a · ⊤ | a |
| 23 | b · ⊤ | b |
| 24 | d_I · ⊤ | d_I |
| 25 | s_C · ⊤ | s_C |

Without these rules, six "passive" elements (those with no special left-behavior) would be left-indistinguishable, violating Ext.

**Block F — Default:**

| # | Pattern | Output |
|---|---------|--------|
| 26 | x · y (all remaining) | p |

**Directed Ext:** In the directed setting, behavioral separability uses left-action: for x ≠ x′, there exists y with x · y ≠ x′ · y. Block E ensures passive elements satisfy this: x · ⊤ = x ≠ x′ = x′ · ⊤.

**Σ_κ:** α ·_κ α = α, α ·_κ β = α, β ·_κ α = α, β ·_κ β = β.

### 24. The Recovery Procedure

An observer is given D(ι) (17 unlabeled elements) and oracle access to ·_ι. They recover all encoders through the following steps:

**Step 1 — Find booleans.** Compute Im_L(x) = {x · y : y ∈ D(ι)} for each x. The unique elements with |Im_L| = 1 and x · y = x for all y are ⊤ and ⊥.

Why this works: ⊤ and ⊥ absorb everything (Block A). Every other element has at least one non-self output: testers output both ⊤ and ⊥; passive elements output both themselves and p; p outputs both ⊤ and p (Rule 19 + default).

**Step 2 — Find testers.** A tester is any t ∉ {⊤, ⊥} with Im_L(t) ⊆ {⊤, ⊥}. Exactly four elements qualify: {e_I, d_K, m_K, m_I}. All others have some non-boolean left-output.

**Step 3 — Distinguish testers and find context tokens.** Compute Dec(t) = {y : t · y = ⊤} for each tester.

| Tester | |Dec| | Dec |
|--------|------|-----|
| m_I | 16 | D(ι) \ {p} |
| e_I | 2 | {i, k} |
| d_K | 2 | {a, b} |
| m_K | 1 | {a} |

m_I and m_K are identified by cardinality (16 and 1). For the two 2-element testers, the observer applies a *right-argument richness test*: check whether the decoded elements serve as productive right-arguments for any non-tester. Dec(e_I) = {i, k} are "rich" (e_D · i = d_I, a non-trivial output). Dec(d_K) = {a, b} are "inert" (no non-tester acts on them non-trivially). So e_I is the context tester.

Context tokens recovered: {i, k} = Dec(e_I).

**Step 4 — Find e_D and e_M.** Search for non-boolean non-tester elements that produce non-trivial outputs when applied to context tokens. Only e_D and e_M do.

Distinguish them: e_M maps both context tokens to *testers* (m_I and m_K). e_D maps them to a *mixed pair* (d_K is a tester, d_I is not). This signature is unique.

Distinguish context tokens: e_M · i = m_I (decoded set of 16), e_M · k = m_K (decoded set of 1). So i is the context token whose actuality code has the large decoded set.

**Step 5 — Identify codes.** d_I = e_D · i. d_K = e_D · k (already known as a tester). m_I = e_M · i (already known). m_K = e_M · k (already known). The κ-elements: a is the unique element in Dec(d_K) ∩ Dec(m_K). b is the other.

**Step 6 — Identify junk.** p is the unique element with m_I · p = ⊥. So M(ι) = Dec(m_I) = D(ι) \ {p}.

**Step 7 — Identify e_Σ, s_C, e_Δ.** Among the four remaining elements {e_Σ, e_Δ, s_C, p}, p is already identified. Search the remaining three for a triple (f, g, h) with f · g = h where h · e_D = d_I. The unique solution is f = e_Σ, g = s_C, h = e_Δ.

**All 17 elements recovered from behavior alone.** ✓

*Machine verification.* Each recovery step is formalized as an independent lemma in `Discoverable.lean`. `boolean_uniqueness` proves Step 1. `tester_characterization` proves Step 2. `tester_card_m_I`, `tester_card_e_I`, `tester_card_d_K`, `tester_card_m_K` prove Step 3. `rich_context_tokens` and `inert_kappa_tokens` prove Step 4. `encoder_pair` and `encoder_asymmetry` prove Step 5. `context_token_discrimination` proves the i/k distinction. `junk_identification` proves Step 6. `triple_identification` and `triple_uniqueness` prove Step 7 — the latter verifying that e_Σ, s_C, e_Δ is the *unique* solution among remaining elements. All proofs are computational over the finite domain via `decide` or `native_decide`.

*Empirical validation.* The recovery procedure is implemented as a true black-box algorithm (`delta2_true_blackbox.py`) that uses no ground truth during recovery. Tested across 1000 random permutations of element labels, all pass.

### 25. Verification of Directed Homomorphism

| Condition | Equation | Status |
|-----------|----------|--------|
| H1 for ι | e_D · i = d_I = ρ(D(ι)) | ✓ |
| H1 for κ | e_D · k = d_K = ρ(D(κ)) | ✓ |
| H2 for ι | e_M · i = m_I = ρ(M(ι)) | ✓ |
| H2 for κ | e_M · k = m_K = ρ(M(κ)) | ✓ |
| H3 | e_Σ · s_C = e_Δ = ρ(Δ) | ✓ |
| IR2 | All encoders ∈ M(ι) | ✓ |
| IR5 | p ∈ D(ι) \ ran(ρ) | ✓ |

### 26. The Cost of Discoverability

| Model | Elements | Synthesis | Reflexivity |
|-------|----------|-----------|-------------|
| Δ₀ | 16 | Symmetric (set-based Σ) | Intrinsic (Level 2) |
| Δ₁ | 17 | Directed (ordered ·) | Discoverable (Level 3) |

The cost of going from self-modeling to self-announcement: **one additional element** (the second boolean ⊥) and the switch from symmetric to directed synthesis.

In Δ₀, a single default element p served as the "junk" output, and no boolean machinery was needed. In Δ₁, the boolean pair {⊤, ⊥} is the foundation of the entire recovery procedure — it provides the stable two-valued output set that makes testers recognizable.

What directionality bought: the ability for elements to have distinct left-behavior (as operators) and right-behavior (as arguments). This resolves the symmetric synthesis barrier entirely.

What was not needed: PAIR, FST, SND, QUOTE, EVAL. The component encoders act directly as operators. Set-codes act directly as membership testers. No quoting or general evaluation machinery is required. The self-model is hard-wired rather than interpreted, but it is fully discoverable.

---

## Part VII: What It All Means

### 27. Existence Is Not a Predicate

Kant argued that "exists" does not add a property to a concept — it says not *what* a thing is but *that* it is. The categorical formalization provides a mathematical vindication, and the concrete independence result (Section 13) makes it machine-checkable.

Three of the four roles (Distinction, Context, Synthesis) are derivable from the distinction category 𝒟. They are structure describing structure. But Actuality is not determined by 𝒟. Two structurally identical worlds can differ in what is actual. The math tells you everything that *could* be distinguished. It does not tell you what *is* distinguished.

The `actuality_irreducibility` theorem makes this precise: two models sharing 322 of 324 operation table entries, both satisfying all axioms and reflexivity conditions, differ only in which element the actuality tester rejects. Equivalently, they are identical outside the `m_I` row. No single predicate can match both actuality assignments. Actuality is a different mathematical type. No categorical operation converts structure into actuality. Existence is not a predicate because it is not a structural property — it lives in a different categorical stratum from all structural properties.

### 28. Structure Cannot Account for Its Own Existence

The reflexivity proof shows the framework can describe everything about its own relational structure. The irreducibility of Actuality shows it cannot derive *why* this structure is actual rather than merely possible.

Complete self-knowledge is achievable: a system can fully describe its own relational structure. Complete self-explanation is not: no system can account for its own Actuality from within. You can know everything about *what* you are without knowing *why* you are.

### 29. Self-Knowledge vs. Communication

The symmetric synthesis barrier reveals that self-modeling and self-announcement are structurally different achievements. A symmetric structure can know itself (intrinsic reflexivity) but cannot make itself known without introducing asymmetry (directionality).

The analogy is suggestive: a mind that understands itself perfectly might still need language — an inherently asymmetric medium with speakers and listeners, subjects and objects — to communicate that understanding. The framework's formal finding echoes this: the gap between self-knowledge and communication is the function/argument distinction.

### 30. The Framework's Own Existence

The framework's own relationship to its proofs instantiates its deepest finding. The *structural* features — what the four concepts are, how they relate — are derivable. But the *actuality* of the framework — that it exists, that it was found — is not derivable from the structure.

The framework predicted this about itself. A proof that Actuality is irreducible *should itself* be irreducibly actual. A framework that says "existence must be encountered, not constructed" *should be* encountered rather than constructed.

### 31. Methodological Caution

The pattern of interpreting every limitation as the framework "correctly identifying its boundary" risks unfalsifiability. We note this risk explicitly. The framework's scope boundary (relational structure only) and its completeness claim (four roles suffice) are interdependent. Until minimality is proven, both claims remain open to revision. What would count as a failure rather than a boundary: a demonstration that some clearly relational phenomenon requires a fifth structural role not reducible to the existing four.

### 32. Toward a Computational Interpretation

The directed Distinction Structure Δ₁ is already a tiny interpreter — a finite algebra with directed application, elements that act as operators, elements that act as data, and a self-model recoverable from behavior. It is hard-wired for one specific program (the self-description). Adding four operators makes it general-purpose.

This extension now exists as working code (`delta2_true_blackbox.py`). Δ₂ extends Δ₁ with 21 atoms (the original 17 plus QUOTE, EVAL, APP, UNAPP):

- **QUOTE** wraps any term into inert data: QUOTE · x = ⌜x⌝, where ⌜x⌝ triggers no operational behavior unless explicitly evaluated.
- **EVAL** unwraps and executes: EVAL · ⌜x⌝ = x, and more generally EVAL · ⌜f · x⌝ = f · x. EVAL is defined recursively over syntax trees — this is the boundary where Δ₂ ceases to be a finite algebra and becomes an interpreter.
- **APP** constructs curried application nodes: APP · f produces a partial application that, when applied to x, yields the application node (f · x) as data.
- **UNAPP** decomposes application nodes into bundles queryable by booleans: (UNAPP · node) · ⊤ = f, (UNAPP · node) · ⊥ = x, reusing the already-discovered boolean vocabulary.

The black-box recovery procedure extends to all 21 elements. QUOTE is identified by its signature (produces structured, non-atom outputs on most inputs). EVAL is identified as QUOTE's inverse. APP and UNAPP are identified by their node-construction and bundle-decomposition behavior. Tested across 1000 random permutations of element labels, all 21 atoms correctly recovered in every case.

Δ₂ is empirically tested (Python) rather than formally verified (no Lean counterpart). The boundary is precise: Δ₁'s 17-element finite algebra is machine-checked in Lean; Δ₂'s recursive EVAL and unbounded term space are not. QUOTE generates unbounded inert values; EVAL is defined recursively over syntax trees. This is the boundary between algebra and computation.

What makes this more than "yet another Lisp" is that the framework's philosophical structure maps onto programming language concepts not by analogy but by structural correspondence:

**Distinction → Types.** A Distinction is a non-identity: *this is not that*. In a programming language, types are exactly this — they distinguish values that are structurally different. The framework's commitment that Distinctions are contextual maps onto the idea that types are relative to a module, scope, or namespace. The "same" type in two different modules is two different Distinctions.

**Context → Environments.** A Context is the locus where Distinctions are sustained. In a programming language, this is the environment — the scope in which variable bindings are active. The framework's finding that Contexts are constituted by their Distinctions (the Yoneda insight) maps onto the idea that an environment *is* its bindings. There is no hidden environment-essence beyond the pattern of what is in scope.

**Actuality → Evaluation.** Actuality is the selection of which Distinctions obtain. In a programming language, this is evaluation — the process of determining which expressions are reduced, which computations are performed, which values are materialized. The framework's finding that Actuality is irreducible maps onto a deep fact: you can describe the semantics of a language completely (its type system, its reduction rules, its operational semantics), and that description still does not tell you which programs are *actually run*. The choice of what to evaluate comes from outside the language.

**Synthesis → Composition.** Synthesis combines Distinctions into higher-order unities. In a programming language, this is function composition, module composition, the assembly of programs from parts. The pragmatic/structural distinction becomes precise: a tuple is pragmatic synthesis (mere grouping), while a function with emergent behavior is structural synthesis (the composite participates in interactions its components do not).

**Self-modeling → Metacircular evaluation.** The framework's intrinsic reflexivity — Δ₀ contains a working model of itself — is exactly what a metacircular evaluator is. Lisp's `eval` applied to a quoted Lisp expression reproduces Lisp's behavior. The framework's Σ applied to encoding elements reproduces the framework's behavior. Adding QUOTE/EVAL would make this explicit and general-purpose rather than hard-wired.

Three properties of a Distinction Structures-based language would have no standard analogue in existing languages:

*Discoverability.* Most programming languages have reflection (the ability to inspect structure at runtime), but no programming language has the property that an external observer with no documentation could recover the language's semantics purely by probing. Δ₁ has this. A language built on this foundation would be not just self-describing but self-explaining.

*Principled laziness.* In a lazy language, expressions are possible but not actual until forced. The framework's M(I) ⊊ D(I) — actuality as a proper subset of possibility — provides a principled foundation. Lazy vs. eager evaluation would not be a global toggle but a Context-dependent property: which Distinctions are actual varies by Context, just as the framework describes.

*Derived directionality.* Most language designers assume function application is ordered because that is how lambda calculus works. The framework *derives* this from the symmetric synthesis barrier: symmetric composition is adequate for internal representation but inadequate for communication. The language needs ordered application not by convention but by theorem.

Whether such a language would be practical for everyday programming is uncertain. But as a *metatheory of computation* — a framework that explains why programming languages have types, environments, evaluation, and composition, and why these are the structural primitives rather than some other set — it offers foundations that existing language theory does not provide.

---

## Part VIII: Status of Claims

### Proven

| Claim | Evidence |
|---|---|
| The axioms are consistent | Explicit model Δ₀ satisfies A1–A6, A7′, Ext |
| Intrinsically reflexive Distinction Structures exist | Theorem 9.1: construction + verification |
| The encoding is behavioral, not nominal | Homomorphism conditions H1–H3 verified |
| The self-model is internal | All encoding elements in D(ι), M(ι), composed by Σ_ι |
| Contextuality is a categorical theorem | Profile-contextuality follows from clique construction |
| Symmetric synthesis obstructs discoverability | Boolean/set-code conflicts proven |
| Discoverably reflexive directed DS exist | Δ₁: 17 elements, full recovery procedure verified |
| The cost of discoverability is small | Δ₁ has 1 more element than Δ₀ |
| Actuality is not determined by compositional structure | Two models on 18-element carrier share 322/324 operation table entries and are identical outside the `m_I` row; no single predicate matches both actuality assignments (`ActualityIrreducibility.lean`) |
| Recovery procedure uniqueness | 8-step recovery filtration with unique global solution (Step 3 tie resolved at Step 4) (`Discoverable.lean`) |
| All proofs machine-verified | Lean 4, zero `sorry` (`Basic.lean`, `Delta0.lean`, `Delta1.lean`, `Discoverable.lean`, `ActualityIrreducibility.lean`) |
| Discoverability tested empirically | Black-box recovery of all 21 Δ₂ elements across 1000 random permutations (`delta2_true_blackbox.py`) |

### Conjectured

| Claim | Key Obstacle |
|---|---|
| Four is the minimum for reflexivity | Gödel/quine objection: syntactic self-reference needs no Actuality |
| Discoverable reflexivity with symmetric Σ is impossible | Barrier demonstrated but impossibility not formally proven |
| Full categorical reflexivity via colimits | Requires finitely presented category construction |

### Retracted

| Claim | Reason |
|---|---|
| Contextuality as disjointness (categorical) | Maximal cliques overlap |
| Colimits in free categories | Free categories lack non-trivial colimits |

### Formal Verification Status

The following results are machine-verified in Lean 4 (version 4.28.0, Mathlib v4.28.0) with zero `sorry`:

| Result | File | Tactic |
|--------|------|--------|
| Δ₀ satisfies all axioms + intrinsic reflexivity | `Delta0.lean` | `decide` / `native_decide` |
| Δ₁ satisfies all axioms + intrinsic reflexivity | `Delta1.lean` | `decide` / `native_decide` |
| 8-step recovery filtration with unique global solution (Step 3 tie resolved at Step 4) | `Discoverable.lean` | `decide` / `native_decide` |
| Actuality independence (two models, shared structure, different M) | `ActualityIrreducibility.lean` | `decide` + constructive proof |

The following results are empirically tested in Python but not formally verified:

| Result | File | Evidence |
|--------|------|----------|
| Δ₂ black-box recovery (21 elements) | `delta2_true_blackbox.py` | 1000 random permutations, all pass |
| QUOTE/EVAL/APP/UNAPP behavior | `delta2_true_blackbox.py` | 4 demo programs, all correct |

The following remain paper-only (no code or formal proof):

- Categorical formalization (Part IV)
- Minimality conjecture (four roles necessary)
- Symmetric impossibility as a general theorem
- Full categorical reflexivity via colimits

---

## Part IX: Open Questions

1. **The Minimality Problem.** Can it be proven that four roles are necessary? The key obstacle is the Gödel/quine objection: standard self-reference uses only syntax and operations, without Actuality. Must show that behavioral self-modeling genuinely exceeds syntactic self-reference.

2. **The Semantic/Syntactic Boundary.** Precisely characterize the difference between Gödel-style self-reference and the behavioral self-modeling here. H3's mild self-referentiality suggests the boundary may be subtler than it first appears. This is likely the key to the minimality proof.

3. **Topos Classification.** Characterize the subobject classifiers of topoi that support reflexive Distinction Structures. This encodes the question "what is the nature of Actuality?" as precise mathematics.

4. **The Symmetric Impossibility Theorem.** Prove as a theorem (not just demonstrate by obstruction) that no Distinction Structure with symmetric Σ can satisfy discoverability conditions.

5. **Scaling Discoverability.** Δ₁ achieves "self-announcing primitives" — the observer recovers the component encoders. Δ₂ extends this with QUOTE/EVAL/APP/UNAPP, achieving general self-interpretation with recovery of all 21 elements from behavior (empirically verified, not yet formally proven). The remaining open question is whether the discoverability property can scale to computationally universal systems — whether an observer can recover the semantics of an arbitrary programming language by probing.

6. **The Pre-Relational Boundary.** Is there a meta-theoretic result about what Distinction Structures cannot express? A theorem of the form "no DS can contain an element satisfying [property P]" would sharpen the scope declaration from philosophy to mathematics.

7. **Quantum Contextuality.** The framework's central thesis (Distinctions are contextual) maps onto quantum contextuality. Can it generate a non-trivial classification?

8. **Computational Foundation.** Δ₂ demonstrates that extending a Distinction Structure with QUOTE, EVAL, APP, and UNAPP produces a working interpreter with black-box recoverable semantics. The structural correspondences (Distinction/types, Context/environments, Actuality/evaluation, Synthesis/composition) hold by construction. The remaining questions: Can this be formalized in Lean (the recursive EVAL is the obstacle)? Can it scale to a practical programming language? And does the discoverability property — proven for 17 atoms, empirically verified for 21 — extend to computationally universal systems?

**Update (2026):** Open question #8 has been partially answered. The Δ₂+74181+IO extension adds 26 atoms to the 21-atom Δ₂ algebra, yielding 47 atoms total. This includes 16 nibble data values (N0–NF forming Z/16Z under addition), 3 ALU dispatch atoms encoding all 32 operations of the classic 74181 4-bit ALU chip, 2 ALU predicates (zero-detect and carry-out), 1 nibble successor, and 4 IO atoms (IO_PUT, IO_GET, IO_RDY, IO_SEQ) for byte-level stdin/stdout. The discoverability property scales: a two-phase recovery procedure identifies all 47 atoms from black-box probing — Phase 1 (Cayley-level) recovers 39 atoms, Phase 2 (term-level) recovers the remaining 8 opaque atoms. Verified across 200+ random permutations at 100% recovery rate. See `delta2_74181.py` and `delta2_74181_blackbox.py`.

---

## Appendix: Review History and Axiom Revisions

This framework was developed over approximately two years of iterative refinement, with the four concepts remaining stable while definitions were progressively tightened through dialogue with multiple AI systems (Claude, GPT, Gemini).

### Revisions from First Review (GPT 5.3)

| Original | Problem | Repair |
|---|---|---|
| Σ partial function | Not total | Σ_I total on Fin*(D(I)) (A6) |
| R5 ("represents") | Informal; nominal encoding | Replaced by homomorphism H1–H3 |
| Σ cross-context | Typing error | Context-closed: Σ_I(S) ∈ D(I) |
| A7 (embedding clause) | Vague | Replaced by A7′ (interaction-profile novelty) |
| Minimality proof | Circular | Retracted; minimality is a conjecture |

### Revisions from Second Review (Gemini)

| Original | Problem | Repair |
|---|---|---|
| Encoding via bijection | Extrinsic | Homomorphic encoding: Σ simulates D, M, Σ internally |

### Additional Axioms

| Axiom | Source | Purpose |
|---|---|---|
| Ext | GPT 5.3 | "Meaning is behavior" formalized |
| A7′ | GPT 5.3 | Novelty via interaction profile |

### Bugs Found in Δ₁ (GPT's Original Construction) and Fixes

| Bug | Problem | Fix |
|---|---|---|
| p is third left-absorber | Observer finds 3 constants, not 2 | Rule 19: p · ⊤ = ⊤ |
| e_I and d_K both 2-element testers | Observer can't distinguish them | Right-argument richness test |
| e_D identification criterion wrong | d_K is a tester, breaking the stated criterion | Asymmetric criterion: e_M maps both to testers; e_D maps to mixed pair |
| Passive elements left-indistinguishable | 6 elements have identical left-behavior | Block E: x · ⊤ = x for passive x |

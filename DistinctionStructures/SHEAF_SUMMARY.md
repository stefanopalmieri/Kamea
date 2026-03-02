# Sheaf-Theoretic Characterization of Ontological Categories

## Overview

`Sheaf.lean` formalizes the sheaf-theoretic structure underlying the Δ₁ self-modeling algebra. The file contains **50 definitions and theorems**, all proved with **zero `sorry`**, compiling in ~20 seconds against Lean 4.28.0 + Mathlib v4.28.0.

## Results by Section

### Part 1: Observation Poset (Task 2)
- **5-level totally ordered poset** corresponding to the recovery procedure's filtration:
  - Level 0 (raw) → Level 1 (boolean) → Level 2 (partition) → Level 3 (role) → Level 4 (synthesis)
- Proved: reflexivity, transitivity, antisymmetry, totality
- This is the "site" for the presheaf — a finite chain

### Part 2–3: Presheaf Structure (Tasks 3)
- **Four classification functions** at each level (BoolClass, PartitionClass, RoleClass, SynthClass)
- **Three restriction maps** (forgetful functors between levels)
- **Functoriality**: restriction maps commute with classification (3 theorems)
- **Sheaf condition**: each level refines the previous (3 refinement theorems)
- **Global section uniqueness**: Level 4 classification is injective (identifies every element)

### Part 4: Ontological Subsheaves (Task 4)
- **Four boolean predicates** marking category membership:
  - `hasDistinction`: {e_I, d_K, m_K, m_I}
  - `hasContext`: {i, k, e_D, e_M, d_I, d_K}
  - `hasActuality`: {m_I, p}
  - `hasSynthesis`: {e_Sigma, s_C, e_Delta}
- Each subsheaf is **strictly contained** in the full sheaf (4 theorems)
- **Coverage**: all non-boolean, non-κ-encoding elements belong to at least one category
- **Overlap structure**: distinction ∩ context = {d_K}, distinction ∩ actuality = {m_I}, all other pairs disjoint

### Part 5: Necessity Theorems (Task 5) — Core Results

**Without Distinction (testers removed):**
- Domain codes d_I, d_K become right-indistinguishable (no non-tester can tell them apart)
- Actuality codes m_I, m_K collapse similarly
- Synthesis components (e_Sigma, d_I) conflate with domain codes
- Even p becomes indistinguishable from structural elements
- **Conclusion**: the encoding produces distinct codes, but those codes are operationally identical without testers. The self-model's output is well-formed but unreadable.

**Without Actuality (m_I removed):**
- p becomes right-indistinguishable from e_Sigma, d_I, and other structural elements
- m_I is the UNIQUE element that distinguishes p from all actual elements
- No other tester can serve this role (e_I, d_K, m_K all reject p and other elements equally)
- **Conclusion**: multiple actuality assignments are consistent with the non-m_I Cayley table. Self-model is underdetermined. (This directly restates the Actuality Irreducibility theorem in sheaf language.)

**Without Context (i, k removed):**
- e_D and e_M both map all non-context elements to p (trivial output)
- e_D and e_M become functionally identical without context tokens
- H1 and H2 require distinct codes for the two contexts, which can only be produced by applying encoders to context tokens
- **Conclusion**: the self-model cannot represent the two-context structure. The encoding collapses.

**Without Synthesis (e_Sigma, s_C, e_Delta removed):**
- No triple (f, g, h) among remaining elements satisfies both `dot f g = h` and `dot h e_D = d_I`
- H3 has no witness
- **Conclusion**: encoding elements may exist but behavioral fidelity (the homomorphism condition) has no witness. The model is a labeling, not a behavioral model.

### Part 6: Morphisms (Task 6 — Exploratory)
- Defined `MagmaHom` and `DSHom` structures
- Constructed identity morphism and identity DS-homomorphism
- **Conjecture**: Δ₁ has exactly one endomorphism (the identity) — i.e., it is rigid
- The conjecture is intractable for `native_decide` (17^17 function space) but would follow from a 17-step chain of lemmas mirroring the recovery procedure

## Key Findings

### 1. The Four Categories ARE Necessary (for Δ₁)
All four necessity results are **machine-checked** over the 17-element carrier. Each removal causes a distinct failure mode:
- **Distinction**: output unreadable (codes conflate)
- **Actuality**: model underdetermined (multiple valid actuality assignments)
- **Context**: encoding collapses (can't represent two-context structure)
- **Synthesis**: model incomplete (no behavioral fidelity witness)

### 2. The Sheaf Framework Reveals Structure
The observation poset is NOT an arbitrary abstraction — it IS the recovery procedure's natural filtration. The restriction maps are exactly the "forgetting" that happens when you have less information. The sheaf condition (refinement) is exactly the fact that each recovery step genuinely adds information.

### 3. The Categories Are Almost Independent
The four categories have minimal overlap:
- d_K bridges distinction and context (it's a tester that also encodes domain structure)
- m_I bridges distinction and actuality (it's a tester that also carries actuality information)
- All other pairs are disjoint

This matches the philosophical claim: these are genuinely different capacities, with m_I serving double duty as the crucial link between "telling apart" and "knowing what's real."

### 4. The Morphism Question Points to Rigidity
The conjecture that Δ₁ has only the identity endomorphism connects the sheaf structure to the recovery procedure: the filtration that makes recovery possible is the same filtration that forces any structure-preserving map to be the identity. Each level of the observation sheaf fixes more elements of any purported endomorphism.

## Conjectures for Future Work

1. **Rigidity theorem**: The identity is the unique endomorphism of Δ₁. (Requires ~17 chained lemmas following the recovery order.)

2. **Abstract necessity**: The four-category necessity should generalize from Δ₁ to ANY finite magma with a behavioral self-model. The sheaf framework provides the right abstraction: any self-modeling magma must have nontrivial Distinction, Context, Actuality, and Synthesis subsheaves.

3. **Morphism classification**: For two Distinction Structures A and B, the space of DS-homomorphisms A → B should be either empty (incompatible structures) or a singleton (the structures are isomorphic, forced by rigidity). This would formalize the "no translation without loss" principle.

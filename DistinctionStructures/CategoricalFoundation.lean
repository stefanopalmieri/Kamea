/- # CategoricalFoundation — Finite Endomorphism Magmas with Categorical Structure

   Standard categorical vocabulary for the forced-roles theorem.
   Every concept here is standard algebra/category theory:
   zero morphisms, retraction pairs, subobject classifiers,
   products with projections, conditional copairing, fixed-point combinators.

   This file defines `CatEndoMagma n`, a structure capturing these concepts
   in the setting of finite endomorphism magmas (magmas on `Fin n`).

   **Relation to standard references:**
   - Zero morphisms: cf. `CategoryTheory.Limits.HasZeroMorphisms`
   - Retraction pairs: cf. `CategoryTheory.RetractOf`
   - Subobject classifier: cf. `CategoryTheory.Subobject.classifier` (topos theory)
   - Products/projections: cf. `CategoryTheory.Limits.BinaryProduct`
   - Copairing: cf. `CategoryTheory.Limits.BinaryCoproduct`
   - Fixed-point combinator: cf. domain theory / Curry's Y combinator

   All axioms are stated in terms any algebraist or category theorist
   would recognize, with no reference to the Ψ framework.
-/

import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

namespace CatFoundation

/-- Predicate identifying the "core" of the magma: elements at indices 2, 3, 4, 5.
    These are the elements on which the retraction pair acts as an isomorphism
    and on which the copairing dispatch is defined. In categorical terms,
    these are the representable objects of the internal category. -/
def in_core {n : Nat} (x : Fin n) : Prop := x.val = 2 ∨ x.val = 3 ∨ x.val = 4 ∨ x.val = 5

instance {n : Nat} : DecidablePred (@in_core n) := fun x =>
  inferInstanceAs (Decidable (x.val = 2 ∨ x.val = 3 ∨ x.val = 4 ∨ x.val = 5))

/-- A finite endomorphism magma with categorical structure.

    All concepts are standard: zero morphisms, retraction pairs,
    subobject classifiers, products with projections, conditional copairing,
    and a fixed-point combinator.

    The carrier is `Fin n` with a binary operation `dot` (composition).
    Ten distinguished elements play specific categorical roles.

    **Design note:** The `n ≥ 10` constraint is not stated explicitly —
    it follows from `distinct_all` (10 pairwise-distinct elements exist). -/
structure CatEndoMagma (n : Nat) where
  /-- The binary operation (composition of endomorphisms). -/
  dot : Fin n → Fin n → Fin n

  /-- First left-zero morphism: `∀ x, dot zero₁ x = zero₁`. -/
  zero₁ : Fin n
  /-- Second left-zero morphism: `∀ x, dot zero₂ x = zero₂`. -/
  zero₂ : Fin n

  /-- Section of the retraction pair (embeds the core into the magma).
      Corresponds to Q in the Ψ framework. -/
  sec : Fin n
  /-- Retraction of the retraction pair (left-inverse of section on core).
      Corresponds to E in the Ψ framework. -/
  ret : Fin n

  /-- Subobject classifier: the unique boolean-valued non-zero morphism.
      Its row contains only zero₁ and zero₂ values, and no other
      non-zero element has this property. Corresponds to τ. -/
  cls : Fin n

  /-- Product object / pair constructor. Its row is "nearly constant"
      (inert in role terms). Corresponds to g. -/
  pair_obj : Fin n
  /-- First projection. Corresponds to f. -/
  proj₁ : Fin n
  /-- Second projection / composition element. Corresponds to η. -/
  proj₂ : Fin n

  /-- Conditional copairing: dispatches between proj₁ and pair_obj
      based on the classifier's output. Corresponds to ρ. -/
  copair : Fin n

  /-- Fixed-point combinator. Corresponds to Y. -/
  fixpt : Fin n

  -- ════════════════════════════════════════════════════════════════
  -- Zero morphism axioms
  -- ════════════════════════════════════════════════════════════════

  /-- First zero morphism absorbs on the left. -/
  zero₁_left : ∀ x : Fin n, dot zero₁ x = zero₁
  /-- Second zero morphism absorbs on the left. -/
  zero₂_left : ∀ x : Fin n, dot zero₂ x = zero₂
  /-- The two zero morphisms are distinct. -/
  zeros_distinct : zero₁ ≠ zero₂
  /-- No other element is a left-zero morphism. -/
  no_other_zeros : ∀ y : Fin n, (∀ x : Fin n, dot y x = y) → y = zero₁ ∨ y = zero₂

  -- ════════════════════════════════════════════════════════════════
  -- Extensionality (faithful action)
  -- ════════════════════════════════════════════════════════════════

  /-- Row extensionality: distinct elements have distinct rows.
      Equivalently, the left-regular representation is faithful. -/
  extensional : ∀ a b : Fin n, (∀ x : Fin n, dot a x = dot b x) → a = b

  -- ════════════════════════════════════════════════════════════════
  -- Retraction pair axioms (on core elements)
  -- ════════════════════════════════════════════════════════════════

  /-- ret ∘ sec = id on core: the retraction inverts the section. -/
  ret_sec : ∀ x : Fin n, in_core x → dot ret (dot sec x) = x
  /-- sec ∘ ret = id on core: the section inverts the retraction. -/
  sec_ret : ∀ x : Fin n, in_core x → dot sec (dot ret x) = x

  -- ════════════════════════════════════════════════════════════════
  -- Subobject classifier axioms
  -- ════════════════════════════════════════════════════════════════

  /-- The classifier's row is boolean-valued: every output is zero₁ or zero₂. -/
  cls_boolean : ∀ x : Fin n, dot cls x = zero₁ ∨ dot cls x = zero₂
  /-- **Kleene dichotomy**: every non-zero element is either a "classifier"
      (all outputs on non-zero inputs are boolean) or "computational"
      (all outputs on non-zero inputs are non-boolean). No mixing.

      In categorical terms: the boolean and non-boolean strata of the
      endomorphism magma are cleanly separated. An endomorphism either
      always factors through the subobject classifier's image {zero₁, zero₂}
      or never does (on non-zero inputs).

      This is the Kleene wall stated as a structural dichotomy. -/
  dichotomy : ∀ a : Fin n, a ≠ zero₁ → a ≠ zero₂ →
    (∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ → dot a x = zero₁ ∨ dot a x = zero₂) ∨
    (∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ → dot a x ≠ zero₁ ∧ dot a x ≠ zero₂)

  -- ════════════════════════════════════════════════════════════════
  -- Conditional copairing axioms (branch dispatch)
  -- ════════════════════════════════════════════════════════════════

  /-- On core elements classified as "true" (mapped to zero₁ by cls),
      the copairing acts as the first projection. -/
  copair_true : ∀ x : Fin n, in_core x →
    dot cls x = zero₁ → dot copair x = dot proj₁ x
  /-- On core elements classified as "false" (mapped to zero₂ by cls),
      the copairing acts as the pair constructor. -/
  copair_false : ∀ x : Fin n, in_core x →
    dot cls x = zero₂ → dot copair x = dot pair_obj x
  /-- The first projection and pair constructor differ on at least one
      core element, ensuring the copairing is non-degenerate. -/
  proj_differ : ∃ x : Fin n, in_core x ∧ dot proj₁ x ≠ dot pair_obj x

  -- ════════════════════════════════════════════════════════════════
  -- Composition through copairing
  -- ════════════════════════════════════════════════════════════════

  /-- The second projection factors through the copairing and pair constructor.
      On core: `proj₂ · x = copair · (pair_obj · x)`. -/
  compose : ∀ x : Fin n, in_core x → dot proj₂ x = dot copair (dot pair_obj x)

  -- ════════════════════════════════════════════════════════════════
  -- Selection axiom
  -- ════════════════════════════════════════════════════════════════

  /-- Composing the second projection with the copairing yields
      the classifier: `proj₂ · copair = cls`.
      This connects composition with classification. -/
  selection : dot proj₂ copair = cls

  -- ════════════════════════════════════════════════════════════════
  -- Fixed-point combinator axioms
  -- ════════════════════════════════════════════════════════════════

  /-- The fixed-point combinator satisfies `fixpt · copair = copair · (fixpt · copair)`. -/
  fixpt_eq : dot fixpt copair = dot copair (dot fixpt copair)
  /-- The fixed point is non-trivial (not a zero morphism). -/
  fixpt_nontrivial : (dot fixpt copair).val ≥ 2

  -- ════════════════════════════════════════════════════════════════
  -- Retraction transparency (retraction preserves zeros)
  -- ════════════════════════════════════════════════════════════════

  /-- The retraction preserves the first zero morphism. -/
  ret_zero₁ : dot ret zero₁ = zero₁
  /-- The retraction preserves the second zero morphism. -/
  ret_zero₂ : dot ret zero₂ = zero₂

  -- ════════════════════════════════════════════════════════════════
  -- Role distinctness
  -- ════════════════════════════════════════════════════════════════

  /-- All 10 named elements are pairwise distinct.
      This is the standard non-degeneracy condition, analogous to
      requiring 0 ≠ 1 in a nontrivial ring.

      The 45 pairs decompose as:
      - 32 are forced by the behavioral axioms alone (proven in CatForcedDistinctness)
      - 13 are additional requirements (the distinctness axiom) -/
  distinct_all :
    zero₁ ≠ zero₂ ∧ zero₁ ≠ cls ∧ zero₁ ≠ sec ∧
    zero₁ ≠ ret ∧ zero₁ ≠ proj₁ ∧ zero₁ ≠ pair_obj ∧
    zero₁ ≠ copair ∧ zero₁ ≠ proj₂ ∧ zero₁ ≠ fixpt ∧
    zero₂ ≠ cls ∧ zero₂ ≠ sec ∧ zero₂ ≠ ret ∧
    zero₂ ≠ proj₁ ∧ zero₂ ≠ pair_obj ∧ zero₂ ≠ copair ∧
    zero₂ ≠ proj₂ ∧ zero₂ ≠ fixpt ∧
    cls ≠ sec ∧ cls ≠ ret ∧ cls ≠ proj₁ ∧
    cls ≠ pair_obj ∧ cls ≠ copair ∧ cls ≠ proj₂ ∧ cls ≠ fixpt ∧
    sec ≠ ret ∧ sec ≠ proj₁ ∧ sec ≠ pair_obj ∧
    sec ≠ copair ∧ sec ≠ proj₂ ∧ sec ≠ fixpt ∧
    ret ≠ proj₁ ∧ ret ≠ pair_obj ∧ ret ≠ copair ∧
    ret ≠ proj₂ ∧ ret ≠ fixpt ∧
    proj₁ ≠ pair_obj ∧ proj₁ ≠ copair ∧ proj₁ ≠ proj₂ ∧ proj₁ ≠ fixpt ∧
    pair_obj ≠ copair ∧ pair_obj ≠ proj₂ ∧ pair_obj ≠ fixpt ∧
    copair ≠ proj₂ ∧ copair ≠ fixpt ∧
    proj₂ ≠ fixpt

end CatFoundation

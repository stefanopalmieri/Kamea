/- # CatWitness — The 16-Element Canonical Witness

   Constructs the specific 16×16 Cayley table Ψ₁₆ᶠ as an instance of
   `CatEndoMagma 16`, proving that the axiom system is satisfiable.

   The table is identical to the one in `Psi16Full.lean`; only the vocabulary
   changes from Ψ-specific (absorber, tester, encoder, inert, branch) to
   standard categorical (zero morphism, classifier, section, retraction,
   projection, copairing).

   Element assignments:
     zero₁ = 0  (⊤)       zero₂ = 1  (⊥)
     proj₁ = 2  (f)        cls   = 3  (τ)
     pair_obj = 4 (g)      sec   = 6  (Q)
     ret   = 7  (E)        copair = 8  (ρ)
     proj₂ = 9  (η)        fixpt = 10 (Y)

   All axiom proofs are computational: `decide` or `native_decide`.
-/

import DistinctionStructures.CategoricalFoundation
import Mathlib.Data.Fintype.Basic

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace CatWitness

open CatFoundation

/-! ## Part 1: The Cayley Table

    Identical to `Psi16Full.rawPsi`. Reproduced here for self-containment
    (same pattern as `Psi16ActualityIrreducibility.lean`). -/

private def rawDot : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  | 2, 0 => 5 | 2, 1 => 1 | 2, 2 => 13 | 2, 3 => 7 | 2, 4 => 11
  | 2, 5 => 5 | 2, 6 => 6  | 2, 7 => 8 | 2, 8 => 2 | 2, 9 => 5
  | 2, 10 => 11 | 2, 11 => 9 | 2, 12 => 4 | 2, 13 => 14 | 2, 14 => 3 | 2, 15 => 15
  | 3, 0 => 0 | 3, 1 => 1 | 3, 2 => 0 | 3, 3 => 0 | 3, 4 => 0
  | 3, 5 => 0 | 3, 6 => 1 | 3, 7 => 1 | 3, 8 => 1 | 3, 9 => 0
  | 3, 10 => 1 | 3, 11 => 1 | 3, 12 => 0 | 3, 13 => 0 | 3, 14 => 1 | 3, 15 => 1
  | 4, 0 => 0 | 4, _ => 11
  | 5, 0 => 0 | 5, 1 => 1 | 5, 2 => 1 | 5, 3 => 1 | 5, 4 => 1
  | 5, 5 => 1 | 5, 6 => 0 | 5, 7 => 1 | 5, 8 => 1 | 5, 9 => 1
  | 5, 10 => 0 | 5, 11 => 1 | 5, 12 => 0 | 5, 13 => 1 | 5, 14 => 1 | 5, 15 => 0
  | 6, 0 => 15 | 6, 1 => 0 | 6, 2 => 5 | 6, 3 => 9 | 6, 4 => 3
  | 6, 5 => 15 | 6, 6 => 14 | 6, 7 => 14 | 6, 8 => 2 | 6, 9 => 12
  | 6, 10 => 8 | 6, 11 => 14 | 6, 12 => 12 | 6, 13 => 4 | 6, 14 => 12 | 6, 15 => 8
  | 7, 0 => 0 | 7, 1 => 1 | 7, 2 => 8 | 7, 3 => 4 | 7, 4 => 13
  | 7, 5 => 2 | 7, 6 => 11 | 7, 7 => 2 | 7, 8 => 14 | 7, 9 => 3
  | 7, 10 => 15 | 7, 11 => 12 | 7, 12 => 14 | 7, 13 => 15 | 7, 14 => 6 | 7, 15 => 5
  | 8, 0 => 12 | 8, 1 => 1 | 8, 2 => 13 | 8, 3 => 7 | 8, 4 => 11
  | 8, 5 => 5 | 8, 6 => 12 | 8, 7 => 11 | 8, 8 => 4 | 8, 9 => 12
  | 8, 10 => 5 | 8, 11 => 14 | 8, 12 => 15 | 8, 13 => 7 | 8, 14 => 11 | 8, 15 => 12
  | 9, 0 => 1 | 9, 1 => 6 | 9, 2 => 14 | 9, 3 => 14 | 9, 4 => 14
  | 9, 5 => 14 | 9, 6 => 9 | 9, 7 => 8 | 9, 8 => 3 | 9, 9 => 15
  | 9, 10 => 5 | 9, 11 => 7 | 9, 12 => 13 | 9, 13 => 11 | 9, 14 => 12 | 9, 15 => 4
  | 10, 0 => 13 | 10, 1 => 1 | 10, 2 => 4 | 10, 3 => 3 | 10, 4 => 12
  | 10, 5 => 11 | 10, 6 => 2 | 10, 7 => 11 | 10, 8 => 5 | 10, 9 => 3
  | 10, 10 => 8 | 10, 11 => 14 | 10, 12 => 9 | 10, 13 => 7 | 10, 14 => 11 | 10, 15 => 11
  | 11, 0 => 14 | 11, 1 => 1 | 11, 2 => 9 | 11, 3 => 10 | 11, 4 => 11
  | 11, 5 => 13 | 11, 6 => 12 | 11, 7 => 7 | 11, 8 => 5 | 11, 9 => 6
  | 11, 10 => 8 | 11, 11 => 2 | 11, 12 => 14 | 11, 13 => 12 | 11, 14 => 10 | 11, 15 => 4
  | 12, 0 => 0 | 12, 1 => 1 | 12, 2 => 1 | 12, 3 => 0 | 12, 4 => 1
  | 12, 5 => 1 | 12, 6 => 0 | 12, 7 => 1 | 12, 8 => 1 | 12, 9 => 1
  | 12, 10 => 0 | 12, 11 => 0 | 12, 12 => 0 | 12, 13 => 0 | 12, 14 => 0 | 12, 15 => 1
  | 13, 0 => 3 | 13, 1 => 0 | 13, 2 => 14 | 13, 3 => 4 | 13, 4 => 14
  | 13, 5 => 6 | 13, 6 => 11 | 13, 7 => 12 | 13, 8 => 7 | 13, 9 => 3
  | 13, 10 => 15 | 13, 11 => 10 | 13, 12 => 14 | 13, 13 => 2 | 13, 14 => 6 | 13, 15 => 8
  | 14, 0 => 14 | 14, 1 => 0 | 14, 2 => 5 | 14, 3 => 4 | 14, 4 => 3
  | 14, 5 => 2 | 14, 6 => 12 | 14, 7 => 5 | 14, 8 => 11 | 14, 9 => 14
  | 14, 10 => 3 | 14, 11 => 14 | 14, 12 => 12 | 14, 13 => 2 | 14, 14 => 6 | 14, 15 => 3
  | 15, 0 => 1 | 15, 1 => 3 | 15, 2 => 13 | 15, 3 => 15 | 15, 4 => 3
  | 15, 5 => 7 | 15, 6 => 14 | 15, 7 => 8 | 15, 8 => 15 | 15, 9 => 4
  | 15, 10 => 11 | 15, 11 => 6 | 15, 12 => 7 | 15, 13 => 14 | 15, 14 => 12 | 15, 15 => 10
  | _, _ => 0

private theorem rawDot_bound (a b : Fin 16) : rawDot a.val b.val < 16 := by
  revert a b; native_decide

/-- The binary operation of the canonical 16-element witness. -/
def dot16 (a b : Fin 16) : Fin 16 := ⟨rawDot a.val b.val, rawDot_bound a b⟩

/-! ## Part 2: The Canonical Witness -/

/-- **The canonical 16-element witness**, presented in categorical language.

    This is the same algebra as Ψ₁₆ᶠ (Psi16Full.psi), wrapped in the
    `CatEndoMagma` structure with standard categorical names.

    Proves satisfiability: `CatEndoMagma 16` is inhabited. -/
def psi16_cat : CatEndoMagma 16 where
  dot := dot16
  zero₁ := 0     -- ⊤
  zero₂ := 1     -- ⊥
  sec := 6        -- Q (section)
  ret := 7        -- E (retraction)
  cls := 3        -- τ (subobject classifier)
  pair_obj := 4   -- g (product object)
  proj₁ := 2      -- f (first projection)
  proj₂ := 9      -- η (second projection)
  copair := 8     -- ρ (conditional copairing)
  fixpt := 10     -- Y (fixed-point combinator)
  -- Zero morphism axioms
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  -- Extensionality
  extensional := by decide
  -- Retraction pair
  ret_sec := by decide
  sec_ret := by decide
  -- Subobject classifier
  cls_boolean := by decide
  dichotomy := by decide
  -- Conditional copairing
  copair_true := by decide
  copair_false := by decide
  proj_differ := by decide
  -- Composition
  compose := by decide
  -- Selection
  selection := by decide
  -- Fixed point
  fixpt_eq := by decide
  fixpt_nontrivial := by decide
  -- Retraction transparency
  ret_zero₁ := by decide
  ret_zero₂ := by decide
  -- All 10 named elements are pairwise distinct
  distinct_all := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The witness inhabits CatEndoMagma 16. -/
instance : Inhabited (CatEndoMagma 16) := ⟨psi16_cat⟩

end CatWitness

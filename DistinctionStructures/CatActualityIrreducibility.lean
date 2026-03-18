/- # CatActualityIrreducibility — Twin-Model Construction

   The subobject classifier's row is structurally underdetermined:
   two valid 17-element extensions of the canonical witness agree on
   all non-classifier rows but disagree on the classifier's assignment
   to a surplus element.

   This demonstrates **actuality irreducibility**: the classifier's
   specific boolean assignments (which elements it maps to zero₁ vs zero₂)
   are genuine degrees of freedom that no combination of structural axioms
   can determine. The structure dictates THAT the classifier classifies,
   but not HOW it classifies individual elements.

   This is the same construction as `Psi16ActualityIrreducibility`,
   restated using categorical vocabulary.

   **Mathematical significance:** In topos theory, the subobject classifier
   Ω has a fixed structure (it classifies subobjects). But in a finite
   endomorphism magma, the classifier's specific row values are free —
   there is no canonical "true" and "false" beyond the structural role.

   All proofs are computational: `native_decide`.
-/

import DistinctionStructures.CatWitness

set_option maxHeartbeats 1600000
set_option autoImplicit false

namespace CatActualityIrreducibility

open CatFoundation CatWitness

/-! ## Part 1: The Twin-Model Construction on Fin 17

    Extend the canonical 16-element witness by adding a surplus element q = 16.
    For all non-classifier rows, column 16 copies column 2 (proj₁'s column).
    Row q copies row proj₁ (element 2) entirely.

    The two models differ ONLY in the classifier's (element 3) row:
    - Model 1 (`dot17₁`): cls · q = zero₂ (1)
    - Model 2 (`dot17₂`): cls · q = zero₁ (0), cls · proj₁ = zero₂ (swapped)

    In categorical terms: both models have a valid subobject classifier
    with boolean-valued row, but they disagree on which elements are
    classified as "true" vs "false". -/

abbrev q : Fin 17 := 16

/-- The base 16×16 table (same as CatWitness.rawDot, reproduced for
    self-containment). -/
private def rawBase : Nat → Nat → Nat
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

/-- Raw operation for model 1: extend witness with cls · q = zero₂ (1). -/
private def rawDot17₁ : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  | 2, 16 => 13 | 2, b => rawBase 2 b
  | 3, 16 => 1  | 3, b => rawBase 3 b   -- cls · q = zero₂ (1)
  | 4, 16 => 11 | 4, b => rawBase 4 b
  | 5, 16 => 1  | 5, b => rawBase 5 b
  | 6, 16 => 5  | 6, b => rawBase 6 b
  | 7, 16 => 8  | 7, b => rawBase 7 b
  | 8, 16 => 13 | 8, b => rawBase 8 b
  | 9, 16 => 14 | 9, b => rawBase 9 b
  | 10, 16 => 4  | 10, b => rawBase 10 b
  | 11, 16 => 9  | 11, b => rawBase 11 b
  | 12, 16 => 1  | 12, b => rawBase 12 b
  | 13, 16 => 14 | 13, b => rawBase 13 b
  | 14, 16 => 5  | 14, b => rawBase 14 b
  | 15, 16 => 13 | 15, b => rawBase 15 b
  | 16, 16 => 13 | 16, b => rawBase 2 b  -- row q copies row proj₁
  | _, _ => 0

/-- Raw operation for model 2: cls · q = zero₁ (0), cls · proj₁ = zero₂ (1). -/
private def rawDot17₂ : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  | 2, 16 => 13 | 2, b => rawBase 2 b
  | 3, 2 => 1 | 3, 16 => 0 | 3, b => rawBase 3 b  -- SWAPPED
  | 4, 16 => 11 | 4, b => rawBase 4 b
  | 5, 16 => 1  | 5, b => rawBase 5 b
  | 6, 16 => 5  | 6, b => rawBase 6 b
  | 7, 16 => 8  | 7, b => rawBase 7 b
  | 8, 16 => 13 | 8, b => rawBase 8 b
  | 9, 16 => 14 | 9, b => rawBase 9 b
  | 10, 16 => 4  | 10, b => rawBase 10 b
  | 11, 16 => 9  | 11, b => rawBase 11 b
  | 12, 16 => 1  | 12, b => rawBase 12 b
  | 13, 16 => 14 | 13, b => rawBase 13 b
  | 14, 16 => 5  | 14, b => rawBase 14 b
  | 15, 16 => 13 | 15, b => rawBase 15 b
  | 16, 16 => 13 | 16, b => rawBase 2 b
  | _, _ => 0

private theorem rawDot17₁_bound (a b : Fin 17) : rawDot17₁ a.val b.val < 17 := by
  revert a b; native_decide

private theorem rawDot17₂_bound (a b : Fin 17) : rawDot17₂ a.val b.val < 17 := by
  revert a b; native_decide

/-- Model 1 operation on Fin 17. -/
def dot17₁ (a b : Fin 17) : Fin 17 := ⟨rawDot17₁ a.val b.val, rawDot17₁_bound a b⟩

/-- Model 2 operation on Fin 17. -/
def dot17₂ (a b : Fin 17) : Fin 17 := ⟨rawDot17₂ a.val b.val, rawDot17₂_bound a b⟩

/-! ## Part 2: Both Models Extend the Canonical Witness -/

/-- Embed Fin 16 into Fin 17. -/
def embed (x : Fin 16) : Fin 17 := ⟨x.val, Nat.lt_trans x.isLt (by omega)⟩

/-- Model 1 agrees with the canonical witness on the original 16 elements. -/
theorem dot17₁_extends : ∀ a b : Fin 16,
    dot17₁ (embed a) (embed b) = embed (dot16 a b) := by native_decide

/-- Model 2 agrees on all except cls · proj₁ (row 3, col 2). -/
theorem dot17₂_extends_non_cls_proj₁ : ∀ a b : Fin 16,
    (a ≠ 3 ∨ b ≠ 2) →
    dot17₂ (embed a) (embed b) = embed (dot16 a b) := by native_decide

/-! ## Part 3: The Models Disagree on the Classifier's Assignment to q -/

/-- The two models disagree on cls · q. -/
theorem models_disagree : dot17₁ 3 q ≠ dot17₂ 3 q := by native_decide

/-- Model 1: cls · q = zero₂ (1). -/
theorem dot17₁_cls_q : dot17₁ 3 q = 1 := by native_decide

/-- Model 2: cls · q = zero₁ (0). -/
theorem dot17₂_cls_q : dot17₂ 3 q = 0 := by native_decide

/-- Model 2 flips cls · proj₁ from zero₁ to zero₂. -/
theorem dot17₂_cls_proj₁_swap : dot17₂ 3 (embed 2) = 1 := by native_decide

/-- Model 1 preserves original cls · proj₁ = zero₁. -/
theorem dot17₁_cls_proj₁_orig : dot17₁ 3 (embed 2) = 0 := by native_decide

/-! ## Part 4: Both Models Preserve Structural Axioms -/

/-- Both models have zero₁ (0) as a left-zero morphism. -/
theorem dot17₁_zero₁_absorbs : ∀ x : Fin 17, dot17₁ 0 x = 0 := by native_decide
theorem dot17₂_zero₁_absorbs : ∀ x : Fin 17, dot17₂ 0 x = 0 := by native_decide

/-- Both models have zero₂ (1) as a left-zero morphism. -/
theorem dot17₁_zero₂_absorbs : ∀ x : Fin 17, dot17₁ 1 x = 1 := by native_decide
theorem dot17₂_zero₂_absorbs : ∀ x : Fin 17, dot17₂ 1 x = 1 := by native_decide

/-- In both models, only 0 and 1 are left-zero morphisms. -/
theorem dot17₁_only_two_zeros : ∀ a : Fin 17,
    (∀ x : Fin 17, dot17₁ a x = a) → (a = 0 ∨ a = 1) := by native_decide
theorem dot17₂_only_two_zeros : ∀ a : Fin 17,
    (∀ x : Fin 17, dot17₂ a x = a) → (a = 0 ∨ a = 1) := by native_decide

/-- The classifier (element 3) is boolean-valued in both models. -/
theorem dot17₁_cls_boolean : ∀ x : Fin 17,
    dot17₁ 3 x = 0 ∨ dot17₁ 3 x = 1 := by native_decide
theorem dot17₂_cls_boolean : ∀ x : Fin 17,
    dot17₂ 3 x = 0 ∨ dot17₂ 3 x = 1 := by native_decide

/-- Retraction transparency holds in both models. -/
theorem dot17₁_ret_zero₁ : dot17₁ 7 0 = 0 := by native_decide
theorem dot17₁_ret_zero₂ : dot17₁ 7 1 = 1 := by native_decide
theorem dot17₂_ret_zero₁ : dot17₂ 7 0 = 0 := by native_decide
theorem dot17₂_ret_zero₂ : dot17₂ 7 1 = 1 := by native_decide

/-- Retraction pair round-trip holds on core in both models. -/
theorem dot17₁_ret_sec : ∀ x : Fin 17,
    (x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5) →
    dot17₁ 7 (dot17₁ 6 x) = x := by native_decide
theorem dot17₂_ret_sec : ∀ x : Fin 17,
    (x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5) →
    dot17₂ 7 (dot17₂ 6 x) = x := by native_decide

/-- All columns are distinct in both models. -/
theorem dot17₁_ext_cols : ∀ a b : Fin 17, a ≠ b →
    ∃ x : Fin 17, dot17₁ x a ≠ dot17₁ x b := by native_decide
theorem dot17₂_ext_cols : ∀ a b : Fin 17, a ≠ b →
    ∃ x : Fin 17, dot17₂ x a ≠ dot17₂ x b := by native_decide

/-! ## Part 5: Non-Classifier Agreement -/

/-- The two models agree on all inputs where the first argument is not
    the classifier (element 3). -/
theorem ops_agree_non_cls : ∀ a b : Fin 17,
    a ≠ 3 → dot17₁ a b = dot17₂ a b := by native_decide

/-! ## Part 6: Main Theorem -/

/-- **Actuality Irreducibility**: There exist two valid 17-element extensions
    of the canonical witness that satisfy all structural axioms yet disagree
    on the classifier's evaluation of the surplus element.

    The classifier's assignment is a genuine degree of freedom — no
    structural axiom can determine it. In categorical terms: the subobject
    classifier's specific truth-value assignments are underdetermined by
    the algebraic structure.

    **Philosophical import:** The algebra dictates THAT classification occurs
    (the classifier must exist and be boolean-valued) but not HOW any
    particular element is classified. This is the sense in which
    "actuality is irreducible to structure." -/
theorem actuality_irreducibility :
    -- Both models have the same zero morphisms
    (∀ x : Fin 17, dot17₁ 0 x = 0) ∧
    (∀ x : Fin 17, dot17₂ 0 x = 0) ∧
    (∀ x : Fin 17, dot17₁ 1 x = 1) ∧
    (∀ x : Fin 17, dot17₂ 1 x = 1) ∧
    -- The classifier is boolean-valued in both
    (∀ x : Fin 17, dot17₁ 3 x = 0 ∨ dot17₁ 3 x = 1) ∧
    (∀ x : Fin 17, dot17₂ 3 x = 0 ∨ dot17₂ 3 x = 1) ∧
    -- Retraction transparency in both
    (dot17₁ 7 0 = 0) ∧ (dot17₁ 7 1 = 1) ∧
    (dot17₂ 7 0 = 0) ∧ (dot17₂ 7 1 = 1) ∧
    -- All columns distinct in both
    (∀ a b : Fin 17, a ≠ b → ∃ x, dot17₁ x a ≠ dot17₁ x b) ∧
    (∀ a b : Fin 17, a ≠ b → ∃ x, dot17₂ x a ≠ dot17₂ x b) ∧
    -- Yet they disagree on cls · q
    (dot17₁ 3 q ≠ dot17₂ 3 q) :=
  ⟨dot17₁_zero₁_absorbs, dot17₂_zero₁_absorbs,
   dot17₁_zero₂_absorbs, dot17₂_zero₂_absorbs,
   dot17₁_cls_boolean, dot17₂_cls_boolean,
   dot17₁_ret_zero₁, dot17₁_ret_zero₂,
   dot17₂_ret_zero₁, dot17₂_ret_zero₂,
   dot17₁_ext_cols, dot17₂_ext_cols,
   models_disagree⟩

end CatActualityIrreducibility

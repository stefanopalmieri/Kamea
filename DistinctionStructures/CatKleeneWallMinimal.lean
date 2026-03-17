/- # CatKleeneWallMinimal — The Kleene Wall: Definitions, Witness, and Universal Proofs

   This file is self-contained. It defines the minimal algebraic structure
   needed for the Kleene wall theorem, constructs the smallest possible
   witness (5 elements), and proves six universal consequences purely
   algebraically — no `decide`, no `native_decide`.

   ## What is the Kleene wall?

   In a finite endomorphism monoid with zero morphisms and a retraction pair,
   the **Kleene dichotomy** holds: every non-zero morphism either maps all
   non-zero inputs to boolean values {zero₁, zero₂} (a "classifier") or maps
   all non-zero inputs to non-boolean values (a "computational" morphism).
   No mixing. This clean separation between judgment and computation is
   called the **Kleene wall**.

   ## Structure of this file

   **Part 1:** `KleeneMonoid` — the minimal structure (6 elements, 14 axioms).
   **Part 2:** The 5-element witness — the smallest `KleeneMonoid`.
              N = 4 is unsatisfiable (verified by Z3 exhaustive search).
   **Part 3:** Six universal theorems, all proved purely algebraically.

   ## Relation to standard algebra

   - Zero morphisms: cf. `CategoryTheory.Limits.HasZeroMorphisms`
   - Retraction pair: cf. `CategoryTheory.RetractOf`
   - Subobject classifier: cf. `CategoryTheory.Subobject.classifier` (topos theory)
   - The Kleene dichotomy is an endomorphism-monoid analogue of the
     separation between logical and computational types in type theory.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace KleeneWall

-- ══════════════════════════════════════════════════════════════════════
-- Part 1: The KleeneMonoid Structure
-- ══════════════════════════════════════════════════════════════════════

/-- A finite endomorphism monoid with zero morphisms, a retraction pair,
    a subobject classifier, and the Kleene dichotomy.

    This is the minimal structure needed for the Kleene wall theorem.
    No products, copairing, fixed points, composition, or selection.

    The bound N ≥ 5 is tight (N = 4 is unsatisfiable, verified by Z3). -/
structure KleeneMonoid (n : Nat) where
  /-- Binary operation (composition of endomorphisms). -/
  dot : Fin n → Fin n → Fin n

  /-- First left-zero morphism. -/
  zero₁ : Fin n
  /-- Second left-zero morphism. -/
  zero₂ : Fin n
  /-- Section of the retraction pair. -/
  sec : Fin n
  /-- Retraction (left-inverse of section on non-zeros). -/
  ret : Fin n
  /-- Subobject classifier (boolean-valued row). -/
  cls : Fin n

  -- === Zero morphisms (4 axioms) ===

  /-- zero₁ absorbs on the left. -/
  zero₁_left : ∀ x : Fin n, dot zero₁ x = zero₁
  /-- zero₂ absorbs on the left. -/
  zero₂_left : ∀ x : Fin n, dot zero₂ x = zero₂
  /-- The two zero morphisms are distinct. -/
  zeros_distinct : zero₁ ≠ zero₂
  /-- No other element is a left-zero morphism. -/
  no_other_zeros : ∀ y : Fin n, (∀ x : Fin n, dot y x = y) → y = zero₁ ∨ y = zero₂

  -- === Extensionality (1 axiom) ===

  /-- Row extensionality: elements with identical rows are equal. -/
  extensional : ∀ a b : Fin n, (∀ x : Fin n, dot a x = dot b x) → a = b

  -- === Retraction pair (3 axioms) ===

  /-- `ret ∘ sec = id` on non-zero elements. -/
  ret_sec : ∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ → dot ret (dot sec x) = x
  /-- `sec ∘ ret = id` on non-zero elements. -/
  sec_ret : ∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ → dot sec (dot ret x) = x
  /-- The retraction preserves zero₁. This is a transparency condition
      ensuring the retraction is anchored to the zero structure. -/
  ret_zero₁ : dot ret zero₁ = zero₁

  -- === Classifier (3 axioms) ===

  /-- The classifier's row is boolean-valued on ALL inputs. -/
  cls_boolean : ∀ x : Fin n, dot cls x = zero₁ ∨ dot cls x = zero₂
  /-- The classifier is not zero₁. -/
  cls_ne_zero₁ : cls ≠ zero₁
  /-- The classifier is not zero₂. -/
  cls_ne_zero₂ : cls ≠ zero₂

  -- === Kleene dichotomy (2 axioms) ===

  /-- Every non-zero element is either all-boolean or all-non-boolean
      on non-zero inputs. No mixing. -/
  kleene : ∀ y : Fin n, y ≠ zero₁ → y ≠ zero₂ →
    (∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ →
      dot y x = zero₁ ∨ dot y x = zero₂) ∨
    (∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ →
      dot y x ≠ zero₁ ∧ dot y x ≠ zero₂)

  /-- A non-zero element with non-boolean output on a non-zero input exists.
      This guarantees the non-classifier class is inhabited. -/
  has_non_classifier : ∃ y : Fin n, y ≠ zero₁ ∧ y ≠ zero₂ ∧
    ∃ x : Fin n, x ≠ zero₁ ∧ x ≠ zero₂ ∧ dot y x ≠ zero₁ ∧ dot y x ≠ zero₂


-- ══════════════════════════════════════════════════════════════════════
-- Part 2: The 5-Element Witness
-- ══════════════════════════════════════════════════════════════════════

/-! ### The minimal witness

    The smallest `KleeneMonoid` has **5 elements**. N = 4 is unsatisfiable
    (verified by Z3).

    ```
    Element assignments:
      0 = zero₁    1 = zero₂    2 = sec    3 = ret    4 = cls

    Cayley table:
         0  1  2  3  4
      0 [0, 0, 0, 0, 0]   ← zero₁ (left-absorber)
      1 [1, 1, 1, 1, 1]   ← zero₂ (left-absorber)
      2 [1, 0, 3, 4, 2]   ← sec (non-classifier: outputs {3,4,2} on non-zeros)
      3 [0, 2, 4, 2, 3]   ← ret (non-classifier: outputs {4,2,3} on non-zeros)
      4 [0, 1, 1, 0, 0]   ← cls (classifier: outputs {1,0,0} ⊆ {0,1} on non-zeros)

    Category distribution:
      Zeros (2):           {0, 1}
      Classifiers (1):     {4}
      Non-classifiers (2): {2, 3}

    Properties: WL-1 rigid, |Aut| = 1, power-associative, no right identity.
    ```
-/

/-- The raw 5×5 Cayley table. -/
private def rawK5 : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 3 | 2, 3 => 4 | 2, 4 => 2
  | 3, 0 => 0 | 3, 1 => 2 | 3, 2 => 4 | 3, 3 => 2 | 3, 4 => 3
  | 4, 0 => 0 | 4, 1 => 1 | 4, 2 => 1 | 4, 3 => 0 | 4, 4 => 0
  | _, _ => 0

private theorem rawK5_bound (a b : Fin 5) : rawK5 a.val b.val < 5 := by
  revert a b; decide

/-- The binary operation of the 5-element witness. -/
def dotK5 (a b : Fin 5) : Fin 5 := ⟨rawK5 a.val b.val, rawK5_bound a b⟩

/-- **The minimal 5-element Kleene monoid.** N = 4 is unsatisfiable. -/
def kleene5 : KleeneMonoid 5 where
  dot := dotK5
  zero₁ := 0
  zero₂ := 1
  sec := 2
  ret := 3
  cls := 4
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide
  ret_sec := by decide
  sec_ret := by decide
  ret_zero₁ := by decide
  cls_boolean := by decide
  cls_ne_zero₁ := by decide
  cls_ne_zero₂ := by decide
  kleene := by decide
  has_non_classifier := by decide


-- ══════════════════════════════════════════════════════════════════════
-- Part 3: Universal Theorems
--
-- All proofs are purely algebraic. No `decide` or `native_decide`.
-- Every theorem holds for ALL KleeneMonoid instances.
-- ══════════════════════════════════════════════════════════════════════

section UniversalTheorems

variable {n : Nat} (M : KleeneMonoid n)

-- ─────────────────────────────────────────────────────────────────────
-- Theorem 1: Classifier distinctness from non-classifiers
-- ─────────────────────────────────────────────────────────────────────

/-- **Classifier distinctness**: any element with a non-boolean output
    differs from the classifier.

    Proof: `cls_boolean` constrains ALL outputs of cls to {zero₁, zero₂}.
    A non-boolean output contradicts this. -/
theorem cls_ne_of_non_boolean (y x : Fin n)
    (hyx : M.dot y x ≠ M.zero₁ ∧ M.dot y x ≠ M.zero₂) :
    y ≠ M.cls := by
  intro heq
  subst heq
  rcases M.cls_boolean x with h | h
  · exact hyx.1 h
  · exact hyx.2 h

-- ─────────────────────────────────────────────────────────────────────
-- Theorem 2: Zero distinctness from non-zeros
-- ─────────────────────────────────────────────────────────────────────

/-- **Zero₁ distinctness**: if `dot y x₀ ≠ y` for some `x₀`, then `y ≠ zero₁`. -/
theorem ne_zero₁_of_nonconstant (y x₀ : Fin n) (h : M.dot y x₀ ≠ y) :
    y ≠ M.zero₁ := by
  intro heq; subst heq; exact h (M.zero₁_left x₀)

/-- **Zero₂ distinctness**: if `dot y x₀ ≠ y` for some `x₀`, then `y ≠ zero₂`. -/
theorem ne_zero₂_of_nonconstant (y x₀ : Fin n) (h : M.dot y x₀ ≠ y) :
    y ≠ M.zero₂ := by
  intro heq; subst heq; exact h (M.zero₂_left x₀)

-- ─────────────────────────────────────────────────────────────────────
-- Theorem 3: Three-category decomposition
-- ─────────────────────────────────────────────────────────────────────

/-- An element is a **zero morphism** if its row is constant at itself. -/
def IsZero (a : Fin n) : Prop := ∀ x : Fin n, M.dot a x = a

/-- An element is a **classifier** if it is non-zero and all-boolean on non-zeros. -/
def IsClassifier (a : Fin n) : Prop :=
  a ≠ M.zero₁ ∧ a ≠ M.zero₂ ∧
  ∀ x : Fin n, x ≠ M.zero₁ → x ≠ M.zero₂ → M.dot a x = M.zero₁ ∨ M.dot a x = M.zero₂

/-- An element is a **non-classifier** if it is non-zero and all-non-boolean on non-zeros. -/
def IsNonClassifier (a : Fin n) : Prop :=
  a ≠ M.zero₁ ∧ a ≠ M.zero₂ ∧
  ∀ x : Fin n, x ≠ M.zero₁ → x ≠ M.zero₂ → M.dot a x ≠ M.zero₁ ∧ M.dot a x ≠ M.zero₂

/-- **Three-category exhaustion**: every element is a zero, classifier,
    or non-classifier. Follows directly from the Kleene dichotomy. -/
theorem three_categories (a : Fin n) :
    IsZero M a ∨ IsClassifier M a ∨ IsNonClassifier M a := by
  by_cases h1 : a = M.zero₁
  · left; subst h1; exact M.zero₁_left
  · by_cases h2 : a = M.zero₂
    · left; subst h2; exact M.zero₂_left
    · rcases M.kleene a h1 h2 with hb | hc
      · exact Or.inr (Or.inl ⟨h1, h2, hb⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, hc⟩)

/-- **Disjointness (classifier vs non-classifier)**: no element is both. -/
theorem classifier_not_non_classifier (a : Fin n)
    (hc : IsClassifier M a) (hnc : IsNonClassifier M a) : False := by
  rcases hc.2.2 M.cls M.cls_ne_zero₁ M.cls_ne_zero₂ with h | h
  · exact (hnc.2.2 M.cls M.cls_ne_zero₁ M.cls_ne_zero₂).1 h
  · exact (hnc.2.2 M.cls M.cls_ne_zero₁ M.cls_ne_zero₂).2 h

-- ─────────────────────────────────────────────────────────────────────
-- Theorem 4: No right identity
-- ─────────────────────────────────────────────────────────────────────

/-- **No right identity** exists in any KleeneMonoid.

    Proof: if `e` is right identity, `dot cls e = cls`. But `cls_boolean`
    forces `dot cls e ∈ {zero₁, zero₂}`, so `cls ∈ {zero₁, zero₂}`.
    Contradicts `cls_ne_zero₁` / `cls_ne_zero₂`. -/
theorem no_right_identity : ¬∃ e : Fin n, ∀ x : Fin n, M.dot x e = x := by
  intro ⟨e, he⟩
  rcases M.cls_boolean e with h | h
  · exact M.cls_ne_zero₁ (he M.cls ▸ h)
  · exact M.cls_ne_zero₂ (he M.cls ▸ h)

-- ─────────────────────────────────────────────────────────────────────
-- Theorem 5: Minimum cardinality ≥ 4
-- ─────────────────────────────────────────────────────────────────────

/-- Helper: the non-classifier witness is not zero₁. -/
private theorem nc_ne_zero₁_aux (y : Fin n)
    (hx : ∃ x : Fin n, x ≠ M.zero₁ ∧ x ≠ M.zero₂ ∧
      M.dot y x ≠ M.zero₁ ∧ M.dot y x ≠ M.zero₂) : y ≠ M.zero₁ := by
  obtain ⟨x, _, _, h1, _⟩ := hx
  intro heq; subst heq; exact h1 (M.zero₁_left x)

/-- Helper: the non-classifier witness is not zero₂. -/
private theorem nc_ne_zero₂_aux (y : Fin n)
    (hx : ∃ x : Fin n, x ≠ M.zero₁ ∧ x ≠ M.zero₂ ∧
      M.dot y x ≠ M.zero₁ ∧ M.dot y x ≠ M.zero₂) : y ≠ M.zero₂ := by
  obtain ⟨x, _, _, _, h2⟩ := hx
  intro heq; subst heq; exact h2 (M.zero₂_left x)

/-- Helper: the non-classifier witness is not cls. -/
private theorem nc_ne_cls_aux (y : Fin n)
    (hx : ∃ x : Fin n, x ≠ M.zero₁ ∧ x ≠ M.zero₂ ∧
      M.dot y x ≠ M.zero₁ ∧ M.dot y x ≠ M.zero₂) : y ≠ M.cls := by
  obtain ⟨x, _, _, h1, h2⟩ := hx
  exact cls_ne_of_non_boolean M y x ⟨h1, h2⟩

end UniversalTheorems

/-- **Minimum cardinality**: every KleeneMonoid has at least 4 elements.

    Proof: {zero₁, zero₂, cls, nc} are 4 pairwise-distinct elements.
    The bound is NOT tight for this structure: the actual minimum is N = 5
    (N = 4 is unsatisfiable due to the retraction pair). -/
theorem card_ge_four {n : Nat} (M : KleeneMonoid n) : 4 ≤ Fintype.card (Fin n) := by
  obtain ⟨nc, _, _, wit⟩ := M.has_non_classifier
  have h12 : M.zero₁ ≠ M.zero₂ := M.zeros_distinct
  have h1c : M.zero₁ ≠ M.cls := fun h => M.cls_ne_zero₁ h.symm
  have h1n : M.zero₁ ≠ nc := fun h => (nc_ne_zero₁_aux M nc wit) h.symm
  have h2c : M.zero₂ ≠ M.cls := fun h => M.cls_ne_zero₂ h.symm
  have h2n : M.zero₂ ≠ nc := fun h => (nc_ne_zero₂_aux M nc wit) h.symm
  have hcn : M.cls ≠ nc := fun h => (nc_ne_cls_aux M nc wit) h.symm
  have hcard : ({M.zero₁, M.zero₂, M.cls, nc} : Finset (Fin n)).card = 4 := by
    simp [h12, h1c, h1n, h2c, h2n, hcn]
  have hsub : ({M.zero₁, M.zero₂, M.cls, nc} : Finset (Fin n)) ⊆ Finset.univ :=
    fun _ _ => Finset.mem_univ _
  calc 4 = ({M.zero₁, M.zero₂, M.cls, nc} : Finset (Fin n)).card := hcard.symm
    _ ≤ Finset.univ.card := Finset.card_le_card hsub
    _ = Fintype.card (Fin n) := Finset.card_univ

section UniversalTheorems2

variable {n : Nat} (M : KleeneMonoid n)

-- ─────────────────────────────────────────────────────────────────────
-- Theorem 6: Retraction pair members are non-classifiers
-- ─────────────────────────────────────────────────────────────────────

/-- **The retraction is not the classifier.**

    Proof: `ret · (sec · nc) = nc` where nc is non-zero. Since
    `cls_boolean` constrains ALL inputs, if ret = cls then
    `nc ∈ {zero₁, zero₂}`, contradicting nc being non-zero. -/
theorem ret_ne_cls : M.ret ≠ M.cls := by
  obtain ⟨nc, hnc1, hnc2, _⟩ := M.has_non_classifier
  intro heq
  have h := M.ret_sec nc hnc1 hnc2
  rw [heq] at h
  rcases M.cls_boolean (M.dot M.sec nc) with hb | hb
  · exact hnc1 (h ▸ hb)
  · exact hnc2 (h ▸ hb)

/-- **The section is not the classifier.** Symmetric argument using `sec_ret`. -/
theorem sec_ne_cls : M.sec ≠ M.cls := by
  obtain ⟨nc, hnc1, hnc2, _⟩ := M.has_non_classifier
  intro heq
  have h := M.sec_ret nc hnc1 hnc2
  rw [heq] at h
  rcases M.cls_boolean (M.dot M.ret nc) with hb | hb
  · exact hnc1 (h ▸ hb)
  · exact hnc2 (h ▸ hb)

/-- **The retraction is not zero₁.** If ret = zero₁, its row is constant,
    but `ret · (sec · nc) = nc ≠ zero₁` gives a contradiction. -/
theorem ret_ne_zero₁ : M.ret ≠ M.zero₁ := by
  obtain ⟨nc, hnc1, hnc2, _⟩ := M.has_non_classifier
  intro heq
  have h := M.ret_sec nc hnc1 hnc2
  rw [heq, M.zero₁_left] at h
  exact hnc1 h.symm

/-- **The retraction is not zero₂.** Same argument. -/
theorem ret_ne_zero₂ : M.ret ≠ M.zero₂ := by
  obtain ⟨nc, hnc1, hnc2, _⟩ := M.has_non_classifier
  intro heq
  have h := M.ret_sec nc hnc1 hnc2
  rw [heq, M.zero₂_left] at h
  exact hnc2 h.symm

/-- **The section is not zero₁.** -/
theorem sec_ne_zero₁ : M.sec ≠ M.zero₁ := by
  obtain ⟨nc, hnc1, hnc2, _⟩ := M.has_non_classifier
  intro heq
  have h := M.sec_ret nc hnc1 hnc2
  rw [heq, M.zero₁_left] at h
  exact hnc1 h.symm

/-- **The section is not zero₂.** -/
theorem sec_ne_zero₂ : M.sec ≠ M.zero₂ := by
  obtain ⟨nc, hnc1, hnc2, _⟩ := M.has_non_classifier
  intro heq
  have h := M.sec_ret nc hnc1 hnc2
  rw [heq, M.zero₂_left] at h
  exact hnc2 h.symm

/-- **The retraction is a non-classifier** (all outputs on non-zero inputs
    are non-boolean).

    Proof strategy:
    1. Show `sec · cls` is non-zero using `ret_zero₁` and `cls_ne_zero₁`.
    2. Show `sec · nc` is non-zero using `ret_zero₁`, injectivity, and `nc ≠ cls`.
    3. Since `sec · nc` is non-zero, `ret · (sec · nc) = nc` (non-boolean)
       witnesses a non-boolean output of ret on a non-zero input.
    4. Kleene dichotomy places ret in the non-classifier class. -/
theorem ret_is_non_classifier : IsNonClassifier M M.ret := by
  have hrnz1 := ret_ne_zero₁ M
  have hrnz2 := ret_ne_zero₂ M
  refine ⟨hrnz1, hrnz2, ?_⟩
  obtain ⟨nc, hnc1, hnc2, x, hx1, hx2, hyx1, hyx2⟩ := M.has_non_classifier
  -- ret is either all-boolean or all-non-boolean on non-zeros
  rcases M.kleene M.ret hrnz1 hrnz2 with hbool | hcomp
  · -- Contradiction: if ret is all-boolean on non-zeros, then for any non-zero y
    -- with sec · y non-zero, ret · (sec · y) ∈ {zero₁, zero₂}. But ret_sec says
    -- ret · (sec · y) = y, forcing y to be zero. We find such a y.
    exfalso
    -- Step 1: sec · cls ≠ zero₁ (otherwise ret_zero₁ gives cls = zero₁)
    have hsc1 : M.dot M.sec M.cls ≠ M.zero₁ := by
      intro heq
      have := M.ret_sec M.cls M.cls_ne_zero₁ M.cls_ne_zero₂
      rw [heq, M.ret_zero₁] at this
      exact M.cls_ne_zero₁ this.symm
    -- Step 2: if sec · cls is non-zero, ret maps it to cls ∈ {zero₁, zero₂}. Contradiction.
    have hsc_zero₂ : M.dot M.sec M.cls = M.zero₂ := by
      by_contra hne
      have hscnz : M.dot M.sec M.cls ≠ M.zero₂ := hne
      -- sec · cls is non-zero, so ret · (sec · cls) ∈ {zero₁, zero₂}
      rcases hbool (M.dot M.sec M.cls) hsc1 hscnz with h | h
      · exact M.cls_ne_zero₁ ((M.ret_sec M.cls M.cls_ne_zero₁ M.cls_ne_zero₂).symm ▸ h)
      · exact M.cls_ne_zero₂ ((M.ret_sec M.cls M.cls_ne_zero₁ M.cls_ne_zero₂).symm ▸ h)
    -- Step 3: sec · nc ≠ zero₁ (by ret_zero₁)
    have hsn1 : M.dot M.sec nc ≠ M.zero₁ := by
      intro heq
      have := M.ret_sec nc hnc1 hnc2
      rw [heq, M.ret_zero₁] at this
      exact hnc1 this.symm
    -- Step 4: sec · nc ≠ zero₂ (= sec · cls, and sec is injective on non-zeros)
    have hcn : nc ≠ M.cls := nc_ne_cls_aux M nc ⟨x, hx1, hx2, hyx1, hyx2⟩
    have hsn2 : M.dot M.sec nc ≠ M.zero₂ := by
      intro heq
      -- sec · nc = zero₂ = sec · cls. If sec's row agrees on nc and cls,
      -- and ret ∘ sec = id on non-zeros, then nc = cls. Contradiction.
      have := M.ret_sec nc hnc1 hnc2
      rw [heq] at this
      have := M.ret_sec M.cls M.cls_ne_zero₁ M.cls_ne_zero₂
      rw [hsc_zero₂] at this
      -- ret · zero₂ = nc AND ret · zero₂ = cls. So nc = cls.
      have hret_z2_nc : M.dot M.ret M.zero₂ = nc := by
        have := M.ret_sec nc hnc1 hnc2; rw [heq] at this; exact this
      have hret_z2_cls : M.dot M.ret M.zero₂ = M.cls := by
        have := M.ret_sec M.cls M.cls_ne_zero₁ M.cls_ne_zero₂; rw [hsc_zero₂] at this; exact this
      exact hcn (hret_z2_nc.symm.trans hret_z2_cls)
    -- Step 5: sec · nc is non-zero, so ret · (sec · nc) = nc ∈ {zero₁, zero₂}. Contradiction.
    rcases hbool (M.dot M.sec nc) hsn1 hsn2 with h | h
    · exact hnc1 ((M.ret_sec nc hnc1 hnc2).symm ▸ h)
    · exact hnc2 ((M.ret_sec nc hnc1 hnc2).symm ▸ h)
  · exact hcomp

/-- **The section is a non-classifier.**

    Proof: since ret is a non-classifier (all-non-boolean on non-zeros),
    `ret · nc` is non-boolean and non-zero. Then `sec · (ret · nc) = nc`
    witnesses a non-boolean output of sec on the non-zero input `ret · nc`. -/
theorem sec_is_non_classifier : IsNonClassifier M M.sec := by
  have hsnz1 := sec_ne_zero₁ M
  have hsnz2 := sec_ne_zero₂ M
  refine ⟨hsnz1, hsnz2, ?_⟩
  obtain ⟨nc, hnc1, hnc2, x, hx1, hx2, hyx1, hyx2⟩ := M.has_non_classifier
  -- ret is a non-classifier: all outputs on non-zeros are non-boolean
  have hret_nc := (ret_is_non_classifier M).2.2
  -- ret · nc is non-zero and non-boolean (since nc is non-zero)
  have hrnc := hret_nc nc hnc1 hnc2
  -- sec · (ret · nc) = nc (by sec_ret, since nc is non-zero)
  have hsec := M.sec_ret nc hnc1 hnc2
  -- sec maps (ret · nc) to nc. nc is non-boolean. ret · nc is non-zero.
  -- So sec has non-boolean output on a non-zero input → non-classifier by Kleene.
  rcases M.kleene M.sec hsnz1 hsnz2 with hbool | hcomp
  · exfalso
    rcases hbool (M.dot M.ret nc) hrnc.1 hrnc.2 with h | h
    · exact hnc1 (hsec ▸ h)
    · exact hnc2 (hsec ▸ h)
  · exact hcomp

end UniversalTheorems2

end KleeneWall

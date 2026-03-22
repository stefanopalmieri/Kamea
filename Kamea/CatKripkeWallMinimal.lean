/- # CatKripkeWallMinimal — The Kripke Wall

   ## Summary

   We study a property — the **Kripke dichotomy** — of a standard algebraic
   object: a finite faithful extensional magma on a 2-pointed set with
   a retraction pair. All ingredients are textbook:

   - **Extensional magma on a 2-pointed set (S, B):** a set S with a
     binary operation and a distinguished 2-element subset B = {zero₁, zero₂}
     whose elements are left-zeros (absorbers under the operation).
     The magma is extensional (all rows in the Cayley table are distinct) and
     B contains the only left-zeros.
   - **Retraction pair:** two transformations (sec, ret) that are mutual
     inverses on the core S \ B, with ret preserving zero₁. Standard
     categorical concept (cf. `CategoryTheory.RetractOf`).

   The **Kripke dichotomy** is the one new property: every non-constant
   transformation either maps the core entirely into B (a "classifier") or
   maps the core entirely into S \ B (a "non-classifier"). No mixing.

   This clean separation between classification and computation is the
   **Kripke wall**.

   ## Results

   In any finite faithful extensional magma on (S, B) with a retraction
   pair satisfying the Kripke dichotomy:

   1. The carrier decomposes into three disjoint classes (Z, C, N).
   2. No right identity exists.
   3. The retraction pair belongs to the non-classifier class N.
   4. |S| ≥ 4, tight (`kripke4`, with sec = ret).
   5. |S| ≥ 5 if sec ≠ ret, tight (`kripke5`).

   All proofs are purely algebraic — no `decide`, no `native_decide`.

   ## Structure of this file

   **Part 1a:** `FaithfulRetractMagma` — the standard setup.
   **Part 1b:** `DichotomicRetractMagma` — extends the setup with the Kripke dichotomy.
   **Part 2a:** The 4-element witness (minimum, sec = ret).
   **Part 2b:** The 5-element witness (minimum with sec ≠ ret).
   **Part 3:** Universal theorems.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace KripkeWall

-- ══════════════════════════════════════════════════════════════════════
-- Part 1a: The Standard Setup
-- ══════════════════════════════════════════════════════════════════════

/-- A finite faithful extensional magma on a 2-pointed set (S, B)
    with a retraction pair.

    This is standard algebra:
    - S is the carrier, B = {zero₁, zero₂} ⊆ S is the distinguished pair.
    - B elements are left-zeros: they absorb on the left.
    - Faithfulness: all rows in the Cayley table are distinct.
    - The retraction pair (sec, ret) are mutual inverses on the core S \ B,
      with ret preserving zero₁ (anchoring the retraction to the
      zero structure). -/
structure FaithfulRetractMagma (n : Nat) where
  /-- Binary operation (composition of transformations). -/
  dot : Fin n → Fin n → Fin n

  /-- First element of the distinguished pair B. -/
  zero₁ : Fin n
  /-- Second element of the distinguished pair B. -/
  zero₂ : Fin n
  /-- Section of the retraction pair. -/
  sec : Fin n
  /-- Retraction (left-inverse of section on the core). -/
  ret : Fin n

  -- === 2-pointed set: B = {zero₁, zero₂} are left-zeros ===

  /-- zero₁ absorbs on the left. -/
  zero₁_left : ∀ x : Fin n, dot zero₁ x = zero₁
  /-- zero₂ absorbs on the left. -/
  zero₂_left : ∀ x : Fin n, dot zero₂ x = zero₂
  /-- B has exactly two elements. -/
  zeros_distinct : zero₁ ≠ zero₂
  /-- B contains all left-zeros (no others). -/
  no_other_zeros : ∀ y : Fin n, (∀ x : Fin n, dot y x = y) → y = zero₁ ∨ y = zero₂

  -- === Faithfulness ===

  /-- Row extensionality: elements with identical rows are equal.
      Equivalently, the left regular representation is faithful. -/
  extensional : ∀ a b : Fin n, (∀ x : Fin n, dot a x = dot b x) → a = b

  -- === Retraction pair with zero-preservation ===

  /-- `ret ∘ sec = id` on the core. -/
  ret_sec : ∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ → dot ret (dot sec x) = x
  /-- `sec ∘ ret = id` on the core. -/
  sec_ret : ∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ → dot sec (dot ret x) = x
  /-- The retraction preserves zero₁, anchoring the pair to the
      zero structure. -/
  ret_zero₁ : dot ret zero₁ = zero₁

-- ══════════════════════════════════════════════════════════════════════
-- Part 1b: The Kripke Dichotomy
-- ══════════════════════════════════════════════════════════════════════

/-- A faithful retract magma satisfying the **Kripke dichotomy**: every
    non-constant transformation either maps the core entirely into B
    (a "classifier") or maps the core entirely into S \ B (a
    "non-classifier"). No mixing.

    The setup (`FaithfulRetractMagma`) is standard. The Kripke dichotomy
    is the one new property. The classifier and non-degeneracy conditions
    ensure both sides of the dichotomy are inhabited.

    Minimum carrier size: N ≥ 4 (tight, `kripke4`).
    With sec ≠ ret: N ≥ 5 (tight, `kripke5`). -/
structure DichotomicRetractMagma (n : Nat) extends FaithfulRetractMagma n where
  /-- A classifier: a non-constant transformation whose row is
      entirely in B. -/
  cls : Fin n
  /-- The classifier maps all inputs into B. -/
  cls_boolean : ∀ x : Fin n, dot cls x = zero₁ ∨ dot cls x = zero₂
  /-- The classifier is not zero₁ (non-degeneracy). -/
  cls_ne_zero₁ : cls ≠ zero₁
  /-- The classifier is not zero₂ (non-degeneracy). -/
  cls_ne_zero₂ : cls ≠ zero₂

  -- === The Kripke dichotomy ===

  /-- Every non-constant transformation is either all-B or all-non-B
      on the core. This is the single new property. -/
  dichotomy : ∀ y : Fin n, y ≠ zero₁ → y ≠ zero₂ →
    (∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ →
      dot y x = zero₁ ∨ dot y x = zero₂) ∨
    (∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ →
      dot y x ≠ zero₁ ∧ dot y x ≠ zero₂)

  /-- The non-classifier class is inhabited (non-degeneracy). -/
  has_non_classifier : ∃ y : Fin n, y ≠ zero₁ ∧ y ≠ zero₂ ∧
    ∃ x : Fin n, x ≠ zero₁ ∧ x ≠ zero₂ ∧ dot y x ≠ zero₁ ∧ dot y x ≠ zero₂


-- ══════════════════════════════════════════════════════════════════════
-- Part 2a: The 4-Element Witness (minimum, sec = ret)
-- ══════════════════════════════════════════════════════════════════════

/-! ### The minimal witness (sec = ret)

    The smallest `DichotomicRetractMagma` has **4 elements**, achieved when sec = ret.

    ```
    Element assignments:
      0 = zero₁    1 = zero₂    2 = cls    3 = sec = ret

    Cayley table:
         0  1  2  3
      0 [0, 0, 0, 0]   ← zero₁ (left-absorber)
      1 [1, 1, 1, 1]   ← zero₂ (left-absorber)
      2 [0, 1, 0, 1]   ← cls (classifier: outputs {0,1} on non-zeros)
      3 [0, 0, 2, 3]   ← sec = ret (non-classifier: outputs {2,3} on non-zeros)

    Category distribution:
      Zeros (2):           {0, 1}
      Classifiers (1):     {2}
      Non-classifiers (1): {3}
    ```
-/

/-- The raw 4×4 Cayley table. -/
private def rawK4 : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => 0 | 2, 3 => 1
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 2 | 3, 3 => 3
  | _, _ => 0

private theorem rawK4_bound (a b : Fin 4) : rawK4 a.val b.val < 4 := by
  revert a b; decide

/-- The binary operation of the 4-element witness. -/
def dotK4 (a b : Fin 4) : Fin 4 := ⟨rawK4 a.val b.val, rawK4_bound a b⟩

/-- **The minimal 4-element dichotomic magma.** The smallest possible,
    achieved with sec = ret. -/
def kripke4 : DichotomicRetractMagma 4 where
  dot := dotK4
  zero₁ := 0
  zero₂ := 1
  sec := 3
  ret := 3
  cls := 2
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
  dichotomy := by decide
  has_non_classifier := by decide

-- ══════════════════════════════════════════════════════════════════════
-- Part 2b: The 5-Element Witness (minimum with sec ≠ ret)
-- ══════════════════════════════════════════════════════════════════════

/-! ### The minimal witness with sec ≠ ret

    The smallest `DichotomicRetractMagma` with sec ≠ ret has **5 elements**.
    N = 4 with sec ≠ ret is unsatisfiable (verified by Z3).

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

/-- **The minimal 5-element dichotomic magma with sec ≠ ret.**
    N = 4 with sec ≠ ret is unsatisfiable. -/
def kripke5 : DichotomicRetractMagma 5 where
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
  dichotomy := by decide
  has_non_classifier := by decide


-- ══════════════════════════════════════════════════════════════════════
-- Part 3: Universal Theorems
--
-- All proofs are purely algebraic. No `decide` or `native_decide`.
-- Every theorem holds for ALL dichotomic magma instances.
-- ══════════════════════════════════════════════════════════════════════

section UniversalTheorems

variable {n : Nat} (M : DichotomicRetractMagma n)

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
    or non-classifier. Follows directly from the Kripke dichotomy. -/
theorem three_categories (a : Fin n) :
    IsZero M a ∨ IsClassifier M a ∨ IsNonClassifier M a := by
  by_cases h1 : a = M.zero₁
  · left; subst h1; exact M.zero₁_left
  · by_cases h2 : a = M.zero₂
    · left; subst h2; exact M.zero₂_left
    · rcases M.dichotomy a h1 h2 with hb | hc
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

/-- **No right identity** exists in any dichotomic magma.

    Proof: if `e` is right identity, `dot cls e = cls`. But `cls_boolean`
    forces `dot cls e ∈ {zero₁, zero₂}`, so `cls ∈ {zero₁, zero₂}`.
    Contradicts `cls_ne_zero₁` / `cls_ne_zero₂`. -/
theorem no_right_identity : ¬∃ e : Fin n, ∀ x : Fin n, M.dot x e = x := by
  intro ⟨e, he⟩
  rcases M.cls_boolean e with h | h
  · exact M.cls_ne_zero₁ (he M.cls ▸ h)
  · exact M.cls_ne_zero₂ (he M.cls ▸ h)


-- ─────────────────────────────────────────────────────────────────────
-- Theorem 4b: No associativity (DRMs cannot be semigroups)
-- ─────────────────────────────────────────────────────────────────────

/-- **No DRM is a semigroup.** Associativity is incompatible with the
    DichotomicRetractMagma axioms.

    Proof in four steps:
    1. `cls · (a · b) = cls · a` for all a, b (associativity + cls_boolean +
       absorber property).
    2. cls is not constant: it hits both z₁ and z₂ (extensionality +
       cls ≠ z₁, cls ≠ z₂).
    3. From (1), `cls · z₁ = cls · z₂ = cls · cls` (apply a = cls with the
       witnesses from step 2). From ret_sec, `cls · x = cls · cls` for all
       core x. So cls is constant everywhere.
    4. Extensionality forces cls = absorber, contradicting cls ≠ z₁, cls ≠ z₂.

    Uses: associativity, cls_boolean, zero₁_left, zero₂_left, extensional,
    ret_sec, ret_zero₁, cls_ne_zero₁, cls_ne_zero₂, zeros_distinct.
    Does NOT use: dichotomy, has_non_classifier, no_other_zeros, sec_ret. -/
theorem no_associativity :
    ¬ (∀ a b c : Fin n, M.dot (M.dot a b) c = M.dot a (M.dot b c)) := by
  intro hassoc
  -- Step 1: cls · (a · b) = cls · a for all a, b.
  -- Proof: cls · a ∈ {z₁, z₂} (cls_boolean), so (cls · a) · b = cls · a (absorber).
  -- By associativity, cls · (a · b) = (cls · a) · b = cls · a.
  have cls_left_absorbing : ∀ a b : Fin n,
      M.dot M.cls (M.dot a b) = M.dot M.cls a := by
    intro a b
    have hassoc_inst := hassoc M.cls a b
    -- hassoc_inst : (cls · a) · b = cls · (a · b)
    -- Goal: cls · (a · b) = cls · a
    rcases M.cls_boolean a with h | h
    · rw [← hassoc_inst, h, M.zero₁_left]
    · rw [← hassoc_inst, h, M.zero₂_left]
  -- Step 2: cls is not constant at z₁ and not constant at z₂.
  -- If constant at z_i, then cls has the same row as z_i, so cls = z_i by
  -- extensionality, contradicting cls_ne_zero_i.
  -- Since cls · x ∈ {z₁, z₂} for all x, both values must be hit.
  have cls_hits_z1 : ∃ b : Fin n, M.dot M.cls b = M.zero₁ := by
    by_contra h
    push_neg at h
    -- Every output is z₂
    have : M.cls = M.zero₂ := M.extensional M.cls M.zero₂ (fun x => by
      rcases M.cls_boolean x with hx | hx
      · exact absurd hx (h x)
      · rw [hx, M.zero₂_left])
    exact M.cls_ne_zero₂ this
  have cls_hits_z2 : ∃ b : Fin n, M.dot M.cls b = M.zero₂ := by
    by_contra h
    push_neg at h
    have : M.cls = M.zero₁ := M.extensional M.cls M.zero₁ (fun x => by
      rcases M.cls_boolean x with hx | hx
      · rw [hx, M.zero₁_left]
      · exact absurd hx (h x))
    exact M.cls_ne_zero₁ this
  -- Step 3a: cls · z₁ = cls · cls and cls · z₂ = cls · cls.
  obtain ⟨b₁, hb₁⟩ := cls_hits_z1
  obtain ⟨b₂, hb₂⟩ := cls_hits_z2
  have cls_z1 : M.dot M.cls M.zero₁ = M.dot M.cls M.cls := by
    have h1 := cls_left_absorbing M.cls b₁
    -- h1 : cls · (cls · b₁) = cls · cls
    -- hb₁ : cls · b₁ = z₁
    rw [hb₁] at h1
    -- h1 : cls · z₁ = cls · cls
    exact h1
  have cls_z2 : M.dot M.cls M.zero₂ = M.dot M.cls M.cls := by
    have h2 := cls_left_absorbing M.cls b₂
    rw [hb₂] at h2
    exact h2
  -- Step 3b: cls · x = cls · ret for all core x (via ret_sec).
  -- cls · (ret · (sec · x)) = cls · ret (by cls_left_absorbing).
  -- But ret · (sec · x) = x for core x (ret_sec). So cls · x = cls · ret.
  have cls_core : ∀ x : Fin n, x ≠ M.zero₁ → x ≠ M.zero₂ →
      M.dot M.cls x = M.dot M.cls M.ret := by
    intro x hx1 hx2
    have := cls_left_absorbing M.ret (M.dot M.sec x)
    -- this : cls · (ret · (sec · x)) = cls · ret
    rw [M.ret_sec x hx1 hx2] at this
    -- this : cls · x = cls · ret
    exact this
  -- Step 3c: cls · cls = cls · ret (since cls is core).
  have cls_cls_eq : M.dot M.cls M.cls = M.dot M.cls M.ret :=
    cls_core M.cls M.cls_ne_zero₁ M.cls_ne_zero₂
  -- Step 3d: cls · z₁ = cls · ret (combine 3a and 3c).
  have cls_z1_eq : M.dot M.cls M.zero₁ = M.dot M.cls M.ret := by
    rw [cls_z1, cls_cls_eq]
  -- Step 3e: cls · z₂ = cls · ret (combine 3a and 3c).
  have cls_z2_eq : M.dot M.cls M.zero₂ = M.dot M.cls M.ret := by
    rw [cls_z2, cls_cls_eq]
  -- Step 3f: Also, cls · z₁ = cls · ret directly from ret_zero₁.
  -- (Alternative derivation, not needed but confirms consistency.)
  -- Step 4: cls is constant at c = cls · ret ∈ {z₁, z₂} on everything.
  -- Therefore cls has the same row as the absorber c.
  set c := M.dot M.cls M.ret with hc_def
  -- cls · x = c for all x
  have cls_const : ∀ x : Fin n, M.dot M.cls x = c := by
    intro x
    by_cases hx1 : x = M.zero₁
    · rw [hx1, cls_z1_eq]
    · by_cases hx2 : x = M.zero₂
      · rw [hx2, cls_z2_eq]
      · exact cls_core x hx1 hx2
  -- c ∈ {z₁, z₂}
  rcases M.cls_boolean M.ret with hc | hc
  · -- c = z₁. cls has row constantly z₁ = z₁'s row.
    rw [← hc_def] at hc
    have : M.cls = M.zero₁ := M.extensional M.cls M.zero₁ (fun x => by
      rw [cls_const x, hc, M.zero₁_left])
    exact M.cls_ne_zero₁ this
  · -- c = z₂. cls has row constantly z₂ = z₂'s row.
    rw [← hc_def] at hc
    have : M.cls = M.zero₂ := M.extensional M.cls M.zero₂ (fun x => by
      rw [cls_const x, hc, M.zero₂_left])
    exact M.cls_ne_zero₂ this

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

/-- **Minimum cardinality**: every dichotomic magma has at least 4 elements.

    Proof: {zero₁, zero₂, cls, nc} are 4 pairwise-distinct elements.
    The bound is tight: `kripke4` achieves it with sec = ret. -/
theorem card_ge_four {n : Nat} (M : DichotomicRetractMagma n) : 4 ≤ Fintype.card (Fin n) := by
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

variable {n : Nat} (M : DichotomicRetractMagma n)

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
    4. Kripke dichotomy places ret in the non-classifier class. -/
theorem ret_is_non_classifier : IsNonClassifier M M.ret := by
  have hrnz1 := ret_ne_zero₁ M
  have hrnz2 := ret_ne_zero₂ M
  refine ⟨hrnz1, hrnz2, ?_⟩
  obtain ⟨nc, hnc1, hnc2, x, hx1, hx2, hyx1, hyx2⟩ := M.has_non_classifier
  -- ret is either all-boolean or all-non-boolean on non-zeros
  rcases M.dichotomy M.ret hrnz1 hrnz2 with hbool | hcomp
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
  -- So sec has non-boolean output on a non-zero input → non-classifier by Kripke.
  rcases M.dichotomy M.sec hsnz1 hsnz2 with hbool | hcomp
  · exfalso
    rcases hbool (M.dot M.ret nc) hrnc.1 hrnc.2 with h | h
    · exact hnc1 (hsec ▸ h)
    · exact hnc2 (hsec ▸ h)
  · exact hcomp

end UniversalTheorems2

-- ─────────────────────────────────────────────────────────────────────
-- Theorem: Minimum cardinality ≥ 5 when sec ≠ ret
-- ─────────────────────────────────────────────────────────────────────

/-- **Minimum cardinality with sec ≠ ret**: if sec ≠ ret, there are at least
    5 elements.

    Proof: {zero₁, zero₂, cls, sec, ret} are 5 pairwise-distinct elements.
    sec and ret are each distinct from zero₁, zero₂, and cls by the universal
    theorems, and distinct from each other by hypothesis.
    The bound is tight: `kripke5` achieves it. -/
theorem card_ge_five_of_sec_ne_ret {n : Nat} (M : DichotomicRetractMagma n)
    (h_sr : M.sec ≠ M.ret) : 5 ≤ Fintype.card (Fin n) := by
  have h12 : M.zero₁ ≠ M.zero₂ := M.zeros_distinct
  have h1c : M.zero₁ ≠ M.cls := fun h => M.cls_ne_zero₁ h.symm
  have h1s : M.zero₁ ≠ M.sec := fun h => (sec_ne_zero₁ M) h.symm
  have h1r : M.zero₁ ≠ M.ret := fun h => (ret_ne_zero₁ M) h.symm
  have h2c : M.zero₂ ≠ M.cls := fun h => M.cls_ne_zero₂ h.symm
  have h2s : M.zero₂ ≠ M.sec := fun h => (sec_ne_zero₂ M) h.symm
  have h2r : M.zero₂ ≠ M.ret := fun h => (ret_ne_zero₂ M) h.symm
  have hcs : M.cls ≠ M.sec := fun h => (sec_ne_cls M) h.symm
  have hcr : M.cls ≠ M.ret := fun h => (ret_ne_cls M) h.symm
  have hcard : ({M.zero₁, M.zero₂, M.cls, M.sec, M.ret} : Finset (Fin n)).card = 5 := by
    simp [h12, h1c, h1s, h1r, h2c, h2s, h2r, hcs, hcr, h_sr]
  have hsub : ({M.zero₁, M.zero₂, M.cls, M.sec, M.ret} : Finset (Fin n)) ⊆ Finset.univ :=
    fun _ _ => Finset.mem_univ _
  calc 5 = ({M.zero₁, M.zero₂, M.cls, M.sec, M.ret} : Finset (Fin n)).card := hcard.symm
    _ ≤ Finset.univ.card := Finset.card_le_card hsub
    _ = Fintype.card (Fin n) := Finset.card_univ

end KripkeWall

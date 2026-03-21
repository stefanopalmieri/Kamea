/- # NoCommutativity — Self-Description Requires Asymmetry

   ## Statement

   No commutative magma can have two distinct left-absorbers.

   In particular, no commutative magma satisfies the axioms of
   `FaithfulRetractMagma` or `DichotomicRetractMagma` from `CatKripkeWallMinimal.lean`.

   ## Proof

   If zero₁ and zero₂ are distinct left-absorbers:
   - `dot zero₁ zero₂ = zero₁`  (zero₁ absorbs)
   - `dot zero₂ zero₁ = zero₂`  (zero₂ absorbs)
   - Commutativity: `dot zero₁ zero₂ = dot zero₂ zero₁`
   - Therefore `zero₁ = zero₂`, contradiction.

   This is the simplest possible impossibility: no Kripke wall, no
   retraction pair, no extensionality. Just two distinct absorbers
   and commutativity.

   Self-description requires asymmetry at the most fundamental level.
-/

import Kamea.CatKripkeWallMinimal

set_option autoImplicit false

namespace KripkeWall

-- ══════════════════════════════════════════════════════════════════════
-- The No-Commutativity Theorem
-- ══════════════════════════════════════════════════════════════════════

section NoCommutativity

variable {n : Nat}

/-- **No commutativity with two absorbers**: if a magma has two distinct
    left-absorbers and is commutative, we get a contradiction.

    This is the weakest possible statement — it doesn't need extensionality,
    retraction pairs, or the Kripke dichotomy. Just the two absorbers. -/
theorem no_comm_two_absorbers
    (dot : Fin n → Fin n → Fin n)
    (zero₁ zero₂ : Fin n)
    (h_abs₁ : ∀ x, dot zero₁ x = zero₁)
    (h_abs₂ : ∀ x, dot zero₂ x = zero₂)
    (h_distinct : zero₁ ≠ zero₂)
    (h_comm : ∀ a b, dot a b = dot b a) :
    False := by
  have h1 : dot zero₁ zero₂ = zero₁ := h_abs₁ zero₂
  have h2 : dot zero₂ zero₁ = zero₂ := h_abs₂ zero₁
  have h3 : dot zero₁ zero₂ = dot zero₂ zero₁ := h_comm zero₁ zero₂
  exact h_distinct (h1 ▸ h3 ▸ h2)

/-- **No commutative FaithfulRetractMagma**: commutativity is incompatible
    with the `FaithfulRetractMagma` axioms. -/
theorem FaithfulRetractMagma.no_commutativity (M : FaithfulRetractMagma n)
    (h_comm : ∀ a b : Fin n, M.dot a b = M.dot b a) :
    False :=
  no_comm_two_absorbers M.dot M.zero₁ M.zero₂
    M.zero₁_left M.zero₂_left M.zeros_distinct h_comm

/-- **No commutative DichotomicRetractMagma**: commutativity is incompatible
    with the `DichotomicRetractMagma` axioms. Immediate from the weaker result. -/
theorem DichotomicRetractMagma.no_commutativity (M : DichotomicRetractMagma n)
    (h_comm : ∀ a b : Fin n, M.dot a b = M.dot b a) :
    False :=
  M.toFaithfulRetractMagma.no_commutativity h_comm

end NoCommutativity

end KripkeWall

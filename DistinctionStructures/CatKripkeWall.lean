/- # CatKripkeWall — The Kripke Wall as a Categorical Theorem

   The Kripke wall (called the "Kripke barrier" or "separation of judgment
   and computation" in the Ψ framework) states that the boolean and
   non-boolean strata of the endomorphism magma are cleanly separated.

   In categorical terms: an endomorphism either always maps non-zero inputs
   to boolean values {zero₁, zero₂} (a "classifier-type" morphism) or
   never does (a "computational" morphism). The subobject classifier cls
   belongs to the first stratum; the section, retraction, projections,
   copairing, and fixed-point combinator belong to the second.

   This separation is the `dichotomy` axiom in `CatEndoMagma`. Here we
   derive its main consequence: the classifier is distinct from any
   element that has a non-boolean output on a non-zero input.
-/

import DistinctionStructures.CategoricalFoundation

set_option autoImplicit false

namespace CatKripkeWall

open CatFoundation

/-- **The Kripke Wall**: if an element has any non-boolean output on
    a non-zero input, then it is not the classifier.

    In the Ψ framework this is called the **Kripke barrier** or the
    **separation of judgment and computation**. It separates classifier-type
    morphisms (which only output boolean values on non-zero inputs)
    from computational morphisms (which never output boolean values
    on non-zero inputs).

    Proof: cls has all-boolean row (by cls_boolean). If y has a non-boolean
    output, then y ≠ cls (since cls's row is all-boolean). -/
theorem kripke_wall {n : Nat} (M : CatEndoMagma n) (y : Fin n)
    (x : Fin n) (hx : M.dot y x ≠ M.zero₁ ∧ M.dot y x ≠ M.zero₂) :
    y ≠ M.cls := by
  intro heq
  rcases M.cls_boolean x with h | h
  · exact hx.1 (heq ▸ h)
  · exact hx.2 (heq ▸ h)

/-- Contrapositive: if y = cls, then all outputs are boolean. -/
theorem cls_all_boolean {n : Nat} (M : CatEndoMagma n) (x : Fin n) :
    M.dot M.cls x = M.zero₁ ∨ M.dot M.cls x = M.zero₂ :=
  M.cls_boolean x

/-- **Kripke dichotomy consequence**: a non-zero element with any
    non-boolean output on a non-zero input has ALL non-boolean
    outputs on non-zero inputs. -/
theorem computational_all_nonboolean {n : Nat} (M : CatEndoMagma n)
    (a : Fin n) (ha1 : a ≠ M.zero₁) (ha2 : a ≠ M.zero₂)
    (x₀ : Fin n) (hx₀1 : x₀ ≠ M.zero₁) (hx₀2 : x₀ ≠ M.zero₂)
    (hnonbool : M.dot a x₀ ≠ M.zero₁ ∧ M.dot a x₀ ≠ M.zero₂) :
    ∀ x : Fin n, x ≠ M.zero₁ → x ≠ M.zero₂ →
      M.dot a x ≠ M.zero₁ ∧ M.dot a x ≠ M.zero₂ := by
  rcases M.dichotomy a ha1 ha2 with hbool | hcomp
  · -- a is boolean-type: contradicts hnonbool
    exfalso
    rcases hbool x₀ hx₀1 hx₀2 with h | h
    · exact hnonbool.1 h
    · exact hnonbool.2 h
  · -- a is computational-type: all outputs on non-zeros are non-boolean
    exact hcomp

end CatKripkeWall

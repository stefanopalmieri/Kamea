import Kamea.CatKripkeWallMinimal

/-!
# Functoriality of the Three-Category Decomposition

The decomposition of a DichotomicRetractMagma into zeros (Z), classifiers (C),
and non-classifiers (N) is preserved by bijective homomorphisms that respect
the zero elements. This makes the decomposition an algebraic invariant —
it depends only on the magma structure, not on any particular presentation.

Formally: if φ : M₁ → M₂ is a DRM isomorphism (bijective, operation-preserving,
zero-preserving), then φ maps Z to Z, C to C, and N to N.

This is the formal content of the claim that the three-category decomposition
is a "functorial invariant shared by all models" (README).
-/

set_option autoImplicit false

namespace KripkeWall

/-- A DRM isomorphism: a bijective function preserving the operation and zeros. -/
structure DRMIso {n : Nat} (M₁ M₂ : DichotomicRetractMagma n) where
  toFun : Fin n → Fin n
  bij : Function.Bijective toFun
  hom : ∀ a b : Fin n, toFun (M₁.dot a b) = M₂.dot (toFun a) (toFun b)
  map_zero₁ : toFun M₁.zero₁ = M₂.zero₁
  map_zero₂ : toFun M₁.zero₂ = M₂.zero₂

variable {n : Nat} {M₁ M₂ : DichotomicRetractMagma n} (φ : DRMIso M₁ M₂)

/-- DRM isomorphisms preserve the zero class. -/
theorem DRMIso.preserves_zero (a : Fin n) (ha : IsZero M₁ a) :
    IsZero M₂ (φ.toFun a) := by
  intro y
  obtain ⟨x, rfl⟩ := φ.bij.2 y
  rw [← φ.hom, ha x]

/-- DRM isomorphisms preserve the classifier class. -/
theorem DRMIso.preserves_classifier (a : Fin n) (ha : IsClassifier M₁ a) :
    IsClassifier M₂ (φ.toFun a) := by
  obtain ⟨hne₁, hne₂, hbool⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact hne₁ (φ.bij.1 (by rw [h, φ.map_zero₁]))
  · intro h; exact hne₂ (φ.bij.1 (by rw [h, φ.map_zero₂]))
  · intro y hy₁ hy₂
    obtain ⟨x, rfl⟩ := φ.bij.2 y
    have hx₁ : x ≠ M₁.zero₁ := fun h => hy₁ (by rw [h, φ.map_zero₁])
    have hx₂ : x ≠ M₁.zero₂ := fun h => hy₂ (by rw [h, φ.map_zero₂])
    rw [← φ.hom]
    cases hbool x hx₁ hx₂ with
    | inl h => left; rw [h, φ.map_zero₁]
    | inr h => right; rw [h, φ.map_zero₂]

/-- DRM isomorphisms preserve the non-classifier class. -/
theorem DRMIso.preserves_non_classifier (a : Fin n) (ha : IsNonClassifier M₁ a) :
    IsNonClassifier M₂ (φ.toFun a) := by
  obtain ⟨hne₁, hne₂, hnonbool⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact hne₁ (φ.bij.1 (by rw [h, φ.map_zero₁]))
  · intro h; exact hne₂ (φ.bij.1 (by rw [h, φ.map_zero₂]))
  · intro y hy₁ hy₂
    obtain ⟨x, rfl⟩ := φ.bij.2 y
    have hx₁ : x ≠ M₁.zero₁ := fun h => hy₁ (by rw [h, φ.map_zero₁])
    have hx₂ : x ≠ M₁.zero₂ := fun h => hy₂ (by rw [h, φ.map_zero₂])
    obtain ⟨hv₁, hv₂⟩ := hnonbool x hx₁ hx₂
    rw [← φ.hom]
    exact ⟨fun h => hv₁ (φ.bij.1 (by rw [h, φ.map_zero₁])),
           fun h => hv₂ (φ.bij.1 (by rw [h, φ.map_zero₂]))⟩

/-- **Functoriality theorem**: the three-category decomposition is a DRM invariant.
    Any DRM isomorphism preserves all three classes simultaneously. -/
theorem DRMIso.preserves_decomposition (a : Fin n) :
    (IsZero M₁ a → IsZero M₂ (φ.toFun a)) ∧
    (IsClassifier M₁ a → IsClassifier M₂ (φ.toFun a)) ∧
    (IsNonClassifier M₁ a → IsNonClassifier M₂ (φ.toFun a)) :=
  ⟨φ.preserves_zero a, φ.preserves_classifier a, φ.preserves_non_classifier a⟩

end KripkeWall

/- # CatRigidity — Automorphism Rigidity of the Categorical Witness

   Every injective endomorphism of the canonical 16-element witness
   (`psi16_cat`) is the identity. Equivalently, `Aut(psi16_cat) = {id}`.

   This is the same result as `Psi16Rigidity.automorphism_trivial`,
   transferred to the categorical structure via table equivalence.
   The algebra has no non-trivial symmetries — its internal structure
   is maximally asymmetric.

   **Mathematical significance:** Rigidity means the algebra's elements
   are structurally distinguishable. Combined with discoverability
   (CatDiscoverable), this shows the algebra is fully self-describing:
   it can identify all its own elements through behavioral probes.

   **Relation to standard results:**
   - cf. `CategoryTheory.Aut` for the automorphism group
   - Rigidity is typical of finite structures with rich internal
     structure (cf. rigid graphs, Fraïssé limits)
-/

import DistinctionStructures.CatWitness
import DistinctionStructures.Psi16Full
import DistinctionStructures.Psi16Rigidity
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 1600000
set_option autoImplicit false

namespace CatRigidity

open CatFoundation CatWitness

/-- The categorical witness's operation is identical to the Ψ₁₆ᶠ operation.
    This allows us to transfer all results between the two formulations. -/
theorem dot16_eq_psi : ∀ a b : Fin 16, dot16 a b = Psi16Full.psi a b := by
  native_decide

/-- An endomorphism of the categorical witness: a function that commutes
    with the binary operation. -/
def is_endomorphism (σ : Fin 16 → Fin 16) : Prop :=
  ∀ a b : Fin 16, σ (dot16 a b) = dot16 (σ a) (σ b)

/-- Endomorphisms of the categorical witness are exactly endomorphisms
    of the Ψ₁₆ᶠ operation. -/
theorem endo_iff_psi_endo (σ : Fin 16 → Fin 16) :
    is_endomorphism σ ↔ Psi16Rigidity.is_endomorphism σ := by
  unfold is_endomorphism Psi16Rigidity.is_endomorphism
  simp only [dot16_eq_psi]

/-- **Automorphism rigidity**: every injective endomorphism of the
    canonical 16-element witness is the identity.

    Equivalently, `Aut(Ψ₁₆ᶠ) = {id}`. The algebra has no non-trivial
    symmetries. This is an emergent property — it follows from the
    Cayley table structure, not from any single axiom.

    **Proof:** Transferred from `Psi16Rigidity.automorphism_trivial`
    via table equivalence (`dot16_eq_psi`). -/
theorem psi16_cat_rigid : ∀ σ : Fin 16 → Fin 16,
    is_endomorphism σ → Function.Injective σ → σ = id := by
  intro σ hendo hinj
  exact Psi16Rigidity.automorphism_trivial σ ((endo_iff_psi_endo σ).mp hendo) hinj

end CatRigidity

/- # CatDiscoverable — Discoverability of the Categorical Witness

   All 16 elements of the canonical witness are uniquely identifiable
   from 4 behavioral probes. Specifically, the function

     `a ↦ (dot a zero₁, dot a zero₂, dot a cls, dot a sec)`

   is injective on `Fin 16`.

   This is the same result as `Psi16Discoverable.four_probe_suffice`,
   restated using categorical vocabulary.

   **Mathematical significance:** Discoverability means the algebra can
   identify all its elements through a small number of "experiments" —
   applying each element to 4 chosen inputs and observing the outputs.
   Combined with rigidity (CatRigidity), this shows the algebra is
   fully self-describing.

   **Probe choice in categorical terms:**
   - zero₁ (first zero morphism): separates absorbers from non-absorbers
   - zero₂ (second zero morphism): orients the two absorbers
   - cls (subobject classifier): separates judgment from computation
   - sec (section of retraction pair): fine-grained encoder discrimination

   Proof is by `native_decide` over the finite domain.
-/

import Kamea.CatWitness

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace CatDiscoverable

open CatFoundation CatWitness

/-- **Four-probe discoverability**: the map
    `a ↦ (dot a zero₁, dot a zero₂, dot a cls, dot a sec)`
    is injective on `Fin 16`.

    Four probes suffice to distinguish all 16 elements of the
    canonical witness. This is the minimum: no 3-probe set achieves
    injectivity (verified computationally in the Ψ framework). -/
theorem psi16_cat_discoverable : ∀ a b : Fin 16,
    dot16 a psi16_cat.zero₁ = dot16 b psi16_cat.zero₁ →
    dot16 a psi16_cat.zero₂ = dot16 b psi16_cat.zero₂ →
    dot16 a psi16_cat.cls = dot16 b psi16_cat.cls →
    dot16 a psi16_cat.sec = dot16 b psi16_cat.sec →
    a = b := by native_decide

/-- Alternative formulation using `Function.Injective`. -/
theorem psi16_cat_discoverable' :
    Function.Injective (fun a : Fin 16 =>
      (dot16 a psi16_cat.zero₁,
       dot16 a psi16_cat.zero₂,
       dot16 a psi16_cat.cls,
       dot16 a psi16_cat.sec)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact psi16_cat_discoverable a b h.1 h.2.1 h.2.2.1 h.2.2.2

end CatDiscoverable

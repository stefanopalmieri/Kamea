/- # Δ₁ Instantiates the Strengthened DirectedDS Axiom Bundle

This file connects:
- concrete fingerprint derivation (`Delta1RoleDerivation.lean`)
- strengthened base axiom bundle (`StrengthenedBaseAxioms.lean`)

and obtains the 17-element lower bound as a theorem from the strengthened
axiom set.
-/

import Kamea.StrengthenedBaseAxioms
import Kamea.Delta1RoleDerivation

namespace Delta1Strengthened

open DirectedDS
open Delta1RoleDerivation

theorem delta1_roleComplete17 : delta1_dirDS.RoleComplete17 := by
  refine ⟨RoleFingerprint, ?_, ?_⟩
  · intro r
    exact roleFingerprint_existsUnique r
  · intro r₁ r₂ x h₁ h₂
    exact roleFingerprint_disjoint h₁ h₂

def delta1_strong : DirectedDS.Strong (D := D1ι) where
  ds := delta1_dirDS
  a2 := delta1_dirDS_A2
  a5 := delta1_dirDS_A5
  ext := delta1_dirDS_Ext
  roleComplete17 := delta1_roleComplete17

theorem delta1_card_ge_17_from_strengthened_axioms :
    17 ≤ Fintype.card D1ι :=
  delta1_strong.card_ge_17

theorem delta1_no_model_below_17_from_strengthened_axioms :
    ¬ Fintype.card D1ι < 17 :=
  delta1_strong.no_model_below_17

end Delta1Strengthened


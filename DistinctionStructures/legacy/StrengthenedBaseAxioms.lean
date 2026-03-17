/- # Strengthening DirectedDS Base Axioms to Force 17-Role Minimality

`Basic.lean` base axioms (`A2`, `A5`, `Ext`) are too weak to force `card ≥ 17`
(see `BaseAxiomDerivation.lean`).

This file defines a strengthened axiom bundle:

- `RoleComplete17`: a role-completeness/disjointness condition over 17 roles.

From this strengthened assumption we prove:

1. `card ≥ 17`
2. no model with `card < 17`

This gives a clean target for "full derivation from axioms":
base DirectedDS + role-completeness assumptions.
-/

import DistinctionStructures.Basic
import DistinctionStructures.Delta1RoleSchema
import Mathlib.Data.Fintype.Card

namespace DirectedDS

variable {D : Type} [DecidableEq D] [Fintype D]

/-- Strengthened role-completeness axiom:
    all 17 roles have unique witnesses, and role predicates are pointwise disjoint. -/
def RoleComplete17 (_ds : DirectedDS D) : Prop :=
  ∃ HasRole : D1Role → D → Prop,
    (∀ r : D1Role, ∃! x : D, HasRole r x) ∧
    (∀ {r₁ r₂ : D1Role} {x : D}, HasRole r₁ x → HasRole r₂ x → r₁ = r₂)

/-- From role-completeness alone, the carrier must have at least 17 elements. -/
theorem card_ge_17_of_roleComplete17 (ds : DirectedDS D) (hR : ds.RoleComplete17) :
    17 ≤ Fintype.card D := by
  classical
  rcases hR with ⟨HasRole, hUnique, hDisjoint⟩
  let witness : D1Role → D := fun r => Classical.choose (hUnique r)
  have hWitness : ∀ r : D1Role, HasRole r (witness r) := by
    intro r
    exact (Classical.choose_spec (hUnique r)).1
  have hInj : Function.Injective witness := by
    intro r₁ r₂ hEq
    have h1 : HasRole r₁ (witness r₁) := hWitness r₁
    have h2 : HasRole r₂ (witness r₁) := by
      simpa [hEq] using hWitness r₂
    exact hDisjoint h1 h2
  have hCard : Fintype.card D1Role ≤ Fintype.card D :=
    Fintype.card_le_of_injective witness hInj
  simpa [card_d1Role] using hCard

theorem no_model_below_17_of_roleComplete17 (ds : DirectedDS D) (hR : ds.RoleComplete17) :
    ¬ Fintype.card D < 17 := by
  exact Nat.not_lt_of_ge (card_ge_17_of_roleComplete17 ds hR)

/-- Convenience record: base DirectedDS properties plus strengthened role-completeness. -/
structure Strong (D : Type) [DecidableEq D] [Fintype D] where
  ds : DirectedDS D
  a2 : ds.A2
  a5 : ds.A5
  ext : ds.Ext
  roleComplete17 : ds.RoleComplete17

theorem Strong.card_ge_17 (S : Strong D) : 17 ≤ Fintype.card D :=
  card_ge_17_of_roleComplete17 S.ds S.roleComplete17

theorem Strong.no_model_below_17 (S : Strong D) : ¬ Fintype.card D < 17 :=
  no_model_below_17_of_roleComplete17 S.ds S.roleComplete17

end DirectedDS

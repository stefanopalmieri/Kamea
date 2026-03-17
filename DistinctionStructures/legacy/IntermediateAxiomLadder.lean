/- # Intermediate Axiom Ladder for 17-Element Forcing

This file isolates the weakest cardinality-forcing condition we currently have:

- `Embedding17 ds := Nonempty (Fin 17 ↪ D)`.

For finite carriers, this is equivalent to `17 ≤ card D`.
It also turns out to be equivalent to the current `RoleComplete17` strengthening
from `StrengthenedBaseAxioms.lean` (because that strengthening is purely
set-theoretic and does not constrain `dot`/`actual` behavior of roles).

Finally, using `BasePlusA7Derivation.lean`, we show base axioms plus generic
directed novelty do not imply `Embedding17`.
-/

import DistinctionStructures.StrengthenedBaseAxioms
import DistinctionStructures.BasePlusA7Derivation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Embedding

namespace IntermediateAxiomLadder

open DirectedDS

variable {D : Type} [DecidableEq D] [Fintype D]

/-- Weak intermediate forcing condition: an injective map `Fin 17 ↪ D`. -/
def Embedding17 (_ds : DirectedDS D) : Prop :=
  Nonempty (Fin 17 ↪ D)

/-- `card ≥ 17` yields an `Embedding17` witness. -/
noncomputable def embedding17_of_card_ge_17 (h : 17 ≤ Fintype.card D) :
    Fin 17 ↪ D :=
  (Fin.castLEEmb h).trans ((Fintype.equivFin D).symm.toEmbedding)

theorem card_ge_17_of_embedding17 (ds : DirectedDS D) (hE : Embedding17 ds) :
    17 ≤ Fintype.card D := by
  rcases hE with ⟨e⟩
  exact Fintype.card_le_of_injective e e.injective

theorem embedding17_iff_card_ge_17 (ds : DirectedDS D) :
    Embedding17 ds ↔ 17 ≤ Fintype.card D := by
  constructor
  · intro hE
    exact card_ge_17_of_embedding17 ds hE
  · intro hCard
    exact ⟨embedding17_of_card_ge_17 hCard⟩

/-- Index roles by `Fin 17` using `Fintype.equivFin` plus cardinal cast. -/
noncomputable def roleIndex : D1Role → Fin 17 :=
  (Fin.cast card_d1Role) ∘ (Fintype.equivFin D1Role)

theorem roleIndex_injective : Function.Injective roleIndex := by
  have hCastInj : Function.Injective (Fin.cast card_d1Role : Fin (Fintype.card D1Role) → Fin 17) :=
    Fin.cast_injective card_d1Role
  exact hCastInj.comp (Fintype.equivFin D1Role).injective

theorem roleComplete17_implies_embedding17 (ds : DirectedDS D) :
    ds.RoleComplete17 → Embedding17 ds := by
  intro hR
  exact (embedding17_iff_card_ge_17 ds).2 (DirectedDS.card_ge_17_of_roleComplete17 ds hR)

theorem embedding17_implies_roleComplete17 (ds : DirectedDS D) :
    Embedding17 ds → ds.RoleComplete17 := by
  intro hE
  rcases hE with ⟨e⟩
  refine ⟨fun r x => x = e (roleIndex r), ?_, ?_⟩
  · intro r
    refine ⟨e (roleIndex r), by rfl, ?_⟩
    intro x hx
    simpa using hx
  · intro r₁ r₂ x hr₁ hr₂
    have hEq : e (roleIndex r₁) = e (roleIndex r₂) := by
      calc
        e (roleIndex r₁) = x := hr₁.symm
        _ = e (roleIndex r₂) := hr₂
    exact roleIndex_injective (e.injective hEq)

theorem roleComplete17_iff_embedding17 (ds : DirectedDS D) :
    ds.RoleComplete17 ↔ Embedding17 ds := by
  constructor
  · exact roleComplete17_implies_embedding17 ds
  · exact embedding17_implies_roleComplete17 ds

theorem not_forced_embedding17_from_base_plus_A7Prime :
    ¬ (∀ {X : Type} [DecidableEq X] [Fintype X] (ds : DirectedDS X),
        ds.A2 → ds.A5 → ds.Ext → BasePlusA7Derivation.DirectedA7Prime ds → Embedding17 ds) := by
  intro h
  have hE : Embedding17 BasePlusA7Derivation.threeDS :=
    h BasePlusA7Derivation.threeDS
      BasePlusA7Derivation.threeDS_A2
      BasePlusA7Derivation.threeDS_A5
      BasePlusA7Derivation.threeDS_Ext
      BasePlusA7Derivation.threeDS_DirectedA7Prime
  have hCard : 17 ≤ Fintype.card BasePlusA7Derivation.Three :=
    card_ge_17_of_embedding17 BasePlusA7Derivation.threeDS hE
  simp [BasePlusA7Derivation.card_three] at hCard

end IntermediateAxiomLadder

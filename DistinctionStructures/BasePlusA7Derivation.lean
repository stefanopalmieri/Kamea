/- # Base DirectedDS Axioms + Generic Directed A7′ Still Do Not Force 17

This file strengthens the negative result from `BaseAxiomDerivation.lean` by
adding a generic directed structural-novelty axiom `DirectedA7Prime`.

We construct a concrete 3-element model satisfying:
- `A2`
- `A5`
- `Ext`
- `DirectedA7Prime`

Hence even this natural strengthening does not force `card ≥ 17`.
-/

import DistinctionStructures.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace BasePlusA7Derivation

open DirectedDS

variable {D : Type} [DecidableEq D] [Fintype D]

/-- A generic directed analog of A7′:
    there is a nontrivial actual set `S`, and some `δ` outside `S` that has a
    novel behavior against a witness input `t` compared to every element of `S`. -/
def DirectedA7Prime (ds : DirectedDS D) : Prop :=
  ∃ (S : Finset D),
    2 ≤ S.card ∧
    (∀ d ∈ S, ds.actual d) ∧
    ∃ δ t : D, δ ∉ S ∧ ∀ d ∈ S, ds.dot δ t ≠ ds.dot d t

/-- 3-element carrier. -/
inductive Three where
  | z0 | z1 | z2
  deriving DecidableEq, Repr

instance : Fintype Three where
  elems := {.z0, .z1, .z2}
  complete := by
    intro x
    cases x <;> simp

def actualThree : Three → Prop
  | .z0 => True
  | .z1 => True
  | .z2 => False

instance : DecidablePred actualThree
  | .z0 => isTrue trivial
  | .z1 => isTrue trivial
  | .z2 => isFalse (by intro h; exact h)

/-- Operation table:
    z0 row: z0 z0 z0
    z1 row: z0 z0 z1
    z2 row: z0 z0 z2 -/
def dotThree : Three → Three → Three
  | .z0, _ => .z0
  | .z1, .z2 => .z1
  | .z1, _ => .z0
  | .z2, .z2 => .z2
  | .z2, _ => .z0

def threeDS : DirectedDS Three where
  actual := actualThree
  dot := dotThree

theorem threeDS_A2 : threeDS.A2 := by
  exact ⟨.z0, by simp [threeDS, actualThree]⟩

theorem threeDS_A5 : threeDS.A5 := by
  exact ⟨.z2, by simp [threeDS, actualThree]⟩

theorem threeDS_Ext : threeDS.Ext := by
  intro x y hxy
  refine ⟨.z2, ?_⟩
  cases x <;> cases y <;> simp [threeDS, dotThree] at hxy ⊢

theorem threeDS_DirectedA7Prime : DirectedA7Prime threeDS := by
  refine ⟨{Three.z0, Three.z1}, by native_decide, ?_, ?_⟩
  · intro d hd
    rcases (by simpa using hd) with rfl | rfl
    · simp [threeDS, actualThree]
    · simp [threeDS, actualThree]
  · refine ⟨Three.z2, Three.z2, by simp, ?_⟩
    intro d hd
    simp at hd
    rcases hd with rfl | rfl
    · decide
    · decide

theorem card_three : Fintype.card Three = 3 := by
  native_decide

theorem countermodel_base_plus_A7Prime :
    threeDS.A2 ∧ threeDS.A5 ∧ threeDS.Ext ∧ DirectedA7Prime threeDS ∧
      Fintype.card Three = 3 := by
  exact ⟨threeDS_A2, threeDS_A5, threeDS_Ext, threeDS_DirectedA7Prime, card_three⟩

theorem not_forced_card_ge_17_from_base_plus_A7Prime :
    ¬ (∀ {X : Type} [DecidableEq X] [Fintype X] (ds : DirectedDS X),
        ds.A2 → ds.A5 → ds.Ext → DirectedA7Prime ds → 17 ≤ Fintype.card X) := by
  intro h
  have h17 : 17 ≤ Fintype.card Three :=
    h threeDS threeDS_A2 threeDS_A5 threeDS_Ext threeDS_DirectedA7Prime
  simp [card_three] at h17

end BasePlusA7Derivation

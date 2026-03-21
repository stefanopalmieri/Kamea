/- # What Follows from Base DirectedDS Axioms Alone

This file formalizes the strongest cardinality consequence of the current base
`DirectedDS` axioms (`A2`, `A5`, `Ext`) in `Basic.lean`.

Result:
- From `A2` and `A5`, one can derive only `card ≥ 2`.
- This bound is tight: a concrete 2-element model satisfies `A2`, `A5`, and `Ext`.

Therefore, a lower bound like `card ≥ 17` is not derivable from these base
axioms alone; additional structural assumptions are necessary.
-/

import Kamea.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace BaseAxiomDerivation

open DirectedDS

theorem card_ge_two_of_A2_A5
    {D : Type} [DecidableEq D] [Fintype D]
    (ds : DirectedDS D) (hA2 : ds.A2) (hA5 : ds.A5) :
    2 ≤ Fintype.card D := by
  rcases hA2 with ⟨a, ha⟩
  rcases hA5 with ⟨b, hb⟩
  have hne : a ≠ b := by
    intro hab
    apply hb
    simpa [hab] using ha
  have hcardAB : ({a, b} : Finset D).card = 2 := by
    simp [hne]
  have hsub : ({a, b} : Finset D) ⊆ (Finset.univ : Finset D) := by
    intro x hx
    simp
  have hle : ({a, b} : Finset D).card ≤ (Finset.univ : Finset D).card :=
    Finset.card_le_card hsub
  simpa [hcardAB] using hle

/-- A concrete 2-element carrier witnessing tightness of the lower bound. -/
inductive Two where
  | t
  | f
  deriving DecidableEq, Repr

instance : Fintype Two where
  elems := {.t, .f}
  complete := by
    intro x
    cases x <;> simp

def actualTwo : Two → Prop
  | .t => True
  | .f => False

instance : DecidablePred actualTwo
  | .t => isTrue trivial
  | .f => isFalse (by intro h; exact h)

def dotTwo : Two → Two → Two
  | x, _ => x

def twoDS : DirectedDS Two where
  actual := actualTwo
  dot := dotTwo

theorem twoDS_A2 : twoDS.A2 := by
  exact ⟨.t, by simp [twoDS, actualTwo]⟩

theorem twoDS_A5 : twoDS.A5 := by
  exact ⟨.f, by simp [twoDS, actualTwo]⟩

theorem twoDS_Ext : twoDS.Ext := by
  intro x y hxy
  refine ⟨.t, ?_⟩
  simpa [twoDS, dotTwo] using hxy

theorem card_two : Fintype.card Two = 2 := by
  native_decide

theorem base_axioms_lower_bound_is_tight :
    twoDS.A2 ∧ twoDS.A5 ∧ twoDS.Ext ∧ Fintype.card Two = 2 := by
  exact ⟨twoDS_A2, twoDS_A5, twoDS_Ext, card_two⟩

theorem not_forced_card_ge_17_from_base_axioms :
    ¬ (∀ {D : Type} [DecidableEq D] [Fintype D] (ds : DirectedDS D),
        ds.A2 → ds.A5 → ds.Ext → 17 ≤ Fintype.card D) := by
  intro h
  have h17 : 17 ≤ Fintype.card Two := h twoDS twoDS_A2 twoDS_A5 twoDS_Ext
  have hFalse : ¬ 17 ≤ Fintype.card Two := by
    simp [card_two]
  exact hFalse h17

end BaseAxiomDerivation

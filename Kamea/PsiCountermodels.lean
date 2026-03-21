/- # Tight Countermodel for PsiStructure Card Bound

A concrete 4-element PsiStructure showing that `card ≥ 4` is sharp.

Carrier: `Four` = {a, b, c, d}
- a = top (absorber), b = bot (absorber), c = tau (tester), d = f_enc (encoder)
- Cayley table: a-row all a, b-row all b, c-row all in {a,b}, d-row has non-boolean output
-/

import Kamea.PsiStructure
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace PsiCountermodels

open PsiRoleAxioms

/-- 4-element carrier. -/
inductive Four where
  | a | b | c | d
  deriving DecidableEq, Repr

instance : Fintype Four where
  elems := {.a, .b, .c, .d}
  complete := by
    intro x
    cases x <;> simp

/-- Operation table:
    a-row: a a a a  (top absorbs)
    b-row: b b b b  (bot absorbs)
    c-row: a b a b  (tester: boolean outputs)
    d-row: a b c d  (encoder: c and d are non-boolean) -/
def dotFour : Four → Four → Four
  | .a, _ => .a
  | .b, _ => .b
  | .c, .a => .a
  | .c, .b => .b
  | .c, .c => .a
  | .c, .d => .b
  | .d, .a => .a
  | .d, .b => .b
  | .d, .c => .c
  | .d, .d => .d

/-- A concrete PsiStructure on Four, verified by `decide`. -/
def fourPS : PsiStructure Four where
  dot := dotFour
  top := .a
  bot := .b
  tau := .c
  f_enc := .d
  top_absorbs := by decide
  bot_absorbs := by decide
  top_ne_bot := by decide
  tau_boolean := by decide
  tau_ne_top := by decide
  tau_ne_bot := by decide
  f_non_boolean := ⟨.c, by decide⟩
  f_ne_top := by decide
  f_ne_bot := by decide
  f_ne_tau := by decide

theorem card_four : Fintype.card Four = 4 := by
  native_decide

/-- The card ≥ 4 bound from PsiStructure axioms is tight:
    there exists a 4-element PsiStructure with exactly 4 elements. -/
theorem tight_card_four :
    (∃ _ : PsiStructure Four, True) ∧ Fintype.card Four = 4 :=
  ⟨⟨fourPS, trivial⟩, card_four⟩

/-- L0–L3 cannot force card ≥ 5: a 4-element countermodel exists. -/
theorem not_forced_card_ge_five_from_L0_L3 :
    ¬ (∀ {D : Type} [DecidableEq D] [Fintype D],
        PsiStructure D → 5 ≤ Fintype.card D) := by
  intro h
  have h5 : 5 ≤ Fintype.card Four := h fourPS
  simp [card_four] at h5

end PsiCountermodels

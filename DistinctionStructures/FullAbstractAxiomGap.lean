/- # Full-Abstract Bridge Attempt: Current Gap Witness

This file formalizes an attempted "full abstract" forcing bundle for directed DS:

- base axioms (`A2`, `A5`, `Ext`),
- generic directed novelty (`DirectedA7Prime`),
- existence of an intrinsic-reflexivity witness (`DirectedIR`) for some secondary context.

We then show this still does *not* force `Embedding17` (hence does not force
`card ≥ 17`) by giving a concrete 6-element countermodel.
-/

import DistinctionStructures.IntermediateAxiomLadder
import DistinctionStructures.BasePlusA7Derivation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace FullAbstractAxiomGap

open DirectedDS
open IntermediateAxiomLadder
open BasePlusA7Derivation

variable {D : Type} [DecidableEq D] [Fintype D]

/-- Attempted full-abstract forcing bundle. -/
def FullAbstractAxioms (ds : DirectedDS D) : Prop :=
  ds.A2 ∧ ds.A5 ∧ ds.Ext ∧ DirectedA7Prime ds ∧
    ∃ (K : Type) (actualK : K → Prop),
      Nonempty (DirectedIR D K ds.actual actualK ds.dot)

/-- 6-element carrier for the gap witness. -/
inductive Six where
  | eI | eD | eM | eSigma | eDelta | n
  deriving DecidableEq, Repr

instance : Fintype Six where
  elems := {.eI, .eD, .eM, .eSigma, .eDelta, .n}
  complete := by
    intro x
    cases x <;> simp

def actualSix : Six → Prop
  | .n => False
  | _ => True

instance : DecidablePred actualSix
  | .eI => isTrue trivial
  | .eD => isTrue trivial
  | .eM => isTrue trivial
  | .eSigma => isTrue trivial
  | .eDelta => isTrue trivial
  | .n => isFalse (by intro h; exact h)

/-- Almost-left-projection, with one H3-enforcing exceptional entry. -/
def dotSix : Six → Six → Six
  | .eSigma, .eI => .eDelta
  | x, _ => x

def sixDS : DirectedDS Six where
  actual := actualSix
  dot := dotSix

theorem sixDS_A2 : sixDS.A2 := by
  exact ⟨.eI, by simp [sixDS, actualSix]⟩

theorem sixDS_A5 : sixDS.A5 := by
  exact ⟨.n, by simp [sixDS, actualSix]⟩

theorem sixDS_Ext : sixDS.Ext := by
  intro x y hxy
  refine ⟨.eD, ?_⟩
  simpa [sixDS, dotSix] using hxy

theorem sixDS_DirectedA7Prime : DirectedA7Prime sixDS := by
  refine ⟨{Six.eI, Six.eD}, by native_decide, ?_, ?_⟩
  · intro d hd
    rcases (by simpa using hd) with rfl | rfl <;> simp [sixDS, actualSix]
  · refine ⟨Six.n, Six.eD, by simp, ?_⟩
    intro d hd
    rcases (by simpa using hd) with rfl | rfl <;> decide

/-- An intrinsic-reflexivity witness exists in this 6-element model,
    but several codes collapse (`d_I = d_K`, `m_I = m_K`, etc.). -/
def sixIR : DirectedIR Six Unit actualSix (fun _ : Unit => True) dotSix where
  e_I := .eI
  e_D := .eD
  e_M := .eM
  e_Sigma := .eSigma
  e_Delta := .eDelta
  enc_ι := .eI
  enc_κ := .eD
  d_I := .eD
  d_K := .eD
  m_I := .eM
  m_K := .eM
  s_C := .eI
  ir1_distinct := by decide
  ir2_actual := by decide
  h1_ι := by decide
  h1_κ := by decide
  h2_ι := by decide
  h2_κ := by decide
  h3 := by decide
  ir4_distinct := by decide

/-- Explicit role-code collapse in the 6-element witness. -/
theorem sixIR_code_collapse :
    sixIR.d_I = sixIR.d_K ∧ sixIR.m_I = sixIR.m_K ∧ sixIR.enc_ι = sixIR.s_C := by
  decide

/-- In this model, 5 out of 6 elements are left-absorbing, so absorber behavior
    is far from the Δ₁ two-boolean pattern. -/
def sixLeftAbsorbers : Finset Six :=
  Finset.univ.filter (fun x => ∀ y : Six, dotSix x y = x)

theorem sixLeftAbsorbers_card : sixLeftAbsorbers.card = 5 := by
  native_decide

theorem sixDS_fullAbstractAxioms : FullAbstractAxioms sixDS := by
  refine ⟨sixDS_A2, sixDS_A5, sixDS_Ext, sixDS_DirectedA7Prime, ?_⟩
  exact ⟨Unit, (fun _ : Unit => True), ⟨sixIR⟩⟩

theorem card_six : Fintype.card Six = 6 := by
  native_decide

theorem sixDS_not_roleComplete17 : ¬ sixDS.RoleComplete17 := by
  intro hR
  have hCard : 17 ≤ Fintype.card Six :=
    DirectedDS.card_ge_17_of_roleComplete17 sixDS hR
  simp [card_six] at hCard

/-- Attempted full-abstract bundle still does not force `Embedding17`. -/
theorem not_forced_embedding17_from_fullAbstractAxioms :
    ¬ (∀ {X : Type} [DecidableEq X] [Fintype X] (ds : DirectedDS X),
        FullAbstractAxioms ds → Embedding17 ds) := by
  intro h
  have hE : Embedding17 sixDS := h sixDS sixDS_fullAbstractAxioms
  have hCard : 17 ≤ Fintype.card Six :=
    card_ge_17_of_embedding17 sixDS hE
  simp [card_six] at hCard

/-- Equivalent cardinality formulation of the same gap witness. -/
theorem not_forced_card_ge_17_from_fullAbstractAxioms :
    ¬ (∀ {X : Type} [DecidableEq X] [Fintype X] (ds : DirectedDS X),
        FullAbstractAxioms ds → 17 ≤ Fintype.card X) := by
  intro h
  have hCard : 17 ≤ Fintype.card Six := h sixDS sixDS_fullAbstractAxioms
  simp [card_six] at hCard

end FullAbstractAxiomGap

/- # Nondegenerate-IR Bridge Attempt

This file strengthens the previous full-abstract bundle by requiring a
nondegenerate intrinsic-reflexivity witness whose context/code token set has
cardinality 7:

`{enc_ι, enc_κ, d_I, d_K, m_I, m_K, s_C}`.

We prove:
1. This strengthening implies `card ≥ 7`.
2. It still does not force `Embedding17` / `card ≥ 17` (13-element countermodel).
-/

import DistinctionStructures.IntermediateAxiomLadder
import DistinctionStructures.BasePlusA7Derivation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace NondegenerateIRBridge

open DirectedDS
open IntermediateAxiomLadder
open BasePlusA7Derivation

variable {D : Type} [DecidableEq D] [Fintype D]

/-- The seven context/code tokens extracted from a directed IR witness. -/
def irCodeSet
    {K : Type} {actualD : D → Prop} {actualK : K → Prop} {dot : D → D → D}
    (ir : DirectedIR D K actualD actualK dot) : Finset D :=
  {ir.enc_ι, ir.enc_κ, ir.d_I, ir.d_K, ir.m_I, ir.m_K, ir.s_C}

/-- A directed DS has a nondegenerate IR witness if those seven tokens are all distinct. -/
def NondegenerateIR (ds : DirectedDS D) : Prop :=
  ∃ (K : Type) (actualK : K → Prop) (ir : DirectedIR D K ds.actual actualK ds.dot),
    (irCodeSet ir).card = 7

/-- Bridge attempt bundle: base + generic novelty + nondegenerate IR. -/
def BridgeAxioms (ds : DirectedDS D) : Prop :=
  ds.A2 ∧ ds.A5 ∧ ds.Ext ∧ DirectedA7Prime ds ∧ NondegenerateIR ds

theorem card_ge_7_of_nondegenerateIR (ds : DirectedDS D) (hN : NondegenerateIR ds) :
    7 ≤ Fintype.card D := by
  rcases hN with ⟨K, actualK, ir, hCard⟩
  have hle : (irCodeSet ir).card ≤ Fintype.card D := by
    simpa [Finset.card_univ] using (Finset.card_le_univ (irCodeSet ir))
  simpa [hCard] using hle

theorem card_ge_7_of_bridgeAxioms (ds : DirectedDS D) (hB : BridgeAxioms ds) :
    7 ≤ Fintype.card D := by
  rcases hB with ⟨_, _, _, _, hN⟩
  exact card_ge_7_of_nondegenerateIR ds hN

/-- 13-element carrier for the nondegenerate-IR gap witness. -/
inductive Gap13 where
  | eI | eD | eM | eSigma | eDelta
  | encI | encK
  | dI | dK
  | mI | mK
  | sC
  | n
  deriving DecidableEq, Repr

instance : Fintype Gap13 where
  elems := {
    .eI, .eD, .eM, .eSigma, .eDelta,
    .encI, .encK,
    .dI, .dK,
    .mI, .mK,
    .sC,
    .n
  }
  complete := by
    intro x
    cases x <;> simp

def actualGap13 : Gap13 → Prop
  | .n => False
  | _ => True

instance : DecidablePred actualGap13
  | .eI => isTrue trivial
  | .eD => isTrue trivial
  | .eM => isTrue trivial
  | .eSigma => isTrue trivial
  | .eDelta => isTrue trivial
  | .encI => isTrue trivial
  | .encK => isTrue trivial
  | .dI => isTrue trivial
  | .dK => isTrue trivial
  | .mI => isTrue trivial
  | .mK => isTrue trivial
  | .sC => isTrue trivial
  | .n => isFalse (by intro h; exact h)

/-- Left-projection with five IR-enforcing exceptions. -/
def dotGap13 : Gap13 → Gap13 → Gap13
  | .eD, .encI => .dI
  | .eD, .encK => .dK
  | .eM, .encI => .mI
  | .eM, .encK => .mK
  | .eSigma, .sC => .eDelta
  | x, _ => x

def gap13DS : DirectedDS Gap13 where
  actual := actualGap13
  dot := dotGap13

theorem gap13DS_A2 : gap13DS.A2 := by
  exact ⟨.eI, by simp [gap13DS, actualGap13]⟩

theorem gap13DS_A5 : gap13DS.A5 := by
  exact ⟨.n, by simp [gap13DS, actualGap13]⟩

theorem gap13DS_Ext : gap13DS.Ext := by
  intro x y hxy
  refine ⟨.n, ?_⟩
  cases x <;> cases y <;> simp [gap13DS, dotGap13] at hxy ⊢

theorem gap13DS_DirectedA7Prime : DirectedA7Prime gap13DS := by
  refine ⟨{Gap13.eI, Gap13.eD}, by native_decide, ?_, ?_⟩
  · intro d hd
    rcases (by simpa using hd) with rfl | rfl <;> simp [gap13DS, actualGap13]
  · refine ⟨Gap13.n, Gap13.encI, by simp, ?_⟩
    intro d hd
    rcases (by simpa using hd) with rfl | rfl <;> decide

def gap13IR : DirectedIR Gap13 Unit actualGap13 (fun _ : Unit => True) dotGap13 where
  e_I := .eI
  e_D := .eD
  e_M := .eM
  e_Sigma := .eSigma
  e_Delta := .eDelta
  enc_ι := .encI
  enc_κ := .encK
  d_I := .dI
  d_K := .dK
  m_I := .mI
  m_K := .mK
  s_C := .sC
  ir1_distinct := by decide
  ir2_actual := by decide
  h1_ι := by decide
  h1_κ := by decide
  h2_ι := by decide
  h2_κ := by decide
  h3 := by decide
  ir4_distinct := by decide

theorem gap13_nondegenerateIR : NondegenerateIR gap13DS := by
  refine ⟨Unit, (fun _ : Unit => True), gap13IR, ?_⟩
  native_decide

/-- Despite nondegenerate IR codes, many rows are still left-absorbing. -/
def gap13LeftAbsorbers : Finset Gap13 :=
  Finset.univ.filter (fun x => ∀ y : Gap13, dotGap13 x y = x)

theorem gap13LeftAbsorbers_card : gap13LeftAbsorbers.card = 10 := by
  native_decide

theorem gap13_bridgeAxioms : BridgeAxioms gap13DS := by
  exact ⟨gap13DS_A2, gap13DS_A5, gap13DS_Ext, gap13DS_DirectedA7Prime, gap13_nondegenerateIR⟩

theorem card_gap13 : Fintype.card Gap13 = 13 := by
  native_decide

theorem gap13DS_not_roleComplete17 : ¬ gap13DS.RoleComplete17 := by
  intro hR
  have hCard : 17 ≤ Fintype.card Gap13 :=
    DirectedDS.card_ge_17_of_roleComplete17 gap13DS hR
  simp [card_gap13] at hCard

theorem not_forced_embedding17_from_bridgeAxioms :
    ¬ (∀ {X : Type} [DecidableEq X] [Fintype X] (ds : DirectedDS X),
        BridgeAxioms ds → Embedding17 ds) := by
  intro h
  have hE : Embedding17 gap13DS := h gap13DS gap13_bridgeAxioms
  have hCard : 17 ≤ Fintype.card Gap13 :=
    card_ge_17_of_embedding17 gap13DS hE
  simp [card_gap13] at hCard

theorem not_forced_card_ge_17_from_bridgeAxioms :
    ¬ (∀ {X : Type} [DecidableEq X] [Fintype X] (ds : DirectedDS X),
        BridgeAxioms ds → 17 ≤ Fintype.card X) := by
  intro h
  have hCard : 17 ≤ Fintype.card Gap13 := h gap13DS gap13_bridgeAxioms
  simp [card_gap13] at hCard

end NondegenerateIRBridge

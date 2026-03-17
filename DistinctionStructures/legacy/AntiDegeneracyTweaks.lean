/- # Anti-Degeneracy Tweaks: Two Candidate Axioms

This file formalizes two proposed refinements:

1. `ExactlyTwoAbsorbers` (directed A4-style).
2. `CodeNonCollapse` (IR code/context non-collapse).

We test them on:
- `Δ₁` (should satisfy both),
- the 6-element countermodel from `FullAbstractAxiomGap` (fails both),
- the 13-element countermodel from `NondegenerateIRBridge` (fails #1 but satisfies #2).
-/

import DistinctionStructures.Delta1
import DistinctionStructures.Discoverable
import DistinctionStructures.FullAbstractAxiomGap
import DistinctionStructures.NondegenerateIRBridge

namespace AntiDegeneracyTweaks

open DirectedDS
open FullAbstractAxiomGap
open NondegenerateIRBridge

variable {D : Type} [DecidableEq D] [Fintype D]

/-- Left-absorbing row: `x·y = x` for all right arguments. -/
def LeftAbsorbing (ds : DirectedDS D) (x : D) : Prop :=
  ∀ y : D, ds.dot x y = x

/-- Decidability of left-absorbing behavior on finite carriers. -/
instance leftAbsorbingDecidablePred (ds : DirectedDS D) : DecidablePred (LeftAbsorbing ds) := by
  intro x
  classical
  unfold LeftAbsorbing
  infer_instance

/-- Directed A4-style strengthening: exactly two left-absorbing elements. -/
def ExactlyTwoAbsorbers (ds : DirectedDS D) : Prop :=
  ∃ top bot : D,
    top ≠ bot ∧
    LeftAbsorbing ds top ∧
    LeftAbsorbing ds bot ∧
    ∀ x : D, LeftAbsorbing ds x → x = top ∨ x = bot

/-- IR code/context non-collapse.

`DirectedIR` is parametric in the secondary context type but does not use values
of that type in fields, so a `Unit` instantiation captures the same content. -/
def CodeNonCollapse (ds : DirectedDS D) : Prop :=
  ∃ ir : DirectedIR D Unit ds.actual (fun _ : Unit => True) ds.dot,
    ir.enc_ι ≠ ir.enc_κ ∧ ir.d_I ≠ ir.d_K ∧ ir.m_I ≠ ir.m_K

def CoreRefinement (ds : DirectedDS D) : Prop :=
  ExactlyTwoAbsorbers ds ∧ CodeNonCollapse ds

def LeftAbsorberSet (ds : DirectedDS D) : Finset D :=
  Finset.univ.filter (fun x => LeftAbsorbing ds x)

theorem leftAbsorberSet_card_le_two_of_exactlyTwo (ds : DirectedDS D)
    (h : ExactlyTwoAbsorbers ds) :
    (LeftAbsorberSet ds).card ≤ 2 := by
  rcases h with ⟨top, bot, htb, htop, hbot, huniq⟩
  have hsub : LeftAbsorberSet ds ⊆ ({top, bot} : Finset D) := by
    intro x hx
    have hL : LeftAbsorbing ds x := (Finset.mem_filter.mp hx).2
    rcases huniq x hL with rfl | rfl <;> simp
  have hCardSub : (LeftAbsorberSet ds).card ≤ ({top, bot} : Finset D).card :=
    Finset.card_le_card hsub
  have hPair : ({top, bot} : Finset D).card = 2 := by
    simp [htb]
  simpa [hPair] using hCardSub

/-! ## Δ₁ satisfies both tweaks -/

def delta1IRUnit : DirectedIR D1ι Unit actual_ι (fun _ : Unit => True) dot where
  e_I := .e_I
  e_D := .e_D
  e_M := .e_M
  e_Sigma := .e_Sigma
  e_Delta := .e_Delta
  enc_ι := .i
  enc_κ := .k
  d_I := .d_I
  d_K := .d_K
  m_I := .m_I
  m_K := .m_K
  s_C := .s_C
  ir1_distinct := by decide
  ir2_actual := by decide
  h1_ι := by decide
  h1_κ := by decide
  h2_ι := by decide
  h2_κ := by decide
  h3 := by decide
  ir4_distinct := by decide

theorem delta1_exactlyTwoAbsorbers : ExactlyTwoAbsorbers delta1_dirDS := by
  refine ⟨.top, .bot, by decide, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro x hx
    have hx' : ∀ y : D1ι, dot x y = x := by
      simpa [LeftAbsorbing, delta1_dirDS] using hx
    simpa using (boolean_uniqueness x).1 hx'

theorem delta1_codeNonCollapse : CodeNonCollapse delta1_dirDS := by
  refine ⟨delta1IRUnit, ?_⟩
  decide

theorem delta1_coreRefinement : CoreRefinement delta1_dirDS := by
  exact ⟨delta1_exactlyTwoAbsorbers, delta1_codeNonCollapse⟩

/-! ## 6-element witness behavior under the tweaks -/

theorem sixDS_not_exactlyTwoAbsorbers : ¬ ExactlyTwoAbsorbers sixDS := by
  intro h
  have hLe2 : (LeftAbsorberSet sixDS).card ≤ 2 :=
    leftAbsorberSet_card_le_two_of_exactlyTwo sixDS h
  have hFive : (LeftAbsorberSet sixDS).card = 5 := by
    native_decide
  have : ¬ ((LeftAbsorberSet sixDS).card ≤ 2) := by
    simp [hFive]
  exact this hLe2

lemma dotSix_eq_self_of_ne_eSigma (x y : Six) (hx : x ≠ .eSigma) :
    dotSix x y = x := by
  cases x <;> cases y <;> simp [dotSix] at hx ⊢

theorem sixIR_forces_code_collapse
    (ir : DirectedIR Six Unit actualSix (fun _ : Unit => True) dotSix) :
    ir.d_I = ir.d_K ∧ ir.m_I = ir.m_K := by
  have hDeltaNeSigma : ir.e_Delta ≠ ir.e_Sigma := ir.ir4_distinct.2.2.2
  have hSigma : ir.e_Sigma = .eSigma := by
    by_contra h
    have hs : dotSix ir.e_Sigma ir.s_C = ir.e_Sigma :=
      dotSix_eq_self_of_ne_eSigma ir.e_Sigma ir.s_C h
    have : ir.e_Delta = ir.e_Sigma := by
      calc
        ir.e_Delta = dotSix ir.e_Sigma ir.s_C := ir.h3.symm
        _ = ir.e_Sigma := hs
    exact hDeltaNeSigma this
  have hSC : ir.s_C = .eI := by
    by_contra h
    have hs : dotSix ir.e_Sigma ir.s_C = ir.e_Sigma := by
      rw [hSigma]
      cases hscEq : ir.s_C with
      | eI =>
          have hsci : ir.s_C = .eI := by simp [hscEq]
          exact False.elim (h hsci)
      | eD =>
          simp [dotSix]
      | eM =>
          simp [dotSix]
      | eSigma =>
          simp [dotSix]
      | eDelta =>
          simp [dotSix]
      | n =>
          simp [dotSix]
    have : ir.e_Delta = ir.e_Sigma := by
      calc
        ir.e_Delta = dotSix ir.e_Sigma ir.s_C := ir.h3.symm
        _ = ir.e_Sigma := hs
    exact ir.ir4_distinct.2.2.2 this
  have hDne : ir.e_D ≠ .eSigma := by
    intro h
    have hEq : ir.e_D = ir.e_Sigma := by simpa [hSigma] using h
    exact (ir.ir1_distinct.2.2.2.2.1) hEq
  have hMne : ir.e_M ≠ .eSigma := by
    intro h
    have hEq : ir.e_M = ir.e_Sigma := by simpa [hSigma] using h
    exact (ir.ir1_distinct.2.2.2.2.2) hEq
  have hdI : ir.d_I = ir.e_D := by
    calc
      ir.d_I = dotSix ir.e_D ir.enc_ι := ir.h1_ι.symm
      _ = ir.e_D := dotSix_eq_self_of_ne_eSigma ir.e_D ir.enc_ι hDne
  have hdK : ir.d_K = ir.e_D := by
    calc
      ir.d_K = dotSix ir.e_D ir.enc_κ := ir.h1_κ.symm
      _ = ir.e_D := dotSix_eq_self_of_ne_eSigma ir.e_D ir.enc_κ hDne
  have hmI : ir.m_I = ir.e_M := by
    calc
      ir.m_I = dotSix ir.e_M ir.enc_ι := ir.h2_ι.symm
      _ = ir.e_M := dotSix_eq_self_of_ne_eSigma ir.e_M ir.enc_ι hMne
  have hmK : ir.m_K = ir.e_M := by
    calc
      ir.m_K = dotSix ir.e_M ir.enc_κ := ir.h2_κ.symm
      _ = ir.e_M := dotSix_eq_self_of_ne_eSigma ir.e_M ir.enc_κ hMne
  exact ⟨hdI.trans hdK.symm, hmI.trans hmK.symm⟩

theorem sixDS_not_codeNonCollapse : ¬ CodeNonCollapse sixDS := by
  intro h
  rcases h with ⟨ir, _, hD, hM⟩
  exact hD (sixIR_forces_code_collapse ir).1

theorem sixDS_not_coreRefinement : ¬ CoreRefinement sixDS := by
  intro h
  exact sixDS_not_exactlyTwoAbsorbers h.1

/-! ## 13-element witness behavior under the tweaks -/

theorem gap13DS_not_exactlyTwoAbsorbers : ¬ ExactlyTwoAbsorbers gap13DS := by
  intro h
  have hLe2 : (LeftAbsorberSet gap13DS).card ≤ 2 :=
    leftAbsorberSet_card_le_two_of_exactlyTwo gap13DS h
  have hTen : (LeftAbsorberSet gap13DS).card = 10 := by
    native_decide
  have : ¬ ((LeftAbsorberSet gap13DS).card ≤ 2) := by
    simp [hTen]
  exact this hLe2

theorem gap13DS_codeNonCollapse : CodeNonCollapse gap13DS := by
  refine ⟨gap13IR, ?_⟩
  decide

theorem gap13DS_not_coreRefinement : ¬ CoreRefinement gap13DS := by
  intro h
  exact gap13DS_not_exactlyTwoAbsorbers h.1

end AntiDegeneracyTweaks

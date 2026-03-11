/- # Universal Bounds for Ψ-Structures

Algebraic (model-independent) consequences of the PsiStructure axioms (L0–L3).

Results:
- No right identity exists in any PsiStructure.
- Every PsiStructure has at least 4 elements.

Both proofs are purely algebraic — no `native_decide` over function spaces.
-/

import DistinctionStructures.PsiStructure
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace PsiUniversalBounds

open PsiRoleAxioms

/-- No right identity exists in any PsiStructure.

Proof: If `e` is a right identity, then `tau·e = tau`. But `tau_boolean` forces
`tau·e ∈ {top, bot}`, so `tau = top ∨ tau = bot`, contradicting the axioms. -/
theorem no_right_identity
    {D : Type} [DecidableEq D] [Fintype D]
    (ps : PsiStructure D) :
    ¬∃ e : D, ∀ x : D, ps.dot x e = x := by
  intro ⟨e, he⟩
  have htau := he ps.tau
  rcases ps.tau_boolean e with h | h
  · exact ps.tau_ne_top (htau ▸ h)
  · exact ps.tau_ne_bot (htau ▸ h)

/-- Every PsiStructure has at least 4 elements.

Proof: The four distinguished elements {top, bot, tau, f_enc} are pairwise
distinct by the axioms. Follows the exact pattern from BaseAxiomDerivation. -/
theorem card_ge_four
    {D : Type} [DecidableEq D] [Fintype D]
    (ps : PsiStructure D) :
    4 ≤ Fintype.card D := by
  have hab : ps.top ≠ ps.bot := ps.top_ne_bot
  have hat : ps.top ≠ ps.tau := fun h => ps.tau_ne_top h.symm
  have haf : ps.top ≠ ps.f_enc := fun h => ps.f_ne_top h.symm
  have hbt : ps.bot ≠ ps.tau := fun h => ps.tau_ne_bot h.symm
  have hbf : ps.bot ≠ ps.f_enc := fun h => ps.f_ne_bot h.symm
  have htf : ps.tau ≠ ps.f_enc := fun h => ps.f_ne_tau h.symm
  have hcard : ({ps.top, ps.bot, ps.tau, ps.f_enc} : Finset D).card = 4 := by
    simp [hab, hat, haf, hbt, hbf, htf]
  have hsub : ({ps.top, ps.bot, ps.tau, ps.f_enc} : Finset D) ⊆
      (Finset.univ : Finset D) := by
    intro x _; simp
  have hle : ({ps.top, ps.bot, ps.tau, ps.f_enc} : Finset D).card ≤
      (Finset.univ : Finset D).card :=
    Finset.card_le_card hsub
  simpa [hcard] using hle

end PsiUniversalBounds

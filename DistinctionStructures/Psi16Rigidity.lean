/- # Ψ₁₆ᶠ Automorphism Rigidity

   Every injective endomorphism of (Fin 16, psi) is the identity.
   Equivalently, Aut(Ψ₁₆ᶠ) = {id}.

   Strategy: Show σ must fix the two idempotents {⊤, ⊥}, then
   propagate through the generation tree using products of fixed
   elements. The swap case (σ ⊤ = ⊥) is eliminated by contradiction.

   All proofs are computational: `decide` or `native_decide`.
-/

import DistinctionStructures.Psi16Full
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 1600000

namespace Psi16Rigidity

open Psi16Full

/-- An endomorphism of (Fin 16, psi). -/
def is_endomorphism (σ : Fin 16 → Fin 16) : Prop :=
  ∀ a b : Fin 16, σ (psi a b) = psi (σ a) (σ b)

/-! ## Helper Lemmas (all by decide/native_decide) -/

private theorem only_idempotents : ∀ a : Fin 16,
    psi a a = a → (a = (0 : Fin 16) ∨ a = (1 : Fin 16)) := by decide

/-- E(7) is the unique element with psi a 0 = 0, psi a 1 = 1, psi a a ∉ {0,1}. -/
private theorem E_unique : ∀ a : Fin 16,
    psi a 0 = 0 → psi a 1 = 1 → psi a a ≠ 0 → psi a a ≠ 1 → a = 7 := by native_decide

/-- The only x with psi 2 x = 7 is x = 3. -/
private theorem f_inv_E : ∀ x : Fin 16, psi 2 x = 7 → x = 3 := by decide

/-- The only x with psi 2 x = x, x ∉ {1, 5, 15}, is x = 6. -/
private theorem f_fixpoint : ∀ x : Fin 16,
    psi 2 x = x → x ≠ 1 → x ≠ 5 → x ≠ 15 → x = 6 := by decide

/-- The only x with psi 7 x = 15 are x = 10 and x = 13. -/
private theorem E_inv_s5 : ∀ x : Fin 16, psi 7 x = 15 → x = 10 ∨ x = 13 := by decide

/-! ## Main Theorem -/

/-- Every injective endomorphism of Ψ₁₆ᶠ is the identity. -/
theorem automorphism_trivial : ∀ σ : Fin 16 → Fin 16,
    is_endomorphism σ → Function.Injective σ → σ = id := by
  intro σ hendo hinj
  -- Shorthand for "σ x ≠ σ y when x ≠ y"
  have hne : ∀ a b : Fin 16, a ≠ b → σ a ≠ σ b :=
    fun _ _ hab h => hab (hinj h)
  -- σ preserves idempotents: psi(σ a)(σ a) = σ(psi a a) = σ a
  have hidem : ∀ a : Fin 16, psi a a = a → σ a = psi (σ a) (σ a) := by
    intro a ha; have h := hendo a a; rwa [ha] at h
  -- Top and bot are the only idempotents
  have htop_01 : σ 0 = 0 ∨ σ 0 = 1 :=
    only_idempotents _ (hidem 0 (by decide)).symm
  have hbot_01 : σ 1 = 0 ∨ σ 1 = 1 :=
    only_idempotents _ (hidem 1 (by decide)).symm
  ---- Step 0: Fix top (σ 0 = 0) ----
  -- Eliminate the swap case by contradiction
  have h0 : σ 0 = 0 := by
    rcases htop_01 with h | h0_eq_1
    · exact h
    · exfalso
      have h1_eq_0 : σ 1 = 0 := by
        rcases hbot_01 with h | h
        · exact h
        · exact absurd (h0_eq_1.trans h.symm) (hne 0 1 (by decide))
      -- psi 7 0 = 0 → σ 0 = psi(σ 7)(σ 0), so psi(σ 7)(1) = 1
      have hE1 : psi (σ 7) 1 = 1 := by
        have h := hendo 7 0
        simp only [show psi 7 0 = (0 : Fin 16) from by decide, h0_eq_1] at h
        exact h.symm
      -- psi 7 1 = 1 → σ 1 = psi(σ 7)(σ 1), so psi(σ 7)(0) = 0
      have hE0 : psi (σ 7) 0 = 0 := by
        have h := hendo 7 1
        simp only [show psi 7 1 = (1 : Fin 16) from by decide, h1_eq_0] at h
        exact h.symm
      -- psi(σ 7)(σ 7) = σ 2, and σ 2 ∉ {0,1}
      have hEE : psi (σ 7) (σ 7) = σ 2 := by
        have h := hendo 7 7
        simp only [show psi 7 7 = (2 : Fin 16) from by decide] at h
        exact h.symm
      -- σ 7 = 7 (unique element satisfying these constraints)
      have hσ7 : σ 7 = 7 := E_unique (σ 7) hE0 hE1
        (fun h => absurd (hinj ((hEE.symm.trans h).trans h1_eq_0.symm)) (by decide))
        (fun h => absurd (hinj ((hEE.symm.trans h).trans h0_eq_1.symm)) (by decide))
      -- Then σ 2 = psi 7 7 = 2
      have hσ2 : σ 2 = 2 := by
        have h := hendo 7 7
        simp only [show psi 7 7 = (2 : Fin 16) from by decide, hσ7] at h
        exact h
      -- psi 2 0 = 5, so σ 5 = psi(2)(1) = 1
      have hσ5 : σ 5 = 1 := by
        have h := hendo 2 0
        simp only [show psi 2 0 = (5 : Fin 16) from by decide, hσ2, h0_eq_1,
                    show psi 2 1 = (1 : Fin 16) from by decide] at h
        exact h
      -- σ 5 = 1 = σ 0, but 5 ≠ 0. Contradiction.
      exact hne 5 0 (by decide) (hσ5.trans h0_eq_1.symm)
  ---- Step 1: Fix bot (σ 1 = 1) ----
  have h1 : σ 1 = 1 := by
    rcases hbot_01 with h | h
    · exact absurd (h0.trans h.symm) (hne 0 1 (by decide))
    · exact h
  ---- Step 2: Fix E(7) ----
  have hE : σ 7 = 7 := by
    have he0 : psi (σ 7) 0 = 0 := by
      have h := hendo 7 0
      simp only [show psi 7 0 = (0 : Fin 16) from by decide, h0] at h; exact h.symm
    have he1 : psi (σ 7) 1 = 1 := by
      have h := hendo 7 1
      simp only [show psi 7 1 = (1 : Fin 16) from by decide, h1] at h; exact h.symm
    have hee : psi (σ 7) (σ 7) = σ 2 := by
      have h := hendo 7 7
      simp only [show psi 7 7 = (2 : Fin 16) from by decide] at h; exact h.symm
    exact E_unique (σ 7) he0 he1
      (fun h => absurd (hinj ((hee.symm.trans h).trans h0.symm)) (by decide))
      (fun h => absurd (hinj ((hee.symm.trans h).trans h1.symm)) (by decide))
  ---- Step 3: Fix f_enc(2) = psi 7 7 ----
  have hf : σ 2 = 2 := by
    have h := hendo 7 7
    simp only [show psi 7 7 = (2 : Fin 16) from by decide, hE] at h; exact h
  ---- Step 4: Fix tau(3) — unique preimage of 7 under psi 2 ----
  have htau : σ 3 = 3 := by
    apply f_inv_E
    have h := hendo 2 3
    simp only [show psi 2 3 = (7 : Fin 16) from by decide, hf, hE] at h; exact h.symm
  ---- Step 5: Fix g(4) = psi 7 3 ----
  have hg : σ 4 = 4 := by
    have h := hendo 7 3
    simp only [show psi 7 3 = (4 : Fin 16) from by decide, hE, htau] at h; exact h
  ---- Step 6: Fix x5(5) = psi 2 0 ----
  have hx5 : σ 5 = 5 := by
    have h := hendo 2 0
    simp only [show psi 2 0 = (5 : Fin 16) from by decide, hf, h0] at h; exact h
  ---- Step 7: Fix Q(6) — unique fixed point of psi 2 ----
  have hQ : σ 6 = 6 := by
    have h := hendo 2 6
    simp only [show psi 2 6 = (6 : Fin 16) from by decide, hf] at h
    -- h : σ 6 = psi 2 (σ 6), i.e., psi 2 (σ 6) = σ 6
    exact f_fixpoint (σ 6) h.symm
      (fun heq => absurd (heq.trans h1.symm) (hne 6 1 (by decide)))
      (fun heq => absurd (heq.trans hx5.symm) (hne 6 5 (by decide)))
      (fun heq => by
        -- If σ 6 = 15, derive contradiction using another equation
        -- psi 7 6 = 11 (E·Q = s3). σ(11) = psi(σ 7)(σ 6) = psi 7 15 = 5.
        -- But σ 5 = 5, so σ 11 = σ 5, contradicting injectivity.
        have h2 := hendo 7 6
        simp only [show psi 7 6 = (11 : Fin 16) from by decide, hE, heq,
                    show psi 7 15 = (5 : Fin 16) from by decide] at h2
        exact absurd (h2.trans hx5.symm) (hne 11 5 (by decide)))
  ---- Step 8: Fix rho(8) = psi 2 7 ----
  have hrho : σ 8 = 8 := by
    have h := hendo 2 7
    simp only [show psi 2 7 = (8 : Fin 16) from by decide, hf, hE] at h; exact h
  ---- Step 9: Fix s3(11) = psi 2 4 ----
  have hs3 : σ 11 = 11 := by
    have h := hendo 2 4
    simp only [show psi 2 4 = (11 : Fin 16) from by decide, hf, hg] at h; exact h
  ---- Step 10: Fix eta(9) = psi 2 11 ----
  have heta : σ 9 = 9 := by
    have h := hendo 2 11
    simp only [show psi 2 11 = (9 : Fin 16) from by decide, hf, hs3] at h; exact h
  ---- Step 11: Fix INC(13) = psi 2 2 ----
  have hINC : σ 13 = 13 := by
    have h := hendo 2 2
    simp only [show psi 2 2 = (13 : Fin 16) from by decide, hf] at h; exact h
  ---- Step 12: Fix s1(14) = psi 2 13 ----
  have hs1 : σ 14 = 14 := by
    have h := hendo 2 13
    simp only [show psi 2 13 = (14 : Fin 16) from by decide, hf, hINC] at h; exact h
  ---- Step 13: Fix s5(15) = psi 7 13 ----
  have hs5 : σ 15 = 15 := by
    have h := hendo 7 13
    simp only [show psi 7 13 = (15 : Fin 16) from by decide, hE, hINC] at h; exact h
  ---- Step 14: Fix Y(10) — psi 7 10 = 15, only 10 or 13 work, 13 is taken ----
  have hY : σ 10 = 10 := by
    have h : psi 7 (σ 10) = 15 := by
      have h := hendo 7 10
      simp only [show psi 7 10 = (15 : Fin 16) from by decide, hE, hs5] at h; exact h.symm
    rcases E_inv_s5 _ h with h | h
    · exact h
    · exact absurd (h.symm ▸ hINC : σ 13 = σ 10) (hne 13 10 (by decide))
  ---- Step 15: Fix s0(12) = psi 7 11 ----
  have hs0 : σ 12 = 12 := by
    have h := hendo 7 11
    simp only [show psi 7 11 = (12 : Fin 16) from by decide, hE, hs3] at h; exact h
  ---- Conclude: all 16 fixed, so σ = id ----
  funext i; simp only [id]
  fin_cases i <;>
    first | exact h0 | exact h1 | exact hf | exact htau | exact hg | exact hx5 |
            exact hQ | exact hE | exact hrho | exact heta | exact hY | exact hs3 |
            exact hs0 | exact hINC | exact hs1 | exact hs5

end Psi16Rigidity

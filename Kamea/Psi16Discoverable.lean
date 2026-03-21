/- # Ψ₁₆ᶠ Discoverability

   All 16 elements are behaviorally identifiable from structural properties
   of the Cayley table. Every element has a unique fingerprint computable
   from a small number of probes.

   All proofs are computational: `decide` or `native_decide`.
-/

import Kamea.Psi16Full
import Mathlib.Data.Finset.Card

set_option maxHeartbeats 800000

namespace Psi16Discoverable

open Psi16Full

/-! ## Part 1: Absorber Discovery -/

/-- Exactly 2 absorbers exist (⊤ and ⊥). -/
theorem boolean_uniqueness : ∀ a : Fin 16,
    (∀ x : Fin 16, psi a x = a) ↔ (a = top ∨ a = bot) := by decide

/-- Column-cardinality asymmetry distinguishes ⊤ from ⊥:
    |{a : psi a 0 = 0}| = 6 ≠ |{a : psi a 1 = 1}| = 9. -/
theorem absorber_orientation :
    (Finset.univ.filter (fun a : Fin 16 => psi a top = top)).card = 6 ∧
    (Finset.univ.filter (fun a : Fin 16 => psi a bot = bot)).card = 9 := by native_decide

/-! ## Part 2: Tester Discovery -/

/-- Exactly 3 testers: τ (3), SEQ (5), s0 (12). -/
theorem tester_characterization : ∀ a : Fin 16,
    is_tester a ↔ (a = tau ∨ a = x5 ∨ a = s0) := by native_decide

/-- SEQ (x5) has unique accept-card 5 among testers (τ and s0 have accept-card 8). -/
theorem tester_discrimination_x5 :
    (Finset.univ.filter (fun x : Fin 16 => psi x5 x = top)).card = 5 ∧
    (Finset.univ.filter (fun x : Fin 16 => psi tau x = top)).card = 8 ∧
    (Finset.univ.filter (fun x : Fin 16 => psi s0 x = top)).card = 8 := by native_decide

/-- τ accepts g_enc but s0 rejects it — this discriminates τ from s0. -/
theorem tester_discrimination_tau_s0 :
    psi tau g_enc = top ∧ psi s0 g_enc = bot := by decide

/-! ## Part 3: Encoder Discovery -/

/-- E is the unique encoder with E·⊤ = ⊤ and E·⊥ = ⊥. -/
theorem encoder_E_unique : ∀ a : Fin 16,
    is_encoder a → psi a top = top → psi a bot = bot → a = E := by native_decide

/-- Q is the unique element satisfying E·(Q·τ) = τ ∧ E·(Q·g) = g. -/
theorem encoder_Q_unique : ∀ a : Fin 16,
    psi E (psi a tau) = tau → psi E (psi a g_enc) = g_enc → a = Q := by native_decide

/-! ## Part 4: Inert Discovery -/

/-- g_enc is an almost-absorber: 15 of 16 outputs equal s3 (psi g_enc bot). -/
theorem g_enc_almost_absorber :
    (Finset.univ.filter (fun x : Fin 16 => psi g_enc x = psi g_enc bot)).card = 15 := by
  native_decide

/-- g_enc is uniquely characterized: the only non-absorber with ≥14 constant outputs. -/
theorem g_enc_unique : ∀ a : Fin 16,
    ¬is_absorber a →
    14 ≤ (Finset.univ.filter (fun x : Fin 16 => psi a x = psi a bot)).card →
    a = g_enc := by native_decide

/-! ## Part 5: Four-Probe Injectivity -/

/-- The map a ↦ (psi a 0, psi a 1, psi a 3, psi a 6) is injective on Fin 16.
    That is, 4 probes suffice to distinguish all 16 elements. -/
theorem four_probe_suffice : ∀ a b : Fin 16,
    psi a top = psi b top →
    psi a bot = psi b bot →
    psi a tau = psi b tau →
    psi a Q = psi b Q →
    a = b := by native_decide

end Psi16Discoverable

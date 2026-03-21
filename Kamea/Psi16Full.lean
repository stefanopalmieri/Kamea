/- # Ψ₁₆ᶠ — The 16-element self-describing algebra (full operations)

   Machine verification of the concrete 16×16 Cayley table with ALL
   operational constraints: L8+C+D+PA+VV+QE+1-inert+E-trans +
   Branch+Compose+Y+Selection + INC(8-cycle)+DEC(reverse) +
   IO(PUT/GET/SEQ) + PAIR/FST/SND(2×2 product) +
   INC2(4-cycle)+SWAP(involution). Active new ops: DEC+PAIR+INC2+SWAP.

   All proofs are computational: `decide` or `native_decide`.
-/

import Mathlib.Data.Fintype.Basic

set_option maxHeartbeats 800000

namespace Psi16Full

/-! ## Part 1: The Cayley Table -/

private def rawPsi : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  -- Row 2: f
  | 2, 0 => 5
  | 2, 1 => 1
  | 2, 2 => 13
  | 2, 3 => 7
  | 2, 4 => 11
  | 2, 5 => 5
  | 2, 6 => 6
  | 2, 7 => 8
  | 2, 8 => 2
  | 2, 9 => 5
  | 2, 10 => 11
  | 2, 11 => 9
  | 2, 12 => 4
  | 2, 13 => 14
  | 2, 14 => 3
  | 2, 15 => 15
  -- Row 3: τ
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 0
  | 3, 6 => 1
  | 3, 7 => 1
  | 3, 8 => 1
  | 3, 9 => 0
  | 3, 10 => 1
  | 3, 11 => 1
  | 3, 12 => 0
  | 3, 13 => 0
  | 3, 14 => 1
  | 3, 15 => 1
  -- Row 4: g
  | 4, 0 => 0
  | 4, 1 => 11
  | 4, 2 => 11
  | 4, 3 => 11
  | 4, 4 => 11
  | 4, 5 => 11
  | 4, 6 => 11
  | 4, 7 => 11
  | 4, 8 => 11
  | 4, 9 => 11
  | 4, 10 => 11
  | 4, 11 => 11
  | 4, 12 => 11
  | 4, 13 => 11
  | 4, 14 => 11
  | 4, 15 => 11
  -- Row 5: SEQ
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 1
  | 5, 3 => 1
  | 5, 4 => 1
  | 5, 5 => 1
  | 5, 6 => 0
  | 5, 7 => 1
  | 5, 8 => 1
  | 5, 9 => 1
  | 5, 10 => 0
  | 5, 11 => 1
  | 5, 12 => 0
  | 5, 13 => 1
  | 5, 14 => 1
  | 5, 15 => 0
  -- Row 6: Q/SND/s2/p01
  | 6, 0 => 15
  | 6, 1 => 0
  | 6, 2 => 5
  | 6, 3 => 9
  | 6, 4 => 3
  | 6, 5 => 15
  | 6, 6 => 14
  | 6, 7 => 14
  | 6, 8 => 2
  | 6, 9 => 12
  | 6, 10 => 8
  | 6, 11 => 14
  | 6, 12 => 12
  | 6, 13 => 4
  | 6, 14 => 12
  | 6, 15 => 8
  -- Row 7: E/INC2/s7
  | 7, 0 => 0
  | 7, 1 => 1
  | 7, 2 => 8
  | 7, 3 => 4
  | 7, 4 => 13
  | 7, 5 => 2
  | 7, 6 => 11
  | 7, 7 => 2
  | 7, 8 => 14
  | 7, 9 => 3
  | 7, 10 => 15
  | 7, 11 => 12
  | 7, 12 => 14
  | 7, 13 => 15
  | 7, 14 => 6
  | 7, 15 => 5
  -- Row 8: ρ/s6
  | 8, 0 => 12
  | 8, 1 => 1
  | 8, 2 => 13
  | 8, 3 => 7
  | 8, 4 => 11
  | 8, 5 => 5
  | 8, 6 => 12
  | 8, 7 => 11
  | 8, 8 => 4
  | 8, 9 => 12
  | 8, 10 => 5
  | 8, 11 => 14
  | 8, 12 => 15
  | 8, 13 => 7
  | 8, 14 => 11
  | 8, 15 => 12
  -- Row 9: η/p10
  | 9, 0 => 1
  | 9, 1 => 6
  | 9, 2 => 14
  | 9, 3 => 14
  | 9, 4 => 14
  | 9, 5 => 14
  | 9, 6 => 9
  | 9, 7 => 8
  | 9, 8 => 3
  | 9, 9 => 15
  | 9, 10 => 5
  | 9, 11 => 7
  | 9, 12 => 13
  | 9, 13 => 11
  | 9, 14 => 12
  | 9, 15 => 4
  -- Row 10: Y/s4
  | 10, 0 => 13
  | 10, 1 => 1
  | 10, 2 => 4
  | 10, 3 => 3
  | 10, 4 => 12
  | 10, 5 => 11
  | 10, 6 => 2
  | 10, 7 => 11
  | 10, 8 => 5
  | 10, 9 => 3
  | 10, 10 => 8
  | 10, 11 => 14
  | 10, 12 => 9
  | 10, 13 => 7
  | 10, 14 => 11
  | 10, 15 => 11
  -- Row 11: PAIR/s3/p11
  | 11, 0 => 14
  | 11, 1 => 1
  | 11, 2 => 9
  | 11, 3 => 10
  | 11, 4 => 11
  | 11, 5 => 13
  | 11, 6 => 12
  | 11, 7 => 7
  | 11, 8 => 5
  | 11, 9 => 6
  | 11, 10 => 8
  | 11, 11 => 2
  | 11, 12 => 14
  | 11, 13 => 12
  | 11, 14 => 10
  | 11, 15 => 4
  -- Row 12: s0/p00
  | 12, 0 => 0
  | 12, 1 => 1
  | 12, 2 => 1
  | 12, 3 => 0
  | 12, 4 => 1
  | 12, 5 => 1
  | 12, 6 => 0
  | 12, 7 => 1
  | 12, 8 => 1
  | 12, 9 => 1
  | 12, 10 => 0
  | 12, 11 => 0
  | 12, 12 => 0
  | 12, 13 => 0
  | 12, 14 => 0
  | 12, 15 => 1
  -- Row 13: INC
  | 13, 0 => 3
  | 13, 1 => 0
  | 13, 2 => 14
  | 13, 3 => 4
  | 13, 4 => 14
  | 13, 5 => 6
  | 13, 6 => 11
  | 13, 7 => 12
  | 13, 8 => 7
  | 13, 9 => 3
  | 13, 10 => 15
  | 13, 11 => 10
  | 13, 12 => 14
  | 13, 13 => 2
  | 13, 14 => 6
  | 13, 15 => 8
  -- Row 14: GET/FST/SWAP/s1
  | 14, 0 => 14
  | 14, 1 => 0
  | 14, 2 => 5
  | 14, 3 => 4
  | 14, 4 => 3
  | 14, 5 => 2
  | 14, 6 => 12
  | 14, 7 => 5
  | 14, 8 => 11
  | 14, 9 => 14
  | 14, 10 => 3
  | 14, 11 => 14
  | 14, 12 => 12
  | 14, 13 => 2
  | 14, 14 => 6
  | 14, 15 => 3
  -- Row 15: DEC/PUT/s5
  | 15, 0 => 1
  | 15, 1 => 3
  | 15, 2 => 13
  | 15, 3 => 15
  | 15, 4 => 3
  | 15, 5 => 7
  | 15, 6 => 14
  | 15, 7 => 8
  | 15, 8 => 15
  | 15, 9 => 4
  | 15, 10 => 11
  | 15, 11 => 6
  | 15, 12 => 7
  | 15, 13 => 14
  | 15, 14 => 12
  | 15, 15 => 10
  | _, _ => 0

private theorem rawPsi_bound (a b : Fin 16) : rawPsi a.val b.val < 16 := by
  revert a b; native_decide

/-- The Ψ₁₆ᶠ binary operation. -/
def psi (a b : Fin 16) : Fin 16 := ⟨rawPsi a.val b.val, rawPsi_bound a b⟩

/-! ## Part 2: Named Constants -/

abbrev top : Fin 16 := 0    -- ⊤
abbrev bot : Fin 16 := 1    -- ⊥
abbrev f_enc : Fin 16 := 2    -- f
abbrev tau : Fin 16 := 3    -- τ
abbrev g_enc : Fin 16 := 4    -- g
abbrev x5 : Fin 16 := 5    -- SEQ
abbrev Q : Fin 16 := 6    -- Q / SND / s2 / p01
abbrev E : Fin 16 := 7    -- E / INC2 / s7
abbrev rho : Fin 16 := 8    -- ρ / s6
abbrev eta : Fin 16 := 9    -- η / p10
abbrev Y_fix : Fin 16 := 10    -- Y / s4
abbrev s3 : Fin 16 := 11    -- PAIR / s3 / p11
abbrev s0 : Fin 16 := 12    -- s0 / p00
abbrev INC : Fin 16 := 13    -- INC
abbrev s1 : Fin 16 := 14    -- GET / FST / SWAP / s1
abbrev s5 : Fin 16 := 15    -- DEC / PUT / s5

abbrev DEC : Fin 16 := 15    -- alias for s5
abbrev PUT : Fin 16 := 15    -- alias for s5
abbrev GET_IO : Fin 16 := 14    -- alias for s1
abbrev SEQ : Fin 16 := 5    -- alias for x5
abbrev PAIR_OP : Fin 16 := 11    -- alias for s3
abbrev FST_OP : Fin 16 := 14    -- alias for s1
abbrev SND_OP : Fin 16 := 6    -- alias for Q
abbrev INC2 : Fin 16 := 7    -- alias for E
abbrev SWAP_OP : Fin 16 := 14    -- alias for s1
abbrev p00 : Fin 16 := 12    -- alias for s0
abbrev p01 : Fin 16 := 6    -- alias for Q
abbrev p10 : Fin 16 := 9    -- alias for eta
abbrev p11 : Fin 16 := 11    -- alias for s3

/-! ## Part 3: Structural Axioms -/

theorem top_absorbs : ∀ x : Fin 16, psi top x = top := by decide
theorem bot_absorbs : ∀ x : Fin 16, psi bot x = bot := by decide
theorem only_two_absorbers : ∀ a : Fin 16,
    (∀ x : Fin 16, psi a x = a) → (a = top ∨ a = bot) := by decide
theorem ext_rows : ∀ a b : Fin 16, a ≠ b →
    ∃ x : Fin 16, psi a x ≠ psi b x := by decide
theorem ext_cols : ∀ a b : Fin 16, a ≠ b →
    ∃ x : Fin 16, psi x a ≠ psi x b := by decide

/-! ## Part 4: Role Classification -/

def is_absorber (a : Fin 16) : Prop := ∀ x : Fin 16, psi a x = a
def is_boolean (v : Fin 16) : Prop := v = top ∨ v = bot
def is_tester (a : Fin 16) : Prop :=
  ¬is_absorber a ∧ ∀ x : Fin 16, is_boolean (psi a x)

instance : DecidablePred is_absorber := fun a =>
  inferInstanceAs (Decidable (∀ x : Fin 16, psi a x = a))
instance : DecidablePred is_boolean := fun v =>
  inferInstanceAs (Decidable (v = top ∨ v = bot))
instance : DecidablePred is_tester := fun a =>
  inferInstanceAs (Decidable (¬is_absorber a ∧ ∀ x : Fin 16, is_boolean (psi a x)))

def is_encoder (a : Fin 16) : Prop :=
  ¬is_absorber a ∧ ¬(∀ x : Fin 16, is_boolean (psi a x)) ∧
  ∃ x y : Fin 16, ¬is_boolean (psi a x) ∧ ¬is_boolean (psi a y) ∧ psi a x ≠ psi a y
instance : DecidablePred is_encoder := fun a =>
  inferInstanceAs (Decidable (¬is_absorber a ∧ ¬(∀ x, is_boolean (psi a x)) ∧
    ∃ x y : Fin 16, ¬is_boolean (psi a x) ∧ ¬is_boolean (psi a y) ∧ psi a x ≠ psi a y))

def is_inert (a : Fin 16) : Prop :=
  ¬is_absorber a ∧ ¬is_tester a ∧ ¬is_encoder a
instance : DecidablePred is_inert := fun a =>
  inferInstanceAs (Decidable (¬is_absorber a ∧ ¬is_tester a ∧ ¬is_encoder a))

theorem tau_is_tester : is_tester tau := by decide
theorem x5_is_tester : is_tester x5 := by decide
theorem s0_is_tester : is_tester s0 := by decide
theorem exactly_3_testers : ∀ a : Fin 16,
    is_tester a → (a = tau ∨ a = x5 ∨ a = s0) := by native_decide

theorem g_enc_is_inert : is_inert g_enc := by decide
theorem exactly_one_inert : ∀ a : Fin 16,
    is_inert a → a = g_enc := by native_decide

/-! ## Part 5: Dichotomy (C) -/

theorem dichotomy : ∀ a x : Fin 16,
    ¬is_absorber a → ¬is_absorber x → is_boolean (psi a x) → is_tester a := by native_decide

/-! ## Part 6: Power-Associativity -/

theorem power_assoc : ∀ x : Fin 16,
    psi (psi x x) x = psi x (psi x x) := by decide
theorem not_associative : ∃ a b c : Fin 16,
    psi (psi a b) c ≠ psi a (psi b c) := by decide

/-! ## Part 7: QE Inverse -/

def in_core (x : Fin 16) : Prop := x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5
instance : DecidablePred in_core := fun x =>
  inferInstanceAs (Decidable (x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))

theorem qe_roundtrip : ∀ x : Fin 16, in_core x →
    psi E (psi Q x) = x := by decide
theorem eq_roundtrip : ∀ x : Fin 16, in_core x →
    psi Q (psi E x) = x := by decide
theorem e_transparent_top : psi E top = top := by decide
theorem e_transparent_bot : psi E bot = bot := by decide

/-! ## Part 8: Computational Structure -/

theorem branch_true : ∀ x : Fin 16, in_core x →
    psi tau x = top → psi rho x = psi f_enc x := by decide
theorem branch_false : ∀ x : Fin 16, in_core x →
    psi tau x = bot → psi rho x = psi g_enc x := by decide
theorem f_g_differ : ∃ x : Fin 16, in_core x ∧ psi f_enc x ≠ psi g_enc x := by decide
theorem compose_def : ∀ x : Fin 16, in_core x →
    psi eta x = psi rho (psi g_enc x) := by decide
theorem y_fixed : psi Y_fix rho = psi rho (psi Y_fix rho) := by decide
theorem y_fixed_value : psi Y_fix rho = x5 := by decide
theorem selection_axiom : psi eta rho = tau := by decide

/-! ## Part 9: INC Counter (8-state) -/

-- Cycle: s0(12) → s1(14) → s2(6) → s3(11) → s4(10) → s5(15) → s6(8) → s7(7) → s0(12)

theorem inc_s0 : psi INC s0 = s1 := by decide
theorem inc_s1 : psi INC s1 = Q := by decide
theorem inc_s2 : psi INC Q = s3 := by decide
theorem inc_s3 : psi INC s3 = Y_fix := by decide
theorem inc_s4 : psi INC Y_fix = s5 := by decide
theorem inc_s5 : psi INC s5 = rho := by decide
theorem inc_s6 : psi INC rho = E := by decide
theorem inc_s7 : psi INC E = s0 := by decide

theorem zero_test_hit : psi tau s0 = top := by decide
theorem zero_test_s1 : psi tau s1 = bot := by decide
theorem zero_test_s2 : psi tau Q = bot := by decide
theorem zero_test_s3 : psi tau s3 = bot := by decide
theorem zero_test_s4 : psi tau Y_fix = bot := by decide
theorem zero_test_s5 : psi tau s5 = bot := by decide
theorem zero_test_s6 : psi tau rho = bot := by decide
theorem zero_test_s7 : psi tau E = bot := by decide

/-! ## Part 10: DEC Counter (reverse 8-cycle) -/

theorem dec_s0 : psi DEC s0 = E := by decide
theorem dec_s1 : psi DEC s1 = s0 := by decide
theorem dec_s2 : psi DEC Q = s1 := by decide
theorem dec_s3 : psi DEC s3 = Q := by decide
theorem dec_s4 : psi DEC Y_fix = s3 := by decide
theorem dec_s5 : psi DEC s5 = Y_fix := by decide
theorem dec_s6 : psi DEC rho = s5 := by decide
theorem dec_s7 : psi DEC E = rho := by decide

/-! ## Part 11: IO -/

theorem io_roundtrip : ∀ x : Fin 16, in_core x →
    psi GET_IO (psi PUT x) = x := by decide
theorem seq_put : psi SEQ PUT ≠ PUT := by decide
theorem seq_get : psi SEQ GET_IO ≠ GET_IO := by decide

/-! ## Part 12: PAIR/FST/SND (2×2 product on {s0,s1}) -/

-- Pair states: p00=12(s0/p00) p01=6(Q/SND/s2/p01) p10=9(η/p10) p11=11(PAIR/s3/p11)

theorem pair_s0_s0 : psi (psi PAIR_OP s0) s0 = p00 := by decide
theorem pair_s0_s1 : psi (psi PAIR_OP s0) s1 = p01 := by decide
theorem pair_s1_s0 : psi (psi PAIR_OP s1) s0 = p10 := by decide
theorem pair_s1_s1 : psi (psi PAIR_OP s1) s1 = p11 := by decide

theorem fst_p00 : psi FST_OP p00 = s0 := by decide
theorem fst_p01 : psi FST_OP p01 = s0 := by decide
theorem fst_p10 : psi FST_OP p10 = s1 := by decide
theorem fst_p11 : psi FST_OP p11 = s1 := by decide

theorem snd_p00 : psi SND_OP p00 = s0 := by decide
theorem snd_p01 : psi SND_OP p01 = s1 := by decide
theorem snd_p10 : psi SND_OP p10 = s0 := by decide
theorem snd_p11 : psi SND_OP p11 = s1 := by decide

/-! ## Part 13: INC2 (4-state sub-counter) -/

theorem inc2_s0 : psi INC2 s0 = s1 := by decide
theorem inc2_s1 : psi INC2 s1 = Q := by decide
theorem inc2_s2 : psi INC2 Q = s3 := by decide
theorem inc2_s3 : psi INC2 s3 = s0 := by decide

/-! ## Part 14: SWAP (involution on core) -/

theorem swap_2 : psi SWAP_OP (2 : Fin 16) = (5 : Fin 16) := by decide
theorem swap_3 : psi SWAP_OP (3 : Fin 16) = (4 : Fin 16) := by decide
theorem swap_4 : psi SWAP_OP (4 : Fin 16) = (3 : Fin 16) := by decide
theorem swap_5 : psi SWAP_OP (5 : Fin 16) = (2 : Fin 16) := by decide
theorem swap_involution : ∀ x : Fin 16, in_core x →
    psi SWAP_OP (psi SWAP_OP x) = x := by decide

/-! ## Part 15: Rigidity -/

theorem fingerprint_unique : ∀ a b : Fin 16, a ≠ b →
    (∃ x, psi a x ≠ psi b x) ∨ (∃ x, psi x a ≠ psi x b) := by decide
theorem row_injective : ∀ a b : Fin 16,
    (∀ x : Fin 16, psi a x = psi b x) → a = b := by decide

/-! ## Part 16: Constructibility -/

theorem fully_producible : ∀ z : Fin 16,
    ∃ a b : Fin 16, psi a b = z := by decide

private def gen_set_0 : Finset (Fin 16) := {top, bot, Q, E}
private def gen_close (S : Finset (Fin 16)) : Finset (Fin 16) :=
  S ∪ Finset.univ.filter (fun z => ∃ a ∈ S, ∃ b ∈ S, psi a b = z)
private def gen_iter : Nat → Finset (Fin 16)
  | 0 => gen_set_0
  | n + 1 => gen_close (gen_iter n)

set_option maxHeartbeats 3200000 in
theorem generates_all : gen_iter 4 = Finset.univ := by native_decide

/-! ## Part 17: Idempotents -/

theorem idem_top : psi top top = top := by decide
theorem idem_bot : psi bot bot = bot := by decide
theorem exactly_2_idempotents : ∀ a : Fin 16,
    psi a a = a → (a = top ∨ a = bot) := by decide

/-! ## Part 18: Additional Properties -/

theorem vv_axiom : ∀ v : Fin 16,
    is_inert v → (is_tester (psi v v) ∨ is_encoder (psi v v)) := by native_decide
theorem inert_propagation : ∀ v x : Fin 16,
    is_inert v → ¬is_absorber x → psi v x ≥ 2 := by native_decide

theorem not_assoc_witness : psi (psi f_enc top) top ≠ psi f_enc (psi top top) := by decide

end Psi16Full

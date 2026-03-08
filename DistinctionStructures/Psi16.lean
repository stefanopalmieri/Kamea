/- # Ψ₁₆ — The 16-element self-describing algebra

   Machine verification of the concrete 16×16 Cayley table extracted from
   the full Phase 5 constraint set (L8+C+D+PA+VV+QE+1-inert+E-trans +
   Branch+Compose+Y + IO PUT/GET/SEQ + 8-state counter with INC + τ zero-test)
   plus the selection axiom η·ρ = τ.

   All proofs are computational: `decide` or `native_decide`.
-/

import Mathlib.Data.Fintype.Basic

set_option maxHeartbeats 800000

namespace Psi16

/-! ## Part 1: The Cayley Table -/

/-- Raw Cayley table as Nat → Nat → Nat for efficient pattern matching. -/
private def rawPsi : Nat → Nat → Nat
  -- Row 0: ⊤ (absorber)
  | 0, _ => 0
  -- Row 1: ⊥ (absorber)
  | 1, _ => 1
  -- Row 2: f(enc) / PUT
  | 2, 0 => 1 | 2, 1 => 11 | 2, 2 => 9 | 2, 3 => 15 | 2, 4 => 11 | 2, 5 => 5
  | 2, 6 => 3 | 2, 7 => 13 | 2, 8 => 8 | 2, 9 => 12 | 2, 10 => 10 | 2, 11 => 4
  | 2, 12 => 6 | 2, 13 => 2 | 2, 14 => 14 | 2, 15 => 7
  -- Row 3: τ (tester)
  | 3, 0 => 1 | 3, 1 => 1 | 3, 2 => 0 | 3, 3 => 1 | 3, 4 => 1 | 3, 5 => 0
  | 3, 6 => 1 | 3, 7 => 0 | 3, 8 => 1 | 3, 9 => 0 | 3, 10 => 1 | 3, 11 => 1
  | 3, 12 => 1 | 3, 13 => 0 | 3, 14 => 1 | 3, 15 => 1
  -- Row 4: g(enc) / GET
  | 4, 0 => 15 | 4, 1 => 0 | 4, 2 => 6 | 4, 3 => 9 | 4, 4 => 14 | 4, 5 => 5
  | 4, 6 => 2 | 4, 7 => 2 | 4, 8 => 11 | 4, 9 => 2 | 4, 10 => 9 | 4, 11 => 4
  | 4, 12 => 6 | 4, 13 => 10 | 4, 14 => 14 | 4, 15 => 3
  -- Row 5: x5 (encoder)
  | 5, 0 => 14 | 5, 1 => 1 | 5, 2 => 9 | 5, 3 => 2 | 5, 4 => 10 | 5, 5 => 5
  | 5, 6 => 11 | 5, 7 => 3 | 5, 8 => 8 | 5, 9 => 2 | 5, 10 => 5 | 5, 11 => 5
  | 5, 12 => 12 | 5, 13 => 11 | 5, 14 => 15 | 5, 15 => 8
  -- Row 6: Q (quote) / s4
  | 6, 0 => 0 | 6, 1 => 0 | 6, 2 => 5 | 6, 3 => 14 | 6, 4 => 2 | 6, 5 => 12
  | 6, 6 => 4 | 6, 7 => 10 | 6, 8 => 7 | 6, 9 => 3 | 6, 10 => 4 | 6, 11 => 7
  | 6, 12 => 3 | 6, 13 => 6 | 6, 14 => 4 | 6, 15 => 3
  -- Row 7: E (eval)
  | 7, 0 => 0 | 7, 1 => 1 | 7, 2 => 4 | 7, 3 => 15 | 7, 4 => 6 | 7, 5 => 2
  | 7, 6 => 15 | 7, 7 => 15 | 7, 8 => 10 | 7, 9 => 12 | 7, 10 => 7 | 7, 11 => 12
  | 7, 12 => 5 | 7, 13 => 15 | 7, 14 => 3 | 7, 15 => 2
  -- Row 8: ρ (branch) / s2
  | 8, 0 => 12 | 8, 1 => 1 | 8, 2 => 9 | 8, 3 => 9 | 8, 4 => 14 | 8, 5 => 5
  | 8, 6 => 12 | 8, 7 => 7 | 8, 8 => 8 | 8, 9 => 8 | 8, 10 => 2 | 8, 11 => 7
  | 8, 12 => 4 | 8, 13 => 10 | 8, 14 => 11 | 8, 15 => 2
  -- Row 9: η (compose) / s0
  | 9, 0 => 10 | 9, 1 => 1 | 9, 2 => 12 | 9, 3 => 8 | 9, 4 => 11 | 9, 5 => 5
  | 9, 6 => 15 | 9, 7 => 5 | 9, 8 => 3 | 9, 9 => 12 | 9, 10 => 9 | 9, 11 => 4
  | 9, 12 => 4 | 9, 13 => 4 | 9, 14 => 3 | 9, 15 => 2
  -- Row 10: Y (fix) / s7
  | 10, 0 => 7 | 10, 1 => 1 | 10, 2 => 7 | 10, 3 => 7 | 10, 4 => 7 | 10, 5 => 7
  | 10, 6 => 7 | 10, 7 => 7 | 10, 8 => 7 | 10, 9 => 7 | 10, 10 => 7 | 10, 11 => 7
  | 10, 12 => 7 | 10, 13 => 7 | 10, 14 => 7 | 10, 15 => 7
  -- Row 11: s5 (tester)
  | 11, 0 => 0 | 11, 1 => 1 | 11, 2 => 1 | 11, 3 => 1 | 11, 4 => 1 | 11, 5 => 0
  | 11, 6 => 0 | 11, 7 => 1 | 11, 8 => 1 | 11, 9 => 1 | 11, 10 => 0 | 11, 11 => 0
  | 11, 12 => 0 | 11, 13 => 1 | 11, 14 => 0 | 11, 15 => 0
  -- Row 12: s6 (encoder)
  | 12, 0 => 1 | 12, 1 => 14 | 12, 2 => 6 | 12, 3 => 2 | 12, 4 => 4 | 12, 5 => 3
  | 12, 6 => 3 | 12, 7 => 13 | 12, 8 => 5 | 12, 9 => 4 | 12, 10 => 13 | 12, 11 => 13
  | 12, 12 => 6 | 12, 13 => 10 | 12, 14 => 4 | 12, 15 => 2
  -- Row 13: INC (encoder)
  | 13, 0 => 13 | 13, 1 => 1 | 13, 2 => 9 | 13, 3 => 8 | 13, 4 => 11 | 13, 5 => 2
  | 13, 6 => 11 | 13, 7 => 2 | 13, 8 => 15 | 13, 9 => 14 | 13, 10 => 9 | 13, 11 => 12
  | 13, 12 => 10 | 13, 13 => 15 | 13, 14 => 8 | 13, 15 => 6
  -- Row 14: s1 (encoder)
  | 14, 0 => 9 | 14, 1 => 0 | 14, 2 => 13 | 14, 3 => 3 | 14, 4 => 14 | 14, 5 => 6
  | 14, 6 => 15 | 14, 7 => 11 | 14, 8 => 12 | 14, 9 => 12 | 14, 10 => 5 | 14, 11 => 2
  | 14, 12 => 10 | 14, 13 => 12 | 14, 14 => 4 | 14, 15 => 8
  -- Row 15: SEQ / s3 (encoder)
  | 15, 0 => 1 | 15, 1 => 2 | 15, 2 => 3 | 15, 3 => 12 | 15, 4 => 6 | 15, 5 => 2
  | 15, 6 => 7 | 15, 7 => 2 | 15, 8 => 2 | 15, 9 => 2 | 15, 10 => 7 | 15, 11 => 6
  | 15, 12 => 2 | 15, 13 => 6 | 15, 14 => 2 | 15, 15 => 10
  -- Default (unreachable for Fin 16)
  | _, _ => 0

private theorem rawPsi_bound (a b : Fin 16) : rawPsi a.val b.val < 16 := by
  revert a b; native_decide

/-- The Ψ₁₆ binary operation (Cayley table). -/
def psi (a b : Fin 16) : Fin 16 := ⟨rawPsi a.val b.val, rawPsi_bound a b⟩

/-! ## Part 2: Named Constants -/

abbrev top : Fin 16 := 0
abbrev bot : Fin 16 := 1
abbrev f_enc : Fin 16 := 2      -- encoder-f / PUT
abbrev tau : Fin 16 := 3        -- tester
abbrev g_enc : Fin 16 := 4      -- encoder-g / GET
abbrev x5 : Fin 16 := 5         -- encoder
abbrev Q : Fin 16 := 6          -- quote / counter s4
abbrev E : Fin 16 := 7          -- eval
abbrev rho : Fin 16 := 8        -- branch / counter s2
abbrev eta : Fin 16 := 9        -- compose / counter s0
abbrev Y : Fin 16 := 10         -- Y-combinator / counter s7
abbrev nu : Fin 16 := 11        -- counter s5 (tester in this model)
abbrev s6 : Fin 16 := 12        -- counter state 6
abbrev INC : Fin 16 := 13       -- counter increment
abbrev s1 : Fin 16 := 14        -- counter state 1
abbrev SEQ : Fin 16 := 15       -- IO sequencer / counter s3

/-! ## Part 3: Structural Axioms (L8 family) -/

/-- L0: top is left absorber. -/
theorem top_absorbs : ∀ x : Fin 16, psi top x = top := by decide

/-- L0: bot is left absorber. -/
theorem bot_absorbs : ∀ x : Fin 16, psi bot x = bot := by decide

/-- L0: No other left absorbers. -/
theorem only_two_absorbers : ∀ a : Fin 16,
    (∀ x : Fin 16, psi a x = a) → (a = top ∨ a = bot) := by decide

/-- L3: Extensionality — all rows distinct. -/
theorem ext_rows : ∀ a b : Fin 16, a ≠ b →
    ∃ x : Fin 16, psi a x ≠ psi b x := by decide

/-- All columns distinct. -/
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

/-- An encoder has ≥2 distinct non-boolean outputs. -/
def is_encoder (a : Fin 16) : Prop :=
  ¬is_absorber a ∧ ¬(∀ x : Fin 16, is_boolean (psi a x)) ∧
  ∃ x y : Fin 16, ¬is_boolean (psi a x) ∧ ¬is_boolean (psi a y) ∧ psi a x ≠ psi a y

instance : DecidablePred is_encoder := fun a =>
  inferInstanceAs (Decidable (¬is_absorber a ∧ ¬(∀ x, is_boolean (psi a x)) ∧
    ∃ x y : Fin 16, ¬is_boolean (psi a x) ∧ ¬is_boolean (psi a y) ∧ psi a x ≠ psi a y))

/-- An inert element is not absorber, not tester, not encoder. -/
def is_inert (a : Fin 16) : Prop :=
  ¬is_absorber a ∧ ¬is_tester a ∧ ¬is_encoder a

instance : DecidablePred is_inert := fun a =>
  inferInstanceAs (Decidable (¬is_absorber a ∧ ¬is_tester a ∧ ¬is_encoder a))

theorem tau_is_tester : is_tester tau := by decide
theorem nu_is_tester : is_tester nu := by decide

theorem exactly_two_testers : ∀ a : Fin 16,
    is_tester a → (a = tau ∨ a = nu) := by native_decide

/-- Y (element 10) is the unique inert element. -/
theorem y_is_inert : is_inert Y := by decide

theorem exactly_one_inert : ∀ a : Fin 16,
    is_inert a → a = Y := by native_decide

/-! ## Part 5: Kleene Constraint (C) -/

/-- Non-testers produce only non-boolean outputs on non-absorber inputs. -/
theorem kleene : ∀ a x : Fin 16,
    ¬is_absorber a → ¬is_absorber x → is_boolean (psi a x) → is_tester a := by native_decide

/-! ## Part 6: Power-Associativity (PA) -/

theorem power_assoc : ∀ x : Fin 16,
    psi (psi x x) x = psi x (psi x x) := by decide

/-- Ψ₁₆ is NOT associative. -/
theorem not_associative : ∃ a b c : Fin 16,
    psi (psi a b) c ≠ psi a (psi b c) := by decide

/-! ## Part 7: QE Inverse Pair -/

/-- Core = {2, 3, 4, 5}. -/
def in_core (x : Fin 16) : Prop := x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5

instance : DecidablePred in_core := fun x =>
  inferInstanceAs (Decidable (x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))

/-- E undoes Q on core. -/
theorem qe_roundtrip : ∀ x : Fin 16, in_core x →
    psi E (psi Q x) = x := by decide

/-- Q undoes E on core. -/
theorem eq_roundtrip : ∀ x : Fin 16, in_core x →
    psi Q (psi E x) = x := by decide

/-- E-transparency: E preserves absorbers. -/
theorem e_transparent_top : psi E top = top := by decide
theorem e_transparent_bot : psi E bot = bot := by decide

/-! ## Part 8: Computational Structure -/

/-- Branch-true: when τ·x = ⊤, ρ dispatches to f. -/
theorem branch_true : ∀ x : Fin 16, in_core x →
    psi tau x = top → psi rho x = psi f_enc x := by decide

/-- Branch-false: when τ·x = ⊥, ρ dispatches to g. -/
theorem branch_false : ∀ x : Fin 16, in_core x →
    psi tau x = bot → psi rho x = psi g_enc x := by decide

/-- f and g differ on core. -/
theorem f_g_differ : ∃ x : Fin 16, in_core x ∧ psi f_enc x ≠ psi g_enc x := by decide

/-- Compose: η·x = ρ·(g·x) on core. -/
theorem compose_def : ∀ x : Fin 16, in_core x →
    psi eta x = psi rho (psi g_enc x) := by decide

/-- Y-combinator: Y·ρ is a fixed point of ρ. -/
theorem y_fixed : psi Y rho = psi rho (psi Y rho) := by decide

/-- The Y-combinator fixed point value. -/
theorem y_fixed_value : psi Y rho = E := by decide

/-! ## Part 9: Counter (INC = element 13) -/

-- The 8-state cycle: s0(9)→s1(14)→s2(8)→s3(15)→s4(6)→s5(11)→s6(12)→s7(10)→s0(9)

theorem inc_s0 : psi INC eta = s1 := by decide        -- 9 → 14
theorem inc_s1 : psi INC s1 = rho := by decide         -- 14 → 8
theorem inc_s2 : psi INC rho = SEQ := by decide         -- 8 → 15
theorem inc_s3 : psi INC SEQ = Q := by decide           -- 15 → 6
theorem inc_s4 : psi INC Q = nu := by decide            -- 6 → 11
theorem inc_s5 : psi INC nu = s6 := by decide           -- 11 → 12
theorem inc_s6 : psi INC s6 = Y := by decide            -- 12 → 10
theorem inc_s7 : psi INC Y = eta := by decide           -- 10 → 9

-- Zero test: τ detects s0 (= η = element 9)
theorem zero_test_hit : psi tau eta = top := by decide
theorem zero_test_s1 : psi tau s1 = bot := by decide
theorem zero_test_s2 : psi tau rho = bot := by decide
theorem zero_test_s3 : psi tau SEQ = bot := by decide
theorem zero_test_s4 : psi tau Q = bot := by decide
theorem zero_test_s5 : psi tau nu = bot := by decide
theorem zero_test_s6 : psi tau s6 = bot := by decide
theorem zero_test_s7 : psi tau Y = bot := by decide

/-! ## Part 10: IO -/

-- PUT = f_enc = 2, GET = g_enc = 4, SEQ = 15
-- Data range = core = {2, 3, 4, 5}

/-- IO roundtrip: GET·(PUT·x) = x on core. -/
theorem io_roundtrip : ∀ x : Fin 16, in_core x →
    psi g_enc (psi f_enc x) = x := by decide

/-- SEQ moves PUT: SEQ·PUT ≠ PUT. -/
theorem seq_put : psi SEQ f_enc ≠ f_enc := by decide

/-- SEQ moves GET: SEQ·GET ≠ GET. -/
theorem seq_get : psi SEQ g_enc ≠ g_enc := by decide

/-! ## Part 11: Rigidity -/

/-- All row–column fingerprint pairs are distinct. -/
theorem fingerprint_unique : ∀ a b : Fin 16, a ≠ b →
    (∃ x, psi a x ≠ psi b x) ∨ (∃ x, psi x a ≠ psi x b) := by decide

/-- Row injectivity: distinct elements have distinct rows. -/
theorem row_injective : ∀ a b : Fin 16,
    (∀ x : Fin 16, psi a x = psi b x) → a = b := by decide

/-! ## Part 12: Constructibility -/

/-- Every element is producible: ∀ z, ∃ a b, psi a b = z. -/
theorem fully_producible : ∀ z : Fin 16,
    ∃ a b : Fin 16, psi a b = z := by decide

/-- {⊤,⊥,Q,E} generates all 16 elements. -/

private def gen_set_0 : Finset (Fin 16) := {top, bot, Q, E}

private def gen_close (S : Finset (Fin 16)) : Finset (Fin 16) :=
  S ∪ Finset.univ.filter (fun z =>
    ∃ a ∈ S, ∃ b ∈ S, psi a b = z)

private def gen_iter : Nat → Finset (Fin 16)
  | 0 => gen_set_0
  | n + 1 => gen_close (gen_iter n)

set_option maxHeartbeats 3200000 in
theorem generates_all : gen_iter 4 = Finset.univ := by native_decide

/-! ## Part 13: Selection Axiom -/

/-- The selection axiom: η·ρ = τ (compose of branch equals tester). -/
theorem selection_axiom : psi eta rho = tau := by decide

/-- τ·τ = ⊥ (tester self-application). -/
theorem tau_self : psi tau tau = bot := by decide

/-! ## Part 14: Idempotents -/

theorem idem_top : psi top top = top := by decide
theorem idem_bot : psi bot bot = bot := by decide
theorem idem_x5 : psi x5 x5 = x5 := by decide
theorem idem_rho : psi rho rho = rho := by decide

theorem exactly_four_idempotents : ∀ a : Fin 16,
    psi a a = a → (a = top ∨ a = bot ∨ a = x5 ∨ a = rho) := by decide

/-! ## Additional Structural Properties -/

/-- VV axiom: if v is inert, then v·v is a tester or encoder. -/
theorem vv_axiom : ∀ v : Fin 16,
    is_inert v → (is_tester (psi v v) ∨ is_encoder (psi v v)) := by native_decide

/-- D axiom: inert elements map core to core (output ≥ 2). -/
theorem inert_propagation : ∀ v x : Fin 16,
    is_inert v → ¬is_absorber x → psi v x ≥ 2 := by native_decide

/-- Ψ₁₆ is not associative: concrete witness. -/
theorem not_assoc_witness : psi (psi f_enc bot) f_enc ≠ psi f_enc (psi bot f_enc) := by decide

end Psi16

/- # Ψ₁₆ᶜ — The 16-element C-interop-optimized algebra

   Machine verification of the Ψ₁₆ᶜ Cayley table, which extends the
   axiom-forced 7-element TC core with INC/DEC/INV extension elements
   having algebraic cancellation identities:

     INC(x) = ((x - 1) & 3) + 2   on core {2,3,4,5}  (4-cycle)
     DEC(x) = ((x - 3) & 3) + 2   on core {2,3,4,5}  (reverse 4-cycle)
     INV(x) = 7 - x               on core {2,3,4,5}  (involution)

   Supercompiler cancellation rules (5 total):
     E·(Q·x) → x, Q·(E·x) → x            (QE/EQ)
     INC·(DEC·x) → x, DEC·(INC·x) → x    (cycle pairs)
     INV·(INV·x) → x                      (involution)

   All proofs are computational: `decide` or `native_decide`.
-/

import Mathlib.Data.Fintype.Basic

set_option maxHeartbeats 800000

namespace Psi16C

/-! ## Part 1: The Cayley Table -/

/-- Raw Cayley table as Nat → Nat → Nat for efficient pattern matching. -/
private def rawPsi : Nat → Nat → Nat
  -- Row 0: ⊤ (absorber)
  | 0, _ => 0
  -- Row 1: ⊥ (absorber)
  | 1, _ => 1
  -- Row 2: f (encoder)
  | 2, 0 => 1 | 2, 1 => 4 | 2, 2 => 7 | 2, 3 => 3 | 2, 4 => 12 | 2, 5 => 5
  | 2, 6 => 9 | 2, 7 => 15 | 2, 8 => 10 | 2, 9 => 15 | 2, 10 => 13 | 2, 11 => 11
  | 2, 12 => 3 | 2, 13 => 8 | 2, 14 => 14 | 2, 15 => 2
  -- Row 3: τ (tester)
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 1 | 3, 3 => 0 | 3, 4 => 0 | 3, 5 => 0
  | 3, 6 => 0 | 3, 7 => 0 | 3, 8 => 1 | 3, 9 => 0 | 3, 10 => 0 | 3, 11 => 0
  | 3, 12 => 0 | 3, 13 => 0 | 3, 14 => 0 | 3, 15 => 0
  -- Row 4: g (constant → 10, inert)
  | 4, _ => 10
  -- Row 5: x5 (tester)
  | 5, 0 => 0 | 5, 1 => 1 | 5, 2 => 0 | 5, 3 => 0 | 5, 4 => 0 | 5, 5 => 0
  | 5, 6 => 0 | 5, 7 => 0 | 5, 8 => 0 | 5, 9 => 0 | 5, 10 => 0 | 5, 11 => 1
  | 5, 12 => 0 | 5, 13 => 0 | 5, 14 => 0 | 5, 15 => 0
  -- Row 6: Q (quote)
  | 6, 0 => 1 | 6, 1 => 8 | 6, 2 => 11 | 6, 3 => 15 | 6, 4 => 10 | 6, 5 => 6
  | 6, 6 => 4 | 6, 7 => 13 | 6, 8 => 7 | 6, 9 => 4 | 6, 10 => 12 | 6, 11 => 14
  | 6, 12 => 3 | 6, 13 => 5 | 6, 14 => 9 | 6, 15 => 2
  -- Row 7: E (eval)
  | 7, 0 => 0 | 7, 1 => 1 | 7, 2 => 15 | 7, 3 => 12 | 7, 4 => 6 | 7, 5 => 13
  | 7, 6 => 5 | 7, 7 => 11 | 7, 8 => 14 | 7, 9 => 8 | 7, 10 => 4 | 7, 11 => 2
  | 7, 12 => 7 | 7, 13 => 7 | 7, 14 => 6 | 7, 15 => 3
  -- Row 8: ρ (branch)
  | 8, 0 => 7 | 8, 1 => 1 | 8, 2 => 10 | 8, 3 => 3 | 8, 4 => 12 | 8, 5 => 5
  | 8, 6 => 12 | 8, 7 => 14 | 8, 8 => 2 | 8, 9 => 4 | 8, 10 => 11 | 8, 11 => 13
  | 8, 12 => 8 | 8, 13 => 6 | 8, 14 => 14 | 8, 15 => 9
  -- Row 9: η (compose/snd)
  | 9, 0 => 4 | 9, 1 => 1 | 9, 2 => 11 | 9, 3 => 11 | 9, 4 => 11 | 9, 5 => 11
  | 9, 6 => 4 | 9, 7 => 5 | 9, 8 => 3 | 9, 9 => 6 | 9, 10 => 2 | 9, 11 => 10
  | 9, 12 => 7 | 9, 13 => 3 | 9, 14 => 13 | 9, 15 => 9
  -- Row 10: Y (encoder in Ψ₁₆ᶜ)
  | 10, 0 => 1 | 10, 1 => 8 | 10, 2 => 2 | 10, 3 => 13 | 10, 4 => 10 | 10, 5 => 7
  | 10, 6 => 7 | 10, 7 => 12 | 10, 8 => 5 | 10, 9 => 9 | 10, 10 => 14 | 10, 11 => 3
  | 10, 12 => 15 | 10, 13 => 4 | 10, 14 => 6 | 10, 15 => 11
  -- Row 11: x11 (encoder)
  | 11, 0 => 1 | 11, 1 => 6 | 11, 2 => 3 | 11, 3 => 3 | 11, 4 => 7 | 11, 5 => 3
  | 11, 6 => 11 | 11, 7 => 2 | 11, 8 => 11 | 11, 9 => 4 | 11, 10 => 8 | 11, 11 => 13
  | 11, 12 => 5 | 11, 13 => 11 | 11, 14 => 11 | 11, 15 => 3
  -- Row 12: SEQ (tester)
  | 12, 0 => 0 | 12, 1 => 0 | 12, 2 => 0 | 12, 3 => 0 | 12, 4 => 0 | 12, 5 => 0
  | 12, 6 => 1 | 12, 7 => 1 | 12, 8 => 0 | 12, 9 => 0 | 12, 10 => 0 | 12, 11 => 0
  | 12, 12 => 0 | 12, 13 => 0 | 12, 14 => 0 | 12, 15 => 0
  -- Row 13: INC (encoder, 4-cycle on core)
  | 13, 0 => 1 | 13, 1 => 2 | 13, 2 => 3 | 13, 3 => 4 | 13, 4 => 5 | 13, 5 => 2
  | 13, 6 => 14 | 13, 7 => 5 | 13, 8 => 12 | 13, 9 => 3 | 13, 10 => 13 | 13, 11 => 11
  | 13, 12 => 13 | 13, 13 => 15 | 13, 14 => 15 | 13, 15 => 5
  -- Row 14: INV (encoder, involution on core)
  | 14, 0 => 1 | 14, 1 => 0 | 14, 2 => 5 | 14, 3 => 4 | 14, 4 => 3 | 14, 5 => 2
  | 14, 6 => 10 | 14, 7 => 9 | 14, 8 => 14 | 14, 9 => 7 | 14, 10 => 6 | 14, 11 => 12
  | 14, 12 => 11 | 14, 13 => 13 | 14, 14 => 8 | 14, 15 => 15
  -- Row 15: DEC (encoder, reverse 4-cycle on core)
  | 15, 0 => 0 | 15, 1 => 3 | 15, 2 => 5 | 15, 3 => 2 | 15, 4 => 3 | 15, 5 => 4
  | 15, 6 => 3 | 15, 7 => 3 | 15, 8 => 5 | 15, 9 => 13 | 15, 10 => 13 | 15, 11 => 4
  | 15, 12 => 12 | 15, 13 => 5 | 15, 14 => 15 | 15, 15 => 14
  -- Default (unreachable for Fin 16)
  | _, _ => 0

private theorem rawPsi_bound (a b : Fin 16) : rawPsi a.val b.val < 16 := by
  revert a b; native_decide

/-- The Ψ₁₆ᶜ binary operation (Cayley table). -/
def psi (a b : Fin 16) : Fin 16 := ⟨rawPsi a.val b.val, rawPsi_bound a b⟩

/-! ## Part 2: Named Constants -/

abbrev top : Fin 16 := 0
abbrev bot : Fin 16 := 1
abbrev f_enc : Fin 16 := 2      -- encoder-f (fst projection)
abbrev tau : Fin 16 := 3        -- tester
abbrev g_enc : Fin 16 := 4      -- inert (constant → 10 in Ψ₁₆ᶜ)
abbrev x5 : Fin 16 := 5         -- tester
abbrev Q : Fin 16 := 6          -- quote / successor
abbrev E : Fin 16 := 7          -- eval / predecessor
abbrev rho : Fin 16 := 8        -- branch
abbrev eta : Fin 16 := 9        -- compose / snd
abbrev Y : Fin 16 := 10         -- Y-combinator (encoder in Ψ₁₆ᶜ)
abbrev x11 : Fin 16 := 11       -- encoder
abbrev SEQ : Fin 16 := 12       -- tester (boolean predicate)
abbrev INC : Fin 16 := 13       -- encoder, 4-cycle on core
abbrev INV : Fin 16 := 14       -- encoder, involution on core
abbrev DEC : Fin 16 := 15       -- encoder, reverse 4-cycle on core

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
theorem x5_is_tester : is_tester x5 := by decide
theorem seq_is_tester : is_tester SEQ := by decide

theorem exactly_three_testers : ∀ a : Fin 16,
    is_tester a → (a = tau ∨ a = x5 ∨ a = SEQ) := by native_decide

/-- g (element 4) is the unique inert element: constant output 10 ≠ 4. -/
theorem g_is_inert : is_inert g_enc := by decide

theorem exactly_one_inert : ∀ a : Fin 16,
    is_inert a → a = g_enc := by native_decide

/-! ## Part 5: Kleene Constraint (C) -/

/-- Non-testers produce only non-boolean outputs on non-absorber inputs. -/
theorem kleene : ∀ a x : Fin 16,
    ¬is_absorber a → ¬is_absorber x → is_boolean (psi a x) → is_tester a := by native_decide

/-! ## Part 6: Power-Associativity (PA) -/

theorem power_assoc : ∀ x : Fin 16,
    psi (psi x x) x = psi x (psi x x) := by decide

/-- Ψ₁₆ᶜ is NOT associative. -/
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

/-- f and g differ on core (trivially: g is constant 10). -/
theorem f_g_differ : ∃ x : Fin 16, in_core x ∧ psi f_enc x ≠ psi g_enc x := by decide

/-- Compose: η·x = ρ·(g·x) on core. -/
theorem compose_def : ∀ x : Fin 16, in_core x →
    psi eta x = psi rho (psi g_enc x) := by decide

/-- Y-combinator: Y·ρ is a fixed point of ρ. -/
theorem y_fixed : psi Y rho = psi rho (psi Y rho) := by decide

/-- The Y-combinator fixed point value. -/
theorem y_fixed_value : psi Y rho = x5 := by decide

/-! ## Part 9: INC/DEC/INV — Extension Elements -/

/-- INC is a 4-cycle on core: 2→3→4→5→2. -/
theorem inc_cycle_2 : psi INC f_enc = tau := by decide       -- 2 → 3
theorem inc_cycle_3 : psi INC tau = g_enc := by decide       -- 3 → 4
theorem inc_cycle_4 : psi INC g_enc = x5 := by decide        -- 4 → 5
theorem inc_cycle_5 : psi INC x5 = f_enc := by decide        -- 5 → 2

/-- DEC is the reverse 4-cycle on core: 2→5→4→3→2. -/
theorem dec_cycle_2 : psi DEC f_enc = x5 := by decide        -- 2 → 5
theorem dec_cycle_3 : psi DEC tau = f_enc := by decide        -- 3 → 2
theorem dec_cycle_4 : psi DEC g_enc = tau := by decide        -- 4 → 3
theorem dec_cycle_5 : psi DEC x5 = g_enc := by decide        -- 5 → 4

/-- INV is an involution on core: INV·x = 7−x. -/
theorem inv_core_2 : psi INV f_enc = x5 := by decide         -- 2 → 5
theorem inv_core_3 : psi INV tau = g_enc := by decide         -- 3 → 4
theorem inv_core_4 : psi INV g_enc = tau := by decide         -- 4 → 3
theorem inv_core_5 : psi INV x5 = f_enc := by decide         -- 5 → 2

/-- Cancellation: INC·(DEC·x) = x on core. -/
theorem inc_dec_cancel : ∀ x : Fin 16, in_core x →
    psi INC (psi DEC x) = x := by decide

/-- Cancellation: DEC·(INC·x) = x on core. -/
theorem dec_inc_cancel : ∀ x : Fin 16, in_core x →
    psi DEC (psi INC x) = x := by decide

/-- INV is a global involution: INV·(INV·x) = x for all x. -/
theorem inv_involution : ∀ x : Fin 16, psi INV (psi INV x) = x := by decide

/-! ## Part 10: Rigidity -/

/-- All row–column fingerprint pairs are distinct. -/
theorem fingerprint_unique : ∀ a b : Fin 16, a ≠ b →
    (∃ x, psi a x ≠ psi b x) ∨ (∃ x, psi x a ≠ psi x b) := by decide

/-- Row injectivity: distinct elements have distinct rows. -/
theorem row_injective : ∀ a b : Fin 16,
    (∀ x : Fin 16, psi a x = psi b x) → a = b := by decide

/-! ## Part 11: Constructibility -/

/-- Every element is producible: ∀ z, ∃ a b, psi a b = z. -/
theorem fully_producible : ∀ z : Fin 16,
    ∃ a b : Fin 16, psi a b = z := by decide

/-- {⊤,⊥,Q,E} generates all 16 elements in 4 closure steps. -/

private def gen_set_0 : Finset (Fin 16) := {top, bot, Q, E}

private def gen_close (S : Finset (Fin 16)) : Finset (Fin 16) :=
  S ∪ Finset.univ.filter (fun z =>
    ∃ a ∈ S, ∃ b ∈ S, psi a b = z)

private def gen_iter : Nat → Finset (Fin 16)
  | 0 => gen_set_0
  | n + 1 => gen_close (gen_iter n)

set_option maxHeartbeats 3200000 in
theorem generates_all : gen_iter 4 = Finset.univ := by native_decide

/-! ## Part 12: Selection Axiom -/

/-- The selection axiom: η·ρ = τ (compose of branch equals tester). -/
theorem selection_axiom : psi eta rho = tau := by decide

/-- τ·τ = ⊤ (tester self-application). -/
theorem tau_self : psi tau tau = top := by decide

/-! ## Part 13: Idempotents -/

theorem idem_top : psi top top = top := by decide
theorem idem_bot : psi bot bot = bot := by decide

/-- Only absorbers are idempotent in Ψ₁₆ᶜ (contrast with 4 in Ψ₁₆). -/
theorem exactly_two_idempotents : ∀ a : Fin 16,
    psi a a = a → (a = top ∨ a = bot) := by decide

/-! ## Additional Structural Properties -/

/-- VV axiom: if v is inert, then v·v is a tester or encoder. -/
theorem vv_axiom : ∀ v : Fin 16,
    is_inert v → (is_tester (psi v v) ∨ is_encoder (psi v v)) := by native_decide

/-- D axiom: inert elements map core to core (output ≥ 2). -/
theorem inert_propagation : ∀ v x : Fin 16,
    is_inert v → ¬is_absorber x → psi v x ≥ 2 := by native_decide

/-- Ψ₁₆ᶜ is not associative: concrete witness. -/
theorem not_assoc_witness : psi (psi f_enc bot) f_enc ≠ psi f_enc (psi bot f_enc) := by decide

/-- g is constant: ∀ x, g·x = Y (element 10). -/
theorem g_constant : ∀ x : Fin 16, psi g_enc x = Y := by decide

end Psi16C

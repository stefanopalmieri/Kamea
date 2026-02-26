/- # Δ₂+74181+IO Recovery — Discoverability Lemmas for 47-Atom Extension

   This file proves that all 47 atoms of the Δ₂+74181+IO extension are
   uniquely recoverable via two phases:

   Phase 1 (atom-level): 22 atoms (16 nibbles, 3 ALU dispatch, 2 ALU predicates,
   N_SUCC) are each uniquely identified by algebraic properties of `dot74181`.

   Phase 2 (term-level): 8 opaque atoms (QUOTE, EVAL, APP, UNAPP, IO_PUT,
   IO_GET, IO_RDY, IO_SEQ) all have identical all-p Cayley rows at atom level.
   They are uniquely identified via `dot47_ext`, the term-level extension that
   includes structured values (Quote, AppNode, Partial, Bundle, IOPutPartial,
   IOSeqPartial).

   Combined with the Δ₁ recovery results (Discoverable.lean), this establishes
   that all 47 atoms are recoverable from black-box access.

   Atom-level proofs close by `native_decide` over A74181 (47 elements).
   Term-level proofs close by `native_decide` over A74181 (47 elements)
   with dot47_ext producing T47 terms.
-/

import DistinctionStructures.Delta1

set_option linter.constructorNameAsVariable false

/-! ## The 47-atom type -/

/-- The 47 atoms of Δ₂+74181+IO. -/
inductive A74181 where
  | top | bot | i | k | a | b
  | e_I | e_D | e_M | e_Sigma | e_Delta
  | d_I | d_K | m_I | m_K | s_C | p
  | QUOTE | EVAL | APP | UNAPP
  | N0 | N1 | N2 | N3 | N4 | N5 | N6 | N7
  | N8 | N9 | NA | NB | NC | ND | NE | NF
  | ALU_LOGIC | ALU_ARITH | ALU_ARITHC
  | ALU_ZERO | ALU_COUT
  | N_SUCC
  | IO_PUT | IO_GET | IO_RDY | IO_SEQ
  deriving DecidableEq, Repr

set_option maxHeartbeats 800000 in
instance : Fintype A74181 where
  elems := {.top, .bot, .i, .k, .a, .b, .e_I, .e_D, .e_M, .e_Sigma, .e_Delta, .d_I, .d_K, .m_I, .m_K, .s_C, .p, .QUOTE, .EVAL, .APP, .UNAPP, .N0, .N1, .N2, .N3, .N4, .N5, .N6, .N7, .N8, .N9, .NA, .NB, .NC, .ND, .NE, .NF, .ALU_LOGIC, .ALU_ARITH, .ALU_ARITHC, .ALU_ZERO, .ALU_COUT, .N_SUCC, .IO_PUT, .IO_GET, .IO_RDY, .IO_SEQ}
  complete := by intro x; cases x <;> simp

/-! ## The Cayley table -/

/-- The atom-level Cayley table for Δ₂+74181+IO (47×47 = 2209 entries). -/
def dot74181 : A74181 → A74181 → A74181
  -- D1 Block A: Boolean absorption
  | .top, _ => .top
  | .bot, _ => .bot
  -- D1 Block B: Testers
  | .e_I, .i => .top
  | .e_I, .k => .top
  | .e_I, _ => .bot
  | .d_K, .a => .top
  | .d_K, .b => .top
  | .d_K, _ => .bot
  | .m_K, .a => .top
  | .m_K, _ => .bot
  | .m_I, .p => .bot
  | .m_I, _ => .top
  -- D1 Block C: Structural encoders
  | .e_D, .i => .d_I
  | .e_D, .k => .d_K
  | .e_M, .i => .m_I
  | .e_M, .k => .m_K
  | .e_Sigma, .s_C => .e_Delta
  | .e_Delta, .e_D => .d_I
  -- D1 Block D: Absorption breaker
  | .p, .top => .top
  -- D1 Block E: Passive self-identification
  | .i, .top => .i
  | .k, .top => .k
  | .a, .top => .a
  | .b, .top => .b
  | .d_I, .top => .d_I
  | .s_C, .top => .s_C
  -- D2 atoms: all return p at atom level
  | .QUOTE, _ => .p
  | .EVAL, _ => .p
  | .APP, _ => .p
  | .UNAPP, _ => .p
  -- Nibble self-id on ⊤
  | .N0, .top => .N0
  | .N1, .top => .N1
  | .N2, .top => .N2
  | .N3, .top => .N3
  | .N4, .top => .N4
  | .N5, .top => .N5
  | .N6, .top => .N6
  | .N7, .top => .N7
  | .N8, .top => .N8
  | .N9, .top => .N9
  | .NA, .top => .NA
  | .NB, .top => .NB
  | .NC, .top => .NC
  | .ND, .top => .ND
  | .NE, .top => .NE
  | .NF, .top => .NF
  -- Nibble × Nibble: Z/16Z addition mod 16
  | .N0, .N0 => .N0
  | .N0, .N1 => .N1
  | .N0, .N2 => .N2
  | .N0, .N3 => .N3
  | .N0, .N4 => .N4
  | .N0, .N5 => .N5
  | .N0, .N6 => .N6
  | .N0, .N7 => .N7
  | .N0, .N8 => .N8
  | .N0, .N9 => .N9
  | .N0, .NA => .NA
  | .N0, .NB => .NB
  | .N0, .NC => .NC
  | .N0, .ND => .ND
  | .N0, .NE => .NE
  | .N0, .NF => .NF
  | .N1, .N0 => .N1
  | .N1, .N1 => .N2
  | .N1, .N2 => .N3
  | .N1, .N3 => .N4
  | .N1, .N4 => .N5
  | .N1, .N5 => .N6
  | .N1, .N6 => .N7
  | .N1, .N7 => .N8
  | .N1, .N8 => .N9
  | .N1, .N9 => .NA
  | .N1, .NA => .NB
  | .N1, .NB => .NC
  | .N1, .NC => .ND
  | .N1, .ND => .NE
  | .N1, .NE => .NF
  | .N1, .NF => .N0
  | .N2, .N0 => .N2
  | .N2, .N1 => .N3
  | .N2, .N2 => .N4
  | .N2, .N3 => .N5
  | .N2, .N4 => .N6
  | .N2, .N5 => .N7
  | .N2, .N6 => .N8
  | .N2, .N7 => .N9
  | .N2, .N8 => .NA
  | .N2, .N9 => .NB
  | .N2, .NA => .NC
  | .N2, .NB => .ND
  | .N2, .NC => .NE
  | .N2, .ND => .NF
  | .N2, .NE => .N0
  | .N2, .NF => .N1
  | .N3, .N0 => .N3
  | .N3, .N1 => .N4
  | .N3, .N2 => .N5
  | .N3, .N3 => .N6
  | .N3, .N4 => .N7
  | .N3, .N5 => .N8
  | .N3, .N6 => .N9
  | .N3, .N7 => .NA
  | .N3, .N8 => .NB
  | .N3, .N9 => .NC
  | .N3, .NA => .ND
  | .N3, .NB => .NE
  | .N3, .NC => .NF
  | .N3, .ND => .N0
  | .N3, .NE => .N1
  | .N3, .NF => .N2
  | .N4, .N0 => .N4
  | .N4, .N1 => .N5
  | .N4, .N2 => .N6
  | .N4, .N3 => .N7
  | .N4, .N4 => .N8
  | .N4, .N5 => .N9
  | .N4, .N6 => .NA
  | .N4, .N7 => .NB
  | .N4, .N8 => .NC
  | .N4, .N9 => .ND
  | .N4, .NA => .NE
  | .N4, .NB => .NF
  | .N4, .NC => .N0
  | .N4, .ND => .N1
  | .N4, .NE => .N2
  | .N4, .NF => .N3
  | .N5, .N0 => .N5
  | .N5, .N1 => .N6
  | .N5, .N2 => .N7
  | .N5, .N3 => .N8
  | .N5, .N4 => .N9
  | .N5, .N5 => .NA
  | .N5, .N6 => .NB
  | .N5, .N7 => .NC
  | .N5, .N8 => .ND
  | .N5, .N9 => .NE
  | .N5, .NA => .NF
  | .N5, .NB => .N0
  | .N5, .NC => .N1
  | .N5, .ND => .N2
  | .N5, .NE => .N3
  | .N5, .NF => .N4
  | .N6, .N0 => .N6
  | .N6, .N1 => .N7
  | .N6, .N2 => .N8
  | .N6, .N3 => .N9
  | .N6, .N4 => .NA
  | .N6, .N5 => .NB
  | .N6, .N6 => .NC
  | .N6, .N7 => .ND
  | .N6, .N8 => .NE
  | .N6, .N9 => .NF
  | .N6, .NA => .N0
  | .N6, .NB => .N1
  | .N6, .NC => .N2
  | .N6, .ND => .N3
  | .N6, .NE => .N4
  | .N6, .NF => .N5
  | .N7, .N0 => .N7
  | .N7, .N1 => .N8
  | .N7, .N2 => .N9
  | .N7, .N3 => .NA
  | .N7, .N4 => .NB
  | .N7, .N5 => .NC
  | .N7, .N6 => .ND
  | .N7, .N7 => .NE
  | .N7, .N8 => .NF
  | .N7, .N9 => .N0
  | .N7, .NA => .N1
  | .N7, .NB => .N2
  | .N7, .NC => .N3
  | .N7, .ND => .N4
  | .N7, .NE => .N5
  | .N7, .NF => .N6
  | .N8, .N0 => .N8
  | .N8, .N1 => .N9
  | .N8, .N2 => .NA
  | .N8, .N3 => .NB
  | .N8, .N4 => .NC
  | .N8, .N5 => .ND
  | .N8, .N6 => .NE
  | .N8, .N7 => .NF
  | .N8, .N8 => .N0
  | .N8, .N9 => .N1
  | .N8, .NA => .N2
  | .N8, .NB => .N3
  | .N8, .NC => .N4
  | .N8, .ND => .N5
  | .N8, .NE => .N6
  | .N8, .NF => .N7
  | .N9, .N0 => .N9
  | .N9, .N1 => .NA
  | .N9, .N2 => .NB
  | .N9, .N3 => .NC
  | .N9, .N4 => .ND
  | .N9, .N5 => .NE
  | .N9, .N6 => .NF
  | .N9, .N7 => .N0
  | .N9, .N8 => .N1
  | .N9, .N9 => .N2
  | .N9, .NA => .N3
  | .N9, .NB => .N4
  | .N9, .NC => .N5
  | .N9, .ND => .N6
  | .N9, .NE => .N7
  | .N9, .NF => .N8
  | .NA, .N0 => .NA
  | .NA, .N1 => .NB
  | .NA, .N2 => .NC
  | .NA, .N3 => .ND
  | .NA, .N4 => .NE
  | .NA, .N5 => .NF
  | .NA, .N6 => .N0
  | .NA, .N7 => .N1
  | .NA, .N8 => .N2
  | .NA, .N9 => .N3
  | .NA, .NA => .N4
  | .NA, .NB => .N5
  | .NA, .NC => .N6
  | .NA, .ND => .N7
  | .NA, .NE => .N8
  | .NA, .NF => .N9
  | .NB, .N0 => .NB
  | .NB, .N1 => .NC
  | .NB, .N2 => .ND
  | .NB, .N3 => .NE
  | .NB, .N4 => .NF
  | .NB, .N5 => .N0
  | .NB, .N6 => .N1
  | .NB, .N7 => .N2
  | .NB, .N8 => .N3
  | .NB, .N9 => .N4
  | .NB, .NA => .N5
  | .NB, .NB => .N6
  | .NB, .NC => .N7
  | .NB, .ND => .N8
  | .NB, .NE => .N9
  | .NB, .NF => .NA
  | .NC, .N0 => .NC
  | .NC, .N1 => .ND
  | .NC, .N2 => .NE
  | .NC, .N3 => .NF
  | .NC, .N4 => .N0
  | .NC, .N5 => .N1
  | .NC, .N6 => .N2
  | .NC, .N7 => .N3
  | .NC, .N8 => .N4
  | .NC, .N9 => .N5
  | .NC, .NA => .N6
  | .NC, .NB => .N7
  | .NC, .NC => .N8
  | .NC, .ND => .N9
  | .NC, .NE => .NA
  | .NC, .NF => .NB
  | .ND, .N0 => .ND
  | .ND, .N1 => .NE
  | .ND, .N2 => .NF
  | .ND, .N3 => .N0
  | .ND, .N4 => .N1
  | .ND, .N5 => .N2
  | .ND, .N6 => .N3
  | .ND, .N7 => .N4
  | .ND, .N8 => .N5
  | .ND, .N9 => .N6
  | .ND, .NA => .N7
  | .ND, .NB => .N8
  | .ND, .NC => .N9
  | .ND, .ND => .NA
  | .ND, .NE => .NB
  | .ND, .NF => .NC
  | .NE, .N0 => .NE
  | .NE, .N1 => .NF
  | .NE, .N2 => .N0
  | .NE, .N3 => .N1
  | .NE, .N4 => .N2
  | .NE, .N5 => .N3
  | .NE, .N6 => .N4
  | .NE, .N7 => .N5
  | .NE, .N8 => .N6
  | .NE, .N9 => .N7
  | .NE, .NA => .N8
  | .NE, .NB => .N9
  | .NE, .NC => .NA
  | .NE, .ND => .NB
  | .NE, .NE => .NC
  | .NE, .NF => .ND
  | .NF, .N0 => .NF
  | .NF, .N1 => .N0
  | .NF, .N2 => .N1
  | .NF, .N3 => .N2
  | .NF, .N4 => .N3
  | .NF, .N5 => .N4
  | .NF, .N6 => .N5
  | .NF, .N7 => .N6
  | .NF, .N8 => .N7
  | .NF, .N9 => .N8
  | .NF, .NA => .N9
  | .NF, .NB => .NA
  | .NF, .NC => .NB
  | .NF, .ND => .NC
  | .NF, .NE => .ND
  | .NF, .NF => .NE
  -- ALU dispatch self-id on ⊤
  | .ALU_LOGIC, .top => .ALU_LOGIC
  | .ALU_ARITH, .top => .ALU_ARITH
  | .ALU_ARITHC, .top => .ALU_ARITHC
  -- ALU_LOGIC × Nibble: identity
  | .ALU_LOGIC, .N0 => .N0
  | .ALU_LOGIC, .N1 => .N1
  | .ALU_LOGIC, .N2 => .N2
  | .ALU_LOGIC, .N3 => .N3
  | .ALU_LOGIC, .N4 => .N4
  | .ALU_LOGIC, .N5 => .N5
  | .ALU_LOGIC, .N6 => .N6
  | .ALU_LOGIC, .N7 => .N7
  | .ALU_LOGIC, .N8 => .N8
  | .ALU_LOGIC, .N9 => .N9
  | .ALU_LOGIC, .NA => .NA
  | .ALU_LOGIC, .NB => .NB
  | .ALU_LOGIC, .NC => .NC
  | .ALU_LOGIC, .ND => .ND
  | .ALU_LOGIC, .NE => .NE
  | .ALU_LOGIC, .NF => .NF
  -- ALU_ARITH × Nibble: successor
  | .ALU_ARITH, .N0 => .N1
  | .ALU_ARITH, .N1 => .N2
  | .ALU_ARITH, .N2 => .N3
  | .ALU_ARITH, .N3 => .N4
  | .ALU_ARITH, .N4 => .N5
  | .ALU_ARITH, .N5 => .N6
  | .ALU_ARITH, .N6 => .N7
  | .ALU_ARITH, .N7 => .N8
  | .ALU_ARITH, .N8 => .N9
  | .ALU_ARITH, .N9 => .NA
  | .ALU_ARITH, .NA => .NB
  | .ALU_ARITH, .NB => .NC
  | .ALU_ARITH, .NC => .ND
  | .ALU_ARITH, .ND => .NE
  | .ALU_ARITH, .NE => .NF
  | .ALU_ARITH, .NF => .N0
  -- ALU_ARITHC × Nibble: double successor
  | .ALU_ARITHC, .N0 => .N2
  | .ALU_ARITHC, .N1 => .N3
  | .ALU_ARITHC, .N2 => .N4
  | .ALU_ARITHC, .N3 => .N5
  | .ALU_ARITHC, .N4 => .N6
  | .ALU_ARITHC, .N5 => .N7
  | .ALU_ARITHC, .N6 => .N8
  | .ALU_ARITHC, .N7 => .N9
  | .ALU_ARITHC, .N8 => .NA
  | .ALU_ARITHC, .N9 => .NB
  | .ALU_ARITHC, .NA => .NC
  | .ALU_ARITHC, .NB => .ND
  | .ALU_ARITHC, .NC => .NE
  | .ALU_ARITHC, .ND => .NF
  | .ALU_ARITHC, .NE => .N0
  | .ALU_ARITHC, .NF => .N1
  -- ALU predicate self-id on ⊤
  | .ALU_ZERO, .top => .ALU_ZERO
  | .ALU_COUT, .top => .ALU_COUT
  -- ALU_ZERO × Nibble: ⊤ iff N0
  | .ALU_ZERO, .N0 => .top
  | .ALU_ZERO, .N1 => .bot
  | .ALU_ZERO, .N2 => .bot
  | .ALU_ZERO, .N3 => .bot
  | .ALU_ZERO, .N4 => .bot
  | .ALU_ZERO, .N5 => .bot
  | .ALU_ZERO, .N6 => .bot
  | .ALU_ZERO, .N7 => .bot
  | .ALU_ZERO, .N8 => .bot
  | .ALU_ZERO, .N9 => .bot
  | .ALU_ZERO, .NA => .bot
  | .ALU_ZERO, .NB => .bot
  | .ALU_ZERO, .NC => .bot
  | .ALU_ZERO, .ND => .bot
  | .ALU_ZERO, .NE => .bot
  | .ALU_ZERO, .NF => .bot
  -- ALU_COUT × Nibble: ⊤ iff ≥ 8
  | .ALU_COUT, .N0 => .bot
  | .ALU_COUT, .N1 => .bot
  | .ALU_COUT, .N2 => .bot
  | .ALU_COUT, .N3 => .bot
  | .ALU_COUT, .N4 => .bot
  | .ALU_COUT, .N5 => .bot
  | .ALU_COUT, .N6 => .bot
  | .ALU_COUT, .N7 => .bot
  | .ALU_COUT, .N8 => .top
  | .ALU_COUT, .N9 => .top
  | .ALU_COUT, .NA => .top
  | .ALU_COUT, .NB => .top
  | .ALU_COUT, .NC => .top
  | .ALU_COUT, .ND => .top
  | .ALU_COUT, .NE => .top
  | .ALU_COUT, .NF => .top
  -- N_SUCC: self-id on ⊤, reset on ⊥, successor on nibbles
  | .N_SUCC, .top => .N_SUCC
  | .N_SUCC, .bot => .N0
  | .N_SUCC, .N0 => .N1
  | .N_SUCC, .N1 => .N2
  | .N_SUCC, .N2 => .N3
  | .N_SUCC, .N3 => .N4
  | .N_SUCC, .N4 => .N5
  | .N_SUCC, .N5 => .N6
  | .N_SUCC, .N6 => .N7
  | .N_SUCC, .N7 => .N8
  | .N_SUCC, .N8 => .N9
  | .N_SUCC, .N9 => .NA
  | .N_SUCC, .NA => .NB
  | .N_SUCC, .NB => .NC
  | .N_SUCC, .NC => .ND
  | .N_SUCC, .ND => .NE
  | .N_SUCC, .NE => .NF
  | .N_SUCC, .NF => .N0
  -- IO atoms: all return p at atom level (like D2 atoms)
  | .IO_PUT, _ => .p
  | .IO_GET, _ => .p
  | .IO_RDY, _ => .p
  | .IO_SEQ, _ => .p
  -- Default: everything else → p
  | _, _ => .p

/-! ## D1 fragment preservation -/

/-- Helper: embed D1ι into A74181. -/
def d1toA74181 : D1ι → A74181
  | .top => .top | .bot => .bot | .i => .i | .k => .k
  | .a => .a | .b => .b | .e_I => .e_I | .e_D => .e_D
  | .e_M => .e_M | .e_Sigma => .e_Sigma | .e_Delta => .e_Delta
  | .d_I => .d_I | .d_K => .d_K | .m_I => .m_I | .m_K => .m_K
  | .s_C => .s_C | .p => .p

/-- The D1 fragment is exactly preserved in dot74181. -/
theorem d1_fragment_preserved_74181 :
    ∀ (x y : D1ι),
      dot74181 (d1toA74181 x) (d1toA74181 y) = d1toA74181 (dot x y) := by
  intro x y; cases x <;> cases y <;> decide

/- Note: 8 atoms are indistinguishable in the atom-level Cayley table:
   QUOTE, EVAL, APP, UNAPP (D2) and IO_PUT, IO_GET, IO_RDY, IO_SEQ (IO).
   All eight map every atom to p. They are separable at the term level via
   structured values, as proved below (dot47_ext / T47).
   The 39 non-opaque atoms ARE pairwise separable at the atom level. -/

/-! ## Nibble group (Z/16Z) properties -/

/-- N0 is the identity of the nibble group. -/
theorem nibble_identity :
    ∀ n : A74181, (n = .N0 ∨ n = .N1 ∨ n = .N2 ∨ n = .N3 ∨
      n = .N4 ∨ n = .N5 ∨ n = .N6 ∨ n = .N7 ∨
      n = .N8 ∨ n = .N9 ∨ n = .NA ∨ n = .NB ∨
      n = .NC ∨ n = .ND ∨ n = .NE ∨ n = .NF) →
    dot74181 .N0 n = n := by
  intro n hn; rcases hn with h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- N_SUCC forms a 16-cycle over nibbles. -/
theorem n_succ_cycle :
    dot74181 .N_SUCC .N0 = .N1 ∧ dot74181 .N_SUCC .N1 = .N2 ∧
    dot74181 .N_SUCC .N2 = .N3 ∧ dot74181 .N_SUCC .N3 = .N4 ∧
    dot74181 .N_SUCC .N4 = .N5 ∧ dot74181 .N_SUCC .N5 = .N6 ∧
    dot74181 .N_SUCC .N6 = .N7 ∧ dot74181 .N_SUCC .N7 = .N8 ∧
    dot74181 .N_SUCC .N8 = .N9 ∧ dot74181 .N_SUCC .N9 = .NA ∧
    dot74181 .N_SUCC .NA = .NB ∧ dot74181 .N_SUCC .NB = .NC ∧
    dot74181 .N_SUCC .NC = .ND ∧ dot74181 .N_SUCC .ND = .NE ∧
    dot74181 .N_SUCC .NE = .NF ∧ dot74181 .N_SUCC .NF = .N0 := by
  decide

/-! ## Nibble uniqueness theorems -/

/-- N0 is the unique atom mapped to ⊤ by ALU_ZERO. -/
theorem N0_uniqueness :
    ∀ x : A74181, dot74181 .ALU_ZERO x = .top ↔ x = .N0 := by
  intro x; cases x <;> native_decide

/-- N1 is the unique atom x where N_SUCC · x = N2. -/
theorem N1_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .N2 ↔ x = .N1 := by
  intro x; cases x <;> native_decide

/-- N2 is the unique atom x where N_SUCC · x = N3. -/
theorem N2_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .N3 ↔ x = .N2 := by
  intro x; cases x <;> native_decide

/-- N3 is the unique atom x where N_SUCC · x = N4. -/
theorem N3_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .N4 ↔ x = .N3 := by
  intro x; cases x <;> native_decide

/-- N4 is the unique atom x where N_SUCC · x = N5. -/
theorem N4_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .N5 ↔ x = .N4 := by
  intro x; cases x <;> native_decide

/-- N5 is the unique atom x where N_SUCC · x = N6. -/
theorem N5_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .N6 ↔ x = .N5 := by
  intro x; cases x <;> native_decide

/-- N6 is the unique atom x where N_SUCC · x = N7. -/
theorem N6_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .N7 ↔ x = .N6 := by
  intro x; cases x <;> native_decide

/-- N7 is the unique atom x where N_SUCC · x = N8. -/
theorem N7_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .N8 ↔ x = .N7 := by
  intro x; cases x <;> native_decide

/-- N8 is the unique atom x where N_SUCC · x = N9. -/
theorem N8_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .N9 ↔ x = .N8 := by
  intro x; cases x <;> native_decide

/-- N9 is the unique atom x where N_SUCC · x = NA. -/
theorem N9_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .NA ↔ x = .N9 := by
  intro x; cases x <;> native_decide

/-- NA is the unique atom x where N_SUCC · x = NB. -/
theorem NA_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .NB ↔ x = .NA := by
  intro x; cases x <;> native_decide

/-- NB is the unique atom x where N_SUCC · x = NC. -/
theorem NB_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .NC ↔ x = .NB := by
  intro x; cases x <;> native_decide

/-- NC is the unique atom x where N_SUCC · x = ND. -/
theorem NC_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .ND ↔ x = .NC := by
  intro x; cases x <;> native_decide

/-- ND is the unique atom x where N_SUCC · x = NE. -/
theorem ND_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .NE ↔ x = .ND := by
  intro x; cases x <;> native_decide

/-- NE is the unique atom x where N_SUCC · x = NF. -/
theorem NE_uniqueness :
    ∀ x : A74181, dot74181 .N_SUCC x = .NF ↔ x = .NE := by
  intro x; cases x <;> native_decide

/-- NF is the unique atom x where N_SUCC · x = N0 and ALU_ZERO · x = ⊥. -/
theorem NF_uniqueness :
    ∀ x : A74181,
      (dot74181 .N_SUCC x = .N0 ∧ dot74181 .ALU_ZERO x = .bot) ↔ x = .NF := by
  intro x; cases x <;> native_decide

/-! ## ALU dispatch uniqueness theorems -/

/-- ALU_LOGIC is the unique atom acting as identity on nibbles with dot(x,x) = p. -/
theorem ALU_LOGIC_uniqueness :
    ∀ x : A74181,
      (dot74181 x .N0 = .N0 ∧ dot74181 x .N1 = .N1 ∧ dot74181 x x = .p) ↔
      x = .ALU_LOGIC := by
  intro x; cases x <;> native_decide

/-- ALU_ARITH is the unique atom acting as successor on nibbles with dot(x,x) = p
    and dot(x, ⊥) = p (distinguishing from N_SUCC). -/
theorem ALU_ARITH_uniqueness :
    ∀ x : A74181,
      (dot74181 x .N0 = .N1 ∧ dot74181 x .N1 = .N2 ∧ dot74181 x x = .p ∧
       dot74181 x .bot = .p) ↔
      x = .ALU_ARITH := by
  intro x; cases x <;> native_decide

/-- ALU_ARITHC is the unique atom acting as double-successor on nibbles with dot(x,x) = p. -/
theorem ALU_ARITHC_uniqueness :
    ∀ x : A74181,
      (dot74181 x .N0 = .N2 ∧ dot74181 x .N1 = .N3 ∧ dot74181 x x = .p) ↔
      x = .ALU_ARITHC := by
  intro x; cases x <;> native_decide

/-! ## ALU predicate uniqueness theorems -/

/-- ALU_ZERO is the unique atom mapping N0 to ⊤ and N1 to ⊥ (zero-tester). -/
theorem ALU_ZERO_uniqueness :
    ∀ x : A74181,
      (dot74181 x .N0 = .top ∧ dot74181 x .N1 = .bot ∧ dot74181 x .top = x) ↔
      x = .ALU_ZERO := by
  intro x; cases x <;> native_decide

/-- ALU_COUT is the unique atom mapping N7 to ⊥ and N8 to ⊤ (carry/high-bit tester). -/
theorem ALU_COUT_uniqueness :
    ∀ x : A74181,
      (dot74181 x .N7 = .bot ∧ dot74181 x .N8 = .top ∧ dot74181 x .top = x) ↔
      x = .ALU_COUT := by
  intro x; cases x <;> native_decide

/-! ## N_SUCC uniqueness theorem -/

/-- N_SUCC is the unique atom acting as successor on nibbles and mapping ⊥ to N0. -/
theorem N_SUCC_uniqueness :
    ∀ x : A74181,
      (dot74181 x .N0 = .N1 ∧ dot74181 x .N1 = .N2 ∧ dot74181 x .bot = .N0) ↔
      x = .N_SUCC := by
  intro x; cases x <;> native_decide

/-! ## Phase 1 recovery theorem (22 atom-level fingerprints) -/

/-- All 22 structured atoms of the 74181 extension are uniquely recoverable
    from `dot74181` by algebraic fingerprint. -/
theorem ext74181_atoms_recoverable :
    (∀ x : A74181, dot74181 .ALU_ZERO x = .top ↔ x = .N0) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N2 ↔ x = .N1) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N3 ↔ x = .N2) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N4 ↔ x = .N3) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N5 ↔ x = .N4) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N6 ↔ x = .N5) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N7 ↔ x = .N6) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N8 ↔ x = .N7) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N9 ↔ x = .N8) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .NA ↔ x = .N9) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .NB ↔ x = .NA) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .NC ↔ x = .NB) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .ND ↔ x = .NC) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .NE ↔ x = .ND) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .NF ↔ x = .NE) ∧
    (∀ x : A74181, (dot74181 .N_SUCC x = .N0 ∧ dot74181 .ALU_ZERO x = .bot) ↔ x = .NF) ∧
    (∀ x : A74181, (dot74181 x .N0 = .N0 ∧ dot74181 x .N1 = .N1 ∧ dot74181 x x = .p) ↔ x = .ALU_LOGIC) ∧
    (∀ x : A74181, (dot74181 x .N0 = .N1 ∧ dot74181 x .N1 = .N2 ∧ dot74181 x x = .p ∧ dot74181 x .bot = .p) ↔ x = .ALU_ARITH) ∧
    (∀ x : A74181, (dot74181 x .N0 = .N2 ∧ dot74181 x .N1 = .N3 ∧ dot74181 x x = .p) ↔ x = .ALU_ARITHC) ∧
    (∀ x : A74181, (dot74181 x .N0 = .top ∧ dot74181 x .N1 = .bot ∧ dot74181 x .top = x) ↔ x = .ALU_ZERO) ∧
    (∀ x : A74181, (dot74181 x .N7 = .bot ∧ dot74181 x .N8 = .top ∧ dot74181 x .top = x) ↔ x = .ALU_COUT) ∧
    (∀ x : A74181, (dot74181 x .N0 = .N1 ∧ dot74181 x .N1 = .N2 ∧ dot74181 x .bot = .N0) ↔ x = .N_SUCC) :=
  ⟨N0_uniqueness, N1_uniqueness, N2_uniqueness, N3_uniqueness, N4_uniqueness, N5_uniqueness, N6_uniqueness, N7_uniqueness, N8_uniqueness, N9_uniqueness, NA_uniqueness, NB_uniqueness, NC_uniqueness, ND_uniqueness, NE_uniqueness, NF_uniqueness, ALU_LOGIC_uniqueness, ALU_ARITH_uniqueness, ALU_ARITHC_uniqueness, ALU_ZERO_uniqueness, ALU_COUT_uniqueness, N_SUCC_uniqueness⟩

/-! ## Phase 2: Opaque atom classification -/

/-- Exactly 8 atoms have all-p Cayley rows (the opaque class). -/
set_option maxHeartbeats 1600000 in
theorem opaque_atoms_all_p :
    ∀ x : A74181, (∀ y : A74181, dot74181 x y = .p) ↔
      (x = .QUOTE ∨ x = .EVAL ∨ x = .APP ∨ x = .UNAPP ∨
       x = .IO_PUT ∨ x = .IO_GET ∨ x = .IO_RDY ∨ x = .IO_SEQ) := by
  intro x; cases x <;> native_decide

/-! ## Term type for Phase 2 recovery -/

/-- Terms in the 47-atom system. Extends atom-level with structured values
    for D2 operations (Quote, AppNode, Partial, Bundle) and IO operations
    (IOPutPartial, IOSeqPartial). -/
inductive T47 where
  | at : A74181 → T47              -- plain atom
  | qu : A74181 → T47              -- quoted atom (from QUOTE)
  | ap : A74181 → A74181 → T47    -- application node (from APP · f then · g)
  | bu : A74181 → A74181 → T47    -- bundle (from UNAPP on ap)
  | pa : A74181 → T47              -- partial application (APP waiting for arg)
  | iop : A74181 → T47             -- IO put partial (IO_PUT waiting for lo nibble)
  | iseq : A74181 → T47            -- IO seq partial (IO_SEQ waiting for second)
  deriving DecidableEq, Repr

/-! ## Term-level operation -/

/-- The term-level operation for the 47-atom system. Extends the atom-level
    Cayley table with structured value handling for D2 and IO atoms. -/
def dot47_ext : T47 → T47 → T47
  -- QUOTE: wrap atom as quoted value
  | .at .QUOTE, .at x => .qu x
  | .at .QUOTE, _ => .at .p
  -- EVAL: unwrap quoted atom or flat-evaluate application node
  | .at .EVAL, .qu x => .at x
  | .at .EVAL, .ap f x => .at (dot74181 f x)
  | .at .EVAL, _ => .at .p
  -- APP: begin curried application
  | .at .APP, .at f => .pa f
  | .at .APP, _ => .at .p
  -- Partial application: complete the node
  | .pa f, .at x => .ap f x
  | .pa _, _ => .at .p
  -- UNAPP: decompose application node into bundle
  | .at .UNAPP, .ap f x => .bu f x
  | .at .UNAPP, _ => .at .p
  -- Bundle queries via booleans
  | .bu f _, .at .top => .at f
  | .bu _ x, .at .bot => .at x
  | .bu _ _, _ => .at .p
  -- IO_PUT: curried byte output (pure model — returns ⊤ on completion)
  | .at .IO_PUT, .at x => .iop x
  | .at .IO_PUT, _ => .at .p
  | .iop _, .at _ => .at .top
  | .iop _, _ => .at .p
  -- IO_GET: returns application node pair (deterministic stub for proofs)
  | .at .IO_GET, .at .top => .ap .N0 .N0
  | .at .IO_GET, _ => .at .p
  -- IO_RDY: readiness check (always ready)
  | .at .IO_RDY, .at .top => .at .top
  | .at .IO_RDY, _ => .at .p
  -- IO_SEQ: sequencing combinator
  | .at .IO_SEQ, .at x => .iseq x
  | .at .IO_SEQ, _ => .at .p
  | .iseq _, .at y => .at y
  | .iseq _, _ => .at .p
  -- D1/nibble/ALU atoms on structured values: inert
  | .at _, .qu _ => .at .p
  | .at _, .ap _ _ => .at .p
  | .at _, .bu _ _ => .at .p
  | .at _, .pa _ => .at .p
  | .at _, .iop _ => .at .p
  | .at _, .iseq _ => .at .p
  -- Atom-atom fallback: use the Cayley table
  | .at x, .at y => .at (dot74181 x y)
  -- Everything else
  | _, _ => .at .p

/-! ## Phase 2 uniqueness theorems (8 opaque atoms) -/

/-- QUOTE is the unique atom that maps every atom to a quoted value. -/
theorem QUOTE_uniqueness_47 :
    ∀ x : A74181, (∀ a : A74181, ∃ y : A74181, dot47_ext (.at x) (.at a) = .qu y) ↔
      x = .QUOTE := by
  intro x; cases x <;> native_decide

/-- EVAL is the unique atom that left-inverts QUOTE on atoms. -/
theorem EVAL_uniqueness_47 :
    ∀ x : A74181,
      (∀ a : A74181, dot47_ext (.at x) (dot47_ext (.at .QUOTE) (.at a)) = .at a) ↔
      x = .EVAL := by
  intro x; cases x <;> native_decide

/-- APP is the unique atom whose composed nodes UNAPP can decompose into bundles. -/
set_option maxHeartbeats 1600000 in
theorem APP_uniqueness_47 :
    ∀ x : A74181,
      (∀ f g : A74181, ∃ r s : A74181,
        dot47_ext (.at .UNAPP) (dot47_ext (dot47_ext (.at x) (.at f)) (.at g)) = .bu r s) ↔
      x = .APP := by
  intro x; cases x <;> native_decide

/-- UNAPP is the unique atom that decomposes APP-built nodes into bundles
    whose components are recoverable via boolean queries ⊤ and ⊥. -/
set_option maxHeartbeats 1600000 in
theorem UNAPP_uniqueness_47 :
    ∀ x : A74181,
      (∀ f g : A74181,
        dot47_ext (.at x) (dot47_ext (dot47_ext (.at .APP) (.at f)) (.at g)) ≠ .at .p ∧
        dot47_ext (dot47_ext (.at x) (dot47_ext (dot47_ext (.at .APP) (.at f)) (.at g))) (.at .top) = .at f ∧
        dot47_ext (dot47_ext (.at x) (dot47_ext (dot47_ext (.at .APP) (.at f)) (.at g))) (.at .bot) = .at g) ↔
      x = .UNAPP := by
  intro x; cases x <;> native_decide

/-- IO_PUT is the unique atom that produces an iop (IO put partial) term. -/
theorem IO_PUT_uniqueness :
    ∀ x : A74181,
      (∃ y : A74181, dot47_ext (.at x) (.at .N0) = .iop y) ↔
      x = .IO_PUT := by
  intro x; cases x <;> native_decide

/-- IO_GET is the unique atom that produces an ap (application node) term
    when applied to ⊤. -/
theorem IO_GET_uniqueness :
    ∀ x : A74181,
      (∃ r s : A74181, dot47_ext (.at x) (.at .top) = .ap r s) ↔
      x = .IO_GET := by
  intro x; cases x <;> native_decide

/-- IO_RDY is the unique atom with an all-p Cayley row that maps ⊤ to ⊤
    at term level. -/
theorem IO_RDY_uniqueness :
    ∀ x : A74181,
      (dot47_ext (.at x) (.at .top) = .at .top ∧ dot74181 x .top = .p) ↔
      x = .IO_RDY := by
  intro x; cases x <;> native_decide

/-- IO_SEQ is the unique atom that produces an iseq (IO seq partial) term. -/
theorem IO_SEQ_uniqueness :
    ∀ x : A74181,
      (∃ y : A74181, dot47_ext (.at x) (.at .N0) = .iseq y) ↔
      x = .IO_SEQ := by
  intro x; cases x <;> native_decide

/-! ## Full 47-atom recovery theorem -/

/-- All 47 atoms are uniquely recoverable: 17 Δ₁ atoms via dot (Discoverable.lean),
    22 structured atoms via dot74181 fingerprints (Phase 1 above), and
    8 opaque atoms via dot47_ext term-level probing (Phase 2 above). -/
theorem all_47_atoms_recoverable :
    -- Phase 1: 22 atom-level uniqueness (nibbles + ALU + N_SUCC)
    (∀ x : A74181, dot74181 .ALU_ZERO x = .top ↔ x = .N0) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N2 ↔ x = .N1) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N3 ↔ x = .N2) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N4 ↔ x = .N3) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N5 ↔ x = .N4) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N6 ↔ x = .N5) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N7 ↔ x = .N6) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N8 ↔ x = .N7) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .N9 ↔ x = .N8) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .NA ↔ x = .N9) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .NB ↔ x = .NA) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .NC ↔ x = .NB) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .ND ↔ x = .NC) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .NE ↔ x = .ND) ∧
    (∀ x : A74181, dot74181 .N_SUCC x = .NF ↔ x = .NE) ∧
    (∀ x : A74181, (dot74181 .N_SUCC x = .N0 ∧ dot74181 .ALU_ZERO x = .bot) ↔ x = .NF) ∧
    (∀ x : A74181, (dot74181 x .N0 = .N0 ∧ dot74181 x .N1 = .N1 ∧ dot74181 x x = .p) ↔ x = .ALU_LOGIC) ∧
    (∀ x : A74181, (dot74181 x .N0 = .N1 ∧ dot74181 x .N1 = .N2 ∧ dot74181 x x = .p ∧ dot74181 x .bot = .p) ↔ x = .ALU_ARITH) ∧
    (∀ x : A74181, (dot74181 x .N0 = .N2 ∧ dot74181 x .N1 = .N3 ∧ dot74181 x x = .p) ↔ x = .ALU_ARITHC) ∧
    (∀ x : A74181, (dot74181 x .N0 = .top ∧ dot74181 x .N1 = .bot ∧ dot74181 x .top = x) ↔ x = .ALU_ZERO) ∧
    (∀ x : A74181, (dot74181 x .N7 = .bot ∧ dot74181 x .N8 = .top ∧ dot74181 x .top = x) ↔ x = .ALU_COUT) ∧
    (∀ x : A74181, (dot74181 x .N0 = .N1 ∧ dot74181 x .N1 = .N2 ∧ dot74181 x .bot = .N0) ↔ x = .N_SUCC) ∧
    -- Phase 2: 8 term-level uniqueness (D2 + IO)
    (∀ x : A74181, (∀ a : A74181, ∃ y : A74181, dot47_ext (.at x) (.at a) = .qu y) ↔ x = .QUOTE) ∧
    (∀ x : A74181, (∀ a : A74181, dot47_ext (.at x) (dot47_ext (.at .QUOTE) (.at a)) = .at a) ↔ x = .EVAL) ∧
    (∀ x : A74181, (∀ f g : A74181, ∃ r s : A74181, dot47_ext (.at .UNAPP) (dot47_ext (dot47_ext (.at x) (.at f)) (.at g)) = .bu r s) ↔ x = .APP) ∧
    (∀ x : A74181, (∀ f g : A74181, dot47_ext (.at x) (dot47_ext (dot47_ext (.at .APP) (.at f)) (.at g)) ≠ .at .p ∧ dot47_ext (dot47_ext (.at x) (dot47_ext (dot47_ext (.at .APP) (.at f)) (.at g))) (.at .top) = .at f ∧ dot47_ext (dot47_ext (.at x) (dot47_ext (dot47_ext (.at .APP) (.at f)) (.at g))) (.at .bot) = .at g) ↔ x = .UNAPP) ∧
    (∀ x : A74181, (∃ y : A74181, dot47_ext (.at x) (.at .N0) = .iop y) ↔ x = .IO_PUT) ∧
    (∀ x : A74181, (∃ r s : A74181, dot47_ext (.at x) (.at .top) = .ap r s) ↔ x = .IO_GET) ∧
    (∀ x : A74181, (dot47_ext (.at x) (.at .top) = .at .top ∧ dot74181 x .top = .p) ↔ x = .IO_RDY) ∧
    (∀ x : A74181, (∃ y : A74181, dot47_ext (.at x) (.at .N0) = .iseq y) ↔ x = .IO_SEQ) :=
  ⟨N0_uniqueness, N1_uniqueness, N2_uniqueness, N3_uniqueness, N4_uniqueness,
   N5_uniqueness, N6_uniqueness, N7_uniqueness, N8_uniqueness, N9_uniqueness,
   NA_uniqueness, NB_uniqueness, NC_uniqueness, ND_uniqueness, NE_uniqueness,
   NF_uniqueness, ALU_LOGIC_uniqueness, ALU_ARITH_uniqueness, ALU_ARITHC_uniqueness,
   ALU_ZERO_uniqueness, ALU_COUT_uniqueness, N_SUCC_uniqueness,
   QUOTE_uniqueness_47, EVAL_uniqueness_47, APP_uniqueness_47, UNAPP_uniqueness_47,
   IO_PUT_uniqueness, IO_GET_uniqueness, IO_RDY_uniqueness, IO_SEQ_uniqueness⟩

/- # Kamea Recovery — Discoverability Lemmas for all 66 atoms

   This file proves that all 66 atoms of the Kamea algebra are each uniquely
   identified by a purely algebraic property of `dot_kamea` (the Cayley table).

   The key insight is QUALE: each opaque atom (D2, IO, W32, MUL) has a unique
   QUALE column entry `dot(x, QUALE) = target`, where `target` is an already-
   identified structurally-distinguishable atom. This eliminates the need for
   term-level probing — all 66 atoms are recoverable from the Cayley table alone.

   All proofs close by `native_decide` after `intro x; cases x`, reducing
   each to a finite enumeration over AKamea (66 elements).
-/

import DistinctionStructures.Delta1

set_option linter.constructorNameAsVariable false

/-! ## The 66-atom type -/

/-- The 66 atoms of the Kamea algebra. -/
inductive AKamea where
  -- D1 (17)
  | top | bot | i | k | a | b
  | e_I | e_D | e_M | e_Sigma | e_Delta
  | d_I | d_K | m_I | m_K | s_C | p
  -- D2 (4)
  | QUOTE | EVAL | APP | UNAPP
  -- Nibbles (16)
  | N0 | N1 | N2 | N3 | N4 | N5 | N6 | N7
  | N8 | N9 | NA | NB | NC | ND | NE | NF
  -- ALU (6)
  | ALU_LOGIC | ALU_ARITH | ALU_ARITHC
  | ALU_ZERO | ALU_COUT
  | N_SUCC
  -- IO (4)
  | IO_PUT | IO_GET | IO_RDY | IO_SEQ
  -- W32 (16)
  | W_PACK8 | W_LO | W_HI | W_MERGE | W_NIB
  | W_ADD | W_SUB | W_CMP
  | W_XOR | W_AND | W_OR | W_NOT
  | W_SHL | W_SHR | W_ROTL | W_ROTR
  -- MUL (2)
  | MUL16 | MAC16
  -- QUALE (1)
  | QUALE
  deriving DecidableEq, Repr

set_option maxHeartbeats 1600000 in
instance : Fintype AKamea where
  elems := {.top, .bot, .i, .k, .a, .b, .e_I, .e_D, .e_M, .e_Sigma, .e_Delta, .d_I, .d_K, .m_I, .m_K, .s_C, .p, .QUOTE, .EVAL, .APP, .UNAPP, .N0, .N1, .N2, .N3, .N4, .N5, .N6, .N7, .N8, .N9, .NA, .NB, .NC, .ND, .NE, .NF, .ALU_LOGIC, .ALU_ARITH, .ALU_ARITHC, .ALU_ZERO, .ALU_COUT, .N_SUCC, .IO_PUT, .IO_GET, .IO_RDY, .IO_SEQ, .W_PACK8, .W_LO, .W_HI, .W_MERGE, .W_NIB, .W_ADD, .W_SUB, .W_CMP, .W_XOR, .W_AND, .W_OR, .W_NOT, .W_SHL, .W_SHR, .W_ROTL, .W_ROTR, .MUL16, .MAC16, .QUALE}
  complete := by intro x; cases x <;> simp

/-! ## The Cayley table -/

/-- The atom-level Cayley table for the Kamea algebra (66x66 = 4356 entries). -/
def dot_kamea : AKamea → AKamea → AKamea
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
  -- QUALE: dot(QUALE, QUALE) = e_I, else p
  | .QUALE, .QUALE => .e_I
  | .QUALE, _ => .p
  -- Opaque atoms: QUALE column gives unique target, else p
  | .QUOTE, .QUALE => .k
  | .QUOTE, _ => .p
  | .EVAL, .QUALE => .i
  | .EVAL, _ => .p
  | .APP, .QUALE => .top
  | .APP, _ => .p
  | .UNAPP, .QUALE => .bot
  | .UNAPP, _ => .p
  | .IO_PUT, .QUALE => .e_Sigma
  | .IO_PUT, _ => .p
  | .IO_GET, .QUALE => .e_Delta
  | .IO_GET, _ => .p
  | .IO_RDY, .QUALE => .d_I
  | .IO_RDY, _ => .p
  | .IO_SEQ, .QUALE => .s_C
  | .IO_SEQ, _ => .p
  | .W_PACK8, .QUALE => .N8
  | .W_PACK8, _ => .p
  | .W_LO, .QUALE => .b
  | .W_LO, _ => .p
  | .W_HI, .QUALE => .a
  | .W_HI, _ => .p
  | .W_MERGE, .QUALE => .p
  | .W_MERGE, _ => .p
  | .W_NIB, .QUALE => .N4
  | .W_NIB, _ => .p
  | .W_ADD, .QUALE => .N_SUCC
  | .W_ADD, _ => .p
  | .W_SUB, .QUALE => .ALU_COUT
  | .W_SUB, _ => .p
  | .W_CMP, .QUALE => .ALU_ZERO
  | .W_CMP, _ => .p
  | .W_XOR, .QUALE => .N6
  | .W_XOR, _ => .p
  | .W_AND, .QUALE => .NB
  | .W_AND, _ => .p
  | .W_OR, .QUALE => .NE
  | .W_OR, _ => .p
  | .W_NOT, .QUALE => .N0
  | .W_NOT, _ => .p
  | .W_SHL, .QUALE => .ALU_ARITH
  | .W_SHL, _ => .p
  | .W_SHR, .QUALE => .ALU_LOGIC
  | .W_SHR, _ => .p
  | .W_ROTL, .QUALE => .ALU_ARITHC
  | .W_ROTL, _ => .p
  | .W_ROTR, .QUALE => .d_K
  | .W_ROTR, _ => .p
  | .MUL16, .QUALE => .N9
  | .MUL16, _ => .p
  | .MAC16, .QUALE => .NA
  | .MAC16, _ => .p
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
  -- Default: everything else → p
  | _, _ => .p

/-! ## D1 fragment preservation -/

/-- Helper: embed D1ι into AKamea. -/
def d1toAKamea : D1ι → AKamea
  | .top => .top | .bot => .bot | .i => .i | .k => .k
  | .a => .a | .b => .b | .e_I => .e_I | .e_D => .e_D
  | .e_M => .e_M | .e_Sigma => .e_Sigma | .e_Delta => .e_Delta
  | .d_I => .d_I | .d_K => .d_K | .m_I => .m_I | .m_K => .m_K
  | .s_C => .s_C | .p => .p

set_option maxHeartbeats 1600000 in
/-- The D1 fragment is exactly preserved in dot_kamea. -/
theorem d1_fragment_preserved_kamea :
    ∀ (x y : D1ι),
      dot_kamea (d1toAKamea x) (d1toAKamea y) = d1toAKamea (dot x y) := by
  intro x y; cases x <;> cases y <;> decide

/-! ## Nibble group (Z/16Z) properties -/

/-- N0 is the identity of the nibble group. -/
theorem nibble_identity :
    ∀ n : AKamea, (n = .N0 ∨ n = .N1 ∨ n = .N2 ∨ n = .N3 ∨
      n = .N4 ∨ n = .N5 ∨ n = .N6 ∨ n = .N7 ∨
      n = .N8 ∨ n = .N9 ∨ n = .NA ∨ n = .NB ∨
      n = .NC ∨ n = .ND ∨ n = .NE ∨ n = .NF) →
    dot_kamea .N0 n = n := by
  intro n hn; rcases hn with h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- N_SUCC forms a 16-cycle over nibbles. -/
theorem n_succ_cycle :
    dot_kamea .N_SUCC .N0 = .N1 ∧
    dot_kamea .N_SUCC .N1 = .N2 ∧
    dot_kamea .N_SUCC .N2 = .N3 ∧
    dot_kamea .N_SUCC .N3 = .N4 ∧
    dot_kamea .N_SUCC .N4 = .N5 ∧
    dot_kamea .N_SUCC .N5 = .N6 ∧
    dot_kamea .N_SUCC .N6 = .N7 ∧
    dot_kamea .N_SUCC .N7 = .N8 ∧
    dot_kamea .N_SUCC .N8 = .N9 ∧
    dot_kamea .N_SUCC .N9 = .NA ∧
    dot_kamea .N_SUCC .NA = .NB ∧
    dot_kamea .N_SUCC .NB = .NC ∧
    dot_kamea .N_SUCC .NC = .ND ∧
    dot_kamea .N_SUCC .ND = .NE ∧
    dot_kamea .N_SUCC .NE = .NF ∧
    dot_kamea .N_SUCC .NF = .N0 := by
  decide

/-! ## Uniqueness theorems for all 66 atoms -/

theorem top_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .top ∧ dot_kamea x .bot = .top ∧ dot_kamea x .p = .top) ↔ x = .top := by
  intro x; cases x <;> native_decide

theorem bot_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .bot ∧ dot_kamea x .i = .bot ∧ dot_kamea x .a = .bot) ↔ x = .bot := by
  intro x; cases x <;> native_decide

theorem i_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .i ↔ x = .i := by
  intro x; cases x <;> native_decide

theorem k_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .k ↔ x = .k := by
  intro x; cases x <;> native_decide

theorem a_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .a ↔ x = .a := by
  intro x; cases x <;> native_decide

theorem b_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .b ↔ x = .b := by
  intro x; cases x <;> native_decide

theorem e_I_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .bot ∧ dot_kamea x .i = .top) ↔ x = .e_I := by
  intro x; cases x <;> native_decide

theorem e_D_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .d_I) ↔ x = .e_D := by
  intro x; cases x <;> native_decide

theorem e_M_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .m_I) ↔ x = .e_M := by
  intro x; cases x <;> native_decide

theorem e_Sigma_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .e_Delta) ↔ x = .e_Sigma := by
  intro x; cases x <;> native_decide

theorem e_Delta_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .d_I) ↔ x = .e_Delta := by
  intro x; cases x <;> native_decide

theorem d_I_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .d_I ↔ x = .d_I := by
  intro x; cases x <;> native_decide

theorem d_K_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .bot ∧ dot_kamea x .i = .bot ∧ dot_kamea x .a = .top ∧ dot_kamea x .b = .top) ↔ x = .d_K := by
  intro x; cases x <;> native_decide

theorem m_I_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .top ∧ dot_kamea x .bot = .top ∧ dot_kamea x .p = .bot) ↔ x = .m_I := by
  intro x; cases x <;> native_decide

theorem m_K_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .bot ∧ dot_kamea x .i = .bot ∧ dot_kamea x .a = .top ∧ dot_kamea x .b = .bot) ↔ x = .m_K := by
  intro x; cases x <;> native_decide

theorem s_C_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .s_C ↔ x = .s_C := by
  intro x; cases x <;> native_decide

theorem p_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .top ∧ dot_kamea x .bot = .p) ↔ x = .p := by
  intro x; cases x <;> native_decide

theorem QUOTE_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .k) ↔ x = .QUOTE := by
  intro x; cases x <;> native_decide

theorem EVAL_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .i) ↔ x = .EVAL := by
  intro x; cases x <;> native_decide

theorem APP_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .top) ↔ x = .APP := by
  intro x; cases x <;> native_decide

theorem UNAPP_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .bot) ↔ x = .UNAPP := by
  intro x; cases x <;> native_decide

theorem N0_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N0 ↔ x = .N0 := by
  intro x; cases x <;> native_decide

theorem N1_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N1 ↔ x = .N1 := by
  intro x; cases x <;> native_decide

theorem N2_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N2 ↔ x = .N2 := by
  intro x; cases x <;> native_decide

theorem N3_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N3 ↔ x = .N3 := by
  intro x; cases x <;> native_decide

theorem N4_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N4 ↔ x = .N4 := by
  intro x; cases x <;> native_decide

theorem N5_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N5 ↔ x = .N5 := by
  intro x; cases x <;> native_decide

theorem N6_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N6 ↔ x = .N6 := by
  intro x; cases x <;> native_decide

theorem N7_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N7 ↔ x = .N7 := by
  intro x; cases x <;> native_decide

theorem N8_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N8 ↔ x = .N8 := by
  intro x; cases x <;> native_decide

theorem N9_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N9 ↔ x = .N9 := by
  intro x; cases x <;> native_decide

theorem NA_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .NA ↔ x = .NA := by
  intro x; cases x <;> native_decide

theorem NB_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .NB ↔ x = .NB := by
  intro x; cases x <;> native_decide

theorem NC_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .NC ↔ x = .NC := by
  intro x; cases x <;> native_decide

theorem ND_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .ND ↔ x = .ND := by
  intro x; cases x <;> native_decide

theorem NE_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .NE ↔ x = .NE := by
  intro x; cases x <;> native_decide

theorem NF_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .NF ↔ x = .NF := by
  intro x; cases x <;> native_decide

theorem ALU_LOGIC_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .ALU_LOGIC ↔ x = .ALU_LOGIC := by
  intro x; cases x <;> native_decide

theorem ALU_ARITH_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .ALU_ARITH ↔ x = .ALU_ARITH := by
  intro x; cases x <;> native_decide

theorem ALU_ARITHC_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .ALU_ARITHC ↔ x = .ALU_ARITHC := by
  intro x; cases x <;> native_decide

theorem ALU_ZERO_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .ALU_ZERO ↔ x = .ALU_ZERO := by
  intro x; cases x <;> native_decide

theorem ALU_COUT_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .ALU_COUT ↔ x = .ALU_COUT := by
  intro x; cases x <;> native_decide

theorem N_SUCC_uniqueness :
    ∀ x : AKamea, dot_kamea x .top = .N_SUCC ↔ x = .N_SUCC := by
  intro x; cases x <;> native_decide

theorem IO_PUT_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .e_Sigma) ↔ x = .IO_PUT := by
  intro x; cases x <;> native_decide

theorem IO_GET_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .e_Delta) ↔ x = .IO_GET := by
  intro x; cases x <;> native_decide

theorem IO_RDY_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .d_I) ↔ x = .IO_RDY := by
  intro x; cases x <;> native_decide

theorem IO_SEQ_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .s_C) ↔ x = .IO_SEQ := by
  intro x; cases x <;> native_decide

theorem W_PACK8_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .N8) ↔ x = .W_PACK8 := by
  intro x; cases x <;> native_decide

theorem W_LO_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .b) ↔ x = .W_LO := by
  intro x; cases x <;> native_decide

theorem W_HI_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .a) ↔ x = .W_HI := by
  intro x; cases x <;> native_decide

theorem W_MERGE_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .p) ↔ x = .W_MERGE := by
  intro x; cases x <;> native_decide

theorem W_NIB_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .N4) ↔ x = .W_NIB := by
  intro x; cases x <;> native_decide

theorem W_ADD_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .N_SUCC) ↔ x = .W_ADD := by
  intro x; cases x <;> native_decide

theorem W_SUB_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .ALU_COUT) ↔ x = .W_SUB := by
  intro x; cases x <;> native_decide

theorem W_CMP_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .ALU_ZERO) ↔ x = .W_CMP := by
  intro x; cases x <;> native_decide

theorem W_XOR_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .N6) ↔ x = .W_XOR := by
  intro x; cases x <;> native_decide

theorem W_AND_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .NB) ↔ x = .W_AND := by
  intro x; cases x <;> native_decide

theorem W_OR_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .NE) ↔ x = .W_OR := by
  intro x; cases x <;> native_decide

theorem W_NOT_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .N0) ↔ x = .W_NOT := by
  intro x; cases x <;> native_decide

theorem W_SHL_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .ALU_ARITH) ↔ x = .W_SHL := by
  intro x; cases x <;> native_decide

theorem W_SHR_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .ALU_LOGIC) ↔ x = .W_SHR := by
  intro x; cases x <;> native_decide

theorem W_ROTL_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .ALU_ARITHC) ↔ x = .W_ROTL := by
  intro x; cases x <;> native_decide

theorem W_ROTR_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .d_K) ↔ x = .W_ROTR := by
  intro x; cases x <;> native_decide

theorem MUL16_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .N9) ↔ x = .MUL16 := by
  intro x; cases x <;> native_decide

theorem MAC16_uniqueness :
    ∀ x : AKamea,
      (dot_kamea x .top = .p ∧ dot_kamea x .i = .p ∧ dot_kamea x .e_D = .p ∧ dot_kamea x .s_C = .p ∧ dot_kamea x .QUALE = .NA) ↔ x = .MAC16 := by
  intro x; cases x <;> native_decide

/-- QUALE is the unique atom where dot(x, x) = e_I. -/
theorem QUALE_uniqueness :
    ∀ x : AKamea, dot_kamea x x = .e_I ↔ x = .QUALE := by
  intro x; cases x <;> native_decide

/-! ## Directed Distinction Structure instance -/

/-- Actuality predicate for the Kamea: every atom except `p` is actual. -/
def actual_kamea (d : AKamea) : Prop := d ≠ AKamea.p

instance : DecidablePred actual_kamea := fun d => inferInstanceAs (Decidable (d ≠ AKamea.p))

/-- The 66-atom Kamea as a Directed Distinction Structure. -/
def kamea_dirDS : DirectedDS AKamea where
  actual := actual_kamea
  dot := dot_kamea

instance : DecidablePred kamea_dirDS.actual := inferInstanceAs (DecidablePred actual_kamea)

/-- A2 (Sustenance): The Kamea has actual distinctions. -/
theorem kamea_A2 : kamea_dirDS.A2 := ⟨.top, by decide⟩

/-- A5 (Selectivity): The Kamea has a non-actual distinction (p). -/
theorem kamea_A5 : kamea_dirDS.A5 := ⟨.p, by decide⟩

set_option maxHeartbeats 3200000 in
/-- Ext (Behavioral Separability): Every pair of distinct atoms in the 66-element
    Kamea is distinguishable by some right argument under `dot_kamea`.
    This is the core recoverability theorem — it means the Cayley table
    alone suffices to identify every atom. -/
theorem kamea_Ext : kamea_dirDS.Ext := by
  unfold DirectedDS.Ext
  simp only [kamea_dirDS]
  native_decide

/-! ## Intrinsic Reflexivity witness -/

/-- The Kamea carries intrinsic reflexivity: the same 13 structural elements
    from Δ₁ satisfy all homomorphism and encoding conditions within the
    full 66-atom algebra. -/
def kamea_IR : DirectedIR AKamea AKamea actual_kamea actual_kamea dot_kamea where
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

/-! ## Nibble Z/16Z group properties -/

set_option maxHeartbeats 3200000 in
/-- Nibble addition is commutative. -/
theorem nibble_commutative :
    ∀ (a b : AKamea),
      (a = .N0 ∨ a = .N1 ∨ a = .N2 ∨ a = .N3 ∨ a = .N4 ∨ a = .N5 ∨ a = .N6 ∨ a = .N7 ∨
       a = .N8 ∨ a = .N9 ∨ a = .NA ∨ a = .NB ∨ a = .NC ∨ a = .ND ∨ a = .NE ∨ a = .NF) →
      (b = .N0 ∨ b = .N1 ∨ b = .N2 ∨ b = .N3 ∨ b = .N4 ∨ b = .N5 ∨ b = .N6 ∨ b = .N7 ∨
       b = .N8 ∨ b = .N9 ∨ b = .NA ∨ b = .NB ∨ b = .NC ∨ b = .ND ∨ b = .NE ∨ b = .NF) →
      dot_kamea a b = dot_kamea b a := by
  intro a b ha hb
  rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  decide

set_option maxHeartbeats 3200000 in
/-- Nibble addition is associative. -/
theorem nibble_associative :
    ∀ (a b c : AKamea),
      (a = .N0 ∨ a = .N1 ∨ a = .N2 ∨ a = .N3 ∨ a = .N4 ∨ a = .N5 ∨ a = .N6 ∨ a = .N7 ∨
       a = .N8 ∨ a = .N9 ∨ a = .NA ∨ a = .NB ∨ a = .NC ∨ a = .ND ∨ a = .NE ∨ a = .NF) →
      (b = .N0 ∨ b = .N1 ∨ b = .N2 ∨ b = .N3 ∨ b = .N4 ∨ b = .N5 ∨ b = .N6 ∨ b = .N7 ∨
       b = .N8 ∨ b = .N9 ∨ b = .NA ∨ b = .NB ∨ b = .NC ∨ b = .ND ∨ b = .NE ∨ b = .NF) →
      (c = .N0 ∨ c = .N1 ∨ c = .N2 ∨ c = .N3 ∨ c = .N4 ∨ c = .N5 ∨ c = .N6 ∨ c = .N7 ∨
       c = .N8 ∨ c = .N9 ∨ c = .NA ∨ c = .NB ∨ c = .NC ∨ c = .ND ∨ c = .NE ∨ c = .NF) →
      dot_kamea (dot_kamea a b) c = dot_kamea a (dot_kamea b c) := by
  intro a b c ha hb hc
  rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  decide

/-- Every nibble has an additive inverse. -/
theorem nibble_inverses :
    ∀ a : AKamea,
      (a = .N0 ∨ a = .N1 ∨ a = .N2 ∨ a = .N3 ∨ a = .N4 ∨ a = .N5 ∨ a = .N6 ∨ a = .N7 ∨
       a = .N8 ∨ a = .N9 ∨ a = .NA ∨ a = .NB ∨ a = .NC ∨ a = .ND ∨ a = .NE ∨ a = .NF) →
      ∃ b : AKamea, dot_kamea a b = .N0 := by
  intro a ha
  rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact ⟨.N0, by decide⟩
  · exact ⟨.NF, by decide⟩
  · exact ⟨.NE, by decide⟩
  · exact ⟨.ND, by decide⟩
  · exact ⟨.NC, by decide⟩
  · exact ⟨.NB, by decide⟩
  · exact ⟨.NA, by decide⟩
  · exact ⟨.N9, by decide⟩
  · exact ⟨.N8, by decide⟩
  · exact ⟨.N7, by decide⟩
  · exact ⟨.N6, by decide⟩
  · exact ⟨.N5, by decide⟩
  · exact ⟨.N4, by decide⟩
  · exact ⟨.N3, by decide⟩
  · exact ⟨.N2, by decide⟩
  · exact ⟨.N1, by decide⟩

set_option maxHeartbeats 3200000 in
/-- Nibble addition is closed: nibble + nibble = nibble. -/
theorem nibble_closure :
    ∀ (a b : AKamea),
      (a = .N0 ∨ a = .N1 ∨ a = .N2 ∨ a = .N3 ∨ a = .N4 ∨ a = .N5 ∨ a = .N6 ∨ a = .N7 ∨
       a = .N8 ∨ a = .N9 ∨ a = .NA ∨ a = .NB ∨ a = .NC ∨ a = .ND ∨ a = .NE ∨ a = .NF) →
      (b = .N0 ∨ b = .N1 ∨ b = .N2 ∨ b = .N3 ∨ b = .N4 ∨ b = .N5 ∨ b = .N6 ∨ b = .N7 ∨
       b = .N8 ∨ b = .N9 ∨ b = .NA ∨ b = .NB ∨ b = .NC ∨ b = .ND ∨ b = .NE ∨ b = .NF) →
      (dot_kamea a b = .N0 ∨ dot_kamea a b = .N1 ∨ dot_kamea a b = .N2 ∨ dot_kamea a b = .N3 ∨
       dot_kamea a b = .N4 ∨ dot_kamea a b = .N5 ∨ dot_kamea a b = .N6 ∨ dot_kamea a b = .N7 ∨
       dot_kamea a b = .N8 ∨ dot_kamea a b = .N9 ∨ dot_kamea a b = .NA ∨ dot_kamea a b = .NB ∨
       dot_kamea a b = .NC ∨ dot_kamea a b = .ND ∨ dot_kamea a b = .NE ∨ dot_kamea a b = .NF) := by
  intro a b ha hb
  rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  decide

/-! ## ALU correctness theorems -/

/-- ALU_LOGIC acts as identity on all nibbles. -/
theorem alu_logic_identity :
    ∀ n : AKamea,
      (n = .N0 ∨ n = .N1 ∨ n = .N2 ∨ n = .N3 ∨ n = .N4 ∨ n = .N5 ∨ n = .N6 ∨ n = .N7 ∨
       n = .N8 ∨ n = .N9 ∨ n = .NA ∨ n = .NB ∨ n = .NC ∨ n = .ND ∨ n = .NE ∨ n = .NF) →
      dot_kamea .ALU_LOGIC n = n := by
  intro n hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  decide

/-- ALU_ARITH acts as successor (mod 16) on all nibbles. -/
theorem alu_arith_successor :
    ∀ n : AKamea,
      (n = .N0 ∨ n = .N1 ∨ n = .N2 ∨ n = .N3 ∨ n = .N4 ∨ n = .N5 ∨ n = .N6 ∨ n = .N7 ∨
       n = .N8 ∨ n = .N9 ∨ n = .NA ∨ n = .NB ∨ n = .NC ∨ n = .ND ∨ n = .NE ∨ n = .NF) →
      dot_kamea .ALU_ARITH n = dot_kamea .N1 n := by
  intro n hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  decide

/-- ALU_ARITHC acts as double-successor (mod 16) on all nibbles. -/
theorem alu_arithc_double_successor :
    ∀ n : AKamea,
      (n = .N0 ∨ n = .N1 ∨ n = .N2 ∨ n = .N3 ∨ n = .N4 ∨ n = .N5 ∨ n = .N6 ∨ n = .N7 ∨
       n = .N8 ∨ n = .N9 ∨ n = .NA ∨ n = .NB ∨ n = .NC ∨ n = .ND ∨ n = .NE ∨ n = .NF) →
      dot_kamea .ALU_ARITHC n = dot_kamea .N2 n := by
  intro n hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  decide

/-- ALU_ZERO is the zero-test predicate: true only on N0. -/
theorem alu_zero_predicate :
    (dot_kamea .ALU_ZERO .N0 = .top) ∧
    (∀ n : AKamea,
      (n = .N1 ∨ n = .N2 ∨ n = .N3 ∨ n = .N4 ∨ n = .N5 ∨ n = .N6 ∨ n = .N7 ∨
       n = .N8 ∨ n = .N9 ∨ n = .NA ∨ n = .NB ∨ n = .NC ∨ n = .ND ∨ n = .NE ∨ n = .NF) →
      dot_kamea .ALU_ZERO n = .bot) := by
  constructor
  · decide
  · intro n hn
    rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    decide

/-- ALU_COUT is the carry-out predicate: true on N8..NF (≥ 8). -/
theorem alu_cout_predicate :
    (∀ n : AKamea,
      (n = .N0 ∨ n = .N1 ∨ n = .N2 ∨ n = .N3 ∨ n = .N4 ∨ n = .N5 ∨ n = .N6 ∨ n = .N7) →
      dot_kamea .ALU_COUT n = .bot) ∧
    (∀ n : AKamea,
      (n = .N8 ∨ n = .N9 ∨ n = .NA ∨ n = .NB ∨ n = .NC ∨ n = .ND ∨ n = .NE ∨ n = .NF) →
      dot_kamea .ALU_COUT n = .top) := by
  constructor
  · intro n hn
    rcases hn with h | h | h | h | h | h | h | h <;> subst h <;> decide
  · intro n hn
    rcases hn with h | h | h | h | h | h | h | h <;> subst h <;> decide

/-! ## QUALE structural properties -/

/-- QUALE breaks symmetry: it is the only atom satisfying dot(x, x) = e_I
    (the self-encoding test), and its column provides unique targets for all
    26 opaque atoms. This is the structural ground of meaning in the Kamea. -/
theorem quale_self_encoding : dot_kamea .QUALE .QUALE = .e_I := by decide

/-- No other atom self-encodes to e_I. -/
theorem quale_self_encoding_unique :
    ∀ x : AKamea, dot_kamea x x = .e_I → x = .QUALE := by
  intro x; cases x <;> native_decide

/-- The QUALE column assigns distinct targets to distinct opaque atoms:
    among the 27 atoms whose row is identically p except on QUALE,
    the QUALE entry is unique. Proved by the individual uniqueness theorems. -/
theorem quale_column_all_distinct :
    dot_kamea .QUOTE .QUALE ≠ dot_kamea .EVAL .QUALE ∧
    dot_kamea .QUOTE .QUALE ≠ dot_kamea .APP .QUALE ∧
    dot_kamea .QUOTE .QUALE ≠ dot_kamea .UNAPP .QUALE ∧
    dot_kamea .EVAL .QUALE ≠ dot_kamea .APP .QUALE ∧
    dot_kamea .APP .QUALE ≠ dot_kamea .UNAPP .QUALE ∧
    dot_kamea .IO_PUT .QUALE ≠ dot_kamea .IO_GET .QUALE ∧
    dot_kamea .IO_PUT .QUALE ≠ dot_kamea .IO_RDY .QUALE ∧
    dot_kamea .IO_PUT .QUALE ≠ dot_kamea .IO_SEQ .QUALE ∧
    dot_kamea .MUL16 .QUALE ≠ dot_kamea .MAC16 .QUALE ∧
    dot_kamea .QUALE .QUALE ≠ dot_kamea .QUOTE .QUALE := by
  decide

/-! ## Boolean absorption -/

/-- ⊤ is a left absorber. -/
theorem top_left_absorber : ∀ x : AKamea, dot_kamea .top x = .top := by
  intro x; cases x <;> decide

/-- ⊥ is a left absorber. -/
theorem bot_left_absorber : ∀ x : AKamea, dot_kamea .bot x = .bot := by
  intro x; cases x <;> decide

/-! ## Full Kamea recovery theorem -/

/-- **Behavioral separability (Ext) for all 66 atoms.**
    Every pair of distinct atoms in the Kamea is distinguishable by some
    right argument under `dot_kamea`. Combined with the 66 individual
    uniqueness theorems, this constitutes a machine-checked proof that
    all 66 atoms are uniquely recoverable from the Cayley table alone. -/
theorem all_66_atoms_recoverable :
    ∀ x y : AKamea, x ≠ y → ∃ z : AKamea, dot_kamea x z ≠ dot_kamea y z :=
  kamea_Ext

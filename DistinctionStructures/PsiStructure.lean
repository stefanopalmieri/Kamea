/- # PsiStructure — Abstract Role Axioms for Ψ-Structures

This file defines the abstract `PsiStructure` capturing the minimal role axioms
(L0–L3) that every Ψ-class magma must satisfy:
- Two distinct absorbers (⊤, ⊥)
- A tester with boolean-valued row
- An encoder with at least one non-boolean output

These are the weakest axioms yielding interesting universal consequences
(no right identity, card ≥ 4).
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace PsiRoleAxioms

/-- A Ψ-structure on a finite type `D`: a magma with two absorbers,
    a boolean-valued tester, and an encoder with non-boolean output. -/
structure PsiStructure (D : Type) [DecidableEq D] [Fintype D] where
  dot : D → D → D
  top : D
  bot : D
  tau : D
  f_enc : D
  -- L0-L1: Absorbers
  top_absorbs : ∀ x, dot top x = top
  bot_absorbs : ∀ x, dot bot x = bot
  top_ne_bot : top ≠ bot
  -- L2: Tester (boolean-valued, non-absorber)
  tau_boolean : ∀ x, dot tau x = top ∨ dot tau x = bot
  tau_ne_top : tau ≠ top
  tau_ne_bot : tau ≠ bot
  -- L3: Encoder (non-boolean output, distinct from absorbers and tester)
  f_non_boolean : ∃ x, dot f_enc x ≠ top ∧ dot f_enc x ≠ bot
  f_ne_top : f_enc ≠ top
  f_ne_bot : f_enc ≠ bot
  f_ne_tau : f_enc ≠ tau

end PsiRoleAxioms

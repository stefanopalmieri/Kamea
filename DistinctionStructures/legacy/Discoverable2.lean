/- # Δ₂ Recovery — Discoverability Lemmas

   This file proves that the four new atoms of Δ₂ (QUOTE, EVAL, APP, UNAPP)
   are each uniquely identified by a purely algebraic property of `dot2`.
   Combined with the Δ₁ recovery results in Discoverable.lean, this establishes
   that all 21 atoms of Δ₂ are recoverable from black-box access to `dot2` alone.

   Strategy: each lemma identifies one atom as the unique element of A2
   satisfying a first-order observable property of `dot2`. All proofs close
   by `native_decide` after `intro x; cases x`, reducing each to a finite
   enumeration over A2 (21 elements).

   Note: Δ₁ recovery (Discoverable.lean) works entirely within D1ι.
   Here we work in A2 (the 21-atom type) and T2 (the 945-element term type),
   using the full `dot2` operation.
-/

import DistinctionStructures.Delta2

set_option linter.constructorNameAsVariable false

/-! ## Lemma 1: QUOTE uniqueness

   QUOTE is the unique atom that maps every atom to a `qu`-term.
   - All 17 Δ₁ atoms produce `at`-terms via the dotA fallback.
   - APP produces `pa`-terms.
   - EVAL and UNAPP produce `at .p` (dotA fallback, since they are not D1ι elements).
   - Only QUOTE produces `qu`-terms: `dot2 (at QUOTE) (at a) = qu a`.
-/

/-- QUOTE is the unique atom x such that applying x to any atom yields a quoted value. -/
theorem quote_uniqueness :
    ∀ x : A2, (∀ a : A2, ∃ y : A2, dot2 (.at x) (.at a) = .qu y) ↔ x = .QUOTE := by
  intro x; cases x <;> native_decide

/-! ## Lemma 2: EVAL uniqueness

   EVAL is the unique left-inverse of QUOTE on atoms.
   `dot2 (at EVAL) (qu a) = at a` for all atoms a.
   All other atoms map `qu a` to `at .p` (via the rule `| .at _, .qu _ => .at .p`).
-/

/-- EVAL is the unique atom x that left-inverts QUOTE: `x · (QUOTE · a) = a` for all atoms a. -/
theorem eval_uniqueness :
    ∀ x : A2,
      (∀ a : A2, dot2 (.at x) (dot2 (.at .QUOTE) (.at a)) = .at a) ↔ x = .EVAL := by
  intro x; cases x <;> native_decide

/-! ## Lemma 3: APP uniqueness

   APP is the unique atom that, when applied to a pair of atoms f and g,
   produces a node that UNAPP can decompose into a bundle.

   Proof of uniqueness:
   - APP: `dot2 (at APP) (at f) = pa f`, then `dot2 (pa f) (at g) = ap f g`,
     then `dot2 (at UNAPP) (ap f g) = bu f g`. ✓
   - All Δ₁ atoms: the dotA fallback gives `at _`, and UNAPP maps `at _` to `at .p`. ✗
   - QUOTE: produces `qu f`, which is inert under UNAPP. ✗
   - EVAL, UNAPP: produce `at .p`, which UNAPP maps to `at .p`. ✗
-/

/-- APP is the unique atom x such that UNAPP can decompose `(x · f) · g` into a bundle
    for every pair of atoms f, g. -/
theorem app_uniqueness :
    ∀ x : A2,
      (∀ f g : A2, ∃ r s : A2,
        dot2 (.at .UNAPP) (dot2 (dot2 (.at x) (.at f)) (.at g)) = .bu r s) ↔
      x = .APP := by
  intro x; cases x <;> native_decide

/-! ## Lemma 4: UNAPP uniqueness

   UNAPP is the unique atom that decomposes APP-built nodes into bundles
   queryable by the booleans ⊤ and ⊥.

   For any APP-built node `n = (APP · f) · g`:
   - `dot2 (at UNAPP) n = bu f g` (non-trivial result)
   - `dot2 (bu f g) (at top) = at f` (recovers function)
   - `dot2 (bu f g) (at bot) = at g` (recovers argument)

   All other atoms map `ap f g` to `at .p` via `| .at _, .ap _ _ => .at .p`.
-/

/-- UNAPP is the unique atom x that decomposes APP-built nodes into bundles
    whose components are recoverable via the boolean queries ⊤ and ⊥. -/
theorem unapp_uniqueness :
    ∀ x : A2,
      (∀ f g : A2,
        dot2 (.at x) (dot2 (dot2 (.at .APP) (.at f)) (.at g)) ≠ .at .p ∧
        dot2 (dot2 (.at x) (dot2 (dot2 (.at .APP) (.at f)) (.at g))) (.at .top) = .at f ∧
        dot2 (dot2 (.at x) (dot2 (dot2 (.at .APP) (.at f)) (.at g))) (.at .bot) = .at g) ↔
      x = .UNAPP := by
  intro x; cases x <;> native_decide

/-! ## Full Δ₂ recovery theorem

   All four Δ₂ atoms are jointly uniquely identified by their algebraic roles
   in `dot2`. Combined with the 8 lemmas in Discoverable.lean (which identify
   all 17 Δ₁ atoms from `dot`), this machine-checks that all 21 atoms of Δ₂
   are recoverable from black-box access to `dot2`.
-/

/-- All four Δ₂ atoms are uniquely recoverable from `dot2` by algebraic fingerprint. -/
theorem d2_atoms_recoverable :
    (∀ x : A2, (∀ a : A2, ∃ y : A2, dot2 (.at x) (.at a) = .qu y) ↔ x = .QUOTE) ∧
    (∀ x : A2,
      (∀ a : A2, dot2 (.at x) (dot2 (.at .QUOTE) (.at a)) = .at a) ↔ x = .EVAL) ∧
    (∀ x : A2,
      (∀ f g : A2, ∃ r s : A2,
        dot2 (.at .UNAPP) (dot2 (dot2 (.at x) (.at f)) (.at g)) = .bu r s) ↔
      x = .APP) ∧
    (∀ x : A2,
      (∀ f g : A2,
        dot2 (.at x) (dot2 (dot2 (.at .APP) (.at f)) (.at g)) ≠ .at .p ∧
        dot2 (dot2 (.at x) (dot2 (dot2 (.at .APP) (.at f)) (.at g))) (.at .top) = .at f ∧
        dot2 (dot2 (.at x) (dot2 (dot2 (.at .APP) (.at f)) (.at g))) (.at .bot) = .at g) ↔
      x = .UNAPP) :=
  ⟨quote_uniqueness, eval_uniqueness, app_uniqueness, unapp_uniqueness⟩

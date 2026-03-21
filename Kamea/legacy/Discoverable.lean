/- # Recovery Procedure — Discoverability Lemmas

   This file proves that the structure of Δ₁ can be recovered purely from
   the binary operation `dot`. Each lemma identifies a structural component
   from observable algebraic properties of `dot`.

   All proofs are by exhaustive computational search over the 17-element
   domain D1ι, using `decide` or `native_decide`.
-/

import Kamea.Delta1

open D1ι

/-! ## Lemma 1: Boolean uniqueness

    `top` and `bot` are the only elements x with dot x y = x for all y.
-/

/-- The booleans are exactly the left-absorbing elements. -/
theorem boolean_uniqueness :
    ∀ x : D1ι, (∀ y : D1ι, dot x y = x) ↔ (x = top ∨ x = bot) := by
  decide

/-! ## Lemma 2: Tester characterization

    e_I, d_K, m_K, m_I are the only non-boolean elements whose
    left-image is contained in {top, bot}.
-/

/-- The testers are exactly the non-boolean elements mapping everything to {top, bot}. -/
theorem tester_characterization :
    ∀ x : D1ι, x ≠ top → x ≠ bot →
      ((∀ y : D1ι, dot x y = top ∨ dot x y = bot) ↔
       (x = e_I ∨ x = d_K ∨ x = m_K ∨ x = m_I)) := by
  decide

/-! ## Lemma 3: Tester cardinality signatures

    The testers have distinct decoded-set sizes:
    - |{y | dot m_I y = top}| = 16
    - |{y | dot e_I y = top}| = 2
    - |{y | dot d_K y = top}| = 2
    - |{y | dot m_K y = top}| = 1
-/

/-- m_I accepts 16 elements. -/
theorem tester_card_m_I :
    (Finset.univ.filter (fun y => dot m_I y = top)).card = 16 := by
  native_decide

/-- e_I accepts 2 elements. -/
theorem tester_card_e_I :
    (Finset.univ.filter (fun y => dot e_I y = top)).card = 2 := by
  native_decide

/-- d_K accepts 2 elements. -/
theorem tester_card_d_K :
    (Finset.univ.filter (fun y => dot d_K y = top)).card = 2 := by
  native_decide

/-- m_K accepts 1 element. -/
theorem tester_card_m_K :
    (Finset.univ.filter (fun y => dot m_K y = top)).card = 1 := by
  native_decide

/-! ## Lemma 4: Rich vs inert discrimination

    The two 2-element testers (e_I and d_K) are distinguishable because
    Dec(e_I) = {i, k} contains elements that serve as productive
    right-arguments for non-testers, while Dec(d_K) = {a, b} does not.

    Specifically: there exists a non-tester f and an element in Dec(e_I)
    such that dot f y ∉ {top, bot, p}. No such pair exists for Dec(d_K).
-/

/-- Dec(e_I) contains productive right-arguments: dot e_D i = d_I ∉ {top, bot, p}. -/
theorem rich_context_tokens :
    ∃ f : D1ι, f ≠ top ∧ f ≠ bot ∧ f ≠ e_I ∧ f ≠ d_K ∧ f ≠ m_K ∧ f ≠ m_I ∧
      ∃ y : D1ι, dot e_I y = top ∧ dot f y ≠ top ∧ dot f y ≠ bot ∧ dot f y ≠ p := by
  exact ⟨e_D, by decide, by decide, by decide, by decide, by decide, by decide,
         i, by decide, by decide, by decide, by decide⟩

/-- Dec(d_K) does not contain productive right-arguments: for all non-testers f
    and all y ∈ Dec(d_K), dot f y ∈ {top, bot, p}. -/
theorem inert_kappa_tokens :
    ∀ f : D1ι, f ≠ top → f ≠ bot → f ≠ e_I → f ≠ d_K → f ≠ m_K → f ≠ m_I →
      ∀ y : D1ι, dot d_K y = top →
        dot f y = top ∨ dot f y = bot ∨ dot f y = p := by
  decide

/-! ## Lemma 5: Encoder asymmetry

    e_D and e_M are the only elements that map both context tokens (i, k)
    to non-trivial, non-boolean outputs. They are distinguished because
    e_M maps both to testers while e_D maps to a mixed pair.
-/

/-- e_D and e_M are exactly the elements producing non-trivial outputs on both
    context tokens. -/
theorem encoder_pair :
    ∀ x : D1ι,
      (dot x i ≠ top ∧ dot x i ≠ bot ∧ dot x i ≠ p ∧
       dot x k ≠ top ∧ dot x k ≠ bot ∧ dot x k ≠ p) ↔
      (x = e_D ∨ x = e_M) := by
  decide

/-- e_M maps both context tokens to testers (m_I and m_K are both testers).
    e_D maps k to a tester (d_K) but i to a non-tester (d_I). -/
theorem encoder_asymmetry :
    -- e_M i = m_I is a tester, e_M k = m_K is a tester
    (∀ y : D1ι, dot (dot e_M i) y = top ∨ dot (dot e_M i) y = bot) ∧
    (∀ y : D1ι, dot (dot e_M k) y = top ∨ dot (dot e_M k) y = bot) ∧
    -- e_D k = d_K is a tester, but e_D i = d_I is NOT a tester
    (∀ y : D1ι, dot (dot e_D k) y = top ∨ dot (dot e_D k) y = bot) ∧
    ¬(∀ y : D1ι, dot (dot e_D i) y = top ∨ dot (dot e_D i) y = bot) := by
  decide

/-! ## Lemma 6: Context token discrimination

    i and k are distinguished by the decoded-set sizes of their actuality
    codes: |Dec(dot e_M i)| = |Dec(m_I)| = 16 ≠ 1 = |Dec(m_K)| = |Dec(dot e_M k)|.
-/

/-- The actuality code of i has much larger decoded set than that of k. -/
theorem context_token_discrimination :
    (Finset.univ.filter (fun y => dot (dot e_M i) y = top)).card = 16 ∧
    (Finset.univ.filter (fun y => dot (dot e_M k) y = top)).card = 1 := by
  constructor <;> native_decide

/-! ## Lemma 7: Junk identification

    p is the unique element with dot m_I p = bot (m_I accepts everything except p).
-/

/-- p is the unique element rejected by m_I. -/
theorem junk_identification :
    ∀ x : D1ι, dot m_I x = bot ↔ x = p := by
  decide

/-! ## Lemma 8: Triple identification

    Among the remaining unidentified elements, e_Sigma, s_C, and e_Delta
    are the unique triple (f, g, h) with dot f g = h and dot h e_D = d_I.
-/

/-- e_Sigma, s_C, e_Delta form the unique triple with the synthesis + verification property. -/
theorem triple_identification :
    dot e_Sigma s_C = e_Delta ∧ dot e_Delta e_D = d_I := by
  decide

/-- No other triple of remaining elements (excluding booleans, testers, encoders,
    context tokens, p) satisfies both conditions. The "remaining" elements after
    steps 1–7 are: {a, b, e_Sigma, e_Delta, d_I, s_C}.
    We show that e_Sigma, s_C, e_Delta is the unique solution among these. -/
theorem triple_uniqueness :
    ∀ f g h : D1ι,
      -- f, g, h are among the remaining elements
      (f = a ∨ f = b ∨ f = e_Sigma ∨ f = e_Delta ∨ f = d_I ∨ f = s_C) →
      (g = a ∨ g = b ∨ g = e_Sigma ∨ g = e_Delta ∨ g = d_I ∨ g = s_C) →
      (h = a ∨ h = b ∨ h = e_Sigma ∨ h = e_Delta ∨ h = d_I ∨ h = s_C) →
      dot f g = h → dot h e_D = d_I →
      f = e_Sigma ∧ g = s_C ∧ h = e_Delta := by
  decide

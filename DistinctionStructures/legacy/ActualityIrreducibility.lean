/- # Actuality Irreducibility Theorem

   This file formalizes the core impossibility result of Distinction Structures:

     Even in a structure where an observer can recover all component encoders
     from behavioral probing, the observer cannot determine which elements are
     actual without querying the actuality tester directly. Actuality is
     underdetermined by the compositional structure.

   **Proof strategy (finite, no recursion):**

   We work with an 18-element carrier set — the 17 elements of Δ₁ plus a
   second surplus element `q`. Both `p` and `q` are "junk" elements that have
   different left-behavior (needed for Ext) but identical *right-behavior*
   under all non-m_I elements.

   1. Define D18 — an 18-element inductive type.
   2. Define `dot1` — the operation for Δ₁, where m_I rejects p (M = D \ {p}).
   3. Define `dot1'` — the operation for Δ₁′, where m_I rejects q (M' = D \ {q}).
   4. Prove both satisfy Ext (behavioral separability).
   5. Prove the operations agree on all (x, y) with x ≠ m_I.
   6. Prove p and q have identical right-images under all non-m_I elements:
      ∀ x ≠ m_I, dot1 x p = dot1' x q.
   7. Conclude: no observation avoiding m_I can determine actuality.

   **Key subtlety:** p and q have *different* left-images (needed for Ext),
   so an observer CAN tell them apart. But even knowing which element is p
   and which is q, the observer cannot determine which is actual — that
   information lives exclusively in m_I's behavior. The operation table
   minus the m_I row is identical in both models. Actuality is the free
   variable: the non-m_I structure is completely fixed, both models satisfy
   all axioms, and the only difference is which element m_I rejects.

   All proofs are by exhaustive finite computation (`decide` / `native_decide`).
   No recursion, no fuel, no unbounded terms.
-/

import DistinctionStructures.Basic

namespace ActualityIrreducibility

/-! ## The 18-Element Carrier Type -/

/-- The 18 distinctions for the irreducibility construction.
    This extends D1ι with a second surplus element `q`. -/
inductive D18 where
  | top   | bot            -- booleans
  | i     | k              -- context tokens
  | a     | b              -- κ-element encodings
  | e_I                    -- context tester
  | e_D   | e_M   | e_Sigma | e_Delta  -- structural encoders
  | d_I   | d_K            -- domain codes
  | m_I   | m_K            -- actuality codes
  | s_C                    -- component-set token
  | p     | q              -- two surplus elements
  deriving DecidableEq, Repr

open D18

instance : Fintype D18 where
  elems := {top, bot, i, k, a, b, e_I, e_D, e_M, e_Sigma,
            e_Delta, d_I, d_K, m_I, m_K, s_C, p, q}
  complete := by intro x; cases x <;> simp

/-! ## Model Δ₁: m_I rejects p, M = D \ {p} -/

/-- Actuality for Δ₁: M(ι) = D \ {p}. -/
def actualM (d : D18) : Prop := d ≠ p

instance : DecidablePred actualM := fun d =>
  if h : d = p then isFalse (by simp [actualM, h]) else isTrue (by simp [actualM, h])

/-- The binary operation for Δ₁.

    All rules from Delta1.lean, plus:
    - q · top = top   (absorption breaker, same as p)
    - q · bot = q     (self-identification under bot — distinguishes q from p for Ext)
    - q · _  = p      (default, same as everything else)

    Critically: p and q have different LEFT-images (p·bot = p, q·bot = q)
    but identical RIGHT-images under all non-m_I elements. -/
def dot1 : D18 → D18 → D18
  -- Block A: Boolean absorption
  | .top,     _      => .top
  | .bot,     _      => .bot
  -- Block B: Testers
  | .e_I,     .i     => .top
  | .e_I,     .k     => .top
  | .e_I,     _      => .bot
  | .d_K,     .a     => .top
  | .d_K,     .b     => .top
  | .d_K,     _      => .bot
  | .m_K,     .a     => .top
  | .m_K,     _      => .bot
  | .m_I,     .p     => .bot      -- m_I rejects p
  | .m_I,     _      => .top      -- m_I accepts everything else (including q)
  -- Block C: Structural encoders
  | .e_D,     .i     => .d_I
  | .e_D,     .k     => .d_K
  | .e_M,     .i     => .m_I
  | .e_M,     .k     => .m_K
  | .e_Sigma, .s_C   => .e_Delta
  | .e_Delta, .e_D   => .d_I
  -- Block D: Absorption breakers
  | .p,       .top   => .top
  | .q,       .top   => .top
  -- Block D': q self-identification (enables Ext between p and q)
  | .q,       .bot   => .q
  -- Block E: Passive self-identification
  | .i,       .top   => .i
  | .k,       .top   => .k
  | .a,       .top   => .a
  | .b,       .top   => .b
  | .d_I,     .top   => .d_I
  | .s_C,     .top   => .s_C
  -- Block F: Default
  | _,        _      => .p

/-! ## Model Δ₁′: m_I rejects q, M' = D \ {q} -/

/-- Actuality for Δ₁′: M′(ι) = D \ {q}. -/
def actualM' (d : D18) : Prop := d ≠ q

instance : DecidablePred actualM' := fun d =>
  if h : d = q then isFalse (by simp [actualM', h]) else isTrue (by simp [actualM', h])

/-- The binary operation for Δ₁′.
    Identical to dot1 EXCEPT m_I swaps its treatment of p and q:
    - m_I · q = bot  (now rejects q)
    - m_I · p = top  (now accepts p)
    ALL other rules — every single non-m_I entry — are exactly the same. -/
def dot1' : D18 → D18 → D18
  -- Block A: Boolean absorption
  | .top,     _      => .top
  | .bot,     _      => .bot
  -- Block B: Testers
  | .e_I,     .i     => .top
  | .e_I,     .k     => .top
  | .e_I,     _      => .bot
  | .d_K,     .a     => .top
  | .d_K,     .b     => .top
  | .d_K,     _      => .bot
  | .m_K,     .a     => .top
  | .m_K,     _      => .bot
  | .m_I,     .q     => .bot      -- CHANGED: m_I now rejects q
  | .m_I,     _      => .top      -- m_I accepts everything else (including p)
  -- Block C: Structural encoders
  | .e_D,     .i     => .d_I
  | .e_D,     .k     => .d_K
  | .e_M,     .i     => .m_I
  | .e_M,     .k     => .m_K
  | .e_Sigma, .s_C   => .e_Delta
  | .e_Delta, .e_D   => .d_I
  -- Block D: Absorption breakers
  | .p,       .top   => .top
  | .q,       .top   => .top
  -- Block D': q self-identification (same rule — NOT an m_I rule)
  | .q,       .bot   => .q
  -- Block E: Passive self-identification
  | .i,       .top   => .i
  | .k,       .top   => .k
  | .a,       .top   => .a
  | .b,       .top   => .b
  | .d_I,     .top   => .d_I
  | .s_C,     .top   => .s_C
  -- Block F: Default
  | _,        _      => .p

/-! ## Section 1: Both models satisfy Ext -/

/-- Ext for Δ₁: all distinct elements are left-separable. -/
theorem ext_dot1 : ∀ (x y : D18), x ≠ y → ∃ z : D18, dot1 x z ≠ dot1 y z := by
  decide

/-- Ext for Δ₁′: all distinct elements are left-separable. -/
theorem ext_dot1' : ∀ (x y : D18), x ≠ y → ∃ z : D18, dot1' x z ≠ dot1' y z := by
  decide

/-! ## Section 2: Homomorphism conditions (H1, H2, H3) -/

theorem dot1_H1_ι  : dot1 e_D i = d_I          := by decide
theorem dot1_H1_κ  : dot1 e_D k = d_K          := by decide
theorem dot1_H2_ι  : dot1 e_M i = m_I          := by decide
theorem dot1_H2_κ  : dot1 e_M k = m_K          := by decide
theorem dot1_H3    : dot1 e_Sigma s_C = e_Delta := by decide

theorem dot1'_H1_ι : dot1' e_D i = d_I          := by decide
theorem dot1'_H1_κ : dot1' e_D k = d_K          := by decide
theorem dot1'_H2_ι : dot1' e_M i = m_I          := by decide
theorem dot1'_H2_κ : dot1' e_M k = m_K          := by decide
theorem dot1'_H3   : dot1' e_Sigma s_C = e_Delta := by decide

/-! ## Section 3: A2, A5, IR conditions -/

theorem dot1_A2  : ∃ d : D18, actualM d  := ⟨top, by decide⟩
theorem dot1_A5  : ∃ d : D18, ¬actualM d := ⟨p, by decide⟩
theorem dot1'_A2 : ∃ d : D18, actualM' d  := ⟨top, by decide⟩
theorem dot1'_A5 : ∃ d : D18, ¬actualM' d := ⟨q, by decide⟩

theorem ir1_both : e_I ≠ e_D ∧ e_I ≠ e_M ∧ e_I ≠ e_Sigma ∧
    e_D ≠ e_M ∧ e_D ≠ e_Sigma ∧ e_M ≠ e_Sigma := by decide

theorem ir2_dot1 : actualM e_I ∧ actualM e_D ∧ actualM e_M ∧
    actualM e_Sigma ∧ actualM e_Delta := by decide

theorem ir2_dot1' : actualM' e_I ∧ actualM' e_D ∧ actualM' e_M ∧
    actualM' e_Sigma ∧ actualM' e_Delta := by decide

theorem ir4_both : e_Delta ≠ e_I ∧ e_Delta ≠ e_D ∧
    e_Delta ≠ e_M ∧ e_Delta ≠ e_Sigma := by decide

theorem a7'_dot1 :
    dot1 e_Delta e_D ≠ dot1 e_I e_D ∧
    dot1 e_Delta e_D ≠ dot1 e_D e_D ∧
    dot1 e_Delta e_D ≠ dot1 e_M e_D ∧
    dot1 e_Delta e_D ≠ dot1 e_Sigma e_D := by decide

theorem a7'_dot1' :
    dot1' e_Delta e_D ≠ dot1' e_I e_D ∧
    dot1' e_Delta e_D ≠ dot1' e_D e_D ∧
    dot1' e_Delta e_D ≠ dot1' e_M e_D ∧
    dot1' e_Delta e_D ≠ dot1' e_Sigma e_D := by decide

/-! ## Section 4: The Operation Tables Are Identical Except at m_I

    This is the central structural fact. The entire Cayley table minus
    the m_I row is the same in both models. The non-m_I structure is
    completely fixed; actuality is the free variable.
-/

/-- **Key structural fact:** dot1 and dot1' produce the same output for
    every pair (x, y) where x ≠ m_I. The operation table minus the m_I
    row is identical in both models. -/
theorem ops_agree_non_mI :
    ∀ (x y : D18), x ≠ m_I → dot1 x y = dot1' x y := by
  decide

/-- The operations disagree ONLY at (m_I, p) and (m_I, q).
    These are the only two entries in the entire 18×18 Cayley table
    that change between Δ₁ and Δ₁′. -/
theorem ops_differ_only_mI :
    ∀ (x y : D18), dot1 x y ≠ dot1' x y →
      x = m_I ∧ (y = p ∨ y = q) := by
  decide

/-! ## Section 5: Right-Image Indistinguishability

    The "right-image" of an element d under element x is dot x d.
    p and q receive identical treatment from every non-m_I element.
    This means: any observation that avoids querying m_I directly
    treats p and q identically as right arguments.
-/

/-- **Within-model right-image agreement:**
    For all x ≠ m_I, dot1 x p = dot1 x q.
    No non-m_I element can distinguish p from q as right arguments. -/
theorem right_image_same_dot1 :
    ∀ x : D18, x ≠ m_I → dot1 x p = dot1 x q := by
  decide

/-- Same property in Δ₁′. -/
theorem right_image_same_dot1' :
    ∀ x : D18, x ≠ m_I → dot1' x p = dot1' x q := by
  decide

/-- **Cross-model right-image agreement:**
    p in Δ₁ and q in Δ₁′ receive the same treatment from every
    non-m_I element. -/
theorem cross_model_right_image :
    ∀ x : D18, x ≠ m_I → dot1 x p = dot1' x q := by
  decide

/-- **The m_I difference:** m_I is the ONLY element that classifies
    p and q differently. In Δ₁, m_I rejects p. In Δ₁′, m_I rejects q. -/
theorem mI_is_unique_discriminator :
    dot1 m_I p = bot ∧ dot1 m_I q = top ∧
    dot1' m_I p = top ∧ dot1' m_I q = bot := by decide

/-! ## Section 6: Non-m_I testers agree on p and q -/

/-- All testers other than m_I classify p and q identically. -/
theorem other_testers_agree :
    (dot1 e_I p = dot1 e_I q) ∧
    (dot1 d_K p = dot1 d_K q) ∧
    (dot1 m_K p = dot1 m_K q) := by decide

/-! ## Section 7: The Actuality Irreducibility Theorem -/

/-- **Actuality Irreducibility — Logical Core:**
    No single predicate on D18 can simultaneously agree with both
    actualM (where p is non-actual) and actualM' (where q is non-actual).
    Since p is actual in Δ₁′ but non-actual in Δ₁, any predicate that
    matches one model must disagree with the other. -/
theorem no_universal_actuality_predicate :
    ¬∃ P : D18 → Prop, (∀ d, P d ↔ actualM d) ∧ (∀ d, P d ↔ actualM' d) := by
  intro ⟨P, hP, hP'⟩
  have h1 : ¬P p := fun hp => absurd ((hP p).mp hp) (by decide : ¬actualM p)
  have h2 : P p := (hP' p).mpr (by decide : actualM' p)
  exact h1 h2

/-- **The Actuality Irreducibility Theorem:**

    Two directed distinction structures Δ₁ and Δ₁′ exist on the same
    18-element carrier such that:

    1. Both satisfy Ext (behavioral separability)
    2. Both satisfy H1, H2, H3 (homomorphism conditions)
    3. Both satisfy IR conditions (IR1, IR2, IR4)
    4. Their operation tables are identical except at m_I:
       ∀ x y, x ≠ m_I → dot1 x y = dot1' x y
    5. Their actuality sets differ: M = D \ {p} vs M′ = D \ {q}
    6. Non-m_I elements treat p and q identically as right arguments:
       ∀ x ≠ m_I, dot1 x p = dot1' x q
    7. No single actuality predicate works for both models

    Conclusion: the operation table minus the m_I rules is completely
    fixed. Both models satisfy all axioms. The only difference is which
    element m_I rejects — and that is the sole determinant of actuality.
    Actuality is not a consequence of compositional structure; it is
    irreducible information carried exclusively by the actuality tester. -/
theorem actuality_irreducibility :
    -- (1) Both satisfy Ext
    (∀ x y : D18, x ≠ y → ∃ z, dot1 x z ≠ dot1 y z) ∧
    (∀ x y : D18, x ≠ y → ∃ z, dot1' x z ≠ dot1' y z) ∧
    -- (2) Both satisfy H1, H2, H3
    (dot1 e_D i = d_I ∧ dot1 e_D k = d_K ∧
     dot1 e_M i = m_I ∧ dot1 e_M k = m_K ∧
     dot1 e_Sigma s_C = e_Delta) ∧
    (dot1' e_D i = d_I ∧ dot1' e_D k = d_K ∧
     dot1' e_M i = m_I ∧ dot1' e_M k = m_K ∧
     dot1' e_Sigma s_C = e_Delta) ∧
    -- (3) Operation tables identical except at m_I
    (∀ x y : D18, x ≠ m_I → dot1 x y = dot1' x y) ∧
    -- (4) Actuality sets differ
    (¬actualM p ∧ actualM' p) ∧
    (actualM q ∧ ¬actualM' q) ∧
    -- (5) Non-m_I right-image indistinguishability
    (∀ x : D18, x ≠ m_I → dot1 x p = dot1' x q) ∧
    -- (6) No universal actuality predicate
    (¬∃ P : D18 → Prop, (∀ d, P d ↔ actualM d) ∧ (∀ d, P d ↔ actualM' d)) :=
  ⟨ext_dot1,
   ext_dot1',
   ⟨by decide, by decide, by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide, by decide⟩,
   ops_agree_non_mI,
   ⟨by decide, by decide⟩,
   ⟨by decide, by decide⟩,
   cross_model_right_image,
   no_universal_actuality_predicate⟩

end ActualityIrreducibility

import Kamea.CatKripkeWallMinimal
import Kamea.Countermodels10
import Kamea.Witness10

/-!
# Internal Composition Property (ICP)

The **Internal Composition Property** characterizes evaluator internalization (H)
as a single abstract property: *partial internal composition*.

## Definition

An extensional magma on a 2-pointed set satisfies ICP when its left-regular
representation admits a non-trivial factorization on core:

  ∃ a b c, pairwise distinct, non-absorber, such that:
  1. b preserves core: b·x ∉ {z₁, z₂} for all core x
  2. Factorization: a·x = c·(b·x) for all core x
  3. Non-triviality: a takes ≥2 distinct values on core

## Results

- **D ⊬ H model**: ICP fails (no non-trivial factorization exists)
- **H ⊬ D model**: ICP holds (witnessed by a=8, b=6, c=7)
- **S+D+H witness**: ICP holds (witnessed by a=8, b=6, c=7)
- **Abstract equivalence**: ICP ↔ ∃ non-trivial Compose+Inert (pure logic)

All model-specific proofs by `native_decide`.
-/

set_option autoImplicit false

namespace KripkeWall

-- ═══════════════════════════════════════════════════════════════════
-- Definition: Internal Composition Property
-- ═══════════════════════════════════════════════════════════════════

/-- The Internal Composition Property (ICP) for a magma on a 2-pointed set.

    The left-regular representation admits a non-trivial factorization on core:
    some element's row on core equals the composition of two other elements' rows,
    with the inner element preserving core. This is partial internal composition.

    Uses disjunction form (`x = z₁ ∨ x = z₂ ∨ P x`) instead of implications
    (`x ≠ z₁ → x ≠ z₂ → P x`) for decidability. -/
@[reducible] def HasICP (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) : Prop :=
  ∃ a b c : Fin n,
    -- Pairwise distinct
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    -- All non-absorber
    a ≠ z₁ ∧ a ≠ z₂ ∧ b ≠ z₁ ∧ b ≠ z₂ ∧ c ≠ z₁ ∧ c ≠ z₂ ∧
    -- b preserves core (disjunction form for decidability)
    (∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ (dot b x ≠ z₁ ∧ dot b x ≠ z₂)) ∧
    -- Factorization: a = c ∘ b on core (disjunction form)
    (∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ dot a x = dot c (dot b x)) ∧
    -- Non-triviality: a takes ≥2 distinct values on core
    (∃ x y : Fin n, x ≠ z₁ ∧ x ≠ z₂ ∧ y ≠ z₁ ∧ y ≠ z₂ ∧ dot a x ≠ dot a y)


-- ═══════════════════════════════════════════════════════════════════
-- Compose+Inert (the current H axioms, existentially quantified)
-- ═══════════════════════════════════════════════════════════════════

/-- The existentially quantified Compose+Inert property with non-triviality.
    This is the current operational definition of H's core. -/
@[reducible] def HasComposeInert (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) : Prop :=
  ∃ g ρ η : Fin n,
    -- Pairwise distinct
    η ≠ g ∧ η ≠ ρ ∧ g ≠ ρ ∧
    -- All non-absorber
    η ≠ z₁ ∧ η ≠ z₂ ∧ g ≠ z₁ ∧ g ≠ z₂ ∧ ρ ≠ z₁ ∧ ρ ≠ z₂ ∧
    -- Inert: g preserves core (disjunction form)
    (∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ (dot g x ≠ z₁ ∧ dot g x ≠ z₂)) ∧
    -- Compose: η = ρ ∘ g on core (disjunction form)
    (∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ dot η x = dot ρ (dot g x)) ∧
    -- Non-triviality: η takes ≥2 distinct values on core
    (∃ x y : Fin n, x ≠ z₁ ∧ x ≠ z₂ ∧ y ≠ z₁ ∧ y ≠ z₂ ∧ dot η x ≠ dot η y)


-- ═══════════════════════════════════════════════════════════════════
-- Abstract equivalence: ICP ↔ Compose+Inert (pure logic, no decide)
-- ═══════════════════════════════════════════════════════════════════

/-- ICP implies Compose+Inert. The witness triple (a, b, c) maps to (g, ρ, η) = (b, c, a).
    HasICP packs (a ≠ b, a ≠ c, b ≠ c); HasComposeInert expects (η ≠ g, η ≠ ρ, g ≠ ρ).
    With η=a, g=b, ρ=c: η≠g = a≠b, η≠ρ = a≠c, g≠ρ = b≠c. Direct match. -/
theorem icp_implies_composeInert (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n) : HasICP n dot z₁ z₂ → HasComposeInert n dot z₁ z₂ := by
  intro ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2,
         hpres, hfact, hnont⟩
  exact ⟨b, c, a, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2,
         hpres, hfact, hnont⟩

/-- Compose+Inert implies ICP. The witness triple (g, ρ, η) maps to (a, b, c) = (η, g, ρ).
    HasComposeInert packs (η ≠ g, η ≠ ρ, g ≠ ρ); HasICP expects (a ≠ b, a ≠ c, b ≠ c).
    With a=η, b=g, c=ρ: a≠b = η≠g, a≠c = η≠ρ, b≠c = g≠ρ. Direct match. -/
theorem composeInert_implies_icp (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n) : HasComposeInert n dot z₁ z₂ → HasICP n dot z₁ z₂ := by
  intro ⟨g, ρ, η, hηg, hηρ, hgρ, hη1, hη2, hg1, hg2, hρ1, hρ2,
         hpres, hcomp, hnont⟩
  exact ⟨η, g, ρ, hηg, hηρ, hgρ, hη1, hη2, hg1, hg2, hρ1, hρ2,
         hpres, hcomp, hnont⟩

/-- **ICP ↔ Compose+Inert**: the two formulations are logically equivalent
    for any magma on a 2-pointed set. Pure logic — no `decide`, no `native_decide`. -/
theorem icp_iff_composeInert (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n) : HasICP n dot z₁ z₂ ↔ HasComposeInert n dot z₁ z₂ :=
  ⟨icp_implies_composeInert n dot z₁ z₂, composeInert_implies_icp n dot z₁ z₂⟩

-- ═══════════════════════════════════════════════════════════════════
-- Model-specific proofs: ICP on the three N=10 counterexamples
-- ═══════════════════════════════════════════════════════════════════

/-- **H ⊬ D model has ICP**: witnessed by a=8 (η), b=6 (g), c=7 (ρ).
    The evaluation core exists despite the Kripke dichotomy failing. -/
theorem hNotD_has_icp : HasICP 10 dotHnotD 0 1 := by native_decide

/-- **S+D+H witness has ICP**: witnessed by a=8 (η), b=6 (g), c=7 (ρ).
    All three capabilities coexist. -/
theorem w10_has_icp : HasICP 10 dotW10 0 1 := by native_decide

/-- **D ⊬ H model has no ICP**: no non-trivial internal composition exists.
    Proved by exhaustive finite search via `native_decide`. -/
theorem dNotH_no_icp : ¬ HasICP 10 dotDnotH 0 1 := by native_decide

-- ═══════════════════════════════════════════════════════════════════
-- Compose+Inert on the same models (via the equivalence)
-- ═══════════════════════════════════════════════════════════════════

/-- D ⊬ H model has no Compose+Inert (non-trivial). -/
theorem dNotH_no_composeInert : ¬ HasComposeInert 10 dotDnotH 0 1 :=
  fun h => dNotH_no_icp ((composeInert_implies_icp 10 dotDnotH 0 1) h)

/-- H ⊬ D model has Compose+Inert. -/
theorem hNotD_has_composeInert : HasComposeInert 10 dotHnotD 0 1 :=
  (icp_implies_composeInert 10 dotHnotD 0 1) hNotD_has_icp

/-- S+D+H witness has Compose+Inert. -/
theorem w10_has_composeInert : HasComposeInert 10 dotW10 0 1 :=
  (icp_implies_composeInert 10 dotW10 0 1) w10_has_icp

-- ═══════════════════════════════════════════════════════════════════
-- Combined independence theorem using ICP
-- ═══════════════════════════════════════════════════════════════════

/-- **D ⊬ ICP**: The classifier dichotomy does not imply partial internal composition.
    The D⊬H model is a DichotomicRetractMagma that fails ICP. -/
theorem dichotomy_not_implies_icp :
    ∃ (_ : DichotomicRetractMagma 10), ¬ HasICP 10 dotDnotH 0 1 :=
  ⟨dNotH, dNotH_no_icp⟩

/-- **ICP ⊬ D**: Partial internal composition does not imply the classifier dichotomy.
    The H⊬D model is a FaithfulRetractMagma with ICP that violates Kripke. -/
theorem icp_not_implies_dichotomy :
    ∃ (_ : FaithfulRetractMagma 10),
    HasICP 10 dotHnotD 0 1 ∧
    ¬ (∀ y : Fin 10, y ≠ hNotD.zero₁ → y ≠ hNotD.zero₂ →
      (∀ x : Fin 10, x ≠ hNotD.zero₁ → x ≠ hNotD.zero₂ →
        hNotD.dot y x = hNotD.zero₁ ∨ hNotD.dot y x = hNotD.zero₂) ∨
      (∀ x : Fin 10, x ≠ hNotD.zero₁ → x ≠ hNotD.zero₂ →
        hNotD.dot y x ≠ hNotD.zero₁ ∧ hNotD.dot y x ≠ hNotD.zero₂)) :=
  ⟨hNotD, hNotD_has_icp, hNotD_violates_dichotomy⟩

/-- **Coexistence**: S+D+ICP all hold at N=10. -/
theorem sdh_icp_witness :
    ∃ (_ : DichotomicRetractMagma 10), HasICP 10 dotW10 0 1 :=
  ⟨witness10_drm, w10_has_icp⟩

end KripkeWall

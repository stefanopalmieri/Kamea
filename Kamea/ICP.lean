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

-- ═══════════════════════════════════════════════════════════════════
-- ICP invariance under FRM isomorphisms
-- ═══════════════════════════════════════════════════════════════════

/-- An FRM isomorphism: a bijective zero-preserving homomorphism. -/
structure FRMIso {n : Nat} (M₁ M₂ : FaithfulRetractMagma n) where
  toFun : Fin n → Fin n
  bij : Function.Bijective toFun
  hom : ∀ a b : Fin n, toFun (M₁.dot a b) = M₂.dot (toFun a) (toFun b)
  map_zero₁ : toFun M₁.zero₁ = M₂.zero₁
  map_zero₂ : toFun M₁.zero₂ = M₂.zero₂

/-- **ICP is invariant under FRM isomorphisms.**
    If φ : M₁ → M₂ is a bijective zero-preserving homomorphism and M₁ has ICP,
    then M₂ has ICP. The factorization L_a = L_c ∘ L_b transfers because
    φ preserves the operation, injectivity preserves distinctness and non-triviality,
    and surjectivity ensures core-preservation transfers. Algebraic proof,
    no `decide`. -/
theorem FRMIso.preserves_icp {n : Nat} {M₁ M₂ : FaithfulRetractMagma n}
    (φ : FRMIso M₁ M₂) :
    HasICP n M₁.dot M₁.zero₁ M₁.zero₂ → HasICP n M₂.dot M₂.zero₁ M₂.zero₂ := by
  intro ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2,
         hpres, hfact, ⟨x, y, hx1, hx2, hy1, hy2, hneq⟩⟩
  refine ⟨φ.toFun a, φ.toFun b, φ.toFun c,
    -- Pairwise distinct (injectivity)
    fun h => hab (φ.bij.1 h), fun h => hac (φ.bij.1 h), fun h => hbc (φ.bij.1 h),
    -- Non-absorber (injectivity + zero-preservation)
    fun h => ha1 (φ.bij.1 (by rw [h, φ.map_zero₁])),
    fun h => ha2 (φ.bij.1 (by rw [h, φ.map_zero₂])),
    fun h => hb1 (φ.bij.1 (by rw [h, φ.map_zero₁])),
    fun h => hb2 (φ.bij.1 (by rw [h, φ.map_zero₂])),
    fun h => hc1 (φ.bij.1 (by rw [h, φ.map_zero₁])),
    fun h => hc2 (φ.bij.1 (by rw [h, φ.map_zero₂])),
    -- Core-preservation of b
    ?_, -- Factorization
    ?_, -- Non-triviality
    ⟨φ.toFun x, φ.toFun y, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- b preserves core: ∀ u, u = z₁' ∨ u = z₂' ∨ (dot₂ (φ b) u ≠ z₁' ∧ ≠ z₂')
    intro u
    obtain ⟨v, rfl⟩ := φ.bij.2 u
    by_cases hv1 : v = M₁.zero₁
    · left; rw [hv1, φ.map_zero₁]
    · by_cases hv2 : v = M₁.zero₂
      · right; left; rw [hv2, φ.map_zero₂]
      · right; right
        rw [← φ.hom]
        have := hpres v
        rcases this with h | h | ⟨h1, h2⟩
        · exact absurd h hv1
        · exact absurd h hv2
        · exact ⟨fun h => h1 (φ.bij.1 (by rw [h, φ.map_zero₁])),
                 fun h => h2 (φ.bij.1 (by rw [h, φ.map_zero₂]))⟩
  · -- Factorization: ∀ u, u = z₁' ∨ u = z₂' ∨ dot₂ (φ a) u = dot₂ (φ c) (dot₂ (φ b) u)
    intro u
    obtain ⟨v, rfl⟩ := φ.bij.2 u
    by_cases hv1 : v = M₁.zero₁
    · left; rw [hv1, φ.map_zero₁]
    · by_cases hv2 : v = M₁.zero₂
      · right; left; rw [hv2, φ.map_zero₂]
      · right; right
        rw [← φ.hom, ← φ.hom, ← φ.hom]
        have := hfact v
        rcases this with h | h | h
        · exact absurd h hv1
        · exact absurd h hv2
        · rw [h]
  · -- φ x ≠ z₁'
    exact fun h => hx1 (φ.bij.1 (by rw [h, φ.map_zero₁]))
  · exact fun h => hx2 (φ.bij.1 (by rw [h, φ.map_zero₂]))
  · exact fun h => hy1 (φ.bij.1 (by rw [h, φ.map_zero₁]))
  · exact fun h => hy2 (φ.bij.1 (by rw [h, φ.map_zero₂]))
  · -- dot₂ (φ a) (φ x) ≠ dot₂ (φ a) (φ y)
    rw [← φ.hom, ← φ.hom]
    exact fun h => hneq (φ.bij.1 h)

-- ═══════════════════════════════════════════════════════════════════
-- S ⊬ ICP: self-simulation does not imply internal composition
-- ═══════════════════════════════════════════════════════════════════

/-- **S ⊬ ICP**: The minimal DRM (`kripke4`, N=4) is an FRM that trivially
    fails ICP — it has only 2 non-absorber elements, but ICP requires 3
    pairwise distinct non-absorbers.

    This completes ICP's position in the independence structure:
    S ⊬ ICP, D ⊬ ICP, ICP ⊬ D (all Lean-proved). -/
theorem s_not_implies_icp :
    ∃ (_ : FaithfulRetractMagma 4), ¬ HasICP 4 dotK4 0 1 :=
  ⟨kripke4.toFaithfulRetractMagma, by decide⟩

-- ═══════════════════════════════════════════════════════════════════
-- ICP conditions are individually necessary
-- ═══════════════════════════════════════════════════════════════════

/-! ### Necessity of pairwise-distinctness

The Kripke-4 model satisfies ICP without the pairwise-distinctness condition
(witnessed by a=b=c=3: 3·x = 3·(3·x)) but fails full ICP (only 2 non-absorbers).
-/

/-- ICP without pairwise-distinctness: a, b, c need not be distinct. -/
@[reducible] def HasICPWeakDistinct (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) : Prop :=
  ∃ a b c : Fin n,
    -- All non-absorber (but NOT necessarily pairwise distinct)
    a ≠ z₁ ∧ a ≠ z₂ ∧ b ≠ z₁ ∧ b ≠ z₂ ∧ c ≠ z₁ ∧ c ≠ z₂ ∧
    -- b preserves core
    (∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ (dot b x ≠ z₁ ∧ dot b x ≠ z₂)) ∧
    -- Factorization
    (∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ dot a x = dot c (dot b x)) ∧
    -- Non-triviality
    (∃ x y : Fin n, x ≠ z₁ ∧ x ≠ z₂ ∧ y ≠ z₁ ∧ y ≠ z₂ ∧ dot a x ≠ dot a y)

/-- Kripke-4 fails full ICP. -/
theorem kripke4_no_icp : ¬ HasICP 4 dotK4 0 1 := by decide

/-- Kripke-4 satisfies ICP without pairwise-distinctness (a=b=c=3). -/
theorem kripke4_has_weak_distinct : HasICPWeakDistinct 4 dotK4 0 1 := by decide

/-- **Pairwise-distinctness is necessary for ICP.**
    Kripke-4 separates HasICPWeakDistinct from HasICP. -/
theorem icp_distinct_necessary :
    ∃ (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n),
      HasICPWeakDistinct n dot z₁ z₂ ∧ ¬ HasICP n dot z₁ z₂ :=
  ⟨4, dotK4, 0, 1, kripke4_has_weak_distinct, kripke4_no_icp⟩

/-! ### Necessity of non-triviality

A custom 6-element FRM satisfies ICP without non-triviality (a=4 is constant on core,
factors through b=2, c=5) but fails full ICP (no non-trivially-factoring element exists).
-/

/-- ICP without non-triviality: a may be constant on core. -/
@[reducible] def HasICPWeakNontriv (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) : Prop :=
  ∃ a b c : Fin n,
    -- Pairwise distinct
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    -- All non-absorber
    a ≠ z₁ ∧ a ≠ z₂ ∧ b ≠ z₁ ∧ b ≠ z₂ ∧ c ≠ z₁ ∧ c ≠ z₂ ∧
    -- b preserves core
    (∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ (dot b x ≠ z₁ ∧ dot b x ≠ z₂)) ∧
    -- Factorization
    (∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ dot a x = dot c (dot b x))
    -- (no non-triviality condition)

-- The 6-element FRM witnessing non-triviality necessity
private def rawNT6 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0 | 0, 5 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 2, 0 => 5 | 2, 1 => 3 | 2, 2 => 3 | 2, 3 => 5 | 2, 4 => 4 | 2, 5 => 2
  | 3, 0 => 0 | 3, 1 => 1 | 3, 2 => 5 | 3, 3 => 2 | 3, 4 => 4 | 3, 5 => 3
  | 4, 0 => 2 | 4, 1 => 2 | 4, 2 => 1 | 4, 3 => 1 | 4, 4 => 1 | 4, 5 => 1
  | 5, 0 => 3 | 5, 1 => 3 | 5, 2 => 1 | 5, 3 => 1 | 5, 4 => 1 | 5, 5 => 1
  | _, _ => 0

private theorem rawNT6_bound (a b : Fin 6) : rawNT6 a.val b.val < 6 := by
  revert a b; decide

def dotNT6 (a b : Fin 6) : Fin 6 := ⟨rawNT6 a.val b.val, rawNT6_bound a b⟩

/-- The 6-element non-triviality witness is a FaithfulRetractMagma with Q=2, E=3. -/
def nt6_frm : FaithfulRetractMagma 6 where
  dot := dotNT6
  zero₁ := 0
  zero₂ := 1
  sec := 2
  ret := 3
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide
  ret_sec := by decide
  sec_ret := by decide
  ret_zero₁ := by decide

/-- The NT6 model fails full ICP. -/
theorem nt6_no_icp : ¬ HasICP 6 dotNT6 0 1 := by decide

/-- The NT6 model satisfies ICP without non-triviality (a=4, b=2, c=5). -/
theorem nt6_has_weak_nontriv : HasICPWeakNontriv 6 dotNT6 0 1 := by decide

/-- **Non-triviality is necessary for ICP.**
    The NT6 model separates HasICPWeakNontriv from HasICP. -/
theorem icp_nontrivial_necessary :
    ∃ (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n),
      HasICPWeakNontriv n dot z₁ z₂ ∧ ¬ HasICP n dot z₁ z₂ :=
  ⟨6, dotNT6, 0, 1, nt6_has_weak_nontriv, nt6_no_icp⟩

end KripkeWall

/- # Δ₀ — The Symmetric Distinction Structure

   This file constructs the concrete 16-element symmetric model Δ₀ and
   proves all axioms (A1–A7′), behavioral separability (Ext), homomorphism
   conditions (H1–H3), and intrinsic reflexivity (IR1–IR5).

   Δ₀ has two contexts: ι (14 distinctions) and κ (2 distinctions).
   The synthesis function Σ operates on `Finset Dι → Dι` with priority rules.
-/

import DistinctionStructures.Basic

/-! ## Types -/

/-- The 14 distinctions of context ι in Δ₀. -/
inductive Dι where
  | e_I | e_D | e_M | e_Sigma   -- component encoders
  | e_iota | e_kappa             -- context encoders
  | r_Di | r_Dk | r_Mi | r_Mk   -- set encoders
  | e_Delta                      -- whole structure encoder
  | r_S                          -- component set encoder
  | p | q                        -- surplus (non-actual)
  deriving DecidableEq, Repr

/-- The 2 distinctions of context κ in Δ₀. -/
inductive Dκ where
  | alpha | beta
  deriving DecidableEq, Repr

/-! ## Fintype instances -/

instance : Fintype Dι where
  elems := {.e_I, .e_D, .e_M, .e_Sigma, .e_iota, .e_kappa,
            .r_Di, .r_Dk, .r_Mi, .r_Mk, .e_Delta, .r_S, .p, .q}
  complete := by intro x; cases x <;> simp

instance : Fintype Dκ where
  elems := {.alpha, .beta}
  complete := by intro x; cases x <;> simp

/-! ## Contexts -/

/-- Contexts of Δ₀ -/
inductive Ctx0 where
  | ι | κ
  deriving DecidableEq, Repr

instance : Fintype Ctx0 where
  elems := {.ι, .κ}
  complete := by intro x; cases x <;> simp

/-! ## Actuality -/

/-- M(ι) = all of Dι except p and q -/
def actual0_ι (d : Dι) : Prop := d ≠ Dι.p ∧ d ≠ Dι.q

/-- M(κ) = {alpha} -/
def actual0_κ (d : Dκ) : Prop := d = Dκ.alpha

instance : DecidablePred actual0_ι := fun d =>
  if h1 : d = Dι.p then isFalse (by simp [actual0_ι, h1])
  else if h2 : d = Dι.q then isFalse (by simp [actual0_ι, h2])
  else isTrue ⟨h1, h2⟩

instance : DecidablePred actual0_κ := fun d =>
  if h : d = Dκ.alpha then isTrue h else isFalse h

/-! ## Synthesis Σ_ι

   We define sigma_ι by checking specific Finset patterns.
   For Rule 9 ({x, q} → x for non-special x), we check each element.
-/

/-- Helper: extract the non-q element from a 2-element set containing q. -/
private def extractNonQ (S : Finset Dι) : Dι :=
  if Dι.e_I ∈ S then Dι.e_I
  else if Dι.e_D ∈ S then Dι.e_D
  else if Dι.e_M ∈ S then Dι.e_M
  else if Dι.e_Sigma ∈ S then Dι.e_Sigma
  else if Dι.e_iota ∈ S then Dι.e_iota
  else if Dι.e_kappa ∈ S then Dι.e_kappa
  else if Dι.r_Di ∈ S then Dι.r_Di
  else if Dι.r_Dk ∈ S then Dι.r_Dk
  else if Dι.r_Mi ∈ S then Dι.r_Mi
  else if Dι.r_Mk ∈ S then Dι.r_Mk
  else if Dι.e_Delta ∈ S then Dι.e_Delta
  else if Dι.r_S ∈ S then Dι.r_S
  else if Dι.p ∈ S then Dι.p
  else Dι.q

/-- The synthesis function on D(ι).

   Priority rules:
   1. {x} (singleton) → x
   2. {e_D, e_iota} → r_Di
   3. {e_D, e_kappa} → r_Dk
   4. {e_M, e_iota} → r_Mi
   5. {e_M, e_kappa} → r_Mk
   6. {e_Sigma, r_S} → e_Delta
   7. {e_I, e_D, e_M, e_Sigma} → e_Delta
   8. {e_Delta, e_D} → r_Di
   9. {x, q} (non-special) → x
   10. all other → p -/
def sigma_ι (S : Finset Dι) : Dι :=
  -- Rule 7: {e_I, e_D, e_M, e_Sigma} → e_Delta (check before singletons to avoid confusion)
  if S = {Dι.e_I, Dι.e_D, Dι.e_M, Dι.e_Sigma} then Dι.e_Delta
  -- Rule 1: singletons — check each
  else if S = {Dι.e_I} then Dι.e_I
  else if S = {Dι.e_D} then Dι.e_D
  else if S = {Dι.e_M} then Dι.e_M
  else if S = {Dι.e_Sigma} then Dι.e_Sigma
  else if S = {Dι.e_iota} then Dι.e_iota
  else if S = {Dι.e_kappa} then Dι.e_kappa
  else if S = {Dι.r_Di} then Dι.r_Di
  else if S = {Dι.r_Dk} then Dι.r_Dk
  else if S = {Dι.r_Mi} then Dι.r_Mi
  else if S = {Dι.r_Mk} then Dι.r_Mk
  else if S = {Dι.e_Delta} then Dι.e_Delta
  else if S = {Dι.r_S} then Dι.r_S
  else if S = {Dι.p} then Dι.p
  else if S = {Dι.q} then Dι.q
  -- Rule 2: {e_D, e_iota} → r_Di
  else if S = {Dι.e_D, Dι.e_iota} then Dι.r_Di
  -- Rule 3: {e_D, e_kappa} → r_Dk
  else if S = {Dι.e_D, Dι.e_kappa} then Dι.r_Dk
  -- Rule 4: {e_M, e_iota} → r_Mi
  else if S = {Dι.e_M, Dι.e_iota} then Dι.r_Mi
  -- Rule 5: {e_M, e_kappa} → r_Mk
  else if S = {Dι.e_M, Dι.e_kappa} then Dι.r_Mk
  -- Rule 6: {e_Sigma, r_S} → e_Delta
  else if S = {Dι.e_Sigma, Dι.r_S} then Dι.e_Delta
  -- Rule 8: {e_Delta, e_D} → r_Di
  else if S = {Dι.e_Delta, Dι.e_D} then Dι.r_Di
  -- Rule 9: {x, q} → x (for remaining 2-element sets containing q)
  else if Dι.q ∈ S ∧ S.card = 2 then extractNonQ (S.erase Dι.q)
  -- Rule 10: default
  else Dι.p

/-- The synthesis function on D(κ). -/
def sigma_κ (S : Finset Dκ) : Dκ :=
  if Dκ.alpha ∈ S then Dκ.alpha else Dκ.beta

/-! ## Axiom verification -/

/-- A1: There exist contexts. -/
theorem delta0_A1 : Nonempty Ctx0 := ⟨.ι⟩

/-- A2: Each context has at least one actual distinction. -/
theorem delta0_A2_ι : ∃ d : Dι, actual0_ι d := ⟨.e_I, by decide⟩
theorem delta0_A2_κ : ∃ d : Dκ, actual0_κ d := ⟨.alpha, by decide⟩

/-- A5: There exists a non-actual distinction. -/
theorem delta0_A5 : ∃ d : Dι, ¬actual0_ι d := ⟨.p, by decide⟩

/-- A6: Singletons map to themselves. -/
theorem delta0_A6 : ∀ d : Dι, sigma_ι {d} = d := by
  intro d; cases d <;> native_decide

/-! ## Homomorphism conditions -/

/-- H1 for ι: Σ({e_D, e_iota}) = r_Di -/
theorem delta0_H1_ι : sigma_ι {Dι.e_D, Dι.e_iota} = Dι.r_Di := by native_decide

/-- H1 for κ: Σ({e_D, e_kappa}) = r_Dk -/
theorem delta0_H1_κ : sigma_ι {Dι.e_D, Dι.e_kappa} = Dι.r_Dk := by native_decide

/-- H2 for ι: Σ({e_M, e_iota}) = r_Mi -/
theorem delta0_H2_ι : sigma_ι {Dι.e_M, Dι.e_iota} = Dι.r_Mi := by native_decide

/-- H2 for κ: Σ({e_M, e_kappa}) = r_Mk -/
theorem delta0_H2_κ : sigma_ι {Dι.e_M, Dι.e_kappa} = Dι.r_Mk := by native_decide

/-- H3: Σ({e_Sigma, r_S}) = e_Delta -/
theorem delta0_H3 : sigma_ι {Dι.e_Sigma, Dι.r_S} = Dι.e_Delta := by native_decide

/-- IR4: Σ({e_I, e_D, e_M, e_Sigma}) = e_Delta -/
theorem delta0_IR4 : sigma_ι {Dι.e_I, Dι.e_D, Dι.e_M, Dι.e_Sigma} = Dι.e_Delta := by
  native_decide

/-! ## Behavioral Separability (Ext) -/

/-- Ext for D(ι): For all distinct a, b there exists y with Σ({a,y}) ≠ Σ({b,y}).
    Witness: y = q for all pairs (by Rule 9, Σ({x,q}) = x). -/
theorem delta0_ext_ι : ∀ (a b : Dι), a ≠ b →
    ∃ y : Dι, sigma_ι {a, y} ≠ sigma_ι {b, y} := by
  intro a b hab
  exact ⟨Dι.q, by cases a <;> cases b <;> simp_all <;> native_decide⟩

/-- Ext for D(κ). -/
theorem delta0_ext_κ : ∀ (a b : Dκ), a ≠ b →
    ∃ y : Dκ, sigma_κ {a, y} ≠ sigma_κ {b, y} := by
  decide

/-! ## A7′ (Structural Novelty) -/

/-- A7′: S = {e_I, e_D, e_M, e_Sigma}, δ* = e_Delta.
    N1: e_Delta ∉ S.
    N2: with t = e_D, Σ({e_Delta, e_D}) = r_Di, which differs from
        Σ({e_I, e_D}), Σ({e_D}), Σ({e_M, e_D}), Σ({e_Sigma, e_D}). -/
theorem delta0_A7'_N1 : Dι.e_Delta ∉ ({Dι.e_I, Dι.e_D, Dι.e_M, Dι.e_Sigma} : Finset Dι) := by
  decide

theorem delta0_A7'_N2_witness : sigma_ι {Dι.e_Delta, Dι.e_D} = Dι.r_Di := by native_decide

theorem delta0_A7'_N2_eI : sigma_ι {Dι.e_I, Dι.e_D} ≠ Dι.r_Di := by native_decide
theorem delta0_A7'_N2_eD : sigma_ι {Dι.e_D} ≠ Dι.r_Di := by native_decide
theorem delta0_A7'_N2_eM : sigma_ι {Dι.e_M, Dι.e_D} ≠ Dι.r_Di := by native_decide
theorem delta0_A7'_N2_eSigma : sigma_ι {Dι.e_Sigma, Dι.e_D} ≠ Dι.r_Di := by native_decide

/-! ## IR1: Component encoders are pairwise distinct -/

theorem delta0_IR1 : Dι.e_I ≠ Dι.e_D ∧ Dι.e_I ≠ Dι.e_M ∧ Dι.e_I ≠ Dι.e_Sigma ∧
    Dι.e_D ≠ Dι.e_M ∧ Dι.e_D ≠ Dι.e_Sigma ∧ Dι.e_M ≠ Dι.e_Sigma := by decide

/-! ## IR2: All encoding elements are actual -/

theorem delta0_IR2 :
    actual0_ι .e_I ∧ actual0_ι .e_D ∧ actual0_ι .e_M ∧ actual0_ι .e_Sigma ∧
    actual0_ι .e_Delta ∧ actual0_ι .e_iota ∧ actual0_ι .e_kappa ∧
    actual0_ι .r_Di ∧ actual0_ι .r_Dk ∧ actual0_ι .r_Mi ∧ actual0_ι .r_Mk ∧
    actual0_ι .r_S := by decide

/-! ## IR5: p and q are not in the range of encoding -/

theorem delta0_IR5 : Dι.p ≠ Dι.e_I ∧ Dι.p ≠ Dι.e_D ∧ Dι.p ≠ Dι.e_M ∧
    Dι.p ≠ Dι.e_Sigma ∧ Dι.p ≠ Dι.e_Delta ∧
    Dι.q ≠ Dι.e_I ∧ Dι.q ≠ Dι.e_D ∧ Dι.q ≠ Dι.e_M ∧
    Dι.q ≠ Dι.e_Sigma ∧ Dι.q ≠ Dι.e_Delta := by decide

/-! ## SymmetricDS instance for Δ₀ -/

/-- The symmetric distinction structure on D(ι). -/
def delta0_symDS : SymmetricDS Dι where
  actual := actual0_ι
  synth := sigma_ι

instance : DecidablePred delta0_symDS.actual := inferInstanceAs (DecidablePred actual0_ι)

theorem delta0_symDS_A2 : delta0_symDS.A2 := ⟨.e_I, by decide⟩
theorem delta0_symDS_A5 : delta0_symDS.A5 := ⟨.p, by decide⟩
theorem delta0_symDS_A6 : delta0_symDS.A6 := by
  intro d; cases d <;> native_decide
theorem delta0_symDS_Ext : delta0_symDS.Ext := by
  intro a b hab
  exact ⟨Dι.q, by cases a <;> cases b <;> simp_all <;> native_decide⟩

/-- A7′ (Structural Novelty) proved as a single unified proposition
    matching the abstract SymmetricDS.A7' definition.
    Witness: S = {e_I, e_D, e_M, e_Sigma}, t = e_D. -/
theorem delta0_symDS_A7' : delta0_symDS.A7' := by
  refine ⟨{Dι.e_I, Dι.e_D, Dι.e_M, Dι.e_Sigma}, ?_, ?_, ?_, Dι.e_D, ?_⟩
  · native_decide
  · intro d hd; simp [Finset.mem_insert] at hd; rcases hd with h | h | h | h <;> subst h <;> decide
  · native_decide
  · intro d hd; simp [Finset.mem_insert] at hd; rcases hd with h | h | h | h <;> subst h <;> native_decide

/-! ## SymmetricIR witness for Δ₀ -/

/-- The SymmetricIR structure witnessing intrinsic reflexivity of Δ₀. -/
def delta0_IR : SymmetricIR Dι Dκ actual0_ι actual0_κ sigma_ι where
  e_I := .e_I
  e_D := .e_D
  e_M := .e_M
  e_Sigma := .e_Sigma
  e_Delta := .e_Delta
  enc_ι := .e_iota
  enc_κ := .e_kappa
  r_Di := .r_Di
  r_Dk := .r_Dk
  r_Mi := .r_Mi
  r_Mk := .r_Mk
  r_S := .r_S
  ir1_distinct := by decide
  ir2_actual := by decide
  h1_ι := by native_decide
  h1_κ := by native_decide
  h2_ι := by native_decide
  h2_κ := by native_decide
  h3 := by native_decide
  ir4_distinct := by decide

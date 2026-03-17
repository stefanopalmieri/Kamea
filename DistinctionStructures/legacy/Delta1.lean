/- # Δ₁ — The Directed Distinction Structure

   This file constructs the concrete 17-element directed model Δ₁ and
   proves all axioms, behavioral separability (Ext), homomorphism
   conditions (H1–H3), and intrinsic reflexivity (IR1–IR5).

   Δ₁ has two contexts: ι (17 distinctions) and κ (2 distinctions).
   The directed binary operation `dot` on D(ι) is defined by 26
   first-match rules. All proofs are computational via `decide` or
   `native_decide`.
-/

import DistinctionStructures.Basic

/-! ## Types -/

/-- The 17 distinctions of context ι in Δ₁. -/
inductive D1ι where
  | top   | bot            -- booleans
  | i     | k              -- context tokens
  | a     | b              -- κ-element encodings
  | e_I                    -- context tester
  | e_D   | e_M   | e_Sigma | e_Delta  -- structural encoders
  | d_I   | d_K            -- domain codes
  | m_I   | m_K            -- actuality codes
  | s_C                    -- component-set token
  | p                      -- surplus/default (non-actual)
  deriving DecidableEq, Repr

/-- The 2 distinctions of context κ in Δ₁. -/
inductive D1κ where
  | alpha | beta
  deriving DecidableEq, Repr

/-! ## Fintype instances -/

instance : Fintype D1ι where
  elems := {.top, .bot, .i, .k, .a, .b, .e_I, .e_D, .e_M, .e_Sigma,
            .e_Delta, .d_I, .d_K, .m_I, .m_K, .s_C, .p}
  complete := by intro x; cases x <;> simp

instance : Fintype D1κ where
  elems := {.alpha, .beta}
  complete := by intro x; cases x <;> simp

/-! ## The two-context system -/

/-- Contexts of Δ₁ -/
inductive Ctx1 where
  | ι | κ
  deriving DecidableEq, Repr

instance : Fintype Ctx1 where
  elems := {.ι, .κ}
  complete := by intro x; cases x <;> simp

/-- Distinctions per context -/
def Dist1 : Ctx1 → Type
  | .ι => D1ι
  | .κ => D1κ

instance (c : Ctx1) : DecidableEq (Dist1 c) := by
  cases c <;> simp [Dist1] <;> infer_instance

instance (c : Ctx1) : Fintype (Dist1 c) := by
  cases c <;> simp [Dist1] <;> infer_instance

/-! ## Actuality predicate -/

/-- M(ι) = everything except p -/
def actual_ι (d : D1ι) : Prop := d ≠ D1ι.p

/-- M(κ) = {alpha} -/
def actual_κ (d : D1κ) : Prop := d = D1κ.alpha

instance : DecidablePred actual_ι := fun d =>
  if h : d = D1ι.p then isFalse (by simp [actual_ι, h]) else isTrue (by simp [actual_ι, h])

instance : DecidablePred actual_κ := fun d =>
  if h : d = D1κ.alpha then isTrue (by simp [actual_κ, h]) else isFalse (by simp [actual_κ, h])

/-- Combined actuality -/
def actual1 : (c : Ctx1) → Dist1 c → Prop
  | .ι => actual_ι
  | .κ => actual_κ

instance (c : Ctx1) : DecidablePred (actual1 c) := by
  cases c <;> simp [actual1] <;> infer_instance

/-! ## The dot operation on D(ι)

   Defined by first-match on 26 rules (Blocks A–F).
-/

/-- The directed binary operation on D(ι).

    Block A — Boolean absorption:
      top · y = top, bot · y = bot

    Block B — Testers (boolean-valued):
      e_I · i = top, e_I · k = top, e_I · _ = bot
      d_K · a = top, d_K · b = top, d_K · _ = bot
      m_K · a = top, m_K · _ = bot
      m_I · p = bot, m_I · _ = top

    Block C — Structural encoders:
      e_D · i = d_I, e_D · k = d_K
      e_M · i = m_I, e_M · k = m_K
      e_Sigma · s_C = e_Delta
      e_Delta · e_D = d_I

    Block D — Absorption breaker:
      p · top = top

    Block E — Passive self-identification (Ext fix):
      i · top = i, k · top = k, a · top = a, b · top = b,
      d_I · top = d_I, s_C · top = s_C

    Block F — Default:
      _ · _ = p
-/
def dot : D1ι → D1ι → D1ι
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
  | .m_I,     .p     => .bot
  | .m_I,     _      => .top
  -- Block C: Structural encoders
  | .e_D,     .i     => .d_I
  | .e_D,     .k     => .d_K
  | .e_M,     .i     => .m_I
  | .e_M,     .k     => .m_K
  | .e_Sigma, .s_C   => .e_Delta
  | .e_Delta, .e_D   => .d_I
  -- Block D: Absorption breaker
  | .p,       .top   => .top
  -- Block E: Passive self-identification
  | .i,       .top   => .i
  | .k,       .top   => .k
  | .a,       .top   => .a
  | .b,       .top   => .b
  | .d_I,     .top   => .d_I
  | .s_C,     .top   => .s_C
  -- Block F: Default
  | _,        _      => .p

/-- The directed operation on D(κ). -/
def dot_κ : D1κ → D1κ → D1κ
  | .alpha, _ => .alpha
  | .beta, .beta => .beta
  | .beta, .alpha => .alpha

/-! ## Axiom verification -/

/-- A1: There exist contexts (trivial). -/
theorem delta1_A1 : Nonempty Ctx1 := ⟨.ι⟩

/-- A2: Each context has at least one actual distinction. -/
theorem delta1_A2 : ∀ (c : Ctx1), ∃ d : Dist1 c, actual1 c d := by
  intro c; cases c
  · exact ⟨.top, by decide⟩
  · exact ⟨.alpha, by decide⟩

/-- A5: There exists a non-actual distinction (p in ι). -/
theorem delta1_A5 : ∃ (c : Ctx1) (d : Dist1 c), ¬actual1 c d := by
  exact ⟨.ι, .p, by decide⟩

/-! ## Behavioral Separability (Ext) -/

/-- Ext for D(ι): For all distinct x, y there exists z with x·z ≠ y·z.
    Proved by exhaustive search over the finite domain. -/
theorem delta1_ext_ι : ∀ (x y : D1ι), x ≠ y → ∃ z : D1ι, dot x z ≠ dot y z := by
  decide

/-- Ext for D(κ): trivially satisfied. -/
theorem delta1_ext_κ : ∀ (x y : D1κ), x ≠ y → ∃ z : D1κ, dot_κ x z ≠ dot_κ y z := by
  decide

/-! ## Homomorphism conditions -/

/-- H1: dot e_D i = d_I -/
theorem delta1_H1_ι : dot .e_D .i = .d_I := by decide

/-- H1: dot e_D k = d_K -/
theorem delta1_H1_κ : dot .e_D .k = .d_K := by decide

/-- H2: dot e_M i = m_I -/
theorem delta1_H2_ι : dot .e_M .i = .m_I := by decide

/-- H2: dot e_M k = m_K -/
theorem delta1_H2_κ : dot .e_M .k = .m_K := by decide

/-- H3: dot e_Sigma s_C = e_Delta -/
theorem delta1_H3 : dot .e_Sigma .s_C = .e_Delta := by decide

/-! ## Intrinsic Reflexivity -/

/-- IR1: The four component encoders are pairwise distinct. -/
theorem delta1_IR1 : D1ι.e_I ≠ D1ι.e_D ∧ D1ι.e_I ≠ D1ι.e_M ∧
    D1ι.e_I ≠ D1ι.e_Sigma ∧ D1ι.e_D ≠ D1ι.e_M ∧
    D1ι.e_D ≠ D1ι.e_Sigma ∧ D1ι.e_M ≠ D1ι.e_Sigma := by decide

/-- IR2: All encoding elements are actual (not p). -/
theorem delta1_IR2 : actual_ι .e_I ∧ actual_ι .e_D ∧ actual_ι .e_M ∧
    actual_ι .e_Sigma ∧ actual_ι .e_Delta := by decide

/-- IR4: e_Delta is distinct from each component encoder. -/
theorem delta1_IR4 : D1ι.e_Delta ≠ D1ι.e_I ∧ D1ι.e_Delta ≠ D1ι.e_D ∧
    D1ι.e_Delta ≠ D1ι.e_M ∧ D1ι.e_Delta ≠ D1ι.e_Sigma := by decide

/-- IR5: p is not in the range of the encoding (p is the only non-actual element). -/
theorem delta1_IR5 : D1ι.p ≠ D1ι.e_I ∧ D1ι.p ≠ D1ι.e_D ∧ D1ι.p ≠ D1ι.e_M ∧
    D1ι.p ≠ D1ι.e_Sigma ∧ D1ι.p ≠ D1ι.e_Delta ∧
    D1ι.p ≠ D1ι.i ∧ D1ι.p ≠ D1ι.k ∧
    D1ι.p ≠ D1ι.a ∧ D1ι.p ≠ D1ι.b ∧
    D1ι.p ≠ D1ι.d_I ∧ D1ι.p ≠ D1ι.d_K ∧
    D1ι.p ≠ D1ι.m_I ∧ D1ι.p ≠ D1ι.m_K ∧
    D1ι.p ≠ D1ι.s_C := by decide

/-- A7′ (Structural Novelty) for the directed case:
    S = {e_I, e_D, e_M, e_Sigma} with δ* = e_Delta (via synthesis of component set).
    e_Delta ∉ S, and using witness t = e_D:
      dot e_Delta e_D = d_I ≠ dot e_I e_D = bot
      dot e_Delta e_D = d_I ≠ dot e_D e_D = p
      dot e_Delta e_D = d_I ≠ dot e_M e_D = p
      dot e_Delta e_D = d_I ≠ dot e_Sigma e_D = p -/
theorem delta1_A7' :
    dot .e_Delta .e_D ≠ dot .e_I .e_D ∧
    dot .e_Delta .e_D ≠ dot .e_D .e_D ∧
    dot .e_Delta .e_D ≠ dot .e_M .e_D ∧
    dot .e_Delta .e_D ≠ dot .e_Sigma .e_D := by decide

/-! ## DirectedDS instance for Δ₁ -/

/-- The directed distinction structure on D(ι). -/
def delta1_dirDS : DirectedDS D1ι where
  actual := actual_ι
  dot := dot

instance : DecidablePred delta1_dirDS.actual := inferInstanceAs (DecidablePred actual_ι)

theorem delta1_dirDS_A2 : delta1_dirDS.A2 := ⟨.top, by decide⟩
theorem delta1_dirDS_A5 : delta1_dirDS.A5 := ⟨.p, by decide⟩
theorem delta1_dirDS_Ext : delta1_dirDS.Ext := delta1_ext_ι

/-- A7′ (Structural Novelty) for the directed case as a unified proposition.
    Witness: S = {e_I, e_D, e_M, e_Sigma}, δ* = e_Delta, t = e_D.
    e_Delta ∉ S and for all d ∈ S, dot e_Delta e_D ≠ dot d e_D. -/
theorem delta1_dirDS_A7' :
    ∃ (S : Finset D1ι),
      2 ≤ S.card ∧
      (∀ d ∈ S, actual_ι d) ∧
      dot (dot .e_Sigma .s_C) .e_D ≠ dot .e_I .e_D ∧
      dot (dot .e_Sigma .s_C) .e_D ≠ dot .e_D .e_D ∧
      dot (dot .e_Sigma .s_C) .e_D ≠ dot .e_M .e_D ∧
      dot (dot .e_Sigma .s_C) .e_D ≠ dot .e_Sigma .e_D := by
  refine ⟨{D1ι.e_I, D1ι.e_D, D1ι.e_M, D1ι.e_Sigma}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · intro d hd; simp [Finset.mem_insert] at hd; rcases hd with h | h | h | h <;> subst h <;> decide
  · decide
  · decide
  · decide
  · decide

/-- The DirectedIR structure witnessing intrinsic reflexivity of Δ₁. -/
def delta1_IR : DirectedIR D1ι D1κ actual_ι actual_κ dot where
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

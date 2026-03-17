/- # Automorphism Rigidity of Δ₁

   Every magma automorphism f : D1ι → D1ι (injective homomorphism) is the identity.

   NOTE: The original conjecture in Sheaf.lean omitted injectivity. The constant
   functions to top, bot, or p are all non-identity endomorphisms, so injectivity
   is required.

   Proof: chain through the recovery filtration from Discoverable.lean, proving
   f fixes each element in turn using previously-fixed elements + homomorphism eqs.
-/

import DistinctionStructures.Delta1
import DistinctionStructures.Discoverable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

open D1ι

set_option maxHeartbeats 1600000

-- Cayley table helper lemmas
private theorem dot_self_top_cases :
    ∀ x : D1ι, dot x x = top → (x = top ∨ x = m_I) := by decide
private theorem dot_eI_x_top_cases :
    ∀ x : D1ι, dot e_I x = top → (x = i ∨ x = k) := by decide
private theorem no_x_dot_k_eq_m_I :
    ∀ x : D1ι, dot x k ≠ m_I := by decide
private theorem dot_x_eD_dI_cases :
    ∀ x : D1ι, dot x e_D = d_I → x = e_Delta := by decide
private theorem dot_mK_x_top_cases :
    ∀ x : D1ι, dot m_K x = top → x = a := by decide
private theorem dot_dK_x_top_cases :
    ∀ x : D1ι, dot d_K x = top → (x = a ∨ x = b) := by decide
private theorem dot_xy_eDelta_cases :
    ∀ x y : D1ι, dot x y = e_Delta → (x = top ∨ x = e_Sigma ∧ y = s_C) := by native_decide
private theorem universal_absorber :
    ∀ x : D1ι, (∀ y : D1ι, dot x y = x) → (x = top ∨ x = bot) := by decide
private theorem eM_unique :
    ∀ x : D1ι, dot x i = m_I → dot x k = m_K → x = e_M := by decide
private theorem eD_from_dot_k :
    ∀ x : D1ι, dot x k = d_K → x = e_D := by decide
private theorem eSigma_sC_unique :
    ∀ x : D1ι, dot e_Sigma x = e_Delta → x = s_C := by decide
-- Accept-card characterization for testers (card 2 = e_I or d_K)
private theorem tester_card_16 :
    ∀ x : D1ι, x = e_I ∨ x = d_K ∨ x = m_K ∨ x = m_I →
    (Finset.univ.filter (fun y => dot x y = top)).card = 16 → x = m_I := by native_decide
private theorem tester_card_1 :
    ∀ x : D1ι, x = e_I ∨ x = d_K ∨ x = m_K ∨ x = m_I →
    (Finset.univ.filter (fun y => dot x y = top)).card = 1 → x = m_K := by native_decide
-- Dot m_K on d_K-accept set: characterize which d_K-accept elements m_K also accepts
private theorem dot_mK_dK_accept :
    ∀ x : D1ι, dot d_K x = top → dot m_K x = top → x = a := by decide
private theorem dot_mK_dK_reject :
    ∀ x : D1ι, dot d_K x = top → dot m_K x = bot → x = b := by decide

-- Surjectivity from injectivity on D1ι
set_option maxHeartbeats 4000000 in
private theorem D1ι_surj_of_inj {f : D1ι → D1ι} (hinj : Function.Injective f) :
    Function.Surjective f := by
  haveI : Finite D1ι := Finite.of_fintype D1ι
  exact Finite.surjective_of_injective hinj

-- Helper: injectivity-based exclusion
private theorem fne {f : D1ι → D1ι} (hinj : Function.Injective f)
    (x y : D1ι) (hxy : x ≠ y) (hfy : f y = y) : f x ≠ y :=
  fun h => hxy (hinj (h.trans hfy.symm))

-- Accept cardinality preservation
private theorem accept_card {f : D1ι → D1ι}
    (htop : f top = top) (hinj : Function.Injective f)
    (fsurj : Function.Surjective f)
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (x : D1ι) :
    (Finset.univ.filter (fun y => dot (f x) y = top)).card =
    (Finset.univ.filter (fun y => dot x y = top)).card := by
  suffices h : Finset.univ.filter (fun y => dot (f x) y = top) =
      (Finset.univ.filter (fun z => dot x z = top)).image f by
    rw [h, Finset.card_image_of_injective _ hinj]
  ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hw; obtain ⟨z, rfl⟩ := fsurj w
    refine ⟨z, ?_, rfl⟩
    have heq := hf x z
    have : f (dot x z) = top := heq.trans hw
    exact hinj (this.trans htop.symm)
  · rintro ⟨z, hz, rfl⟩
    have heq := hf x z; rw [hz, htop] at heq; exact heq.symm

-- Phase 1: Boolean fixpoints

private theorem fix_top {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f top = top := by
  have fsurj := D1ι_surj_of_inj hinj
  have abs : ∀ w : D1ι, dot (f top) w = f top := by
    intro w; obtain ⟨z, rfl⟩ := fsurj w
    have := hf top z; simp only [dot] at this; exact this.symm
  by_contra hne
  rcases universal_absorber (f top) abs with htop_eq | htop_eq
  · exact hne htop_eq
  · -- f top = bot
    have fbot_abs : ∀ w : D1ι, dot (f bot) w = f bot := by
      intro w; obtain ⟨z, rfl⟩ := fsurj w
      have := hf bot z; simp only [dot] at this; exact this.symm
    have fbot_ne_bot : f bot ≠ bot := by
      intro h; exact absurd (hinj (h.trans htop_eq.symm)) (by decide)
    rcases universal_absorber (f bot) fbot_abs with fbot_eq | fbot_eq
    · -- f bot = top
      have h1 := hf e_I e_I
      have : dot e_I e_I = bot := by decide
      rw [this, fbot_eq] at h1
      -- h1 : top = dot (f e_I) (f e_I)
      have h2 := hf d_K d_K
      have : dot d_K d_K = bot := by decide
      rw [this, fbot_eq] at h2
      -- h2 : top = dot (f d_K) (f d_K)
      have feI_mI : f e_I = m_I := by
        rcases dot_self_top_cases (f e_I) h1.symm with h | h
        · exact absurd (hinj (h.trans fbot_eq.symm)) (by decide)
        · exact h
      have fdK_mI : f d_K = m_I := by
        rcases dot_self_top_cases (f d_K) h2.symm with h | h
        · exact absurd (hinj (h.trans fbot_eq.symm)) (by decide)
        · exact h
      exact absurd (hinj (feI_mI.trans fdK_mI.symm)) (by decide)
    · exact fbot_ne_bot fbot_eq

private theorem fix_bot {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f bot = bot := by
  have fsurj := D1ι_surj_of_inj hinj
  have htop := fix_top hf hinj
  have abs : ∀ w : D1ι, dot (f bot) w = f bot := by
    intro w; obtain ⟨z, rfl⟩ := fsurj w
    have := hf bot z; simp only [dot] at this; exact this.symm
  rcases universal_absorber (f bot) abs with h | h
  · exact absurd (hinj (h.trans htop.symm)) (by decide)
  · exact h

-- Phase 2: Tester identification

private theorem tester_image {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f)
    (x : D1ι) (hnt : x ≠ top) (hnb : x ≠ bot)
    (ht : ∀ y, dot x y = top ∨ dot x y = bot) :
    f x = e_I ∨ f x = d_K ∨ f x = m_K ∨ f x = m_I := by
  have htop := fix_top hf hinj
  have hbot := fix_bot hf hinj
  have fsurj := D1ι_surj_of_inj hinj
  have hfnt : f x ≠ top := fne hinj x top hnt htop
  have hfnb : f x ≠ bot := fne hinj x bot hnb hbot
  have : ∀ w, dot (f x) w = top ∨ dot (f x) w = bot := by
    intro w; obtain ⟨z, rfl⟩ := fsurj w
    rcases ht z with h | h
    · left; have := hf x z; rw [h, htop] at this; exact this.symm
    · right; have := hf x z; rw [h, hbot] at this; exact this.symm
  exact (tester_characterization (f x) hfnt hfnb).mp this

private theorem fix_m_I {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f m_I = m_I := by
  have htop := fix_top hf hinj
  have fsurj := D1ι_surj_of_inj hinj
  have hcard := accept_card htop hinj fsurj hf m_I
  have : (Finset.univ.filter (fun y => dot m_I y = top)).card = 16 := by native_decide
  rw [this] at hcard
  exact tester_card_16 (f m_I)
    (tester_image hf hinj m_I (by decide) (by decide) (by decide))
    hcard

private theorem fix_m_K {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f m_K = m_K := by
  have htop := fix_top hf hinj
  have fsurj := D1ι_surj_of_inj hinj
  have hcard := accept_card htop hinj fsurj hf m_K
  have : (Finset.univ.filter (fun y => dot m_K y = top)).card = 1 := by native_decide
  rw [this] at hcard
  exact tester_card_1 (f m_K)
    (tester_image hf hinj m_K (by decide) (by decide) (by decide))
    hcard

-- e_I vs d_K: both have accept card 2. Distinguish structurally.
-- If f e_I = d_K, then from hf e_I i: top = dot d_K (f i), so f i ∈ {a,b}.
-- From hf m_K i: bot = dot m_K (f i). But dot m_K a = top, so f i = b.
-- From hf m_K k: bot = dot m_K (f k). If f k ∈ {a,b} too, then f k = b = f i,
-- contradicting injectivity. Actually need f k from hf e_I k: top = dot d_K (f k),
-- so f k ∈ {a,b}, f k ≠ f i = b, so f k = a. Then dot m_K a = top but we need
-- f(dot m_K k) = f(bot) = bot = dot m_K (f k) = dot m_K a = top. Contradiction!

private theorem fix_e_I {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f e_I = e_I := by
  have htop := fix_top hf hinj
  have hbot := fix_bot hf hinj
  have hmI := fix_m_I hf hinj
  have hmK := fix_m_K hf hinj
  rcases tester_image hf hinj e_I (by decide) (by decide) (by decide) with h | h | h | h
  · exact h
  · exfalso -- f e_I = d_K
    -- From hf e_I i and hf e_I k with f e_I = d_K:
    have h_eIi := hf e_I i; simp only [dot] at h_eIi; rw [htop, h] at h_eIi
    have h_eIk := hf e_I k; simp only [dot] at h_eIk; rw [htop, h] at h_eIk
    -- h_eIi : top = dot d_K (f i), h_eIk : top = dot d_K (f k)
    have fi_ab := dot_dK_x_top_cases (f i) h_eIi.symm
    -- From hf m_K i: f(bot) = dot m_K (f i), i.e. bot = dot m_K (f i)
    have h_mKi := hf m_K i
    have hdot_mKi : dot m_K i = bot := by decide
    rw [hdot_mKi, hbot, hmK] at h_mKi
    -- h_mKi : bot = dot m_K (f i)
    -- dot m_K a = top ≠ bot, so f i ≠ a, hence f i = b
    have fi_b : f i = b := by
      rcases fi_ab with hi | hi
      · exfalso; rw [hi] at h_mKi
        have : dot m_K a = top := by decide
        rw [this] at h_mKi; exact absurd h_mKi (by decide)
      · exact hi
    -- f k ∈ {a,b}, f k ≠ f i = b, so f k = a
    have fk_ab := dot_dK_x_top_cases (f k) h_eIk.symm
    have fk_a : f k = a := by
      rcases fk_ab with hk | hk
      · exact hk
      · exfalso; exact absurd (hinj (hk.trans fi_b.symm)) (by decide)
    -- hf m_K k: f(bot) = dot m_K (f k) = dot m_K a = top
    have h_mKk := hf m_K k
    have hdot_mKk : dot m_K k = bot := by decide
    rw [hdot_mKk, hbot, hmK, fk_a] at h_mKk
    -- h_mKk : bot = dot m_K a, i.e. bot = top
    have : dot m_K a = top := by decide
    rw [this] at h_mKk
    exact absurd h_mKk (by decide)
  · exact absurd (h.trans hmK.symm) (fun heq => absurd (hinj heq) (by decide))
  · exact absurd (h.trans hmI.symm) (fun heq => absurd (hinj heq) (by decide))

private theorem fix_d_K {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f d_K = d_K := by
  have heI := fix_e_I hf hinj
  have hmI := fix_m_I hf hinj
  have hmK := fix_m_K hf hinj
  rcases tester_image hf hinj d_K (by decide) (by decide) (by decide) with h | h | h | h
  · exact absurd (h.trans heI.symm) (fun heq => absurd (hinj heq) (by decide))
  · exact h
  · exact absurd (h.trans hmK.symm) (fun heq => absurd (hinj heq) (by decide))
  · exact absurd (h.trans hmI.symm) (fun heq => absurd (hinj heq) (by decide))

-- Phase 3: Context tokens

private theorem fix_i {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f i = i := by
  have htop := fix_top hf hinj
  have heI := fix_e_I hf hinj
  have hmI := fix_m_I hf hinj
  have h_eIi := hf e_I i; simp only [dot] at h_eIi; rw [htop, heI] at h_eIi
  rcases dot_eI_x_top_cases (f i) h_eIi.symm with h | h
  · exact h
  · exfalso
    have h_eMi := hf e_M i; simp only [dot] at h_eMi; rw [hmI, h] at h_eMi
    exact no_x_dot_k_eq_m_I (f e_M) h_eMi.symm

private theorem fix_k {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f k = k := by
  have htop := fix_top hf hinj
  have heI := fix_e_I hf hinj
  have hi := fix_i hf hinj
  have h_eIk := hf e_I k; simp only [dot] at h_eIk; rw [htop, heI] at h_eIk
  rcases dot_eI_x_top_cases (f k) h_eIk.symm with h | h
  · exact absurd (h.trans hi.symm) (fun heq => absurd (hinj heq) (by decide))
  · exact h

-- Phase 4: Encoder pair

private theorem fix_e_M {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f e_M = e_M := by
  have hmI := fix_m_I hf hinj; have hmK := fix_m_K hf hinj
  have hi := fix_i hf hinj; have hk := fix_k hf hinj
  have h1 := hf e_M i; simp only [dot] at h1; rw [hmI, hi] at h1
  have h2 := hf e_M k; simp only [dot] at h2; rw [hmK, hk] at h2
  exact eM_unique (f e_M) h1.symm h2.symm

private theorem fix_e_D {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f e_D = e_D := by
  have hdK := fix_d_K hf hinj; have hk := fix_k hf hinj
  have h1 := hf e_D k; simp only [dot] at h1; rw [hdK, hk] at h1
  exact eD_from_dot_k (f e_D) h1.symm

-- Phase 5: Derived elements

private theorem fix_d_I {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f d_I = d_I := by
  have heD := fix_e_D hf hinj; have hi := fix_i hf hinj
  have := hf e_D i; simp only [dot] at this; rw [heD, hi] at this; exact this

private theorem fix_p {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f p = p := by
  have hmI := fix_m_I hf hinj; have hbot := fix_bot hf hinj
  have := hf m_I p; simp only [dot] at this; rw [hmI, hbot] at this
  exact (junk_identification (f p)).mp this.symm

private theorem fix_e_Delta {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f e_Delta = e_Delta := by
  have hdI := fix_d_I hf hinj; have heD := fix_e_D hf hinj
  have := hf e_Delta e_D; simp only [dot] at this; rw [hdI, heD] at this
  exact dot_x_eD_dI_cases (f e_Delta) this.symm

private theorem fix_e_Sigma {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f e_Sigma = e_Sigma := by
  have heDelta := fix_e_Delta hf hinj; have htop := fix_top hf hinj
  have := hf e_Sigma s_C; simp only [dot] at this; rw [heDelta] at this
  rcases dot_xy_eDelta_cases (f e_Sigma) (f s_C) this.symm with h | ⟨h, _⟩
  · exact absurd h (fne hinj e_Sigma top (by decide) htop)
  · exact h

private theorem fix_s_C {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f s_C = s_C := by
  have heSigma := fix_e_Sigma hf hinj; have heDelta := fix_e_Delta hf hinj
  have := hf e_Sigma s_C; simp only [dot] at this; rw [heDelta, heSigma] at this
  exact eSigma_sC_unique (f s_C) this.symm

private theorem fix_a {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f a = a := by
  have hmK := fix_m_K hf hinj; have htop := fix_top hf hinj
  have := hf m_K a; simp only [dot] at this; rw [hmK, htop] at this
  exact dot_mK_x_top_cases (f a) this.symm

private theorem fix_b {f : D1ι → D1ι}
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) : f b = b := by
  have hdK := fix_d_K hf hinj; have htop := fix_top hf hinj; have ha := fix_a hf hinj
  have := hf d_K b; simp only [dot] at this; rw [hdK, htop] at this
  rcases dot_dK_x_top_cases (f b) this.symm with h | h
  · exact absurd (h.trans ha.symm) (fun heq => absurd (hinj heq) (by decide))
  · exact h

-- Main theorem

/-- Every injective magma endomorphism of (D1ι, dot) is the identity.

    This resolves the conjecture from Sheaf.lean (lines 577-593), corrected
    to require injectivity. The proof follows the 8-step recovery filtration
    from Discoverable.lean: each element is pinned in turn using the
    homomorphism equation and previously-fixed elements. -/
theorem rigid_automorphism (f : D1ι → D1ι)
    (hf : ∀ x y : D1ι, f (dot x y) = dot (f x) (f y))
    (hinj : Function.Injective f) :
    ∀ x : D1ι, f x = x := by
  intro x; cases x
  · exact fix_top hf hinj
  · exact fix_bot hf hinj
  · exact fix_i hf hinj
  · exact fix_k hf hinj
  · exact fix_a hf hinj
  · exact fix_b hf hinj
  · exact fix_e_I hf hinj
  · exact fix_e_D hf hinj
  · exact fix_e_M hf hinj
  · exact fix_e_Sigma hf hinj
  · exact fix_e_Delta hf hinj
  · exact fix_d_I hf hinj
  · exact fix_d_K hf hinj
  · exact fix_m_I hf hinj
  · exact fix_m_K hf hinj
  · exact fix_s_C hf hinj
  · exact fix_p hf hinj

-- Counterexamples: injectivity is necessary

/-- The constant functions to top, bot, and p are non-identity endomorphisms,
    showing that injectivity is necessary for rigidity. -/
theorem const_top_endomorphism :
    ∀ x y : D1ι, (fun _ => top) (dot x y) = dot ((fun _ => top) x) ((fun _ => top) y) := by
  decide

theorem const_bot_endomorphism :
    ∀ x y : D1ι, (fun _ => bot) (dot x y) = dot ((fun _ => bot) x) ((fun _ => bot) y) := by
  decide

theorem const_p_endomorphism :
    ∀ x y : D1ι, (fun _ => p) (dot x y) = dot ((fun _ => p) x) ((fun _ => p) y) := by
  decide

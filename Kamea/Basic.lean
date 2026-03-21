/- # Distinction Structures — Abstract Definitions

   This file defines the abstract notion of a Distinction Structure (DS)
   as a quadruple ⟨𝐈, D, M, Σ⟩ together with the axioms A1–A7′, Ext,
   and intrinsic reflexivity conditions IR1–IR5.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-! ## Symmetric Distinction Structures -/

/-- A Distinction Structure with a single context type `D` and synthesis on Finsets.
    We parametrize by a single context for simplicity; the concrete models
    handle multiple contexts directly. -/
structure SymmetricDS (D : Type) [DecidableEq D] [Fintype D] where
  /-- Actuality predicate: whether a distinction is in M -/
  actual : D → Prop
  /-- Decidable actuality -/
  [actualDec : DecidablePred actual]
  /-- Synthesis function on finite subsets of D -/
  synth : Finset D → D

namespace SymmetricDS

variable {D : Type} [DecidableEq D] [Fintype D] (ds : SymmetricDS D)

/-- A2 (Sustenance): At least one actual distinction. -/
def A2 : Prop := ∃ d : D, ds.actual d

/-- A5 (Selectivity): Some distinction is non-actual. -/
def A5 : Prop := ∃ d : D, ¬ds.actual d

/-- A6 (Total Synthesis): Singletons map to themselves. -/
def A6 : Prop := ∀ d : D, ds.synth {d} = d

/-- Ext (Behavioral Separability): Distinct elements are separable by Σ. -/
def Ext : Prop := ∀ a b : D, a ≠ b → ∃ y : D,
  ds.synth {a, y} ≠ ds.synth {b, y}

/-- A7′ (Structural Novelty): Synthesis produces genuinely new elements. -/
def A7' : Prop := ∃ (S : Finset D),
  2 ≤ S.card ∧
  (∀ d ∈ S, ds.actual d) ∧
  ds.synth S ∉ S ∧
  ∃ t : D, ∀ d ∈ S,
    ds.synth {ds.synth S, t} ≠ ds.synth {d, t}

end SymmetricDS

/-! ## Directed Distinction Structures -/

/-- A Directed Distinction Structure replaces set-based Σ with a
    binary operation `dot : D → D → D`. -/
structure DirectedDS (D : Type) [DecidableEq D] [Fintype D] where
  /-- Actuality predicate -/
  actual : D → Prop
  /-- Decidable actuality -/
  [actualDec : DecidablePred actual]
  /-- Binary synthesis operation -/
  dot : D → D → D

namespace DirectedDS

variable {D : Type} [DecidableEq D] [Fintype D] (ds : DirectedDS D)

/-- A2: At least one actual distinction. -/
def A2 : Prop := ∃ d : D, ds.actual d

/-- A5: Some distinction is non-actual. -/
def A5 : Prop := ∃ d : D, ¬ds.actual d

/-- Directed Ext: For all distinct x, y there exists z with x·z ≠ y·z. -/
def Ext : Prop := ∀ x y : D, x ≠ y → ∃ z : D, ds.dot x z ≠ ds.dot y z

end DirectedDS

/-! ## Intrinsic Reflexivity for Directed DS

    Specialized to a two-context system with binary operation on the
    primary context. -/

/-- Intrinsic reflexivity witness for a directed DS over type D_ι. -/
structure DirectedIR
    (D_ι : Type) (D_κ : Type)
    (actual_ι : D_ι → Prop) (actual_κ : D_κ → Prop)
    (dot_ι : D_ι → D_ι → D_ι)
    where
  /-- Component encoder for 𝐈 -/
  e_I : D_ι
  /-- Component encoder for D -/
  e_D : D_ι
  /-- Component encoder for M -/
  e_M : D_ι
  /-- Component encoder for Σ -/
  e_Sigma : D_ι
  /-- Whole-structure encoder -/
  e_Delta : D_ι
  /-- Context encoder for ι -/
  enc_ι : D_ι
  /-- Context encoder for κ -/
  enc_κ : D_ι
  /-- Domain code for ι -/
  d_I : D_ι
  /-- Domain code for κ -/
  d_K : D_ι
  /-- Actuality code for ι -/
  m_I : D_ι
  /-- Actuality code for κ -/
  m_K : D_ι
  /-- Component-set token -/
  s_C : D_ι
  /-- IR1: The four component encoders are pairwise distinct -/
  ir1_distinct : e_I ≠ e_D ∧ e_I ≠ e_M ∧ e_I ≠ e_Sigma ∧
                 e_D ≠ e_M ∧ e_D ≠ e_Sigma ∧ e_M ≠ e_Sigma
  /-- IR2: All encoding elements are actual -/
  ir2_actual : actual_ι e_I ∧ actual_ι e_D ∧ actual_ι e_M ∧
               actual_ι e_Sigma ∧ actual_ι e_Delta
  /-- H1: dot e_D (enc_K) = domain code for K -/
  h1_ι : dot_ι e_D enc_ι = d_I
  h1_κ : dot_ι e_D enc_κ = d_K
  /-- H2: dot e_M (enc_K) = actuality code for K -/
  h2_ι : dot_ι e_M enc_ι = m_I
  h2_κ : dot_ι e_M enc_κ = m_K
  /-- H3: dot e_Sigma s_C = e_Delta -/
  h3 : dot_ι e_Sigma s_C = e_Delta
  /-- IR4: e_Delta is distinct from the component encoders -/
  ir4_distinct : e_Delta ≠ e_I ∧ e_Delta ≠ e_D ∧ e_Delta ≠ e_M ∧ e_Delta ≠ e_Sigma

/-! ## Intrinsic Reflexivity for Symmetric DS

    Specialized to a two-context system with set-based synthesis on the
    primary context. -/

/-- Intrinsic reflexivity witness for a symmetric DS over type D_ι. -/
structure SymmetricIR
    (D_ι : Type) (D_κ : Type)
    [DecidableEq D_ι]
    (actual_ι : D_ι → Prop) (actual_κ : D_κ → Prop)
    (synth_ι : Finset D_ι → D_ι)
    where
  /-- Component encoder for 𝐈 -/
  e_I : D_ι
  /-- Component encoder for D -/
  e_D : D_ι
  /-- Component encoder for M -/
  e_M : D_ι
  /-- Component encoder for Σ -/
  e_Sigma : D_ι
  /-- Whole-structure encoder -/
  e_Delta : D_ι
  /-- Context encoder for ι -/
  enc_ι : D_ι
  /-- Context encoder for κ -/
  enc_κ : D_ι
  /-- Set encoder: domain of ι -/
  r_Di : D_ι
  /-- Set encoder: domain of κ -/
  r_Dk : D_ι
  /-- Set encoder: actuality of ι -/
  r_Mi : D_ι
  /-- Set encoder: actuality of κ -/
  r_Mk : D_ι
  /-- Component-set encoder -/
  r_S : D_ι
  /-- IR1: The four component encoders are pairwise distinct -/
  ir1_distinct : e_I ≠ e_D ∧ e_I ≠ e_M ∧ e_I ≠ e_Sigma ∧
                 e_D ≠ e_M ∧ e_D ≠ e_Sigma ∧ e_M ≠ e_Sigma
  /-- IR2: All encoding elements are actual -/
  ir2_actual : actual_ι e_I ∧ actual_ι e_D ∧ actual_ι e_M ∧
               actual_ι e_Sigma ∧ actual_ι e_Delta
  /-- H1: synth {e_D, enc_ι} = r_Di -/
  h1_ι : synth_ι {e_D, enc_ι} = r_Di
  /-- H1: synth {e_D, enc_κ} = r_Dk -/
  h1_κ : synth_ι {e_D, enc_κ} = r_Dk
  /-- H2: synth {e_M, enc_ι} = r_Mi -/
  h2_ι : synth_ι {e_M, enc_ι} = r_Mi
  /-- H2: synth {e_M, enc_κ} = r_Mk -/
  h2_κ : synth_ι {e_M, enc_κ} = r_Mk
  /-- H3: synth {e_Sigma, r_S} = e_Delta -/
  h3 : synth_ι {e_Sigma, r_S} = e_Delta
  /-- IR4: e_Delta is distinct from the component encoders -/
  ir4_distinct : e_Delta ≠ e_I ∧ e_Delta ≠ e_D ∧ e_Delta ≠ e_M ∧ e_Delta ≠ e_Sigma

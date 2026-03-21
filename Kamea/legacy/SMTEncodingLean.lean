/- # Lean Formalization of the N=17 Fixed-Role SMT Encoding

This file mirrors the `ds_search.py` fixed-role N=17 encoding assumptions
in Lean (non-relaxed, Block-F/default-p active) and proves:

1. `dot` from `Delta1.lean` satisfies the full assumption set.
2. Any table satisfying those assumptions equals `dot`.
3. Therefore `assumptions ∧ exclude_delta1` is UNSAT in Lean.

Scope: this corresponds to the N=17 fixed-role table encoding with Block F,
not the weaker abstract base DirectedDS axioms.
-/

import Kamea.Delta1

namespace SMTEncodingLean

open D1ι

/-- Core positions explicitly constrained by non-default SMT rules
    (Blocks A–E + H/A7' + fixed discovery constraints). -/
def isCoreConstrained (x y : D1ι) : Prop :=
  x = .top ∨ x = .bot ∨ x = .e_I ∨ x = .d_K ∨ x = .m_K ∨ x = .m_I ∨
  (x = .e_D ∧ (y = .i ∨ y = .k)) ∨
  (x = .e_M ∧ (y = .i ∨ y = .k)) ∨
  (x = .e_Sigma ∧ y = .s_C) ∨
  (x = .e_Delta ∧ y = .e_D) ∨
  (x = .p ∧ y = .top) ∨
  (y = .top ∧ (x = .i ∨ x = .k ∨ x = .a ∨ x = .b ∨ x = .d_I ∨ x = .s_C))

def nontrivialOut (v : D1ι) : Prop :=
  v ≠ .top ∧ v ≠ .bot ∧ v ≠ .p

/-- Full N=17 fixed-role SMT assumption set (non-relaxed). -/
structure SMT17Assumptions (tbl : D1ι → D1ι → D1ι) : Prop where
  -- A.1/A.2 absorbers
  top_row : ∀ y : D1ι, tbl .top y = .top
  bot_row : ∀ y : D1ι, tbl .bot y = .bot
  -- A.4 exactly two absorbers
  no_third_absorber : ∀ x : D1ι, x ≠ .top → x ≠ .bot → ∃ y : D1ι, tbl x y ≠ x

  -- Tester rows are boolean-valued
  tester_rows_boolean :
    ∀ x : D1ι,
      (x = .e_I ∨ x = .d_K ∨ x = .m_K ∨ x = .m_I) →
      ∀ y : D1ι, tbl x y = .top ∨ tbl x y = .bot
  -- Exactly four testers
  non_testers_have_nonbool :
    ∀ x : D1ι,
      x ≠ .top → x ≠ .bot → x ≠ .e_I → x ≠ .d_K → x ≠ .m_K → x ≠ .m_I →
      ∃ y : D1ι, tbl x y ≠ .top ∧ tbl x y ≠ .bot

  -- Exact tester partitions
  eI_row : ∀ y : D1ι, tbl .e_I y = (if y = .i ∨ y = .k then .top else .bot)
  dK_row : ∀ y : D1ι, tbl .d_K y = (if y = .a ∨ y = .b then .top else .bot)
  mK_row : ∀ y : D1ι, tbl .m_K y = (if y = .a then .top else .bot)
  mI_row : ∀ y : D1ι, tbl .m_I y = (if y = .p then .bot else .top)

  -- Ext
  ext : ∀ x y : D1ι, x ≠ y → ∃ z : D1ι, tbl x z ≠ tbl y z

  -- H conditions
  h1_i : tbl .e_D .i = .d_I
  h1_k : tbl .e_D .k = .d_K
  h2_i : tbl .e_M .i = .m_I
  h2_k : tbl .e_M .k = .m_K
  h3 : tbl .e_Sigma .s_C = .e_Delta

  -- Block D / E
  p_top : tbl .p .top = .top
  self_i : tbl .i .top = .i
  self_k : tbl .k .top = .k
  self_a : tbl .a .top = .a
  self_b : tbl .b .top = .b
  self_dI : tbl .d_I .top = .d_I
  self_sC : tbl .s_C .top = .s_C

  -- A7'
  eDelta_eD_eq : tbl .e_Delta .e_D = .d_I
  eDelta_ne_eI_eD : tbl .e_Delta .e_D ≠ tbl .e_I .e_D
  eDelta_ne_eD_eD : tbl .e_Delta .e_D ≠ tbl .e_D .e_D
  eDelta_ne_eM_eD : tbl .e_Delta .e_D ≠ tbl .e_M .e_D
  eDelta_ne_eSigma_eD : tbl .e_Delta .e_D ≠ tbl .e_Sigma .e_D

  -- Discovery uniqueness constraints used by SMT encoding
  dI_not_tester : ∃ y : D1ι, tbl .d_I y ≠ .top ∧ tbl .d_I y ≠ .bot
  only_eD_eM_nontrivial_on_i_k :
    ∀ x : D1ι, x ≠ .e_D → x ≠ .e_M →
      ¬ (nontrivialOut (tbl x .i) ∧ nontrivialOut (tbl x .k))
  inert_kappa :
    ∀ x : D1ι,
      x ≠ .top → x ≠ .bot → x ≠ .e_I → x ≠ .d_K → x ≠ .m_K → x ≠ .m_I →
      (tbl x .a = .top ∨ tbl x .a = .bot ∨ tbl x .a = .p) ∧
      (tbl x .b = .top ∨ tbl x .b = .bot ∨ tbl x .b = .p)

  -- Block F default behavior
  default_p :
    ∀ x y : D1ι, ¬ isCoreConstrained x y → tbl x y = .p

def excludeDelta1 (tbl : D1ι → D1ι → D1ι) : Prop :=
  ∃ x y : D1ι, tbl x y ≠ dot x y

theorem dot_satisfies_smt17 : SMT17Assumptions dot := by
  refine
    { top_row := by native_decide
      bot_row := by native_decide
      no_third_absorber := by native_decide
      tester_rows_boolean := by native_decide
      non_testers_have_nonbool := by native_decide
      eI_row := by native_decide
      dK_row := by native_decide
      mK_row := by native_decide
      mI_row := by native_decide
      ext := delta1_ext_ι
      h1_i := by native_decide
      h1_k := by native_decide
      h2_i := by native_decide
      h2_k := by native_decide
      h3 := by native_decide
      p_top := by native_decide
      self_i := by native_decide
      self_k := by native_decide
      self_a := by native_decide
      self_b := by native_decide
      self_dI := by native_decide
      self_sC := by native_decide
      eDelta_eD_eq := by native_decide
      eDelta_ne_eI_eD := by native_decide
      eDelta_ne_eD_eD := by native_decide
      eDelta_ne_eM_eD := by native_decide
      eDelta_ne_eSigma_eD := by native_decide
      dI_not_tester := by native_decide
      only_eD_eM_nontrivial_on_i_k := by
        intro x hxD hxM
        cases x <;> simp_all [nontrivialOut, dot]
      inert_kappa := by native_decide
      default_p := by
        intro x y hnc
        cases x <;> cases y <;> simp_all [isCoreConstrained, dot] }

theorem table_eq_dot {tbl : D1ι → D1ι → D1ι} (h : SMT17Assumptions tbl) :
    tbl = dot := by
  funext x y
  by_cases hc : isCoreConstrained x y
  · cases x <;> cases y <;>
      simp [isCoreConstrained, dot] at hc ⊢
      <;> first
        | exact h.top_row _
        | exact h.bot_row _
        | simpa using h.eI_row _
        | simpa using h.dK_row _
        | simpa using h.mK_row _
        | simpa using h.mI_row _
        | simpa using h.h1_i
        | simpa using h.h1_k
        | simpa using h.h2_i
        | simpa using h.h2_k
        | simpa using h.h3
        | simpa using h.eDelta_eD_eq
        | simpa using h.p_top
        | simpa using h.self_i
        | simpa using h.self_k
        | simpa using h.self_a
        | simpa using h.self_b
        | simpa using h.self_dI
        | simpa using h.self_sC
  · have hp : tbl x y = .p := h.default_p x y hc
    cases x <;> cases y <;> simp [isCoreConstrained, dot] at hc ⊢
    all_goals simpa using hp

theorem uniqueness_smt17 : ∃! tbl : D1ι → D1ι → D1ι, SMT17Assumptions tbl := by
  refine ⟨dot, dot_satisfies_smt17, ?_⟩
  intro tbl htbl
  exact table_eq_dot htbl

theorem unsat_exclude_delta1 :
    ¬ ∃ tbl : D1ι → D1ι → D1ι, SMT17Assumptions tbl ∧ excludeDelta1 tbl := by
  intro h
  rcases h with ⟨tbl, htbl, hex⟩
  have hEq : tbl = dot := table_eq_dot htbl
  rcases hex with ⟨x, y, hneq⟩
  simp [hEq] at hneq

end SMTEncodingLean

/- # Δ₃ — Recursive Evaluation Extension

   Δ₃ extends Δ₂ with recursive EVAL: evaluating a quoted application
   node recursively evaluates both subterms, then applies the results.

   The mutual recursion between dot3 and eval3 is resolved via a fuel
   parameter. All properties are proved without sorry.
-/

import DistinctionStructures.Delta2

set_option linter.constructorNameAsVariable false

/-! ## Term type for Δ₃ -/

/-- Terms in Δ₃. Arbitrary nesting allowed. -/
inductive T3 where
  | at : A2 → T3
  | qu : T3 → T3
  | ap : T3 → T3 → T3
  | bu : T3 → T3 → T3
  | pa : T3 → T3
  deriving DecidableEq, Repr

/-! ## Fuel-bounded evaluator

    We encode eval and dot as a single function with a Bool tag.
    Recursion decreases on the Nat fuel parameter. -/

/-- Combined interpreter. tag=true → eval mode, tag=false → dot mode. -/
def interp : Nat → Bool → T3 → T3 → T3
  -- Eval mode (second T3 arg is unused dummy)
  | _, true, T3.at x, _ => T3.at x
  | _, true, T3.qu t, _ => T3.qu t
  | _, true, T3.bu f x, _ => T3.bu f x
  | _, true, T3.pa f, _ => T3.pa f
  | 0, true, T3.ap _ _, _ => T3.at .p
  | n + 1, true, T3.ap f x, _ =>
      interp n false (interp n true f (T3.at .p)) (interp n true x (T3.at .p))
  -- Dot mode: QUOTE
  | _, false, T3.at .QUOTE, t => T3.qu t
  -- Dot mode: EVAL
  | 0, false, T3.at .EVAL, _ => T3.at .p
  | n + 1, false, T3.at .EVAL, T3.qu t => interp n true t (T3.at .p)
  | _, false, T3.at .EVAL, _ => T3.at .p
  -- Dot mode: APP
  | _, false, T3.at .APP, T3.at f => T3.pa (T3.at f)
  | _, false, T3.at .APP, _ => T3.at .p
  -- Dot mode: partial completion
  | _, false, T3.pa f, T3.at x => T3.ap f (T3.at x)
  | _, false, T3.pa _, _ => T3.at .p
  -- Dot mode: UNAPP
  | _, false, T3.at .UNAPP, T3.ap f x => T3.bu f x
  | _, false, T3.at .UNAPP, _ => T3.at .p
  -- Dot mode: bundle queries
  | _, false, T3.bu f _, T3.at .top => f
  | _, false, T3.bu _ x, T3.at .bot => x
  | _, false, T3.bu _ _, _ => T3.at .p
  -- Dot mode: structured values inert under atoms
  | _, false, T3.at _, T3.qu _ => T3.at .p
  | _, false, T3.at _, T3.ap _ _ => T3.at .p
  | _, false, T3.at _, T3.bu _ _ => T3.at .p
  | _, false, T3.at _, T3.pa _ => T3.at .p
  -- Dot mode: Δ₁ fallback
  | _, false, T3.at x, T3.at y => T3.at (dotA x y)
  -- Default
  | _, false, _, _ => T3.at .p
termination_by n => n

/-- Evaluate a term with bounded fuel. -/
def eval3 (n : Nat) (t : T3) : T3 := interp n true t (T3.at .p)

/-- Apply two terms with bounded fuel. -/
def dot3 (n : Nat) (a b : T3) : T3 := interp n false a b

/-! ## Concrete computations (proved by `native_decide` on specific fuel) -/

/-- QUOTE wraps atoms. -/
theorem quote_atom :
    dot3 1 (T3.at .QUOTE) (T3.at .e_D) = T3.qu (T3.at .e_D) := by native_decide

/-- EVAL · QUOTE roundtrip. -/
theorem eval_quote_roundtrip :
    dot3 2 (T3.at .EVAL) (dot3 2 (T3.at .QUOTE) (T3.at .e_D)) = T3.at .e_D := by
  native_decide

/-- All 21 atoms roundtrip through QUOTE/EVAL. -/
theorem eval_quote_all_atoms :
    ∀ x : A2, dot3 2 (T3.at .EVAL) (T3.qu (T3.at x)) = T3.at x := by
  intro x; cases x <;> native_decide

/-- APP builds partial from atom. -/
theorem app_builds_partial :
    dot3 1 (T3.at .APP) (T3.at .e_D) = T3.pa (T3.at .e_D) := by native_decide

/-- UNAPP decomposes app nodes. -/
theorem unapp_decomposes :
    ∀ (f x : A2),
      dot3 1 (T3.at .UNAPP) (T3.ap (T3.at f) (T3.at x)) =
      T3.bu (T3.at f) (T3.at x) := by
  intro f x; cases f <;> cases x <;> native_decide

/-- Bundle · ⊤ = function. -/
theorem bundle_top :
    ∀ (f x : A2),
      dot3 1 (T3.bu (T3.at f) (T3.at x)) (T3.at .top) = T3.at f := by
  intro f x; cases f <;> cases x <;> native_decide

/-- Bundle · ⊥ = argument. -/
theorem bundle_bot :
    ∀ (f x : A2),
      dot3 1 (T3.bu (T3.at f) (T3.at x)) (T3.at .bot) = T3.at x := by
  intro f x; cases f <;> cases x <;> native_decide

/-- Flat eval: eval(app(e_D, k)) = d_K -/
theorem flat_eval_eD_k :
    eval3 2 (T3.ap (T3.at .e_D) (T3.at .k)) = T3.at .d_K := by native_decide

/-- Flat eval: eval(app(e_M, i)) = m_I -/
theorem flat_eval_eM_i :
    eval3 2 (T3.ap (T3.at .e_M) (T3.at .i)) = T3.at .m_I := by native_decide

/-- Flat eval: eval(app(e_Sigma, s_C)) = e_Delta -/
theorem flat_eval_eSigma_sC :
    eval3 2 (T3.ap (T3.at .e_Sigma) (T3.at .s_C)) = T3.at .e_Delta := by native_decide

/-- EVAL on quoted flat app: eval · quote(app(e_D, k)) = d_K -/
theorem eval_quoted_flat :
    dot3 3 (T3.at .EVAL) (T3.qu (T3.ap (T3.at .e_D) (T3.at .k))) = T3.at .d_K := by
  native_decide

/-- Nested eval: eval(app(e_D, app(e_I, i)))
    Inner: e_I · i = top. Outer: e_D · top = p (default — e_D only acts on i,k). -/
theorem nested_eval :
    eval3 3 (T3.ap (T3.at .e_D) (T3.ap (T3.at .e_I) (T3.at .i))) = T3.at .p := by
  native_decide

/-- Nested eval with meaningful result: eval(app(m_I, app(e_I, i)))
    Inner: e_I · i = top. Outer: m_I · top = top. -/
theorem nested_eval_mI :
    eval3 3 (T3.ap (T3.at .m_I) (T3.ap (T3.at .e_I) (T3.at .i))) = T3.at .top := by
  native_decide

/-- EVAL on quoted nested app -/
theorem eval_quoted_nested :
    dot3 4 (T3.at .EVAL)
      (T3.qu (T3.ap (T3.at .m_I) (T3.ap (T3.at .e_I) (T3.at .i))))
    = T3.at .top := by
  native_decide

/-- Δ₁ atom-atom preserved. -/
theorem d1_preserved :
    ∀ (a b : D1ι),
      dot3 1 (T3.at (d1toA2 a)) (T3.at (d1toA2 b)) = T3.at (d1toA2 (dot a b)) := by
  intro a b; cases a <;> cases b <;> native_decide

/-- Quoted values inert under Δ₁ atoms. -/
theorem quoted_inert :
    ∀ (d : D1ι),
      dot3 1 (T3.at (d1toA2 d)) (T3.qu (T3.at .e_D)) = T3.at .p := by
  intro d; cases d <;> native_decide

/-- Full APP/UNAPP roundtrip with bundle queries. -/
theorem full_app_unapp_roundtrip :
    let node := dot3 2 (dot3 2 (T3.at .APP) (T3.at .e_D)) (T3.at .k)
    let bun := dot3 2 (T3.at .UNAPP) node
    dot3 2 bun (T3.at .top) = T3.at .e_D ∧
    dot3 2 bun (T3.at .bot) = T3.at .k := by
  native_decide

/-- Triple nesting: eval(app(e_M, app(e_D, app(e_I, i))))
    Innermost: e_I · i = top
    Middle: e_D · top = top
    Outer: e_M · top = p (default) -/
theorem triple_nesting :
    eval3 4
      (T3.ap (T3.at .e_M)
        (T3.ap (T3.at .e_D)
          (T3.ap (T3.at .e_I) (T3.at .i))))
    = T3.at .p := by
  native_decide

/-- Self-model query via recursive eval:
    eval(app(e_D, k)) = d_K, then eval(app(d_K, a)) = top -/
theorem self_model_query :
    eval3 2 (T3.ap (T3.at .d_K) (T3.at .a)) = T3.at .top := by native_decide

/- # Δ₂ — Flat Quoting Extension of Δ₁

   Δ₂ extends Δ₁ with QUOTE, EVAL, APP, UNAPP restricted to flat
   (non-recursive) terms. The carrier is finite and the operation
   is total and decidable.

   We represent terms as an inductive type and prove key properties:
   - QUOTE/EVAL are inverses on atoms
   - APP/UNAPP roundtrip correctly
   - Bundle queries work via booleans
   - EVAL performs flat evaluation via Δ₁'s dot
   - Quoted values are inert under Δ₁ atoms
   - The Δ₁ fragment is preserved exactly

   All proofs are by exhaustive `decide` over the finite atom type.
-/

import DistinctionStructures.Delta1

/-! ## The 21-atom type -/

/-- The 21 atoms of Δ₂. -/
inductive A2 where
  | top | bot | i | k | a | b
  | e_I | e_D | e_M | e_Sigma | e_Delta
  | d_I | d_K | m_I | m_K | s_C | p
  | QUOTE | EVAL | APP | UNAPP
  deriving DecidableEq, Repr

instance : Fintype A2 where
  elems := {.top, .bot, .i, .k, .a, .b, .e_I, .e_D, .e_M, .e_Sigma,
            .e_Delta, .d_I, .d_K, .m_I, .m_K, .s_C, .p,
            .QUOTE, .EVAL, .APP, .UNAPP}
  complete := by intro x; cases x <;> simp

/-! ## Term type -/

/-- Terms in Δ₂. The carrier includes atoms plus structured values. -/
inductive T2 where
  | at : A2 → T2                    -- plain atom
  | qu : A2 → T2                    -- quoted atom
  | ap : A2 → A2 → T2              -- application node (flat)
  | bu : A2 → A2 → T2              -- bundle (from UNAPP)
  | pa : A2 → T2                    -- partial (APP waiting for arg)
  deriving DecidableEq, Repr

/-! ## Δ₁ embedding -/

/-- Map D1ι to A2. -/
def d1toA2 : D1ι → A2
  | .top => .top | .bot => .bot | .i => .i | .k => .k
  | .a => .a | .b => .b | .e_I => .e_I | .e_D => .e_D
  | .e_M => .e_M | .e_Sigma => .e_Sigma | .e_Delta => .e_Delta
  | .d_I => .d_I | .d_K => .d_K | .m_I => .m_I | .m_K => .m_K
  | .s_C => .s_C | .p => .p

/-- Map A2 back to D1ι (for Δ₁ atoms only). -/
def a2toD1 : A2 → Option D1ι
  | .top => some .top | .bot => some .bot | .i => some .i | .k => some .k
  | .a => some .a | .b => some .b | .e_I => some .e_I | .e_D => some .e_D
  | .e_M => some .e_M | .e_Sigma => some .e_Sigma | .e_Delta => some .e_Delta
  | .d_I => some .d_I | .d_K => some .d_K | .m_I => some .m_I | .m_K => some .m_K
  | .s_C => some .s_C | .p => some .p
  | _ => none

/-- Δ₁ dot lifted to A2 atoms. Returns p for non-Δ₁ atoms. -/
def dotA : A2 → A2 → A2 :=
  fun x y =>
    match a2toD1 x, a2toD1 y with
    | some dx, some dy => d1toA2 (dot dx dy)
    | _, _ => .p

/-! ## The Δ₂ operation -/

/-- The full Δ₂ operation on terms. -/
def dot2 : T2 → T2 → T2
  -- QUOTE: wrap atom as inert data
  | .at .QUOTE, .at x => .qu x
  | .at .QUOTE, _ => .at .p
  -- EVAL: unwrap quoted atom
  | .at .EVAL, .qu x => .at x
  -- EVAL: flat evaluation of application node
  | .at .EVAL, .ap f x => .at (dotA f x)
  | .at .EVAL, _ => .at .p
  -- APP: begin curried application
  | .at .APP, .at f => .pa f
  | .at .APP, _ => .at .p
  -- Partial application: complete the node
  | .pa f, .at x => .ap f x
  | .pa _, _ => .at .p
  -- UNAPP: decompose application node
  | .at .UNAPP, .ap f x => .bu f x
  | .at .UNAPP, _ => .at .p
  -- Bundle queries via booleans
  | .bu f _, .at .top => .at f
  | .bu _ x, .at .bot => .at x
  | .bu _ _, _ => .at .p
  -- Δ₁ atoms on structured values: inert
  | .at _, .qu _ => .at .p
  | .at _, .ap _ _ => .at .p
  | .at _, .bu _ _ => .at .p
  | .at _, .pa _ => .at .p
  -- Δ₁ fallback: atom-atom
  | .at x, .at y => .at (dotA x y)
  -- Everything else
  | _, _ => .at .p

/-! ## Properties -/

/-- QUOTE and EVAL are inverses on atoms. -/
theorem eval_quote_inverse :
    ∀ x : A2, dot2 (.at .EVAL) (dot2 (.at .QUOTE) (.at x)) = .at x := by
  intro x; cases x <;> decide

/-- APP builds nodes that UNAPP decomposes into bundles. -/
theorem unapp_app_roundtrip :
    ∀ f x : A2,
      dot2 (.at .UNAPP) (dot2 (dot2 (.at .APP) (.at f)) (.at x)) = .bu f x := by
  intro f x; cases f <;> cases x <;> decide

/-- Bundle · ⊤ = function. -/
theorem bundle_query_top :
    ∀ f x : A2, dot2 (.bu f x) (.at .top) = .at f := by
  intro f x; cases f <;> cases x <;> decide

/-- Bundle · ⊥ = argument. -/
theorem bundle_query_bot :
    ∀ f x : A2, dot2 (.bu f x) (.at .bot) = .at x := by
  intro f x; cases f <;> cases x <;> decide

/-- EVAL on an application node performs Δ₁'s dot (flat, non-recursive). -/
theorem eval_appnode :
    ∀ f x : D1ι,
      dot2 (.at .EVAL) (.ap (d1toA2 f) (d1toA2 x)) = .at (d1toA2 (dot f x)) := by
  intro f x; cases f <;> cases x <;> decide

/-- Quoted values are inert under all Δ₁ atoms.
    For any Δ₁ element d and any atom y: dot2 (at d) (qu y) = at p. -/
theorem quoted_inert_d1 :
    ∀ (d : D1ι) (y : A2),
      dot2 (.at (d1toA2 d)) (.qu y) = .at .p := by
  intro d y; cases d <;> cases y <;> decide

/-- The Δ₁ fragment is exactly preserved. -/
theorem d1_fragment_preserved :
    ∀ (x y : D1ι),
      dot2 (.at (d1toA2 x)) (.at (d1toA2 y)) = .at (d1toA2 (dot x y)) := by
  intro x y; cases x <;> cases y <;> decide

/-- Full roundtrip: build an application, quote it (not possible — it's not an atom),
    but we CAN: build app(f,x), eval it, and get dot(f,x). -/
theorem eval_app_computes :
    ∀ f x : D1ι,
      dot2 (.at .EVAL) (dot2 (dot2 (.at .APP) (.at (d1toA2 f))) (.at (d1toA2 x)))
      = .at (d1toA2 (dot f x)) := by
  intro f x; cases f <;> cases x <;> decide

/-- Concrete example: eval(app(e_D, k)) = d_K -/
theorem example_eval_eD_k :
    dot2 (.at .EVAL) (dot2 (dot2 (.at .APP) (.at .e_D)) (.at .k)) = .at .d_K := by
  decide

/-- Concrete example: eval(app(e_M, i)) = m_I -/
theorem example_eval_eM_i :
    dot2 (.at .EVAL) (dot2 (dot2 (.at .APP) (.at .e_M)) (.at .i)) = .at .m_I := by
  decide

/-- Concrete example: eval(app(e_Sigma, s_C)) = e_Delta -/
theorem example_eval_eSigma_sC :
    dot2 (.at .EVAL) (dot2 (dot2 (.at .APP) (.at .e_Sigma)) (.at .s_C)) = .at .e_Delta := by
  decide

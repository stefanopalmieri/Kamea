/- # Delta3 Alternate Evaluation Strategies

This file adds orchestration strategies around the existing fuel-bounded
`eval3` from `Delta3.lean`.

1. `eval3Iterative`: iterative deepening over fuel, stopping on a fixed point.
2. `eval3Hybrid`: iterative deepening with both fixed-point and cycle checks.

These do not replace `eval3`; they provide alternate ways to select a
result while retaining totality.
-/

import DistinctionStructures.Delta3

/-- Syntactic depth used as a warmup threshold for convergence checks. -/
def termDepth : T3 → Nat
  | T3.at _ => 1
  | T3.qu t => termDepth t + 1
  | T3.pa t => termDepth t + 1
  | T3.ap f x => Nat.max (termDepth f) (termDepth x) + 1
  | T3.bu f x => Nat.max (termDepth f) (termDepth x) + 1

/-- Iterative-deepening loop.
    `fuel` is the current depth, `remaining` is the number of additional
    increments to try, `prev` is the previously observed result. -/
def eval3IterativeLoop (t : T3) (minFuel : Nat) : Nat → Nat → T3 → T3
  | _, 0, prev => prev
  | fuel, remaining + 1, prev =>
      let nextFuel := fuel + 1
      let out := eval3 nextFuel t
      if nextFuel < minFuel then
        eval3IterativeLoop t minFuel nextFuel remaining out
      else if out = prev then
        out
      else
        eval3IterativeLoop t minFuel nextFuel remaining out

/-- Iterative deepening strategy: start at fuel 0 and stop once the result
    stabilizes across consecutive fuel levels (after warmup), or when
    `maxFuel` is reached. -/
def eval3Iterative (maxFuel : Nat) (t : T3) : T3 :=
  eval3IterativeLoop t (termDepth t) 0 maxFuel (eval3 0 t)

/-- Hybrid loop with cycle detection in addition to fixed-point detection.
    `seen` stores prior outputs from smaller fuel values. -/
def eval3HybridLoop (t : T3) (minFuel : Nat) : Nat → Nat → T3 → List T3 → T3
  | _, 0, prev, _ => prev
  | fuel, remaining + 1, prev, seen =>
      let nextFuel := fuel + 1
      let out := eval3 nextFuel t
      if nextFuel < minFuel then
        eval3HybridLoop t minFuel nextFuel remaining out (out :: seen)
      else if out = prev then
        out
      else if out ∈ seen then
        out
      else
        eval3HybridLoop t minFuel nextFuel remaining out (out :: seen)

/-- Hybrid strategy: iterative deepening + cycle detection. -/
def eval3Hybrid (maxFuel : Nat) (t : T3) : T3 :=
  let seed := eval3 0 t
  eval3HybridLoop t (termDepth t) 0 maxFuel seed [seed]

theorem eval3Iterative_zero (t : T3) :
    eval3Iterative 0 t = eval3 0 t := by
  rfl

theorem eval3Hybrid_zero (t : T3) :
    eval3Hybrid 0 t = eval3 0 t := by
  rfl

/-! ## Representative checks

These demonstrate the alternate strategies recover the same outcomes
as the fuel-based evaluator on recursive examples from `Delta3.lean`.
-/

theorem iterative_flat_eval_eD_k :
    eval3Iterative 5 (T3.ap (T3.at .e_D) (T3.at .k)) = T3.at .d_K := by
  native_decide

theorem hybrid_flat_eval_eD_k :
    eval3Hybrid 5 (T3.ap (T3.at .e_D) (T3.at .k)) = T3.at .d_K := by
  native_decide

theorem iterative_nested_eval_mI :
    eval3Iterative 6
      (T3.ap (T3.at .m_I) (T3.ap (T3.at .e_I) (T3.at .i))) = T3.at .top := by
  native_decide

theorem hybrid_nested_eval_mI :
    eval3Hybrid 6
      (T3.ap (T3.at .m_I) (T3.ap (T3.at .e_I) (T3.at .i))) = T3.at .top := by
  native_decide

theorem iterative_eval_quoted_nested :
    eval3Iterative 7
      (T3.ap (T3.at .EVAL)
        (T3.qu (T3.ap (T3.at .m_I) (T3.ap (T3.at .e_I) (T3.at .i))))) = T3.at .top := by
  native_decide

theorem hybrid_eval_quoted_nested :
    eval3Hybrid 7
      (T3.ap (T3.at .EVAL)
        (T3.qu (T3.ap (T3.at .m_I) (T3.ap (T3.at .e_I) (T3.at .i))))) = T3.at .top := by
  native_decide

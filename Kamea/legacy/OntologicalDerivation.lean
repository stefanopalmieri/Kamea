/- # Ontological Derivation Signatures for Δ₂ Primitives

   This file is an exploratory formalization of the idea that the four Δ₂
   computational primitives are not arbitrary additions, but are forced by
   category-style behavioral signatures:

   - Distinction-lift signature    -> QUOTE
   - Synthesis-lift signature      -> EVAL
   - Context-build signature       -> APP
   - Context-project signature     -> UNAPP

   We reuse the uniqueness theorems from Discoverable2.lean and package them
   as "exists unique" derivation statements.
-/

import Kamea.Discoverable2

namespace OntologicalDerivation

open A2

/-- Distinction lifted to the operational level:
    applying x to an atom always yields quoted data. -/
def DistinctionLift (x : A2) : Prop :=
  ∀ atom : A2, ∃ y : A2, dot2 (.at x) (.at atom) = .qu y

/-- Synthesis lifted to quoted terms:
    x evaluates quoted atoms back to atoms. -/
def SynthesisLift (x : A2) : Prop :=
  ∀ atom : A2, dot2 (.at x) (dot2 (.at .QUOTE) (.at atom)) = .at atom

/-- Context construction at the term layer:
    x builds nodes that UNAPP can decompose into bundles. -/
def ContextBuildLift (x : A2) : Prop :=
  ∀ f g : A2, ∃ r s : A2,
    dot2 (.at .UNAPP) (dot2 (dot2 (.at x) (.at f)) (.at g)) = .bu r s

/-- Context projection at the term layer:
    x recovers function/argument roles from APP-built nodes via booleans. -/
def ContextProjectLift (x : A2) : Prop :=
  ∀ f g : A2,
    dot2 (.at x) (dot2 (dot2 (.at .APP) (.at f)) (.at g)) ≠ .at .p ∧
    dot2 (dot2 (.at x) (dot2 (dot2 (.at .APP) (.at f)) (.at g))) (.at .top) = .at f ∧
    dot2 (dot2 (.at x) (dot2 (dot2 (.at .APP) (.at f)) (.at g))) (.at .bot) = .at g

theorem distinctionLift_iff_quote :
    ∀ x : A2, DistinctionLift x ↔ x = .QUOTE := by
  intro x
  simpa [DistinctionLift] using (quote_uniqueness (x := x))

theorem synthesisLift_iff_eval :
    ∀ x : A2, SynthesisLift x ↔ x = .EVAL := by
  intro x
  simpa [SynthesisLift] using (eval_uniqueness (x := x))

theorem contextBuildLift_iff_app :
    ∀ x : A2, ContextBuildLift x ↔ x = .APP := by
  intro x
  simpa [ContextBuildLift] using (app_uniqueness (x := x))

theorem contextProjectLift_iff_unapp :
    ∀ x : A2, ContextProjectLift x ↔ x = .UNAPP := by
  intro x
  simpa [ContextProjectLift] using (unapp_uniqueness (x := x))

theorem distinctionLift_existsUnique : ∃! x : A2, DistinctionLift x := by
  refine ⟨.QUOTE, ?_, ?_⟩
  · exact (distinctionLift_iff_quote .QUOTE).2 rfl
  · intro x hx
    exact (distinctionLift_iff_quote x).1 hx

theorem synthesisLift_existsUnique : ∃! x : A2, SynthesisLift x := by
  refine ⟨.EVAL, ?_, ?_⟩
  · exact (synthesisLift_iff_eval .EVAL).2 rfl
  · intro x hx
    exact (synthesisLift_iff_eval x).1 hx

theorem contextBuildLift_existsUnique : ∃! x : A2, ContextBuildLift x := by
  refine ⟨.APP, ?_, ?_⟩
  · exact (contextBuildLift_iff_app .APP).2 rfl
  · intro x hx
    exact (contextBuildLift_iff_app x).1 hx

theorem contextProjectLift_existsUnique : ∃! x : A2, ContextProjectLift x := by
  refine ⟨.UNAPP, ?_, ?_⟩
  · exact (contextProjectLift_iff_unapp .UNAPP).2 rfl
  · intro x hx
    exact (contextProjectLift_iff_unapp x).1 hx

/-- Bundle result: the four Δ₂ primitives are uniquely forced by the four
    lift signatures above. -/
theorem primitives_forced_by_lifts :
    (∃! x : A2, DistinctionLift x) ∧
    (∃! x : A2, SynthesisLift x) ∧
    (∃! x : A2, ContextBuildLift x) ∧
    (∃! x : A2, ContextProjectLift x) := by
  exact ⟨distinctionLift_existsUnique, synthesisLift_existsUnique,
    contextBuildLift_existsUnique, contextProjectLift_existsUnique⟩

/-- Pointwise form of the same result. -/
theorem primitive_tuple_unique :
    ∀ q e ap un : A2,
      DistinctionLift q → SynthesisLift e → ContextBuildLift ap → ContextProjectLift un →
      q = .QUOTE ∧ e = .EVAL ∧ ap = .APP ∧ un = .UNAPP := by
  intro q e ap un hq he hap hun
  exact ⟨(distinctionLift_iff_quote q).1 hq,
    (synthesisLift_iff_eval e).1 he,
    (contextBuildLift_iff_app ap).1 hap,
    (contextProjectLift_iff_unapp un).1 hun⟩

end OntologicalDerivation

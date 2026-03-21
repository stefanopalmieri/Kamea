/- # Ontological Minimality of the Δ₂ Primitive Basis

   Building on OntologicalDerivation.lean, this file proves an internal
   minimality statement for Δ₂:

   1. Any finite set of atoms that covers all four lift signatures must have
      cardinality at least 4.
   2. If such a set has cardinality exactly 4, it is exactly
      {QUOTE, EVAL, APP, UNAPP}.

   This is a Δ₂-internal minimality result (not yet a model-independent theorem
   for all possible extensions).
-/

import Kamea.OntologicalDerivation
import Mathlib.Data.Finset.Card

namespace OntologicalMinimality

open A2
open OntologicalDerivation

/-- Canonical Δ₂ computational primitive basis. -/
def canonicalPrimitiveSet : Finset A2 := {.QUOTE, .EVAL, .APP, .UNAPP}

/-- A finite set covers the four lift signatures if it contains at least one
    witness for each signature class. -/
def CoversLiftSignatures (S : Finset A2) : Prop :=
  (∃ x : A2, x ∈ S ∧ DistinctionLift x) ∧
  (∃ x : A2, x ∈ S ∧ SynthesisLift x) ∧
  (∃ x : A2, x ∈ S ∧ ContextBuildLift x) ∧
  (∃ x : A2, x ∈ S ∧ ContextProjectLift x)

theorem canonical_covers : CoversLiftSignatures canonicalPrimitiveSet := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨.QUOTE, by simp [canonicalPrimitiveSet], (distinctionLift_iff_quote .QUOTE).2 rfl⟩
  · exact ⟨.EVAL, by simp [canonicalPrimitiveSet], (synthesisLift_iff_eval .EVAL).2 rfl⟩
  · exact ⟨.APP, by simp [canonicalPrimitiveSet], (contextBuildLift_iff_app .APP).2 rfl⟩
  · exact ⟨.UNAPP, by simp [canonicalPrimitiveSet], (contextProjectLift_iff_unapp .UNAPP).2 rfl⟩

theorem canonical_card : canonicalPrimitiveSet.card = 4 := by
  native_decide

/-- Any signature-covering set must contain each canonical primitive. -/
theorem cover_contains_canonical :
    ∀ S : Finset A2, CoversLiftSignatures S →
      .QUOTE ∈ S ∧ .EVAL ∈ S ∧ .APP ∈ S ∧ .UNAPP ∈ S := by
  intro S hS
  rcases hS with ⟨hD, hSYN, hCB, hCP⟩
  rcases hD with ⟨xD, hxD, hDxD⟩
  rcases hSYN with ⟨xSYN, hxSYN, hSYNx⟩
  rcases hCB with ⟨xCB, hxCB, hCBx⟩
  rcases hCP with ⟨xCP, hxCP, hCPx⟩
  have hq : xD = .QUOTE := (distinctionLift_iff_quote xD).1 hDxD
  have he : xSYN = .EVAL := (synthesisLift_iff_eval xSYN).1 hSYNx
  have ha : xCB = .APP := (contextBuildLift_iff_app xCB).1 hCBx
  have hu : xCP = .UNAPP := (contextProjectLift_iff_unapp xCP).1 hCPx
  subst hq he ha hu
  exact ⟨hxD, hxSYN, hxCB, hxCP⟩

/-- Signature coverage implies `canonicalPrimitiveSet ⊆ S`. -/
theorem canonical_subset_of_cover :
    ∀ S : Finset A2, CoversLiftSignatures S → canonicalPrimitiveSet ⊆ S := by
  intro S hS atom hmem
  rcases cover_contains_canonical S hS with ⟨hQ, hE, hA, hU⟩
  simp [canonicalPrimitiveSet] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hQ
  · exact hE
  · exact hA
  · exact hU

/-- Any signature-covering set has cardinality at least 4. -/
theorem cover_card_ge_four :
    ∀ S : Finset A2, CoversLiftSignatures S → 4 ≤ S.card := by
  intro S hS
  have hsub : canonicalPrimitiveSet ⊆ S := canonical_subset_of_cover S hS
  have hcanon_le : canonicalPrimitiveSet.card ≤ S.card := Finset.card_le_card hsub
  simp [canonical_card] at hcanon_le
  exact hcanon_le

/-- If a covering set has cardinality exactly 4, it is exactly the canonical set. -/
theorem cover_card_eq_four_unique :
    ∀ S : Finset A2, CoversLiftSignatures S → S.card = 4 → S = canonicalPrimitiveSet := by
  intro S hS hcardS
  have hsub : canonicalPrimitiveSet ⊆ S := canonical_subset_of_cover S hS
  have hle : S.card ≤ canonicalPrimitiveSet.card := by
    simp [canonical_card, hcardS]
  have hEq : canonicalPrimitiveSet = S := Finset.eq_of_subset_of_card_le hsub hle
  exact hEq.symm

/-- Minimality characterization without additional order-theory machinery:
    a cover of size 4 exists, and every cover has size at least 4. -/
theorem cover_card_minimal_characterization :
    (∃ S : Finset A2, CoversLiftSignatures S ∧ S.card = 4) ∧
    (∀ S : Finset A2, CoversLiftSignatures S → 4 ≤ S.card) := by
  refine ⟨⟨canonicalPrimitiveSet, canonical_covers, canonical_card⟩, ?_⟩
  intro S hS
  exact cover_card_ge_four S hS

end OntologicalMinimality

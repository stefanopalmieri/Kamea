/- # Abstract Four-Lift Schema Theorem

   This file states and proves an abstract version of the Δ₂ derivation result.

   Given a schema with four computational lifts (Distinction, Synthesis,
   Context-build, Context-project) satisfying behavioral axioms, we prove:

   1. Each lift role has a unique witness atom.
   2. Any finite set covering all four lift roles has cardinality at least 4.
   3. Any covering set of cardinality exactly 4 is the unique canonical basis.

   This is model-independent at the level of the schema assumptions.
-/

import Mathlib.Data.Finset.Card

universe u v

/-- Abstract schema for four lifted computational roles. -/
structure FourLiftSchema where
  Atom : Type u
  Term : Type v
  [decEqAtom : DecidableEq Atom]
  [fintypeAtom : Fintype Atom]

  embed : Atom → Term
  dot : Term → Term → Term

  quote : Atom
  eval : Atom
  app : Atom
  unapp : Atom
  top : Atom
  bot : Atom
  p : Atom

  qu : Atom → Term
  pa : Atom → Term
  ap : Atom → Atom → Term
  bu : Atom → Atom → Term

  -- Distinction-lift behavior
  quote_on_atoms : ∀ a : Atom, dot (embed quote) (embed a) = qu a
  nonquote_not_qu : ∀ x : Atom, x ≠ quote → ∀ a y : Atom, dot (embed x) (embed a) ≠ qu y

  -- Synthesis-lift behavior
  eval_on_quoted : ∀ a : Atom, dot (embed eval) (qu a) = embed a
  noneval_breaks_eval : ∀ x : Atom, x ≠ eval → ∃ a : Atom, dot (embed x) (qu a) ≠ embed a

  -- Context-build behavior
  app_builds_node : ∀ f g : Atom, dot (dot (embed app) (embed f)) (embed g) = ap f g
  unapp_decomposes : ∀ f g : Atom, dot (embed unapp) (ap f g) = bu f g
  nonapp_not_bundle :
    ∀ x : Atom, x ≠ app →
      ∃ f g : Atom, ∀ r s : Atom,
        dot (embed unapp) (dot (dot (embed x) (embed f)) (embed g)) ≠ bu r s

  -- Context-project behavior
  bundle_query_top : ∀ f g : Atom, dot (bu f g) (embed top) = embed f
  bundle_query_bot : ∀ f g : Atom, dot (bu f g) (embed bot) = embed g
  bu_ne_at_p : ∀ f g : Atom, bu f g ≠ embed p
  nonunapp_breaks_project :
    ∀ x : Atom, x ≠ unapp →
      ∃ f g : Atom,
        dot (embed x) (ap f g) = embed p ∨
        dot (dot (embed x) (ap f g)) (embed top) ≠ embed f ∨
        dot (dot (embed x) (ap f g)) (embed bot) ≠ embed g

  -- Primitive distinctness
  primitive_distinct :
    quote ≠ eval ∧ quote ≠ app ∧ quote ≠ unapp ∧
    eval ≠ app ∧ eval ≠ unapp ∧ app ≠ unapp

attribute [instance] FourLiftSchema.decEqAtom FourLiftSchema.fintypeAtom

namespace FourLiftSchema

variable (S : FourLiftSchema)

/-- Distinction-lift role predicate. -/
def DistinctionLift (x : S.Atom) : Prop :=
  ∀ a : S.Atom, ∃ y : S.Atom, S.dot (S.embed x) (S.embed a) = S.qu y

/-- Synthesis-lift role predicate. -/
def SynthesisLift (x : S.Atom) : Prop :=
  ∀ a : S.Atom, S.dot (S.embed x) (S.qu a) = S.embed a

/-- Context-build role predicate. -/
def ContextBuildLift (x : S.Atom) : Prop :=
  ∀ f g : S.Atom, ∃ r s : S.Atom,
    S.dot (S.embed S.unapp) (S.dot (S.dot (S.embed x) (S.embed f)) (S.embed g)) = S.bu r s

/-- Context-project role predicate. -/
def ContextProjectLift (x : S.Atom) : Prop :=
  ∀ f g : S.Atom,
    S.dot (S.embed x) (S.ap f g) ≠ S.embed S.p ∧
    S.dot (S.dot (S.embed x) (S.ap f g)) (S.embed S.top) = S.embed f ∧
    S.dot (S.dot (S.embed x) (S.ap f g)) (S.embed S.bot) = S.embed g

theorem distinctionLift_iff_quote (x : S.Atom) :
    S.DistinctionLift x ↔ x = S.quote := by
  constructor
  · intro hx
    by_contra hneq
    rcases hx S.quote with ⟨y, hy⟩
    exact (S.nonquote_not_qu x hneq S.quote y) hy
  · intro hx
    subst hx
    intro a
    exact ⟨a, S.quote_on_atoms a⟩

theorem synthesisLift_iff_eval (x : S.Atom) :
    S.SynthesisLift x ↔ x = S.eval := by
  constructor
  · intro hx
    by_contra hneq
    rcases S.noneval_breaks_eval x hneq with ⟨a, ha⟩
    exact ha (hx a)
  · intro hx
    subst hx
    intro a
    exact S.eval_on_quoted a

theorem contextBuildLift_iff_app (x : S.Atom) :
    S.ContextBuildLift x ↔ x = S.app := by
  constructor
  · intro hx
    by_contra hneq
    rcases S.nonapp_not_bundle x hneq with ⟨f, g, hbad⟩
    rcases hx f g with ⟨r, s, hrs⟩
    exact (hbad r s) hrs
  · intro hx
    subst hx
    intro f g
    refine ⟨f, g, ?_⟩
    simpa [S.app_builds_node f g] using S.unapp_decomposes f g

theorem contextProjectLift_iff_unapp (x : S.Atom) :
    S.ContextProjectLift x ↔ x = S.unapp := by
  constructor
  · intro hx
    by_contra hneq
    rcases S.nonunapp_breaks_project x hneq with ⟨f, g, hfail⟩
    rcases hx f g with ⟨hNotP, hTop, hBot⟩
    rcases hfail with h1 | h2 | h3
    · exact hNotP h1
    · exact h2 hTop
    · exact h3 hBot
  · intro hx
    subst hx
    intro f g
    have hun : S.dot (S.embed S.unapp) (S.ap f g) = S.bu f g := S.unapp_decomposes f g
    refine ⟨?_, ?_, ?_⟩
    · simpa [hun] using S.bu_ne_at_p f g
    · calc
        S.dot (S.dot (S.embed S.unapp) (S.ap f g)) (S.embed S.top)
            = S.dot (S.bu f g) (S.embed S.top) := by simp [hun]
        _ = S.embed f := S.bundle_query_top f g
    · calc
        S.dot (S.dot (S.embed S.unapp) (S.ap f g)) (S.embed S.bot)
            = S.dot (S.bu f g) (S.embed S.bot) := by simp [hun]
        _ = S.embed g := S.bundle_query_bot f g

theorem lifts_exist_unique :
    (∃! x : S.Atom, S.DistinctionLift x) ∧
    (∃! x : S.Atom, S.SynthesisLift x) ∧
    (∃! x : S.Atom, S.ContextBuildLift x) ∧
    (∃! x : S.Atom, S.ContextProjectLift x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨S.quote, ?_, ?_⟩
    · exact (S.distinctionLift_iff_quote S.quote).2 rfl
    · intro x hx
      exact (S.distinctionLift_iff_quote x).1 hx
  · refine ⟨S.eval, ?_, ?_⟩
    · exact (S.synthesisLift_iff_eval S.eval).2 rfl
    · intro x hx
      exact (S.synthesisLift_iff_eval x).1 hx
  · refine ⟨S.app, ?_, ?_⟩
    · exact (S.contextBuildLift_iff_app S.app).2 rfl
    · intro x hx
      exact (S.contextBuildLift_iff_app x).1 hx
  · refine ⟨S.unapp, ?_, ?_⟩
    · exact (S.contextProjectLift_iff_unapp S.unapp).2 rfl
    · intro x hx
      exact (S.contextProjectLift_iff_unapp x).1 hx

/-- Canonical primitive basis in the schema. -/
def canonicalPrimitiveSet : Finset S.Atom := {S.quote, S.eval, S.app, S.unapp}

theorem canonical_card : (S.canonicalPrimitiveSet).card = 4 := by
  rcases S.primitive_distinct with ⟨hqe, hqa, hqu, hea, heu, hau⟩
  simp [canonicalPrimitiveSet, hqe, hqa, hqu, hea, heu, hau]

/-- A finite set covers all four lift roles if it contains a witness for each. -/
def CoversLiftSignatures (T : Finset S.Atom) : Prop :=
  (∃ x : S.Atom, x ∈ T ∧ S.DistinctionLift x) ∧
  (∃ x : S.Atom, x ∈ T ∧ S.SynthesisLift x) ∧
  (∃ x : S.Atom, x ∈ T ∧ S.ContextBuildLift x) ∧
  (∃ x : S.Atom, x ∈ T ∧ S.ContextProjectLift x)

theorem canonical_covers : S.CoversLiftSignatures S.canonicalPrimitiveSet := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨S.quote, by simp [canonicalPrimitiveSet], (S.distinctionLift_iff_quote S.quote).2 rfl⟩
  · exact ⟨S.eval, by simp [canonicalPrimitiveSet], (S.synthesisLift_iff_eval S.eval).2 rfl⟩
  · exact ⟨S.app, by simp [canonicalPrimitiveSet], (S.contextBuildLift_iff_app S.app).2 rfl⟩
  · exact ⟨S.unapp, by simp [canonicalPrimitiveSet], (S.contextProjectLift_iff_unapp S.unapp).2 rfl⟩

theorem cover_contains_canonical (T : Finset S.Atom) :
    S.CoversLiftSignatures T →
      S.quote ∈ T ∧ S.eval ∈ T ∧ S.app ∈ T ∧ S.unapp ∈ T := by
  intro hT
  rcases hT with ⟨hD, hSYN, hCB, hCP⟩
  rcases hD with ⟨xD, hxD, hDxD⟩
  rcases hSYN with ⟨xSYN, hxSYN, hSYNx⟩
  rcases hCB with ⟨xCB, hxCB, hCBx⟩
  rcases hCP with ⟨xCP, hxCP, hCPx⟩
  have hq : xD = S.quote := (S.distinctionLift_iff_quote xD).1 hDxD
  have he : xSYN = S.eval := (S.synthesisLift_iff_eval xSYN).1 hSYNx
  have ha : xCB = S.app := (S.contextBuildLift_iff_app xCB).1 hCBx
  have hu : xCP = S.unapp := (S.contextProjectLift_iff_unapp xCP).1 hCPx
  subst hq he ha hu
  exact ⟨hxD, hxSYN, hxCB, hxCP⟩

theorem canonical_subset_of_cover (T : Finset S.Atom) :
    S.CoversLiftSignatures T → S.canonicalPrimitiveSet ⊆ T := by
  intro hT atom hmem
  rcases S.cover_contains_canonical T hT with ⟨hQ, hE, hA, hU⟩
  simp [canonicalPrimitiveSet] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hQ
  · exact hE
  · exact hA
  · exact hU

theorem cover_card_ge_four (T : Finset S.Atom) :
    S.CoversLiftSignatures T → 4 ≤ T.card := by
  intro hT
  have hsub : S.canonicalPrimitiveSet ⊆ T := S.canonical_subset_of_cover T hT
  have hcanon_le : S.canonicalPrimitiveSet.card ≤ T.card := Finset.card_le_card hsub
  rw [S.canonical_card] at hcanon_le
  exact hcanon_le

theorem cover_card_eq_four_unique (T : Finset S.Atom) :
    S.CoversLiftSignatures T → T.card = 4 → T = S.canonicalPrimitiveSet := by
  intro hT hcardT
  have hsub : S.canonicalPrimitiveSet ⊆ T := S.canonical_subset_of_cover T hT
  have hle : T.card ≤ S.canonicalPrimitiveSet.card := by
    rw [hcardT, S.canonical_card]
  have hEq : S.canonicalPrimitiveSet = T := Finset.eq_of_subset_of_card_le hsub hle
  exact hEq.symm

theorem cover_card_minimal_characterization :
    (∃ T : Finset S.Atom, S.CoversLiftSignatures T ∧ T.card = 4) ∧
    (∀ T : Finset S.Atom, S.CoversLiftSignatures T → 4 ≤ T.card) := by
  refine ⟨⟨S.canonicalPrimitiveSet, S.canonical_covers, S.canonical_card⟩, ?_⟩
  intro T hT
  exact S.cover_card_ge_four T hT

end FourLiftSchema

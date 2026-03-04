/- # Abstract Δ₁ Role Schema: Minimality and Uniqueness

This file gives an encoding-independent theorem schema for the 17-role Δ₁ core.

Assumptions:
- a finite carrier type with a binary operation,
- 17 abstract roles,
- each role has a unique witness element,
- different roles cannot be witnessed by the same element.

Main consequences:
1. Any model satisfying the schema has at least 17 elements.
2. Any finite set covering all 17 roles has cardinality at least 17.
3. Any role-covering set of cardinality exactly 17 is uniquely the canonical role core.
4. At carrier size 17, there is a unique role-preserving transport map between any
   two models (hence a unique role-preserving equivalence).
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

universe u

/-- The 17 structural roles of the Δ₁ core. -/
inductive D1Role where
  | top | bot
  | i | k | a | b
  | e_I | e_D | e_M | e_Sigma | e_Delta
  | d_I | d_K
  | m_I | m_K
  | s_C
  | p
  deriving DecidableEq, Repr

instance : Fintype D1Role where
  elems := {
    .top, .bot, .i, .k, .a, .b,
    .e_I, .e_D, .e_M, .e_Sigma, .e_Delta,
    .d_I, .d_K, .m_I, .m_K, .s_C, .p
  }
  complete := by
    intro r
    cases r <;> simp

theorem card_d1Role : Fintype.card D1Role = 17 := by
  native_decide

/-- Abstract role schema for Δ₁-style models. -/
structure Delta1RoleSchema where
  Carrier : Type u
  [decEqCarrier : DecidableEq Carrier]
  [fintypeCarrier : Fintype Carrier]

  dot : Carrier → Carrier → Carrier
  HasRole : D1Role → Carrier → Prop

  role_unique : ∀ r : D1Role, ∃! x : Carrier, HasRole r x
  role_disjoint :
    ∀ {r₁ r₂ : D1Role} {x : Carrier},
      HasRole r₁ x → HasRole r₂ x → r₁ = r₂

attribute [instance] Delta1RoleSchema.decEqCarrier Delta1RoleSchema.fintypeCarrier

namespace Delta1RoleSchema

variable (S : Delta1RoleSchema)

/-- Canonical witness for a role (chosen from `role_unique`). -/
noncomputable def roleWitness (r : D1Role) : S.Carrier :=
  Classical.choose (S.role_unique r)

theorem roleWitness_spec (r : D1Role) :
    S.HasRole r (S.roleWitness r) := by
  exact (Classical.choose_spec (S.role_unique r)).1

theorem roleWitness_unique (r : D1Role) (x : S.Carrier) (hx : S.HasRole r x) :
    x = S.roleWitness r := by
  exact (Classical.choose_spec (S.role_unique r)).2 x hx

theorem roleWitness_injective : Function.Injective S.roleWitness := by
  intro r₁ r₂ hEq
  have h1 : S.HasRole r₁ (S.roleWitness r₁) := S.roleWitness_spec r₁
  have h2 : S.HasRole r₂ (S.roleWitness r₁) := by
    simpa [hEq] using S.roleWitness_spec r₂
  exact S.role_disjoint (r₁ := r₁) (r₂ := r₂) (x := S.roleWitness r₁) h1 h2

/-- Lower bound: at least 17 elements are required to realize 17 distinct roles. -/
theorem card_ge_17 : 17 ≤ Fintype.card S.Carrier := by
  have hle : Fintype.card D1Role ≤ Fintype.card S.Carrier :=
    Fintype.card_le_of_injective S.roleWitness S.roleWitness_injective
  simpa [card_d1Role] using hle

theorem no_model_below_17 : ¬ Fintype.card S.Carrier < 17 := by
  exact Nat.not_lt_of_ge S.card_ge_17

/-- Canonical role core: the 17 role witnesses. -/
noncomputable def canonicalRoleSet : Finset S.Carrier :=
  (Finset.univ : Finset D1Role).image S.roleWitness

theorem canonicalRoleSet_card : S.canonicalRoleSet.card = 17 := by
  unfold canonicalRoleSet
  have hcard :
      ((Finset.univ : Finset D1Role).image S.roleWitness).card =
        (Finset.univ : Finset D1Role).card :=
    Finset.card_image_of_injective (s := (Finset.univ : Finset D1Role))
      (f := S.roleWitness) S.roleWitness_injective
  simpa [card_d1Role] using hcard

/-- A finite set covers all roles if each role has a witness inside it. -/
def CoversRoles (T : Finset S.Carrier) : Prop :=
  ∀ r : D1Role, ∃ x : S.Carrier, x ∈ T ∧ S.HasRole r x

theorem canonical_covers : S.CoversRoles S.canonicalRoleSet := by
  intro r
  refine ⟨S.roleWitness r, ?_, S.roleWitness_spec r⟩
  unfold canonicalRoleSet
  exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩

theorem cover_contains_canonical (T : Finset S.Carrier) :
    S.CoversRoles T → S.canonicalRoleSet ⊆ T := by
  intro hT x hx
  unfold canonicalRoleSet at hx
  rcases Finset.mem_image.mp hx with ⟨r, -, hrx⟩
  rcases hT r with ⟨y, hyT, hyRole⟩
  have hyEq : y = S.roleWitness r := S.roleWitness_unique r y hyRole
  have hwT : S.roleWitness r ∈ T := by
    simpa [hyEq] using hyT
  simpa [hrx] using hwT

/-- Minimality: any role-covering set must have cardinality at least 17. -/
theorem cover_card_ge_seventeen (T : Finset S.Carrier) :
    S.CoversRoles T → 17 ≤ T.card := by
  intro hT
  have hsub : S.canonicalRoleSet ⊆ T := S.cover_contains_canonical T hT
  have hle : S.canonicalRoleSet.card ≤ T.card := Finset.card_le_card hsub
  rw [S.canonicalRoleSet_card] at hle
  exact hle

/-- Uniqueness of the minimal role core among role-covering sets. -/
theorem cover_card_eq_seventeen_unique (T : Finset S.Carrier) :
    S.CoversRoles T → T.card = 17 → T = S.canonicalRoleSet := by
  intro hT hcardT
  have hsub : S.canonicalRoleSet ⊆ T := S.cover_contains_canonical T hT
  have hle : T.card ≤ S.canonicalRoleSet.card := by
    rw [hcardT, S.canonicalRoleSet_card]
  have hEq : S.canonicalRoleSet = T := Finset.eq_of_subset_of_card_le hsub hle
  exact hEq.symm

theorem cover_card_minimal_characterization :
    (∃ T : Finset S.Carrier, S.CoversRoles T ∧ T.card = 17) ∧
    (∀ T : Finset S.Carrier, S.CoversRoles T → 17 ≤ T.card) := by
  refine ⟨⟨S.canonicalRoleSet, S.canonical_covers, S.canonicalRoleSet_card⟩, ?_⟩
  intro T hT
  exact S.cover_card_ge_seventeen T hT

/-- If the carrier has exactly 17 elements, the canonical role core is all of it. -/
theorem canonical_eq_univ_of_card_eq_17 :
    Fintype.card S.Carrier = 17 →
    S.canonicalRoleSet = (Finset.univ : Finset S.Carrier) := by
  intro hcard
  have hsub : S.canonicalRoleSet ⊆ (Finset.univ : Finset S.Carrier) := by
    intro x hx
    simp
  have hle : (Finset.univ : Finset S.Carrier).card ≤ S.canonicalRoleSet.card := by
    rw [Finset.card_univ, hcard, S.canonicalRoleSet_card]
  exact Finset.eq_of_subset_of_card_le hsub hle

theorem unique_role_core_at_card_eq_17
    (hcard : Fintype.card S.Carrier = 17) :
    ∀ T : Finset S.Carrier, S.CoversRoles T → T.card = 17 →
      T = (Finset.univ : Finset S.Carrier) := by
  intro T hCover hcardT
  calc
    T = S.canonicalRoleSet := S.cover_card_eq_seventeen_unique T hCover hcardT
    _ = (Finset.univ : Finset S.Carrier) := S.canonical_eq_univ_of_card_eq_17 hcard

theorem exists_role_of_card_eq_17 (hcard : Fintype.card S.Carrier = 17) :
    ∀ x : S.Carrier, ∃ r : D1Role, S.HasRole r x := by
  intro x
  have hx : x ∈ S.canonicalRoleSet := by
    rw [S.canonical_eq_univ_of_card_eq_17 hcard]
    simp
  unfold canonicalRoleSet at hx
  rcases Finset.mem_image.mp hx with ⟨r, -, hrx⟩
  exact ⟨r, by simpa [hrx] using S.roleWitness_spec r⟩

/-- Chosen role label for an element when `card = 17`. -/
noncomputable def roleOf (hcard : Fintype.card S.Carrier = 17) (x : S.Carrier) : D1Role :=
  Classical.choose (S.exists_role_of_card_eq_17 hcard x)

theorem roleOf_spec (hcard : Fintype.card S.Carrier = 17) (x : S.Carrier) :
    S.HasRole (S.roleOf hcard x) x := by
  exact Classical.choose_spec (S.exists_role_of_card_eq_17 hcard x)

theorem roleOf_eq_of_hasRole (hcard : Fintype.card S.Carrier = 17)
    {x : S.Carrier} {r : D1Role} (hx : S.HasRole r x) :
    S.roleOf hcard x = r := by
  exact S.role_disjoint (S.roleOf_spec hcard x) hx

/-- Role-preserving maps between two schemas. -/
def RolePreserving (T : Delta1RoleSchema) (f : S.Carrier → T.Carrier) : Prop :=
  ∀ r : D1Role, ∀ x : S.Carrier, S.HasRole r x → T.HasRole r (f x)

/-- Canonical role transport at cardinality 17. -/
noncomputable def roleTransport (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17) :
    S.Carrier → T.Carrier :=
  fun x => T.roleWitness (S.roleOf hcardS x)

theorem roleTransport_rolePreserving (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17) :
    S.RolePreserving T (S.roleTransport T hcardS) := by
  intro r x hx
  have hRoleEq : S.roleOf hcardS x = r := S.roleOf_eq_of_hasRole hcardS hx
  unfold roleTransport
  simpa [hRoleEq] using T.roleWitness_spec r

theorem rolePreserving_unique (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17)
    (f : S.Carrier → T.Carrier)
    (hf : S.RolePreserving T f) :
    f = S.roleTransport T hcardS := by
  funext x
  have hx : S.HasRole (S.roleOf hcardS x) x := S.roleOf_spec hcardS x
  have hfxRole : T.HasRole (S.roleOf hcardS x) (f x) := hf (S.roleOf hcardS x) x hx
  exact T.roleWitness_unique (S.roleOf hcardS x) (f x) hfxRole

theorem existsUnique_rolePreservingMap (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17) :
    ∃! f : S.Carrier → T.Carrier, S.RolePreserving T f := by
  refine ⟨S.roleTransport T hcardS, S.roleTransport_rolePreserving T hcardS, ?_⟩
  intro f hf
  exact S.rolePreserving_unique T hcardS f hf

theorem roleTransport_leftInverse (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17)
    (hcardT : Fintype.card T.Carrier = 17) :
    Function.LeftInverse (T.roleTransport S hcardT) (S.roleTransport T hcardS) := by
  intro x
  change S.roleWitness (T.roleOf hcardT (T.roleWitness (S.roleOf hcardS x))) = x
  have hRoleOf :
      T.roleOf hcardT (T.roleWitness (S.roleOf hcardS x)) = S.roleOf hcardS x := by
    exact T.roleOf_eq_of_hasRole hcardT (T.roleWitness_spec (S.roleOf hcardS x))
  rw [hRoleOf]
  exact (S.roleWitness_unique (S.roleOf hcardS x) x (S.roleOf_spec hcardS x)).symm

theorem roleTransport_rightInverse (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17)
    (hcardT : Fintype.card T.Carrier = 17) :
    Function.RightInverse (T.roleTransport S hcardT) (S.roleTransport T hcardS) := by
  intro y
  exact T.roleTransport_leftInverse (T := S) hcardT hcardS y

theorem roleTransport_bijective (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17)
    (hcardT : Fintype.card T.Carrier = 17) :
    Function.Bijective (S.roleTransport T hcardS) := by
  refine ⟨?_, ?_⟩
  · exact Function.LeftInverse.injective (S.roleTransport_leftInverse T hcardS hcardT)
  · exact Function.RightInverse.surjective (S.roleTransport_rightInverse T hcardS hcardT)

/-- Unique role-preserving equivalence between any two size-17 schemas. -/
noncomputable def roleEquiv (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17)
    (hcardT : Fintype.card T.Carrier = 17) :
    S.Carrier ≃ T.Carrier where
  toFun := S.roleTransport T hcardS
  invFun := T.roleTransport S hcardT
  left_inv := S.roleTransport_leftInverse T hcardS hcardT
  right_inv := S.roleTransport_rightInverse T hcardS hcardT

theorem roleEquiv_rolePreserving (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17)
    (hcardT : Fintype.card T.Carrier = 17) :
    S.RolePreserving T (S.roleEquiv T hcardS hcardT).toFun := by
  simpa [roleEquiv] using S.roleTransport_rolePreserving T hcardS

theorem roleEquiv_unique (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17)
    (hcardT : Fintype.card T.Carrier = 17)
    (e : S.Carrier ≃ T.Carrier)
    (he : S.RolePreserving T e.toFun) :
    e = S.roleEquiv T hcardS hcardT := by
  have hfun : e.toFun = S.roleTransport T hcardS :=
    S.rolePreserving_unique T hcardS e.toFun he
  ext x
  exact congrArg (fun f => f x) hfun

theorem existsUnique_roleEquiv (T : Delta1RoleSchema)
    (hcardS : Fintype.card S.Carrier = 17)
    (hcardT : Fintype.card T.Carrier = 17) :
    ∃! e : S.Carrier ≃ T.Carrier, S.RolePreserving T e.toFun := by
  refine ⟨S.roleEquiv T hcardS hcardT, S.roleEquiv_rolePreserving T hcardS hcardT, ?_⟩
  intro e he
  exact S.roleEquiv_unique T hcardS hcardT e he

end Delta1RoleSchema

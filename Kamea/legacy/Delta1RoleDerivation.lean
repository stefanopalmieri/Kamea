/- # Δ₁ Role-Schema Derivation from Behavioral Fingerprints

This file bridges the abstract `Delta1RoleSchema` theorem to the concrete `Δ₁`
algebra by defining 17 behavioral role-fingerprints on `D1ι` and proving:

1. Each fingerprint has a unique witness.
2. Different roles cannot share a witness.
3. Therefore `Δ₁` instantiates `Delta1RoleSchema`.
4. The abstract minimality/uniqueness theorems apply to `Δ₁` without any SMT encoding.

This is still not a full derivation from only `DirectedDS` base axioms
(`A2`, `A5`, `Ext`, `A7'`) for arbitrary models, but it closes the immediate
bridge between concrete behavioral recovery and the abstract schema theorem.
-/

import Kamea.Delta1RoleSchema
import Kamea.Discoverable

namespace Delta1RoleDerivation

open D1ι

/-- Canonical concrete representative for each abstract Δ₁ role. -/
def roleValue : D1Role → D1ι
  | .top => .top
  | .bot => .bot
  | .i => .i
  | .k => .k
  | .a => .a
  | .b => .b
  | .e_I => .e_I
  | .e_D => .e_D
  | .e_M => .e_M
  | .e_Sigma => .e_Sigma
  | .e_Delta => .e_Delta
  | .d_I => .d_I
  | .d_K => .d_K
  | .m_I => .m_I
  | .m_K => .m_K
  | .s_C => .s_C
  | .p => .p

/-- Behavioral fingerprints for the 17 Δ₁ roles. -/
def RoleFingerprint : D1Role → D1ι → Prop
  | .top, x =>
      dot x .i = .top ∧ dot x .bot = .top ∧ dot x .p = .top
  | .bot, x =>
      dot x .i = .bot ∧ dot x .top = .bot ∧ dot x .a = .bot
  | .i, x =>
      dot x .top = .i ∧ dot .e_I x = .top ∧ dot .e_D x = .d_I
  | .k, x =>
      dot x .top = .k ∧ dot .e_I x = .top ∧ dot .e_D x = .d_K
  | .a, x =>
      dot .m_K x = .top
  | .b, x =>
      dot .d_K x = .top ∧ dot .m_K x = .bot
  | .e_I, x =>
      dot x .i = .top ∧ dot x .k = .top ∧ dot x .a = .bot ∧ dot x .b = .bot
  | .e_D, x =>
      dot x .i = .d_I ∧ dot x .k = .d_K
  | .e_M, x =>
      dot x .i = .m_I ∧ dot x .k = .m_K
  | .e_Sigma, x =>
      dot x .s_C = .e_Delta
  | .e_Delta, x =>
      dot x .e_D = .d_I
  | .d_I, x =>
      dot x .top = .d_I ∧ dot .m_I x = .top
  | .d_K, x =>
      dot x .a = .top ∧ dot x .b = .top ∧ dot x .i = .bot
  | .m_I, x =>
      dot x .p = .bot ∧ dot x .k = .top ∧ dot x .a = .top
  | .m_K, x =>
      dot x .a = .top ∧ dot x .k = .bot ∧ dot x .p = .bot ∧ dot x .b = .bot
  | .s_C, x =>
      dot .e_Sigma x = .e_Delta ∧ dot x .top = .s_C
  | .p, x =>
      dot .m_I x = .bot

theorem roleFingerprint_iff_eq :
    ∀ r : D1Role, ∀ x : D1ι, RoleFingerprint r x ↔ x = roleValue r := by
  intro r x
  cases r <;> cases x <;> simp [RoleFingerprint, roleValue, dot]

theorem roleValue_injective : Function.Injective roleValue := by
  native_decide

theorem roleFingerprint_existsUnique (r : D1Role) :
    ∃! x : D1ι, RoleFingerprint r x := by
  refine ⟨roleValue r, ?_, ?_⟩
  · exact (roleFingerprint_iff_eq r (roleValue r)).2 rfl
  · intro x hx
    exact (roleFingerprint_iff_eq r x).1 hx

theorem roleFingerprint_disjoint :
    ∀ {r₁ r₂ : D1Role} {x : D1ι},
      RoleFingerprint r₁ x → RoleFingerprint r₂ x → r₁ = r₂ := by
  intro r₁ r₂ x hr₁ hr₂
  have hx₁ : x = roleValue r₁ := (roleFingerprint_iff_eq r₁ x).1 hr₁
  have hx₂ : x = roleValue r₂ := (roleFingerprint_iff_eq r₂ x).1 hr₂
  apply roleValue_injective
  exact hx₁.symm.trans hx₂

/-- Concrete `Δ₁` packaged as an instance of the abstract role schema, with
    role assumptions derived from behavioral fingerprints. -/
def delta1RoleSchemaFromFingerprints : Delta1RoleSchema where
  Carrier := D1ι
  dot := dot
  HasRole := RoleFingerprint
  role_unique := roleFingerprint_existsUnique
  role_disjoint := @roleFingerprint_disjoint

/-- Encoding-independent lower bound recovered for `Δ₁` via the abstract schema. -/
theorem delta1_card_ge_17_via_schema :
    17 ≤ Fintype.card D1ι :=
  Delta1RoleSchema.card_ge_17 delta1RoleSchemaFromFingerprints

/-- No role-schema realization below size 17 (concrete `Δ₁` bridge form). -/
theorem delta1_no_model_below_17_via_schema :
    ¬ Fintype.card D1ι < 17 :=
  Delta1RoleSchema.no_model_below_17 delta1RoleSchemaFromFingerprints

/-- At cardinality 17, any role-covering set is the whole carrier. -/
theorem delta1_unique_role_core_via_schema :
    ∀ T : Finset D1ι,
      (Delta1RoleSchema.CoversRoles delta1RoleSchemaFromFingerprints T) →
      T.card = 17 →
      T = (Finset.univ : Finset D1ι) := by
  have hcard : Fintype.card D1ι = 17 := by
    native_decide
  exact Delta1RoleSchema.unique_role_core_at_card_eq_17
    (S := delta1RoleSchemaFromFingerprints) hcard

end Delta1RoleDerivation

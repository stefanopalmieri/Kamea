import Kamea.CatKripkeWallMinimal
import Kamea.ICP

/-!
# Extensional 2-Pointed Magma (E2PM) and Full Independence

An **extensional 2-pointed magma** is the common base for all three capabilities:
a finite set with a binary operation, exactly two left-absorbers, and row-extensionality.
It is `FaithfulRetractMagma` without the retraction pair.

## Definitions

- `Ext2PointedMagma n`: extensional magma with exactly two absorbers.
- `HasRetractPair`: the E2PM admits a retraction pair (capability S).
- `HasDichotomy`: the E2PM satisfies the Kripke dichotomy (capability D).
- `HasICP`: already defined in `ICP.lean` (capability H).

## Results

- `d_not_implies_s`: D ⇏ S — an E2PM with dichotomy but no retraction pair (N=5).
- `h_not_implies_s`: H ⇏ S — an E2PM with ICP but no retraction pair (N=6).

Combined with the four existing directions (S ⇏ D, S ⇏ H, D ⇏ H, H ⇏ D),
this gives full 6-way independence of S, D, H.
-/

set_option autoImplicit false

namespace KripkeWall

-- ═══════════════════════════════════════════════════════════════════
-- The base structure: Extensional 2-Pointed Magma
-- ═══════════════════════════════════════════════════════════════════

/-- An extensional 2-pointed magma: a finite set with a binary operation,
    exactly two left-absorbers, and row-extensionality. This is the common
    base for capabilities S, D, and H. -/
structure Ext2PointedMagma (n : Nat) where
  dot : Fin n → Fin n → Fin n
  zero₁ : Fin n
  zero₂ : Fin n
  zero₁_left : ∀ x : Fin n, dot zero₁ x = zero₁
  zero₂_left : ∀ x : Fin n, dot zero₂ x = zero₂
  zeros_distinct : zero₁ ≠ zero₂
  no_other_zeros : ∀ y : Fin n, (∀ x : Fin n, dot y x = y) → y = zero₁ ∨ y = zero₂
  extensional : ∀ a b : Fin n, (∀ x : Fin n, dot a x = dot b x) → a = b

/-- An E2PM admits a retraction pair: capability S. -/
@[reducible] def HasRetractPair (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) : Prop :=
  ∃ sec ret : Fin n,
    (∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot ret (dot sec x) = x) ∧
    (∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot sec (dot ret x) = x) ∧
    dot ret z₁ = z₁

/-- An E2PM satisfies the Kripke dichotomy: capability D.
    Uses disjunction form for decidability. -/
@[reducible] def HasDichotomy (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) : Prop :=
  -- A classifier exists
  (∃ cls : Fin n, cls ≠ z₁ ∧ cls ≠ z₂ ∧
    ∀ x : Fin n, dot cls x = z₁ ∨ dot cls x = z₂) ∧
  -- The dichotomy holds (disjunction form)
  (∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
    (∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ (dot y x = z₁ ∨ dot y x = z₂)) ∨
    (∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ (dot y x ≠ z₁ ∧ dot y x ≠ z₂))) ∧
  -- Non-degeneracy: a non-classifier exists
  (∃ y : Fin n, y ≠ z₁ ∧ y ≠ z₂ ∧
    ∃ x : Fin n, x ≠ z₁ ∧ x ≠ z₂ ∧ dot y x ≠ z₁ ∧ dot y x ≠ z₂)

-- ═══════════════════════════════════════════════════════════════════
-- Every FRM is an E2PM (forgetful map)
-- ═══════════════════════════════════════════════════════════════════

/-- Every FaithfulRetractMagma yields an Ext2PointedMagma by forgetting the retraction pair. -/
def FaithfulRetractMagma.toE2PM {n : Nat} (M : FaithfulRetractMagma n) : Ext2PointedMagma n where
  dot := M.dot
  zero₁ := M.zero₁
  zero₂ := M.zero₂
  zero₁_left := M.zero₁_left
  zero₂_left := M.zero₂_left
  zeros_distinct := M.zeros_distinct
  no_other_zeros := M.no_other_zeros
  extensional := M.extensional

/-- Every FRM has a retraction pair (by definition). -/
theorem FaithfulRetractMagma.hasRetractPair {n : Nat} (M : FaithfulRetractMagma n) :
    HasRetractPair n M.dot M.zero₁ M.zero₂ :=
  ⟨M.sec, M.ret, M.ret_sec, M.sec_ret, M.ret_zero₁⟩

-- ═══════════════════════════════════════════════════════════════════
-- D ⇏ S witness: N=5 E2PM with dichotomy, no retraction pair
-- ═══════════════════════════════════════════════════════════════════

private def rawDnoS : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 1 | 2, 3 => 0 | 2, 4 => 0
  | 3, 0 => 4 | 3, 1 => 2 | 3, 2 => 4 | 3, 3 => 2 | 3, 4 => 4
  | 4, 0 => 2 | 4, 1 => 2 | 4, 2 => 3 | 4, 3 => 3 | 4, 4 => 3
  | _, _ => 0

private theorem rawDnoS_bound (a b : Fin 5) : rawDnoS a.val b.val < 5 := by
  revert a b; decide

def dotDnoS (a b : Fin 5) : Fin 5 := ⟨rawDnoS a.val b.val, rawDnoS_bound a b⟩

/-- The N=5 D⇏S witness is an E2PM. -/
def dNoS_e2pm : Ext2PointedMagma 5 where
  dot := dotDnoS
  zero₁ := 0
  zero₂ := 1
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide

/-- The D⇏S witness satisfies the Kripke dichotomy. -/
theorem dNoS_has_dichotomy : HasDichotomy 5 dotDnoS 0 1 := by decide

/-- The D⇏S witness has NO retraction pair. -/
theorem dNoS_no_retract : ¬ HasRetractPair 5 dotDnoS 0 1 := by decide

/-- **D ⇏ S**: The classifier dichotomy does not imply the existence of a retraction pair. -/
theorem d_not_implies_s :
    ∃ (_ : Ext2PointedMagma 5),
    HasDichotomy 5 dotDnoS 0 1 ∧ ¬ HasRetractPair 5 dotDnoS 0 1 :=
  ⟨dNoS_e2pm, dNoS_has_dichotomy, dNoS_no_retract⟩

-- ═══════════════════════════════════════════════════════════════════
-- H ⇏ S witness: N=6 E2PM with ICP, no retraction pair
-- ═══════════════════════════════════════════════════════════════════

private def rawHnoS : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0 | 0, 5 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 2, 0 => 3 | 2, 1 => 3 | 2, 2 => 2 | 2, 3 => 2 | 2, 4 => 2 | 2, 5 => 4
  | 3, 0 => 0 | 3, 1 => 2 | 3, 2 => 2 | 3, 3 => 2 | 3, 4 => 4 | 3, 5 => 0
  | 4, 0 => 4 | 4, 1 => 3 | 4, 2 => 2 | 4, 3 => 2 | 4, 4 => 4 | 4, 5 => 5
  | 5, 0 => 0 | 5, 1 => 0 | 5, 2 => 2 | 5, 3 => 2 | 5, 4 => 2 | 5, 5 => 4
  | _, _ => 0

private theorem rawHnoS_bound (a b : Fin 6) : rawHnoS a.val b.val < 6 := by
  revert a b; decide

def dotHnoS (a b : Fin 6) : Fin 6 := ⟨rawHnoS a.val b.val, rawHnoS_bound a b⟩

/-- The N=6 H⇏S witness is an E2PM. -/
def hNoS_e2pm : Ext2PointedMagma 6 where
  dot := dotHnoS
  zero₁ := 0
  zero₂ := 1
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide

/-- The H⇏S witness satisfies ICP (witnessed by a=2, b=4, c=5). -/
theorem hNoS_has_icp : HasICP 6 dotHnoS 0 1 := by decide

/-- The H⇏S witness has NO retraction pair. -/
theorem hNoS_no_retract : ¬ HasRetractPair 6 dotHnoS 0 1 := by decide

/-- **H ⇏ S**: The Internal Composition Property does not imply the existence
    of a retraction pair. -/
theorem h_not_implies_s :
    ∃ (_ : Ext2PointedMagma 6),
    HasICP 6 dotHnoS 0 1 ∧ ¬ HasRetractPair 6 dotHnoS 0 1 :=
  ⟨hNoS_e2pm, hNoS_has_icp, hNoS_no_retract⟩

-- ═══════════════════════════════════════════════════════════════════
-- Structural S ⇏ H witness: N=6 E2PM with retraction pair, no ICP
-- ═══════════════════════════════════════════════════════════════════

/-! The N=4 S⇏H witness (Kripke-4, in `ICP.lean`) is a cardinality obstruction:
    ICP needs 3 pairwise distinct core elements, but N=4 has only 2.
    This N=6 witness has 4 core elements, so ICP is non-vacuous.
    The retraction pair is an involution: s=r=2 with 2·(2·x)=x on core.
    No triple satisfies ICP — the failure is structural. -/

private def rawSnoH6 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0 | 0, 5 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 2, 0 => 0 | 2, 1 => 3 | 2, 2 => 3 | 2, 3 => 2 | 2, 4 => 5 | 2, 5 => 4
  | 3, 0 => 2 | 3, 1 => 4 | 3, 2 => 5 | 3, 3 => 5 | 3, 4 => 1 | 3, 5 => 4
  | 4, 0 => 5 | 4, 1 => 3 | 4, 2 => 0 | 4, 3 => 0 | 4, 4 => 3 | 4, 5 => 2
  | 5, 0 => 4 | 5, 1 => 2 | 5, 2 => 2 | 5, 3 => 2 | 5, 4 => 2 | 5, 5 => 2
  | _, _ => 0

private theorem rawSnoH6_bound (a b : Fin 6) : rawSnoH6 a.val b.val < 6 := by
  revert a b; decide

def dotSnoH6 (a b : Fin 6) : Fin 6 := ⟨rawSnoH6 a.val b.val, rawSnoH6_bound a b⟩

/-- The N=6 structural S⇏H witness is an E2PM. -/
def sNoH6_e2pm : Ext2PointedMagma 6 where
  dot := dotSnoH6
  zero₁ := 0
  zero₂ := 1
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide

/-- The structural S⇏H witness has a retraction pair (s=r=2, an involution). -/
theorem sNoH6_has_retract : HasRetractPair 6 dotSnoH6 0 1 := by decide

/-- The structural S⇏H witness has NO ICP — despite having 4 core elements. -/
theorem sNoH6_no_icp : ¬ HasICP 6 dotSnoH6 0 1 := by decide

/-- **Structural S ⇏ H**: A retraction pair does not imply the Internal
    Composition Property, even when enough core elements exist for ICP
    to be non-vacuous. -/
theorem s_not_implies_icp_structural :
    ∃ (_ : Ext2PointedMagma 6),
    HasRetractPair 6 dotSnoH6 0 1 ∧ ¬ HasICP 6 dotSnoH6 0 1 :=
  ⟨sNoH6_e2pm, sNoH6_has_retract, sNoH6_no_icp⟩

-- ═══════════════════════════════════════════════════════════════════
-- Full 6-way independence summary
-- ═══════════════════════════════════════════════════════════════════

/-!
## Full Independence of S, D, H

With all six directions now Lean-verified:

| Direction | Model | File |
|-----------|-------|------|
| S ⇏ D | N=8 FRM, dichotomy fails | `Countermodel.lean` |
| S ⇏ H | N=6 E2PM with retraction pair, ICP fails (structural) | this file |
| S ⇏ H | N=4 FRM (Kripke-4), ICP fails (cardinality) | `ICP.lean` |
| D ⇏ H | N=10 DRM, ICP fails | `Countermodels10.lean` + `ICP.lean` |
| H ⇏ D | N=10 FRM with ICP, dichotomy fails | `Countermodels10.lean` + `ICP.lean` |
| D ⇏ S | N=5 E2PM with dichotomy, no retraction pair | this file |
| H ⇏ S | N=6 E2PM with ICP, no retraction pair | this file |

No capability implies any other.
-/

end KripkeWall

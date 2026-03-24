import Kamea.CatKripkeWallMinimal
import Kamea.ICP

/-!
# Lean-Verified Coexistence Witness: S+D+ICP at N=5

A concrete 5-element algebra satisfying all three capabilities simultaneously:
  S (self-representation): retraction pair Q=E=2 (identity on core)
  D (self-description): classifier τ=3 with Kripke dichotomy
  H (self-execution): ICP witnessed by a=3, b=2, c=4

**Optimal minimum cardinality**: N=5 is the smallest possible witness for
S+D+H coexistence. At N=4, the core has only 2 elements, but ICP requires
3 pairwise distinct non-absorbers (`kripke4_no_icp` in ICP.lean).

The retraction pair is the identity on core (sec=ret=2), making this the
simplest possible S witness. The ICP factorization a·x = c·(b·x) with
b=identity reduces to a·x = c·x on core — the two classifiers (3 and 4)
agree on core but differ on absorber columns.

```
     0  1  2  3  4
  0 [0, 0, 0, 0, 0]   ← z₁ (absorber)
  1 [1, 1, 1, 1, 1]   ← z₂ (absorber)
  2 [0, 2, 2, 3, 4]   ← sec=ret (identity on core, non-classifier)
  3 [0, 0, 0, 1, 0]   ← classifier (a in ICP)
  4 [0, 1, 0, 1, 0]   ← classifier (c in ICP)

Category distribution:
  Zeros (2):           {0, 1}
  Classifiers (2):     {3, 4}
  Non-classifiers (1): {2}
```

Table verified by Z3 SAT solver, independently verified in Lean.
-/

set_option autoImplicit false

namespace KripkeWall

-- ═══════════════════════════════════════════════════════════════════
-- The N=5 S+D+ICP witness
-- ═══════════════════════════════════════════════════════════════════

private def rawW5 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 2 | 2, 3 => 3 | 2, 4 => 4
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 0 | 3, 3 => 1 | 3, 4 => 0
  | 4, 0 => 0 | 4, 1 => 1 | 4, 2 => 0 | 4, 3 => 1 | 4, 4 => 0
  | _, _ => 0

private theorem rawW5_bound (a b : Fin 5) : rawW5 a.val b.val < 5 := by
  revert a b; decide

def dotW5 (a b : Fin 5) : Fin 5 := ⟨rawW5 a.val b.val, rawW5_bound a b⟩

-- ═══════════════════════════════════════════════════════════════════
-- Capability S: FaithfulRetractMagma (self-representation)
-- ═══════════════════════════════════════════════════════════════════

/-- The N=5 witness is a FaithfulRetractMagma with Q=E=2 (identity on core). -/
def witness5_frm : FaithfulRetractMagma 5 where
  dot := dotW5
  zero₁ := 0
  zero₂ := 1
  sec := 2
  ret := 2
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide
  ret_sec := by decide
  sec_ret := by decide
  ret_zero₁ := by decide

-- ═══════════════════════════════════════════════════════════════════
-- Capability D: DichotomicRetractMagma (self-description)
-- ═══════════════════════════════════════════════════════════════════

/-- The N=5 witness is a DichotomicRetractMagma with τ=3. -/
def witness5_drm : DichotomicRetractMagma 5 where
  dot := dotW5
  zero₁ := 0
  zero₂ := 1
  sec := 2
  ret := 2
  cls := 3
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide
  ret_sec := by decide
  sec_ret := by decide
  ret_zero₁ := by decide
  cls_boolean := by decide
  cls_ne_zero₁ := by decide
  cls_ne_zero₂ := by decide
  dichotomy := by decide
  has_non_classifier := by decide

-- ═══════════════════════════════════════════════════════════════════
-- Capability H: ICP (self-execution)
-- ═══════════════════════════════════════════════════════════════════

/-- ICP holds at N=5, witnessed by a=3, b=2, c=4.
    Since b=2 is the identity on core, the factorization reduces to
    3·x = 4·x for all core x: the two classifiers agree on core. -/
theorem w5_has_icp : HasICP 5 dotW5 0 1 := by decide

-- ═══════════════════════════════════════════════════════════════════
-- Coexistence witness theorem
-- ═══════════════════════════════════════════════════════════════════

/-- **Lean-verified coexistence**: S+D+ICP all hold at N=5.
    This is the smallest possible witness for simultaneous S+D+H
    (at N=4, ICP is vacuously false since only 2 core elements exist). -/
theorem sdh_witness_5 :
    ∃ (_ : FaithfulRetractMagma 5),
    ∃ (_ : DichotomicRetractMagma 5),
    HasICP 5 dotW5 0 1 :=
  ⟨witness5_frm, witness5_drm, w5_has_icp⟩

-- ═══════════════════════════════════════════════════════════════════
-- Optimality: N=4 is impossible
-- ═══════════════════════════════════════════════════════════════════

/-- **N=5 is optimal**: At N=4, ICP fails for any E2PM (only 2 core elements,
    but ICP needs 3 pairwise distinct non-absorbers). Combined with
    `sdh_witness_5`, this shows N=5 is the minimum cardinality for
    S+D+H coexistence.

    Proof: ICP requires a, b, c pairwise distinct, all ∉ {0,1}. In Fin 4,
    the only non-absorbers are {2, 3} — a 2-element set cannot contain
    3 distinct elements. Pure pigeonhole, no `decide`. -/
theorem no_icp_at_4 (dot : Fin 4 → Fin 4 → Fin 4) : ¬ HasICP 4 dot 0 1 := by
  intro ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2, _, _, _⟩
  have mem : ∀ (x : Fin 4), x ≠ 0 → x ≠ 1 → x = 2 ∨ x = 3 := by decide
  rcases mem a ha1 ha2 with rfl | rfl <;> rcases mem b hb1 hb2 with rfl | rfl <;>
    rcases mem c hc1 hc2 with rfl | rfl <;> simp_all

end KripkeWall

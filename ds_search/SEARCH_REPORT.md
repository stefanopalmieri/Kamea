# Machine Search for Distinction Structures: Report

## Summary

Using Z3 SMT solver, we searched for finite magmas satisfying the Distinction Structure constraints encoded in `ds_search.py` (including fixed role indices and Block F default-to-`p` core behavior unless relaxed). The central result:

**Δ₁ is unique at N=17 under this encoding.** No other 17-element magma satisfies the full encoded constraint set. For N<17, a separate symbolic role-injection check (without fixed role-index assignment) is UNSAT. For N=18, SAT models exist and the 17×17 core is forced to Δ₁, but extensions are not unique up to isomorphism.

## Method

### Axiom Encoding

We encoded the DS axioms as Z3 integer constraints over an N×N Cayley table. The 17 structural roles (top, bot, i, k, a, b, e_I, e_D, e_M, e_Sigma, e_Delta, d_I, d_K, m_I, m_K, s_C, p) are fixed to indices 0–16 as symmetry breaking for this search encoding.

The constraint groups correspond directly to the Lean axioms:

| Group | Axioms | Constraints |
|-------|--------|-------------|
| Boolean absorption | A1–A4 | top, bot are left-absorbers; no third absorber |
| Testers | A5 | e_I, d_K, m_K, m_I have image ⊆ {top, bot}; no other element does |
| Tester partitions | — | Exact accept/reject sets for each tester |
| Ext | Ext | All row pairs are behaviorally distinct |
| H conditions | H1–H3 | e_D·i=d_I, e_D·k=d_K, e_M·i=m_I, e_M·k=m_K, e_Sigma·s_C=e_Delta |
| Structural novelty | A7' | e_Delta·e_D=d_I, distinct from e_I/e_D/e_M/e_Sigma applied to e_D |
| Self-identification | Block E | i·top=i, k·top=k, a·top=a, b·top=b, d_I·top=d_I, s_C·top=s_C |
| Default behavior (encoding assumption) | Block F | All unconstrained entries default to p |
| Discovery | D4–D5 | Encoder pair uniqueness, inert κ-tokens |

Block F is critical: in Δ₁, all 174 entries not governed by an explicit axiom evaluate to p. A dedicated independence check (`3.2b`) shows Block F is **not derivable** from the remaining constraints: with `default_p` relaxed, forcing one unconstrained Block-F slot to be non-`p` is SAT.

### Independent Verifier

A separate brute-force verifier (30 checks) validates every model returned by Z3, ensuring no encoding errors.

## Results

### Campaign Summary

| Search | N | Result | Time | Key Finding |
|--------|---|--------|------|-------------|
| 3.1: Find Δ₁ | 17 | SAT (≅ Δ₁) | 0.1s | Encoding verified |
| 3.2: Uniqueness | 17 | **UNSAT** | 0.1s | **Δ₁ is unique at N=17 under this encoding** |
| 3.2c: Symbolic role-injection bound (N=14,16) | 14, 16 | **UNSAT** | 0.0s | Lower bound without fixed role indices |
| 3.2c: Symbolic role-injection bound (N=17) | 17 | SAT | 0.0s | Tightness witness for the role-count bound |
| 3.2b: Block F independence witness | 17 | SAT | 0.1s | `default_p` is not implied by other constraints |
| 3.3: N=14 | 14 | UNSAT | 0.0s | Too small (need 17 roles) |
| 3.3: N=16 | 16 | UNSAT | 0.0s | Too small |
| 3.4: N=18 | 18 | SAT | 0.1s | Core = Δ₁, extra element is junk |
| 3.4b: N=18 with core mismatch forced | 18 | **UNSAT** | 0.1s | Core cannot differ from Δ₁ |
| 3.4c: N=18 sampled extension isomorphism classes | 18 | CLASSIFIED | 171.4s | 6 sampled models gave 6 iso classes (+ more SAT) |
| 3.4d: N=18 actuality variants with fixed non-m_I rows | 18 | CLASSIFIED | 0.4s | Exactly 18 consistent `m_I`-row variants |
| 3.5: Relax default_p | 17 | SAT (NEW) | 0.1s | Junk entries vary freely |
| 3.5: Relax discovery | 17 | UNSAT | 0.1s | Discovery forced by other axioms |
| 3.5: Relax synthesis | 17 | UNSAT | 0.1s | Synthesis entries can't be p |
| 3.5: Relax H conditions | 17 | UNSAT | 0.1s | H entries can't be p |
| 3.5: Relax self-id | 17 | UNSAT | 0.1s | Self-id entries can't be p |

### Result 1: Uniqueness at N=17 (Encoding-Qualified)

With the full encoded constraint set (including Block F default behavior), Z3 proves UNSAT when excluding Δ₁. The search space is 17^289 ≈ 10^356 possible Cayley tables, yet only ONE satisfies all encoded constraints.

This uniqueness is not trivial — it relies on the interplay of ALL axiom groups plus Block F. The Ext axiom (behavioral separability) forces every row to be distinct, which combined with the tester structure and default behavior, pins down every table entry.

### Result 1b: Block F Is Independent (Encoding-Qualified)

In campaign step `3.2b`, we relax only `default_p`, keep the rest of the encoding intact, and force at least one unconstrained Block-F core entry to be non-`p`. Z3 returns SAT in 0.1s (verification 30/30, all categories present). Therefore Block F is not a consequence of the other encoded constraints.

### Result 2: No Smaller Model in the Fixed-Role Encoding

For N<17, the encoding is trivially UNSAT: 17 fixed role variables cannot fit in fewer than 17 carrier elements. This is a lower bound of the encoding, not an independent Lean theorem of model-minimality.

### Result 2b: Role-Count Lower Bound Without Fixed Indices

To decouple the lower bound from fixed role indices, we added a separate SMT check with 17 **anonymous symbolic role slots** constrained only by:

- each slot in `[0, N)`,
- strict increasing order across slots (symmetry breaking only).

Results: `N=14` and `N=16` are UNSAT; `N=17` is SAT. This is the pigeonhole lower bound in SMT form and does not rely on assigning specific indices to named roles.

### Result 3: Larger DS = Δ₁ + Junk

At N=18, Z3 finds a model, and the 17×17 core is identical to Δ₁. An explicit core-mismatch check (`N=18` with any forced difference in the 17×17 core) is UNSAT. The extra elements are unconstrained except by global constraints such as Ext and tester behavior.

The 18th element is "actual" (m_I accepts it) and distinguishable from all core elements, but carries no structural information.

### Result 3b: N=18 Extensions Are Not Unique Up To Isomorphism

A bounded classification pass (`3.4c`) sampled 6 SAT models at N=18 and compared them by explicit isomorphism checks. All 6 landed in different isomorphism classes, and the solver still had additional SAT models after the sample cap. So N=18 extensions are not unique up to isomorphism in this encoding.

### Result 3c: Structural Invariance vs Actuality Choice

In `3.4d`, we fixed all non-`m_I` rows to a canonical N=18 model, relaxed only `actuality`, and enumerated all consistent `m_I` rows. The solver returned exactly 18 variants, one for each possible rejected index in the carrier.

This gives a precise invariance statement: non-`m_I` structure can be held fixed while actuality assignment varies, so structural observations that avoid `m_I` underdetermine actuality.

### Result 4: Axiom Sensitivity

The relaxation results reveal tight coupling between axiom groups:

**With default_p active (excluding Δ₁):**
All individual axiom relaxations give UNSAT. This means: if you take Δ₁'s table and replace any axiom-governed entry with p (the default), the resulting table violates some other axiom (typically Ext). Each non-default entry is structurally load-bearing.

**Without default_p (excluding Δ₁):**
All relaxations give SAT, but the models differ from Δ₁ only in junk entries and fail exactly the checks corresponding to the relaxed axiom:

| Relaxation | Failed Checks | Categories |
|-----------|---------------|------------|
| No discovery uniqueness | inert_kappa, encoder_pair_unique | D✓ C✓ A✓ S✓ |
| No synthesis | H3, A7', e_Delta·e_D=d_I | D✓ C✓ A✓ S✓ |
| No H conditions | H1(e_D,i), H1(e_D,k), H2(e_M,i), H2(e_M,k) | D✓ C✓ A✓ S✓ |
| No self-identification | i/k/a/b/d_I/s_C self-id | D✓ C✓ A✓ S✓ |
| No Ext | (none — Ext happens to hold anyway) | D✓ C✓ A✓ S✓ |
| No actuality | mI_rejects_p_only | D✓ C✓ **A✗** S✓ |

The actuality relaxation is notable: it's the only one that breaks a category. Without the m_I constraint, the model loses the actuality category entirely.

## Interpretation

### 1. The Distinction Structure Is Rigid in the Strongest Sense

Within this encoding, Δ₁ is not merely unique up to isomorphism at N=17 — it is the unique table with fixed role names **given Block F**. The symmetry-breaking argument (fixed role indices) combined with UNSAT at N=17 excluding Δ₁ yields a single satisfying Cayley table.

### 2. Every Table Entry Is Necessary

The 174 "default-to-p" entries are not arbitrary padding once Block F is assumed. They are coupled to the non-default entries by Ext and the other constraints. If any axiom-governed entry is changed to p, the system becomes inconsistent under the default-to-p encoding.

### 3. N=18 Admits Many Extensions

No smaller carrier can accommodate 17 roles. At N=18, the core remains forced to Δ₁, but extension space is large: even a small sampled classification produced multiple non-isomorphic classes.

### 4. Actuality Is the Category-Critical Axiom

Among all individual relaxations, only removing the actuality constraint (m_I behavior) destroys an ontological category. The other axioms can be relaxed (in the junk-free setting) without losing any category — their violation shows up only in structural checks, not in category membership. This aligns with the Lean-verified Actuality Irreducibility theorem.

## Technical Notes

- **Solver**: Z3 4.13+, invoked via Python bindings
- **Runtime**: Core SAT/UNSAT checks complete in ~0.1s; sampled N=18 isomorphism classification (`3.4c`) is the expensive step (~171s for 6-model sample).
- **Verification**: Independent 30-check brute-force verifier confirms every SAT result
- **Isomorphism**: Fixed-role N=17 checks use literal equality; N=18 classification (`3.4c`) uses explicit permutation-isomorphism checks via Z3.
- **Encoding size**: ~5000 Z3 constraints for N=17

## Conjectures

1. **Categorical uniqueness**: Δ₁ may be the unique *finite* DS of any size, up to the addition of inert junk elements. (We've verified this for N ≤ 18.)

2. **Axiom independence**: The individual axiom groups appear to be independent (no single group is derivable from the others), but this requires separate verification.

3. **Generalization**: The Z3 encoding could be adapted to search for *symmetric* DS (using Basic.lean's `SymmetricDS` axioms) or other algebraic structures with self-modeling properties.

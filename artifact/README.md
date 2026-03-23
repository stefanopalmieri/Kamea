# Artifact: Three Independent Capabilities of Reflective Computation in Finite Algebras

## Quick verification

```bash
lake build    # compiles all Lean 4 files, verifies zero sorry
```

Expected output: `Build completed successfully (637 jobs).`

To verify zero `sorry`:
```bash
grep -rn sorry Kamea/*.lean | grep -v legacy | grep -v "without sorry"
```
Expected output: empty (no matches).

## Lean file inventory

All files are in `Kamea/`. Proof styles: **Algebraic** = pure equational reasoning (no `decide`); **decide** = kernel computation (N ≤ 8); **native_decide** = compiled native code (N = 10).

| File | Theorems | Style | Content |
|------|----------|-------|---------|
| `CatKripkeWallMinimal.lean` | 17 | Algebraic | Core definitions (`FaithfulRetractMagma`, `DichotomicRetractMagma`), three-category decomposition, cardinality bounds, no right identity, no associativity, minimal witnesses (N=4, N=5) |
| `NoCommutativity.lean` | 3 | Algebraic | No extensional magma with two absorbers is commutative |
| `Functoriality.lean` | 4 | Algebraic | Three-category decomposition preserved by DRM isomorphisms |
| `SelfSimulation.lean` | 5 | Algebraic | Self-simulation forces injective encoding and injective partial application |
| `ICP.lean` | 20 | Algebraic + decide | ICP ↔ Compose+Inert equivalence (universal); ICP invariance under isomorphisms; model-specific ICP verification on all counterexamples; ICP condition necessity (both conditions individually necessary) |
| `Countermodel.lean` | 5 | decide | S ⊬ D: 8-element FRM with classifier that violates dichotomy |
| `Countermodels10.lean` | 9 | native_decide | D ⊬ H: 10-element DRM with no ICP triple; H ⊬ D: 10-element FRM with ICP but violated dichotomy |
| `Witness10.lean` | 6 | native_decide | S+D+H coexistence at N=10 (all roles distinct) |
| `Witness6.lean` | 3 | decide | S+D+H coexistence at N=6 (role overlap: retraction pair = ICP witnesses) |

**Total: 72 public theorems, zero sorry.**

## Counterexample tables

Frozen Cayley tables for all counterexamples: `counterexamples.json`

Each table can be cross-checked against the Lean source by reading the `raw*` function definitions in the corresponding `.lean` file.

## Key theorems by paper section

| Paper claim | Lean theorem | File |
|-------------|-------------|------|
| ICP ↔ Compose+Inert (Thm 5.1) | `icp_iff_composeInert` | `ICP.lean` |
| S ⊬ D (Thm 6.1, item 1) | `frm_independent_of_dichotomy` | `Countermodel.lean` |
| D ⊬ H (Thm 6.1, item 2) | `dNotH_no_icp` | `ICP.lean` |
| H ⊬ D (Thm 6.1, item 3) | `hNotD_has_icp` + `hNotD_violates_dichotomy` | `ICP.lean` + `Countermodels10.lean` |
| S ⊬ H (Thm 6.1, item 4) | `s_not_implies_icp` | `ICP.lean` |
| S+D+H at N=10 (Thm 7.1) | `sdh_witness_10` | `Witness10.lean` / `ICP.lean` |
| S+D+H at N=6 | `sdh_witness_6` | `Witness6.lean` |
| No right identity (Thm 3.5) | `no_right_identity` | `CatKripkeWallMinimal.lean` |
| No associativity (Thm 3.6) | `no_associativity` | `CatKripkeWallMinimal.lean` |
| Functoriality (Thm 4.1) | `DRMIso.preserves_decomposition` | `Functoriality.lean` |
| ICP invariance | `FRMIso.preserves_icp` | `ICP.lean` |
| ICP distinctness necessary | `icp_distinct_necessary` | `ICP.lean` |
| ICP non-triviality necessary | `icp_nontrivial_necessary` | `ICP.lean` |

## Requirements

- Lean 4 (tested with the version specified in `lean-toolchain`)
- `lake` build system
- Internet connection for first build (downloads mathlib cache)

## Build time

First build: ~5 minutes (downloading mathlib). Subsequent builds: ~30 seconds.

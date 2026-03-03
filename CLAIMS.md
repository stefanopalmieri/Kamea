# Claims Contract

This file is the canonical status registry for claims made in this repository.

## Claim Tiers

- `Lean-proved`: Machine-checked theorem in Lean (`lake build` passes).
- `SMT-encoding-qualified`: Proved by Z3 for the specific encoding in `ds_search/ds_search.py` (including its assumptions).
- `Empirical`: Supported by repeatable experiments/scripts, not a formal proof.
- `Conjecture/Open`: Not proved; hypothesis, interpretation, or open problem.

## Promotion Rules

- `Empirical -> Lean-proved`: requires a Lean theorem (or equivalent formal proof artifact in-repo).
- `SMT-encoding-qualified -> Lean-proved`: requires removing encoding-specific assumptions or proving them independently.
- `Conjecture/Open -> any proved tier`: requires explicit artifact + reproducible command.

## Current Claim Registry

| Claim | Tier | Primary Evidence | Reproduce |
|---|---|---|---|
| Intrinsically reflexive DS models exist (`Delta0`, `Delta1`) | Lean-proved | `DistinctionStructures/Delta0.lean`, `DistinctionStructures/Delta1.lean` | `lake build` |
| Directed DS recoverability (8-step filtration; Step 3 tie resolved at Step 4) | Lean-proved | `DistinctionStructures/Discoverable.lean` | `lake build` |
| Actuality irreducibility on 18-element carrier (`Δ₁`, `Δ₁'`) | Lean-proved | `DistinctionStructures/ActualityIrreducibility.lean` | `lake build` |
| Sheaf-style filtration + four-category necessity for `Δ₁` | Lean-proved | `DistinctionStructures/Sheaf.lean` | `lake build` |
| Full 66-atom Kamea uniqueness/Ext package | Lean-proved | `DistinctionStructures/DiscoverableKamea.lean` | `lake build` |
| `Δ₁` uniqueness at `N=17` | SMT-encoding-qualified | `ds_search/ds_search.py`, `ds_search/results/campaign.json` | `uv run python -m ds_search.ds_search` |
| No `N<17` model in search campaign | SMT-encoding-qualified | Encoding uses 17 fixed role variables in `encode_ds` | `uv run python -m ds_search.ds_search` |
| At `N=18`, 17x17 core forced to `Δ₁` | SMT-encoding-qualified | `3.4b` core-mismatch UNSAT in campaign | `uv run python -m ds_search.ds_search` |
| Removing `default_p` permits additional non-isomorphic models | SMT-encoding-qualified | `3.5: Relaxed (No default-to-p)` campaign result | `uv run python -m ds_search.ds_search` |
| `Δ₂` black-box recovery of all 21 atoms | Empirical | `delta2_true_blackbox.py` | `uv run python delta2_true_blackbox.py` |
| WL census: structureless rigid magmas often efficiently recoverable | Empirical | `rigid_census.py`, `counterexample_search.py` | `uv run python rigid_census.py` and `uv run python counterexample_search.py` |
| GNN learns permutation-invariant discriminative embeddings for Kamea atoms | Empirical | `gnn_fingerprint.py`, `gnn_output/` | `uv run python gnn_fingerprint.py` |
| Four roles are minimal in general | Conjecture/Open | Discussed as open in docs | N/A |
| Symmetric discoverability impossibility (fully general theorem) | Conjecture/Open | Demonstrated for constructions, not fully formalized | N/A |
| Unique endomorphism rigidity of `Δ₁` | Conjecture/Open | Marked as conjecture in `Sheaf.lean` | N/A |

## Scope Notes

- Statements labeled `SMT-encoding-qualified` are true for the encoded search problem, not automatically for all abstract DS models.
- Statements labeled `Empirical` are evidence-backed but may change with stronger tests or alternative implementations.
- Any top-level claim added to `README.md` should map to one row in this file.

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
| Δ₂ primitives (`QUOTE`,`EVAL`,`APP`,`UNAPP`) are uniquely forced by four lift-signatures | Lean-proved | `DistinctionStructures/OntologicalDerivation.lean` | `lake build` |
| Δ₂ internal minimal basis: any signature-covering set has card ≥ 4; card-4 cover is uniquely `{QUOTE,EVAL,APP,UNAPP}` | Lean-proved | `DistinctionStructures/OntologicalMinimality.lean` | `lake build` |
| Abstract schema theorem: any `FourLiftSchema` has unique lift witnesses and unique minimal card-4 covering basis | Lean-proved | `DistinctionStructures/OntologicalSchema.lean` | `lake build` |
| Abstract Δ₁ role-schema theorem: 17 distinct roles force `card ≥ 17`; any role-covering set has `card ≥ 17` and unique card-17 core; at `card = 17`, role-preserving equivalence is unique | Lean-proved | `DistinctionStructures/Delta1RoleSchema.lean` | `lake build` |
| Concrete Δ₁ bridge: behavioral fingerprints derive the abstract role-schema assumptions, enabling schema minimality/uniqueness theorems on `Δ₁` without SMT encoding assumptions | Lean-proved | `DistinctionStructures/Delta1RoleDerivation.lean` | `lake build` |
| Base DirectedDS axioms (`A2`,`A5`,`Ext`) imply only `card ≥ 2`, and this bound is tight (2-element countermodel) | Lean-proved | `DistinctionStructures/BaseAxiomDerivation.lean` | `lake build` |
| Base DirectedDS + generic directed novelty (`DirectedA7Prime`) still does not force `card ≥ 17` (3-element countermodel exists) | Lean-proved | `DistinctionStructures/BasePlusA7Derivation.lean` | `lake build` |
| Strengthened DirectedDS axioms (`A2`,`A5`,`Ext` + `RoleComplete17`) force `card ≥ 17` (hence no model with `card < 17`) | Lean-proved | `DistinctionStructures/StrengthenedBaseAxioms.lean` | `lake build` |
| `Δ₁` satisfies the strengthened axiom bundle, yielding `card ≥ 17` from strengthened axioms alone | Lean-proved | `DistinctionStructures/Delta1Strengthened.lean` | `lake build` |
| Intermediate ladder result: weakest found forcing condition is `Embedding17` (`Nonempty (Fin 17 ↪ D)`), with `Embedding17 ↔ card ≥ 17` and `RoleComplete17 ↔ Embedding17` | Lean-proved | `DistinctionStructures/IntermediateAxiomLadder.lean` | `lake build` |
| Fixed-role + `default_p` N=17 table assumptions have a unique solution (`dot`), and excluding `dot` is UNSAT (`unsat_exclude_delta1`) | Lean-proved | `DistinctionStructures/SMTEncodingLean.lean` | `lake build DistinctionStructures.SMTEncodingLean` |
| Z3 campaign also reports `Δ₁` uniqueness at `N=17` under the same fixed-role + `default_p` encoding assumptions | SMT-encoding-qualified | `ds_search/ds_search.py`, `ds_search/results/campaign.json` | `uv run python -m ds_search.ds_search` |
| `default_p` is independent of the other encoded constraints (countermodel exists with `default_p` relaxed and at least one Block-F slot forced non-`p`) | SMT-encoding-qualified | `3.2b: Block F independence witness` in `ds_search/results/campaign.json` | `uv run python -m ds_search.ds_search` |
| No `N<17` model for encodings that require 17 distinct roles (independent of fixed role indices) | SMT-encoding-qualified | `3.2c: Symbolic role-injection bound N=14,16` in `ds_search/results/campaign.json` | `uv run python -m ds_search.ds_search` |
| At `N=18`, 17x17 core forced to `Δ₁` | SMT-encoding-qualified | `3.4b` core-mismatch UNSAT in campaign | `uv run python -m ds_search.ds_search` |
| At `N=18`, extensions are not unique up to isomorphism (sampled 6 models gave 6 isomorphism classes; more models still SAT) | SMT-encoding-qualified | `3.4c: N=18 sampled extension isomorphism classes` in `ds_search/results/campaign.json` | `uv run python -m ds_search.ds_search` |
| With `N=18` non-`m_I` rows fixed and `actuality` relaxed, there are exactly 18 consistent `m_I`-row variants (one reject index each), so non-`m_I` structure underdetermines actuality | SMT-encoding-qualified | `3.4d: N=18 actuality variants with fixed non-m_I rows` in `ds_search/results/campaign.json` | `uv run python -m ds_search.ds_search` |
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

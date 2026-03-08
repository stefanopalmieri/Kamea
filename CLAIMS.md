# Claims Contract

This file is the canonical status registry for claims made in this repository.

## Claim Tiers

- `Lean-proved`: Machine-checked theorem in Lean (`lake build` passes).
- `Empirical`: Supported by repeatable experiments/scripts, not a formal proof.
- `Conjecture/Open`: Not proved; hypothesis, interpretation, or open problem.

## Promotion Rules

- `Empirical -> Lean-proved`: requires a Lean theorem (or equivalent formal proof artifact in-repo).
- `Conjecture/Open -> any proved tier`: requires explicit artifact + reproducible command.

## Current Claim Registry

| Claim | Tier | Primary Evidence | Reproduce |
|---|---|---|---|
| Abstract schema theorem: any `FourLiftSchema` has unique lift witnesses and unique minimal card-4 covering basis | Lean-proved | `DistinctionStructures/OntologicalSchema.lean` | `lake build` |
| Base DirectedDS axioms (`A2`,`A5`,`Ext`) imply only `card >= 2`, and this bound is tight (2-element countermodel) | Lean-proved | `DistinctionStructures/BaseAxiomDerivation.lean` | `lake build` |
| Base DirectedDS + generic directed novelty (`DirectedA7Prime`) still does not force `card >= 17` (3-element countermodel exists) | Lean-proved | `DistinctionStructures/BasePlusA7Derivation.lean` | `lake build` |
| Psi16 satisfies all structural + computational axioms (L0-L8, C, D, PA, VV, QE, 1-inert, E-trans, Branch, Compose, Y, Selection, IO, 8-state counter) | Lean-proved | `DistinctionStructures/Psi16.lean` (42 theorems) | `lake build` |
| Psi16-full satisfies all axioms plus DEC, PAIR/FST/SND, INC2, SWAP (full operational saturation) | Lean-proved | `DistinctionStructures/Psi16Full.lean` (83 theorems) | `lake build` |
| Psi16 is WL-1 discrete (rigid) and fully producible; {top,bot,Q,E} generates all 16 in <=4 steps | Lean-proved | `DistinctionStructures/Psi16.lean` | `lake build` |
| Psi16-full is WL-1 discrete (rigid) and fully producible; {top,bot,Q,E} generates all 16 in <=4 steps | Lean-proved | `DistinctionStructures/Psi16Full.lean` | `lake build` |
| Full axiom set is SAT at N=16 (all phases including IO + 8-state counter + selection + DEC/PAIR/INC2/SWAP) | Empirical | `ds_search/stacking_analysis.py` (`extract_psi16_full()`) | `uv run python -c "from ds_search.stacking_analysis import extract_psi16_full; extract_psi16_full()"` |
| Full axiom set is SAT at N=12 with 117/144 free cells (18.8% determination) | Empirical | `ds_search/stacking_analysis.py` (`etrans_residual_freedom()`) | `uv run python -c "from ds_search.stacking_analysis import etrans_residual_freedom; etrans_residual_freedom()"` |
| QE requires N>=8; Branch/Compose/Y require N>=12 | Empirical | `ds_search/stacking_analysis.py` | SAT/UNSAT checks at various N |
| WL census: structureless rigid magmas often efficiently recoverable | Empirical | `rigid_census.py`, `counterexample_search.py` | `uv run python rigid_census.py` |
| Actuality irreducibility: tester row is completely free (all core tester cells can independently flip) | Empirical | `ds_search/stacking_analysis.py`, `ds_search/n16_freedom.py` | SAT-verified with push/pop at N=8, 12, 16 |
| Full axiom set at N=16: 64/256 cells fixed (25.0% determination), 192 free | Empirical | `ds_search/n16_freedom.py` | `uv run python ds_search/n16_freedom.py` |
| Chirality: E-transparency does not cascade to tester cells | Empirical | `ds_search/stacking_analysis.py` | SAT push/pop: all tester-cell values remain SAT |
| No right identity under full axiom set | Empirical | `ds_search/stacking_analysis.py` | UNSAT at N≥6 |
| No full associativity under full axiom set | Empirical | `ds_search/stacking_analysis.py` | UNSAT; no associative sub-magma of size ≥ 4 |
| Encoder-tester non-commutativity | Empirical | `ds_search/stacking_analysis.py` | SAT-verified |
| Black-box recovery: all 16 elements recoverable from shuffled oracle (3 methods, 100% on 1000 seeds) | Empirical | `psi_blackbox.py` | `uv run python psi_blackbox.py --seeds 1000 --compare` |
| Decidability boundary: Y-combinator introduces undecidable termination | Conjecture/Open | Structural argument in README | Not formally proved |
| Four roles are minimal in general | Conjecture/Open | Discussed as open in docs | N/A |
| Symmetric discoverability impossibility (fully general theorem) | Conjecture/Open | Demonstrated for constructions, not fully formalized | N/A |

## Scope Notes

- Statements labeled `Empirical` are evidence-backed but may change with stronger tests or alternative implementations.
- Any top-level claim added to `README.md` should map to one row in this file.

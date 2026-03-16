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
| Psi16 automorphism rigidity: every injective endomorphism is the identity (Aut = {id}) | Lean-proved | `DistinctionStructures/Psi16Rigidity.lean` | `lake build` |
| Psi16 discoverability: all 16 elements behaviorally identifiable; 4 probes suffice (injective fingerprint) | Lean-proved | `DistinctionStructures/Psi16Discoverable.lean` | `lake build` |
| Psi16 actuality irreducibility: twin 17-element models agree on all structure but disagree on tester assignment | Lean-proved | `DistinctionStructures/Psi16ActualityIrreducibility.lean` | `lake build` |
| Full axiom set is SAT at N=16 (all phases including IO + 8-state counter + selection + DEC/PAIR/INC2/SWAP) | Empirical | `ds_search/stacking_analysis.py` (`extract_psi16_full()`) | `uv run python -c "from ds_search.stacking_analysis import extract_psi16_full; extract_psi16_full()"` |
| Full axiom set is SAT at N=12 with 117/144 free cells (18.8% determination) | Empirical | `ds_search/stacking_analysis.py` (`etrans_residual_freedom()`) | `uv run python -c "from ds_search.stacking_analysis import etrans_residual_freedom; etrans_residual_freedom()"` |
| QE requires N>=8; Branch/Compose/Y require N>=12 | Empirical | `ds_search/stacking_analysis.py` | SAT/UNSAT checks at various N |
| WL census: structureless rigid magmas often efficiently recoverable | Empirical | `ds_search/rigid_census.py`, `ds_search/counterexample_search.py` | `uv run python ds_search/rigid_census.py` |
| Actuality irreducibility: tester row is completely free (all core tester cells can independently flip) | Empirical | `ds_search/stacking_analysis.py`, `ds_search/n16_freedom.py` | SAT-verified with push/pop at N=8, 12, 16 |
| Full axiom set at N=16: 64/256 cells fixed (25.0% determination), 192 free | Empirical | `ds_search/n16_freedom.py` | `uv run python ds_search/n16_freedom.py` |
| Chirality: E-transparency does not cascade to tester cells | Empirical | `ds_search/stacking_analysis.py` | SAT push/pop: all tester-cell values remain SAT |
| No right identity in any PsiStructure (L0–L3 role axioms) | Lean-proved | `DistinctionStructures/PsiUniversalBounds.lean` | `lake build` |
| Card ≥ 4 from role axioms (L0–L3), tight (4-element countermodel) | Lean-proved | `DistinctionStructures/PsiUniversalBounds.lean`, `DistinctionStructures/PsiCountermodels.lean` | `lake build` |
| No full associativity under full axiom set | Empirical | `ds_search/stacking_analysis.py` | UNSAT; no associative sub-magma of size ≥ 4 |
| Encoder-tester non-commutativity | Empirical | `ds_search/stacking_analysis.py` | SAT-verified |
| Black-box recovery: all 16 elements recoverable from shuffled oracle (3 methods, 100% on 1000 seeds) | Empirical | `psi_blackbox.py` | `uv run python psi_blackbox.py --seeds 1000 --compare` |
| Ψ∗ Turing-completeness: 7 axiom-forced elements (⊤, Q, E, f, g, η, ρ) simulate 2-counter machines; universal across all models | Empirical | `psi_star.py` — stepped 2CM matches reference interpreter on 4 test programs | `uv run python psi_star.py` |
| 1-bit logic (AND/OR/XOR): curried dispatch on {s0,s1} embeds all three Boolean gates simultaneously; model stays WL-1 rigid | Empirical | SAT-verified at N=16 with full axiom set + all operational constraints | `ds_search/n16_freedom.py` build_solver + XOR/AND/OR constraints |
| Five behavioral categories forced (32/45 role pairs UNSAT, min 5 elements) | Empirical | `ds_search/forced_roles_test.py` — role-aliasing at N=12; `docs/forced_roles.md` | `uv run python -m ds_search.forced_roles_test` |
| Kleene wall: τ cannot merge with any encoder or inert role (9/9 pairs UNSAT) | Empirical | `ds_search/forced_roles_test.py` | `uv run python -m ds_search.forced_roles_test --quick` |
| Inert wall: g cannot merge with any other role (9/9 pairs UNSAT) | Empirical | `ds_search/forced_roles_test.py` | `uv run python -m ds_search.forced_roles_test --quick` |
| Rigidity survives all collapse levels: 6/6 levels WL-1 rigid, |Aut|=1, 1-probe discoverable | Empirical | `ds_search/collapse_rigidity_test.py` | `uv run python -m ds_search.collapse_rigidity_test` |
| Model diversity at maximal collapse: 20+ distinct rigid models, 116/144 cells free | Empirical | `ds_search/collapse_model_count.py` | `uv run python -m ds_search.collapse_model_count` |
| Maximal expressiveness selects 7-role specialization (49 vs 16 1-step cells, monotone in k) | Empirical | `ds_search/compositional_expressiveness.py`; `docs/forced_roles_theorem.md` | `uv run python -m ds_search.compositional_expressiveness` |
| Emergent pair structure from Branch + 1-Inert (g as CONS not axiomatized) | Empirical | Structural analysis in `docs/forced_roles_theorem.md` | N/A |
| Futamura projection 1: supercompile(interpreter, program) = supercompile(program) for all 10 test cases | Empirical | `examples/psi_futamura.psi` | `python3 psi_supercompile.py --table=c examples/psi_futamura.psi` |
| Cancellation rule soundness: INC/DEC/QE restricted to verified element domain (exhaustive 16-element check) | Empirical | `psi_supercompile.py` — counterexample: INC(DEC(12))=13≠12 | N/A |
| Ψ-Lisp → C/Rust transpiler: compiled output matches interpreter on fibonacci + recursion | Empirical | `psi_transpile.py --target c\|rust` | `python3 psi_transpile.py --target rust examples/psi_fibonacci.lisp > /tmp/fib.rs && cp psi_runtime.rs /tmp/ && rustc -O -o /tmp/fib /tmp/fib.rs && /tmp/fib` |
| MMTk GC stress test: 10M cons cells in 4MB heap (MarkSweep + shadow stack roots) | Empirical | `kamea-rs/crates/wispy-gc/` + `wispy-stress/` | `cd kamea-rs && HEAP_MB=4 cargo run -p wispy-stress --release` |
| Variational principle as formal theorem (cell count monotonicity → uniqueness) | Conjecture/Open | Empirically demonstrated; formal proof open | N/A |
| Four roles are minimal in general | Conjecture/Open | Discussed as open in docs | N/A |
| Symmetric discoverability impossibility (fully general theorem) | Conjecture/Open | Demonstrated for constructions, not fully formalized | N/A |

## Scope Notes

- Statements labeled `Empirical` are evidence-backed but may change with stronger tests or alternative implementations.
- Any top-level claim added to `README.md` should map to one row in this file.

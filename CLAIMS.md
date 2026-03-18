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
| Expressiveness independently justifies distinctness axiom (49 vs 16 1-step cells, monotone in k) | Empirical | `ds_search/compositional_expressiveness.py`; `docs/forced_roles_theorem.md` | `uv run python -m ds_search.compositional_expressiveness` |
| Emergent pair structure from Branch + 1-Inert (g as CONS not axiomatized) | Empirical | Structural analysis in `docs/forced_roles_theorem.md` | N/A |
| Distinctness axiom: 32 forced + 13 added, SAT at N=12 and N=16, compatible with both Ψ₁₆ᶠ and Ψ₁₆ᶜ | Empirical | `ds_search/distinctness_test.py` | `uv run python -m ds_search.distinctness_test` |
| Futamura projection 1: supercompile(interpreter, program) = supercompile(program) for all 10 test cases | Empirical | `examples/psi_futamura.psi` | `python3 psi_supercompile.py --table=c examples/psi_futamura.psi` |
| Futamura projection 2: specializer on tagged-pair IR eliminates interpreter | Empirical | `examples/psi_specialize.lisp` | `python3 psi_lisp.py --table=c examples/psi_specialize.lisp` |
| Futamura projection 3: self-hosted transpiler fixed point (compiled = interpreted output) | Empirical | `examples/psi_transpile.lisp` + `psi_transpile.py` | `python3 psi_lisp.py --table=c examples/psi_transpile_test.lisp` |
| Self-hosted transpiler: Ψ-Lisp → Rust (6 expression types, INC/INV/DEC specialization) | Empirical | `examples/psi_transpile.lisp` + `psi_runtime.rs` | See `docs/technical_overview.md` §6 |
| Psi16C satisfies all listed operations (table, roles, QE, branch, INC/DEC/INV) | Lean-proved | `DistinctionStructures/Psi16C.lean` | `lake build` |
| Psi16C cancellation laws (INC∘DEC, DEC∘INC, INV∘INV on core) | Lean-proved | `DistinctionStructures/Psi16C.lean` | `lake build` |
| Psi16C rigidity (fingerprint uniqueness, row injectivity) | Lean-proved | `DistinctionStructures/Psi16C.lean` | `lake build` |
| Psi16C constructibility ({⊤,⊥,Q,E} generates all 16 in ≤4 steps) | Lean-proved | `DistinctionStructures/Psi16C.lean` | `lake build` |
| Cancellation rule soundness: INC/DEC/QE restricted to verified element domain (exhaustive 16-element check) | Empirical | `psi_supercompile.py` — counterexample: INC(DEC(12))=13≠12 | N/A |
| Ψ-Lisp → C/Rust transpiler: compiled output matches interpreter on fibonacci + recursion | Empirical | `psi_transpile.py --target c\|rust` | `python3 psi_transpile.py --target rust examples/psi_fibonacci.lisp > /tmp/fib.rs && cp psi_runtime.rs /tmp/ && rustc -O -o /tmp/fib /tmp/fib.rs && /tmp/fib` |
| MMTk GC stress test: 10M cons cells in 4MB heap (MarkSweep + shadow stack roots) | Empirical | `kamea-rs/crates/wispy-gc/` + `wispy-stress/` | `cd kamea-rs && HEAP_MB=4 cargo run -p wispy-stress --release` |
| 3 categories universal (absorbers, classifiers, transformers from all 4+ axiom systems) | Empirical | `ds_search/alternative_axioms.py`, `ds_search/categorical_topos.py` | `uv run python -m ds_search.alternative_axioms` |
| Kleene wall universal (classifiers ≠ transformers in all systems) | Empirical | `ds_search/alternative_axioms.py`, `ds_search/categorical_topos.py` | `uv run python -m ds_search.categorical_topos` |
| Rigidity emerges from categorical axioms (50/50 models, no rigidity axiom) | Empirical | `ds_search/categorical_topos.py` | `uv run python -m ds_search.categorical_topos` |
| Discoverability emerges from categorical axioms (49/50 models) | Empirical | `ds_search/categorical_topos.py` | `uv run python -m ds_search.categorical_topos` |
| Substrate existence selected by expressiveness (inert=0 degenerate: 1/10 discoverable) | Empirical | `ds_search/inert_expressiveness.py` | `uv run python -m ds_search.inert_expressiveness` |
| Substrate uniqueness NOT selected by expressiveness (inert=1 ties inert=2) | Empirical | `ds_search/inert_expressiveness.py` | `uv run python -m ds_search.inert_expressiveness` |
| g=CONS forced by Branch+Compose (100% of 1-inert Ψ models; 0% of categorical-only models) | Empirical | `ds_search/inert_expressiveness.py` | `uv run python -m ds_search.inert_expressiveness` |
| 3 redundant axioms identified (InertProp, VV, 1-Inert implied by remaining 8) | Empirical | `ds_search/axiom_archaeology_deep.py` | `uv run python -c "from ds_search.axiom_archaeology_deep import axiom_dependencies; axiom_dependencies()"` |
| Minimal non-associative encoder pair: {ρ, η} | Empirical | `ds_search/axiom_archaeology_deep.py`; 14/15 pairs SAT, {ρ,η} UNSAT | `uv run python -m ds_search.axiom_archaeology` |
| Distinctness decomposition: 32/45 pairs forced by categorical axioms, 3/45 forced by TC (lazy/eager + projection uniqueness), 10/45 are standard algebraic practice | Empirical | `ds_search/forced_roles_test.py` (32 categorical), `ds_search/tc_distinctness_test.py` (3 TC), `ds_search/tc_distinctness_deep.py` (E=f artifact) | `uv run python -m ds_search.tc_distinctness_test && uv run python -m ds_search.tc_distinctness_deep` |
| Three-category decomposition (zero / classifier / non-classifier) | Lean-proved | `DistinctionStructures/CatKleeneWallMinimal.lean` — algebraic proof, no `decide` | `lake build` |
| Kleene wall: classifier ∩ non-classifier = ∅ | Lean-proved | `DistinctionStructures/CatKleeneWallMinimal.lean` — algebraic proof, no `decide` | `lake build` |
| No right identity (any KleeneMagma) | Lean-proved | `DistinctionStructures/CatKleeneWallMinimal.lean` — algebraic proof, no `decide` | `lake build` |
| Card ≥ 4 (any KleeneMagma) | Lean-proved | `DistinctionStructures/CatKleeneWallMinimal.lean` — algebraic proof, no `decide` | `lake build` |
| Retraction pair ∈ non-classifier class | Lean-proved | `DistinctionStructures/CatKleeneWallMinimal.lean` — algebraic proof, no `decide` | `lake build` |
| Minimal KleeneMagma witness: N=4 (sec=ret), N=5 (sec≠ret, tight) | Lean-proved | `DistinctionStructures/CatKleeneWallMinimal.lean` — witnesses by `decide` | `lake build` |
| Card ≥ 5 when sec ≠ ret (tight) | Lean-proved | `DistinctionStructures/CatKleeneWallMinimal.lean` — algebraic proof | `lake build` |
| 32/45 role pairs forced distinct (16-element witness) | Lean-proved | `DistinctionStructures/CatForcedDistinctness.lean` — `native_decide` | `lake build` |
| Rigidity of 16-element categorical witness | Lean-proved | `DistinctionStructures/CatRigidity.lean` — via table equivalence | `lake build` |
| Discoverability of 16-element categorical witness | Lean-proved | `DistinctionStructures/CatDiscoverable.lean` — `native_decide` | `lake build` |
| Actuality irreducibility (categorical twin-model) | Lean-proved | `DistinctionStructures/CatActualityIrreducibility.lean` — `native_decide` | `lake build` |
| Four roles are minimal in general | Conjecture/Open | Discussed as open in docs | N/A |
| Symmetric discoverability impossibility (fully general theorem) | Conjecture/Open | Demonstrated for constructions, not fully formalized | N/A |

## Scope Notes

- Statements labeled `Empirical` are evidence-backed but may change with stronger tests or alternative implementations.
- Any top-level claim added to `README.md` should map to one row in this file.

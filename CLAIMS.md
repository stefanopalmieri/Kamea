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
| Abstract schema theorem: any `FourLiftSchema` has unique lift witnesses and unique minimal card-4 covering basis | Lean-proved | `Kamea/OntologicalSchema.lean` | `lake build` |
| Base DirectedDS axioms (`A2`,`A5`,`Ext`) imply only `card >= 2`, and this bound is tight (2-element countermodel) | Lean-proved | `Kamea/BaseAxiomDerivation.lean` | `lake build` |
| Base DirectedDS + generic directed novelty (`DirectedA7Prime`) still does not force `card >= 17` (3-element countermodel exists) | Lean-proved | `Kamea/BasePlusA7Derivation.lean` | `lake build` |
| Psi16 satisfies all structural + computational axioms (L0-L8, C, D, PA, VV, QE, 1-inert, E-trans, Branch, Compose, Y, Selection, IO, 8-state counter) | Lean-proved | `Kamea/Psi16.lean` (42 theorems) | `lake build` |
| Psi16-full satisfies all axioms plus DEC, PAIR/FST/SND, INC2, SWAP (full operational saturation) | Lean-proved | `Kamea/Psi16Full.lean` (83 theorems) | `lake build` |
| Psi16 is WL-1 discrete (rigid) and fully producible; {top,bot,Q,E} generates all 16 in <=4 steps | Lean-proved | `Kamea/Psi16.lean` | `lake build` |
| Psi16-full is WL-1 discrete (rigid) and fully producible; {top,bot,Q,E} generates all 16 in <=4 steps | Lean-proved | `Kamea/Psi16Full.lean` | `lake build` |
| Psi16 automorphism rigidity: every injective endomorphism is the identity (Aut = {id}) | Lean-proved | `Kamea/Psi16Rigidity.lean` | `lake build` |
| Psi16 discoverability: all 16 elements behaviorally identifiable; 4 probes suffice (injective fingerprint) | Lean-proved | `Kamea/Psi16Discoverable.lean` | `lake build` |
| Psi16 actuality irreducibility: twin 17-element models agree on all structure but disagree on tester assignment | Lean-proved | `Kamea/Psi16ActualityIrreducibility.lean` | `lake build` |
| Full axiom set is SAT at N=16 (all phases including IO + 8-state counter + selection + DEC/PAIR/INC2/SWAP) | Empirical | `ds_search/stacking_analysis.py` (`extract_psi16_full()`) | `uv run python -c "from ds_search.stacking_analysis import extract_psi16_full; extract_psi16_full()"` |
| Full axiom set is SAT at N=12 with 117/144 free cells (18.8% determination) | Empirical | `ds_search/stacking_analysis.py` (`etrans_residual_freedom()`) | `uv run python -c "from ds_search.stacking_analysis import etrans_residual_freedom; etrans_residual_freedom()"` |
| QE requires N>=8; Branch/Compose/Y require N>=12 | Empirical | `ds_search/stacking_analysis.py` | SAT/UNSAT checks at various N |
| WL census: structureless rigid magmas often efficiently recoverable | Empirical | `ds_search/rigid_census.py`, `ds_search/counterexample_search.py` | `uv run python ds_search/rigid_census.py` |
| Actuality irreducibility: tester row is completely free (all core tester cells can independently flip) | Empirical | `ds_search/stacking_analysis.py`, `ds_search/n16_freedom.py` | SAT-verified with push/pop at N=8, 12, 16 |
| Full axiom set at N=16: 64/256 cells fixed (25.0% determination), 192 free | Empirical | `ds_search/n16_freedom.py` | `uv run python ds_search/n16_freedom.py` |
| Chirality: E-transparency does not cascade to tester cells | Empirical | `ds_search/stacking_analysis.py` | SAT push/pop: all tester-cell values remain SAT |
| No right identity in any PsiStructure (L0–L3 role axioms) | Lean-proved | `Kamea/PsiUniversalBounds.lean` | `lake build` |
| Card ≥ 4 from role axioms (L0–L3), tight (4-element countermodel) | Lean-proved | `Kamea/PsiUniversalBounds.lean`, `Kamea/PsiCountermodels.lean` | `lake build` |
| No full associativity under full axiom set | Empirical | `ds_search/stacking_analysis.py` | UNSAT; no associative sub-magma of size ≥ 4 |
| Encoder-tester non-commutativity | Empirical | `ds_search/stacking_analysis.py` | SAT-verified |
| Black-box recovery: all 16 elements recoverable from shuffled oracle (3 methods, 100% on 1000 seeds) | Empirical | `psi_blackbox.py` | `uv run python psi_blackbox.py --seeds 1000 --compare` |
| Ψ∗ Turing-completeness: 7 axiom-forced elements (⊤, Q, E, f, g, η, ρ) simulate 2-counter machines; universal across all models | Empirical | `psi_star.py` — stepped 2CM matches reference interpreter on 4 test programs | `uv run python psi_star.py` |
| 1-bit logic (AND/OR/XOR): curried dispatch on {s0,s1} embeds all three Boolean gates simultaneously; model stays WL-1 rigid | Empirical | SAT-verified at N=16 with full axiom set + all operational constraints | `ds_search/n16_freedom.py` build_solver + XOR/AND/OR constraints |
| Five behavioral categories forced (32/45 role pairs UNSAT, min 5 elements) | Empirical | `ds_search/forced_roles_test.py` — role-aliasing at N=12; `docs/forced_roles.md` | `uv run python -m ds_search.forced_roles_test` |
| Classifier wall: τ cannot merge with any encoder or inert role (9/9 pairs UNSAT) | Empirical | `ds_search/forced_roles_test.py` | `uv run python -m ds_search.forced_roles_test --quick` |
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
| Psi16C satisfies all listed operations (table, roles, QE, branch, INC/DEC/INV) | Lean-proved | `Kamea/Psi16C.lean` | `lake build` |
| Psi16C cancellation laws (INC∘DEC, DEC∘INC, INV∘INV on core) | Lean-proved | `Kamea/Psi16C.lean` | `lake build` |
| Psi16C rigidity (fingerprint uniqueness, row injectivity) | Lean-proved | `Kamea/Psi16C.lean` | `lake build` |
| Psi16C constructibility ({⊤,⊥,Q,E} generates all 16 in ≤4 steps) | Lean-proved | `Kamea/Psi16C.lean` | `lake build` |
| Cancellation rule soundness: INC/DEC/QE restricted to verified element domain (exhaustive 16-element check) | Empirical | `psi_supercompile.py` — counterexample: INC(DEC(12))=13≠12 | N/A |
| Ψ-Lisp → C/Rust transpiler: compiled output matches interpreter on fibonacci + recursion | Empirical | `psi_transpile.py --target c\|rust` | `python3 psi_transpile.py --target rust examples/psi_fibonacci.lisp > /tmp/fib.rs && cp psi_runtime.rs /tmp/ && rustc -O -o /tmp/fib /tmp/fib.rs && /tmp/fib` |
| MMTk GC stress test: 10M cons cells in 4MB heap (MarkSweep + shadow stack roots) | Empirical | `kamea-rs/crates/wispy-gc/` + `wispy-stress/` | `cd kamea-rs && HEAP_MB=4 cargo run -p wispy-stress --release` |
| 3 categories universal (absorbers, classifiers, transformers from all 4+ axiom systems) | Empirical | `ds_search/alternative_axioms.py`, `ds_search/categorical_topos.py` | `uv run python -m ds_search.alternative_axioms` |
| Classifier wall universal (classifiers ≠ transformers in all systems) | Empirical | `ds_search/alternative_axioms.py`, `ds_search/categorical_topos.py` | `uv run python -m ds_search.categorical_topos` |
| Rigidity emerges from categorical axioms (50/50 models, no rigidity axiom) | Empirical | `ds_search/categorical_topos.py` | `uv run python -m ds_search.categorical_topos` |
| Discoverability emerges from categorical axioms (49/50 models) | Empirical | `ds_search/categorical_topos.py` | `uv run python -m ds_search.categorical_topos` |
| Substrate existence selected by expressiveness (inert=0 degenerate: 1/10 discoverable) | Empirical | `ds_search/inert_expressiveness.py` | `uv run python -m ds_search.inert_expressiveness` |
| Substrate uniqueness NOT selected by expressiveness (inert=1 ties inert=2) | Empirical | `ds_search/inert_expressiveness.py` | `uv run python -m ds_search.inert_expressiveness` |
| g=CONS forced by Branch+Compose (100% of 1-inert Ψ models; 0% of categorical-only models) | Empirical | `ds_search/inert_expressiveness.py` | `uv run python -m ds_search.inert_expressiveness` |
| 3 redundant axioms identified (InertProp, VV, 1-Inert implied by remaining 8) | Empirical | `ds_search/axiom_archaeology_deep.py` | `uv run python -c "from ds_search.axiom_archaeology_deep import axiom_dependencies; axiom_dependencies()"` |
| Minimal non-associative encoder pair: {ρ, η} | Empirical | `ds_search/axiom_archaeology_deep.py`; 14/15 pairs SAT, {ρ,η} UNSAT | `uv run python -m ds_search.axiom_archaeology` |
| Distinctness decomposition: 32/45 pairs forced by categorical axioms, 3/45 forced by TC (lazy/eager + projection uniqueness), 10/45 are standard algebraic practice | Empirical | `ds_search/forced_roles_test.py` (32 categorical), `ds_search/tc_distinctness_test.py` (3 TC), `ds_search/tc_distinctness_deep.py` (E=f artifact) | `uv run python -m ds_search.tc_distinctness_test && uv run python -m ds_search.tc_distinctness_deep` |
| Three-category decomposition (zero / classifier / non-classifier) | Lean-proved | `Kamea/CatKripkeWallMinimal.lean` — algebraic proof, no `decide` | `lake build` |
| Classifier wall: classifier ∩ non-classifier = ∅ | Lean-proved | `Kamea/CatKripkeWallMinimal.lean` — algebraic proof, no `decide` | `lake build` |
| No right identity (any DichotomicRetractMagma) | Lean-proved | `Kamea/CatKripkeWallMinimal.lean` — algebraic proof, no `decide` | `lake build` |
| Card ≥ 4 (any DichotomicRetractMagma) | Lean-proved | `Kamea/CatKripkeWallMinimal.lean` — algebraic proof, no `decide` | `lake build` |
| Retraction pair ∈ non-classifier class | Lean-proved | `Kamea/CatKripkeWallMinimal.lean` — algebraic proof, no `decide` | `lake build` |
| Minimal DichotomicRetractMagma witness: N=4 (sec=ret), N=5 (sec≠ret, tight) | Lean-proved | `Kamea/CatKripkeWallMinimal.lean` — witnesses by `decide` | `lake build` |
| Card ≥ 5 when sec ≠ ret (tight) | Lean-proved | `Kamea/CatKripkeWallMinimal.lean` — algebraic proof | `lake build` |
| 32/45 role pairs forced distinct (16-element witness) | Lean-proved | `Kamea/CatForcedDistinctness.lean` — `native_decide` | `lake build` |
| Rigidity of 16-element categorical witness | Lean-proved | `Kamea/CatRigidity.lean` — via table equivalence | `lake build` |
| Discoverability of 16-element categorical witness | Lean-proved | `Kamea/CatDiscoverable.lean` — `native_decide` | `lake build` |
| Actuality irreducibility (categorical twin-model) | Lean-proved | `Kamea/CatActualityIrreducibility.lean` — `native_decide` | `lake build` |
| No commutative magma admits two distinct left-absorbers (asymmetry theorem) | Lean-proved | `Kamea/NoCommutativity.lean` — 3-line algebraic proof, no `decide` | `lake build` |
| Asymmetry extends to FaithfulRetractMagma and DichotomicRetractMagma | Lean-proved | `Kamea/NoCommutativity.lean` — immediate corollaries | `lake build` |
| Composition closure (10 roles form sub-magma) compatible but kills 0/10 expressiveness pairs | Empirical | `ds_search/composition_closure_test.py` | `uv run python -m ds_search.composition_closure_test` |
| Tighter closure variants (6-element computational core, 8-element non-zeros, one-sided) all UNSAT | Empirical | `ds_search/composition_closure_test.py` | `uv run python -m ds_search.composition_closure_test` |
| Reflection distinctness: 0/10 nontriviality pairs killed by full reflective tower | Empirical | `ds_search/reflection_distinctness_test.py` | `uv run python -m ds_search.reflection_distinctness_test` |
| 10 nontriviality pairs exhaustively characterized (categorical + TC + closure + reflection all tested) | Empirical | `ds_search/tc_distinctness_test.py`, `reflection_distinctness_test.py`, `composition_closure_test.py` | See individual scripts |
| 112 non-isomorphic DichotomicRetractMagmas at N=4 (minimal model not unique) | Empirical | `ds_search/kripke_canonicity.py` | `uv run python -m ds_search.kripke_canonicity` |
| 0 homomorphisms from N=4/5 Lean witnesses to Ψ₁₆ᶠ (weak or strict) | Empirical | `ds_search/kripke_canonicity.py` | `uv run python -m ds_search.kripke_canonicity` |
| Three-class decomposition (Z, C, N) is functorial invariant of all DichotomicRetractMagma models | Lean-proved | `Kamea/CatKripkeWallMinimal.lean` — `three_categories`; `Kamea/Functoriality.lean` — `DRMIso.preserves_decomposition` (DRM isos preserve Z, C, N; algebraic proof, no `decide`) | `lake build` |
| No initial object in category DRMag | Empirical | `ds_search/kripke_canonicity.py` — 112 iso classes + 0 homomorphisms | `uv run python -m ds_search.kripke_canonicity` |
| Compiled reflective tower: 2.2 ms native, ~20,000x over interpreted (meta-circular evaluator + continuation reification + branch swap in single binary) | Empirical | `psi_transpile.py --target rust` on metacircular + tower | `python3 psi_transpile.py --target rust examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp > /tmp/tower.rs && cp psi_runtime_f.rs /tmp/ && rustc -O -o /tmp/tower /tmp/tower.rs && /tmp/tower` |
| Transpiler handles metaprograms: quoted symbol encoding, cons-cell data construction, arena threading | Empirical | Compiled tower produces identical output to interpreted tower | `diff <(python3 psi_lisp.py examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp 2>/dev/null) <(/tmp/tower)` |
| Partial application injectivity: self-simulation + extensionality + compositionality ⇒ `a ↦ eval(App(t, rep(a)))` injective | Lean-proved | `Kamea/SelfSimulation.lean` — algebraic proof, no `decide` | `lake build` |
| Partial application distinctness: distinct elements ⇒ distinct intermediate terms | Lean-proved | `Kamea/SelfSimulation.lean` — contrapositive of injectivity | `lake build` |
| Encoding injectivity: self-simulation ⇒ Q-depth encoding is injective | Lean-proved | `Kamea/SelfSimulation.lean` — corollary of injectivity | `lake build` |
| Row determination: equal partial applications ⇒ identical rows | Lean-proved | `Kamea/SelfSimulation.lean` — algebraic proof, no `decide` | `lake build` |
| Self-simulation possible: brute-force simulator computes all 256 cells | Empirical | `examples/psi_self_simulator.lisp`, `self_simulation_investigation.py` | `python3 self_simulation_investigation.py` |
| Role-aware simulator: 60/256 cells (23.4%) from algebraic rules, all 7 TC elements referenced | Empirical | `examples/psi_self_simulator.lisp`, `self_simulation_investigation.py` | `python3 self_simulation_investigation.py` |
| Discrimination derived from self-simulation (Q-depth decoding requires binary test) | Empirical + Argument | `docs/self_simulation_necessity.md` — Phase 3 Step 1 | `python3 self_simulation_investigation.py` |
| Branching derived from self-simulation (dispatch requires conditionals) | Empirical + Argument | `docs/self_simulation_necessity.md` — Phase 3 Step 2 | `python3 self_simulation_investigation.py` |
| Y-combinator derived from universal self-simulation (unbounded Q-depth requires recursion) | Argument | `docs/self_simulation_necessity.md` — Phase 3 Step 4 | N/A |
| Compose independent of self-simulation (SAT counterexample at N=10) | Empirical | `self_simulation_investigation.py` — Test D | `python3 self_simulation_investigation.py` |
| Inert independent of self-simulation (SAT counterexample at N=10) | Empirical | `self_simulation_investigation.py` — Test E | `python3 self_simulation_investigation.py` |
| Classifier dichotomy independent of self-simulation: N=8 non-dichotomic retraction magma self-simulates (64/64 cells) | Empirical | `self_simulation_investigation.py` — Test B + universal self-simulator | `python3 self_simulation_investigation.py` |
| Universal self-simulator: one program computes dot(a,b) for any Ψ model (verified on Ψ₁₆ᶠ and Ψ₁₆ᶜ) | Empirical | `universal_self_simulator.py` | `python3 universal_self_simulator.py` |
| Self-simulation is a property of the theory, not any model (same code, different tables, both pass) | Empirical | `universal_self_simulator.py` — both Ψ₁₆ᶠ and Ψ₁₆ᶜ | `python3 universal_self_simulator.py` |
| Machine boundary: instruction set (classifier, branch, Y) derived; machine (compose, inert) chosen | Argument | `docs/self_simulation_necessity.md` | N/A |
| Four roles are minimal in general | Conjecture/Open | Discussed as open in docs | N/A |

### Capability Independence (S, D, H)

The three capabilities — self-representation (S), self-description (D), self-execution (H) — are fully independent. No capability implies any other. All counterexamples are generated, independently verified, and frozen in `counterexamples.json`.

| Claim | Tier | Primary Evidence | Reproduce |
|---|---|---|---|
| S ⊬ D: N=8 FRM self-simulates (retraction pair), violates Classifier dichotomy (2 mixed elements) | Lean-proved | `Kamea/Countermodel.lean` — `countermodel8_violates_dichotomy`, `frm_independent_of_dichotomy` | `lake build Kamea.Countermodel` |
| D ⊬ H (Compose): N=10 DRM satisfies classifier dichotomy, no element satisfies Compose axiom | Lean-proved | `Kamea/Countermodels10.lean` — `dNotH` (DRM instance) + `dNotH_no_compose` | `lake build Kamea.Countermodels10` |
| D ⊬ H (Inert): N=10 DRM satisfies classifier dichotomy, no inert element exists (all non-absorbers are testers or encoders) | Empirical | `independence_results.py` — D_not_H_inert | `python3 independence_results.py` |
| H ⊬ D (diagonal): N=10 FRM has Branch+Compose+Y (all H machinery), violates classifier dichotomy (4 mixed elements) | Lean-proved | `Kamea/Countermodels10.lean` — `hNotD` (FRM) + `hNotD_branch/compose/y_fixpoint` + `hNotD_violates_dichotomy` | `lake build Kamea.Countermodels10` |
| **S+D+H coexist at N=5 (optimal)**. ICP needs 3 pairwise distinct core elements, so N ≥ 5. N=5 witness: sec=ret=2, cls=3, ICP a=3,b=2,c=4. | Lean-proved | `Kamea/Witness5.lean` — `sdh_witness_5`, `no_icp_at_4` | `lake build Kamea.Witness5` |
| S+D+H coexist at N=6 with sec ≠ ret (non-degenerate retraction). | Lean-proved | `Kamea/Witness6.lean` — `sdh_witness_6` | `lake build Kamea.Witness6` |
| S+D+H coexist at N=10 with all 10 roles distinct. | Lean-proved | `Kamea/Witness10.lean` — `witness10_drm` + `sdh_witness_10` | `lake build Kamea.Witness10` |
| N=5 witness self-simulates (sim term = classifier). | Lean-proved | `Kamea/SelfSim5.lean` — `witness5_self_simulates` | `lake build Kamea.SelfSim5` |
| N=6 witness self-simulates (sim term = retraction element). | Lean-proved | `Kamea/SelfSim6.lean` — `witness6_self_simulates` | `lake build Kamea.SelfSim6` |
| D ⊬ S: N=5 E2PM with dichotomy but no retraction pair. | Lean-proved | `Kamea/E2PM.lean` — `d_not_implies_s` | `lake build Kamea.E2PM` |
| H ⊬ S: N=6 E2PM with ICP but no retraction pair. | Lean-proved | `Kamea/E2PM.lean` — `h_not_implies_s` | `lake build Kamea.E2PM` |
| S ⊬ H (structural): N=6 E2PM with retraction pair, 4 core elements, no ICP. | Lean-proved | `Kamea/E2PM.lean` — `s_not_implies_icp_structural` | `lake build Kamea.E2PM` |
| Full axiom stack (capabilities + organizational ladder) requires N=12 | Empirical | `minimal_sdh_test.py`, `ds_search/stacking_analysis.py` | `python3 minimal_sdh_test.py` |
| Classifier wall is epistemic, not computational: H machinery does not force D | Empirical | `independence_results.py` — H_not_D counterexample | `python3 independence_results.py` |
| Counterexample tables frozen and independently verified (all properties checked without Z3) | Empirical | `counterexamples.json`, `independence_results.py` verification functions | `python3 independence_results.py` |
| Partial minimality: each capability's axiom set is irredundant (no axiom derivable from the others) | Empirical | `axiom_irredundancy_test.py` — 5/5 SAT (E-trans, Branch, Compose, Inert, Y all irredundant) | `python3 axiom_irredundancy_test.py` |

## Scope Notes

- Statements labeled `Empirical` are evidence-backed but may change with stronger tests or alternative implementations.
- Any top-level claim added to `README.md` should map to one row in this file.
- Independence counterexamples are SAT-generated and independently verified (property checks run on the extracted table without Z3). Frozen tables in `counterexamples.json` allow re-verification without re-solving.
- The three capabilities (S, D, H) are fully independent — no capability implies any other. The Classifier dichotomy (D) is an epistemic axiom about role coherence, not a computational consequence of evaluation machinery (H).

Last updated: 2026-03-21

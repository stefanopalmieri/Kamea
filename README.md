# Distinction Structures

**A minimal self-modeling framework for relational description, with machine-checked proofs in Lean 4.**

---

## Three Theorems and Two Extensions

This repository contains Lean 4 formalizations of five results about finite algebraic structures that model themselves. All proofs compile with **zero `sorry`** on Lean 4.28.0 / Mathlib v4.28.0.

**Theorem 1 (Existence).** Intrinsically reflexive Distinction Structures exist. A 16-element symmetric algebra (Δ₀) and a 17-element directed algebra (Δ₁) each satisfy axioms A1--A7', Ext, and contain behavioral self-models: internal encodings whose elements, when composed by the structure's own operation, reproduce the behavior of the structure's own components.

**Theorem 2 (Discoverability).** Discoverably reflexive Distinction Structures exist. The 17-element directed model Δ₁ has a self-model that is recoverable from black-box probing alone, with each of the 8 recovery steps proved unique. An observer with no prior knowledge can identify every structural component purely from the operation table.

**Theorem 3 (Irreducibility).** Actuality is not determined by structure. Two models (Δ₁ and Δ₁') on the same 18-element carrier share 322 out of 324 operation table entries, both satisfy all axioms and reflexivity conditions, yet differ in actuality assignment. No structural predicate resolves the difference. The only way to determine which elements are actual is to query the actuality tester directly.

**Extension 1 (Δ₂ -- Flat Quoting).** Δ₁ extended with QUOTE, EVAL, APP, UNAPP restricted to flat (one-level) evaluation. The carrier is finite, the operation is total, and all properties are proved by `decide`. This is the Datalog-level extension: naming without executing, inspecting without reducing.

**Extension 2 (Δ₃ -- Recursive Evaluation).** Δ₂ extended with recursive EVAL via a fuel-bounded interpreter. Evaluating a quoted application node recursively evaluates both subterms, then applies the results. Proved in Lean using a combined eval/dot function structurally recursive on fuel. Concrete computations (flat eval, nested eval, triple nesting, QUOTE/EVAL roundtrips) verified by `native_decide`.

Five machine-checked results. Self-description is possible. Communication is possible. Computation is possible. But the question of what's real cannot be settled by structure alone.

---

## Why It Matters

Many systems can represent themselves (Godel numbering, quines, metacircular evaluators). Fewer do so *behaviorally* -- where the encoding elements don't just name components but act like them under the system's own operation. Fewer still are *discoverable* -- where an external observer can recover the self-model with no documentation.

Δ₁ achieves all three: self-representation, behavioral fidelity, and black-box recoverability. The recovery procedure is not a heuristic -- each step is a uniqueness lemma, machine-checked over the finite domain.

The irreducibility result shows what the framework *cannot* do. Given a complete structural description of a self-modeling system, the question "which elements are actual?" has multiple valid answers, and the structure alone does not select among them. Two fully valid self-modeling Distinction Structures can agree on every compositional fact and disagree only on actuality. The actuality tester carries irreducible information: there is no structural back door.

This is "existence is not a predicate" as a machine-checked theorem. Not as a philosophical argument, not as an interpretation, not as a slogan -- as a Lean theorem that compiles with zero sorry.

The extensions (Δ₂, Δ₃) show the path from algebra to computation: Δ₂ adds data representation (quoting without executing), Δ₃ adds recursive evaluation (executing quoted terms). Both are machine-verified. The boundary between finite decidable algebra and recursive interpretation is precisely located.

---

## Repository Structure

```
DistinctionStructures/
├── lakefile.lean                                # Build configuration
├── lean-toolchain                               # Lean version pin
├── DistinctionStructures/
│   ├── Basic.lean                               # Abstract DS definitions and axioms
│   ├── Delta0.lean                              # Δ₀: 16-element symmetric model
│   ├── Delta1.lean                              # Δ₁: 17-element directed model
│   ├── Discoverable.lean                        # 8 recovery lemmas (discoverability)
│   ├── ActualityIrreducibility.lean             # Actuality irreducibility theorem
│   ├── Delta2.lean                              # Δ₂: flat quoting (finite, decidable)
│   └── Delta3.lean                              # Δ₃: recursive eval (fuel-bounded)
├── delta2_true_blackbox.py                      # Δ₃ black-box recovery demo (Python)
├── ai_interpretability/                         # ML interpretability experiments
├── docs/
│   ├── Distinction_Structures.md                # Full document with proofs and philosophy
│   └── Distinction_Structures.docx              # Word format
└── README.md
```

## Building

```bash
# Requires Lean 4.28.0 and Mathlib v4.28.0
lake build
```

All theorems are checked by `decide` or `native_decide`, which is appropriate and complete for finite carrier types with decidable equality. The full project is ~1630 lines of Lean across 7 files. Zero sorry.

---

## The Five Results in Detail

### Theorem 1: Existence (Δ₀ and Δ₁)

| Property | Δ₀ (Symmetric) | Δ₁ (Directed) |
|----------|----------------|----------------|
| Elements in D(ι) | 14 (+ 2 in D(κ)) | 17 (+ 2 in D(κ)) |
| Operation | Σ : Finset D(ι) → D(ι) | · : D(ι) → D(ι) → D(ι) |
| Rules | Priority-based on Finset | 26 first-match rules |
| Self-model | 12 encoding elements | Encoding elements with H1--H3 |
| Reflexivity | Intrinsic | Discoverable |
| Lean files | `Delta0.lean` | `Delta1.lean` + `Discoverable.lean` |

Both models satisfy A1--A7', Ext, H1--H3, and IR1--IR5. The switch from symmetric to directed composition costs one additional element but unlocks discoverability.

### Theorem 2: Discoverability (Recovery Lemmas)

An observer with access only to the operation `dot : D → D → D` (no documentation, no labels) can recover every structural component of Δ₁:

| Step | What is recovered | Lean theorem |
|------|-------------------|-------------|
| 1 | Booleans (top, bot) -- the only left-absorbers | `boolean_uniqueness` |
| 2 | Testers (e_I, d_K, m_K, m_I) -- non-booleans with boolean-valued output | `tester_characterization` |
| 3 | Tester signatures by decoded-set size (16, 2, 2, 1) | `tester_card_m_I`, `tester_card_e_I`, `tester_card_d_K`, `tester_card_m_K` |
| 4 | Context tester vs domain tester -- rich vs inert decoded elements | `rich_context_tokens`, `inert_kappa_tokens` |
| 5 | e_D vs e_M -- encoder asymmetry | `encoder_pair`, `encoder_asymmetry` |
| 6 | i vs k -- context token discrimination | `context_token_discrimination` |
| 7 | p (non-actual element) -- unique m_I reject | `junk_identification` |
| 8 | e_Sigma, s_C, e_Delta -- unique triple with synthesis property | `triple_identification`, `triple_uniqueness` |

Each step has exactly one solution. The recovery is not heuristic -- it is mechanically verified.

### Theorem 3: Actuality Irreducibility

Two models, Δ₁ and Δ₁', are constructed on the same 18-element carrier (the 17 elements of Δ₁ plus a second surplus element q). They differ in exactly two entries of the 18x18 operation table -- both in the m_I row:

| | Δ₁ | Δ₁' |
|---|---|---|
| m_I · p | bot (rejects p) | top (accepts p) |
| m_I · q | top (accepts q) | bot (rejects q) |
| All other 322 entries | identical | identical |
| Actuality set | M = D \ {p} | M' = D \ {q} |

Both models independently satisfy Ext, H1--H3, IR1--IR4, A2, A5, A7'.

Key theorems in `ActualityIrreducibility.lean`:

| Theorem | What it proves |
|---------|---------------|
| `ops_agree_non_mI` | ∀ x y, x ≠ m_I → dot1 x y = dot1' x y |
| `ops_differ_only_mI` | The only disagreements are at (m_I, p) and (m_I, q) |
| `right_image_same_dot1` | ∀ x ≠ m_I, dot1 x p = dot1 x q |
| `cross_model_right_image` | ∀ x ≠ m_I, dot1 x p = dot1' x q |
| `mI_is_unique_discriminator` | m_I is the only element that classifies p and q differently |
| `no_universal_actuality_predicate` | No predicate matches actualM in Δ₁ and actualM' in Δ₁' |
| `actuality_irreducibility` | Combined 7-conjunct theorem |

### Extension 1: Δ₂ -- Flat Quoting

Δ₂ adds QUOTE, EVAL, APP, UNAPP to Δ₁'s 17 atoms (21 total). Evaluation is flat: EVAL on a quoted application node looks up Δ₁'s dot table once. No recursion, no unbounded terms. The carrier includes atoms, quoted atoms, application nodes, bundles, and partial applications -- all finite.

Key theorems in `Delta2.lean`:

| Theorem | What it proves |
|---------|---------------|
| `eval_quote_inverse` | ∀ x, EVAL · (QUOTE · x) = x |
| `unapp_app_roundtrip` | ∀ f x, UNAPP · (APP · f · x) = bundle(f, x) |
| `bundle_query_top/bot` | ∀ f x, bundle(f,x) · top = f, bundle(f,x) · bot = x |
| `eval_appnode` | ∀ f x : D1ι, EVAL · app(f,x) = dot(f,x) |
| `eval_app_computes` | ∀ f x : D1ι, EVAL · (APP · f · x) = dot(f,x) |
| `d1_fragment_preserved` | ∀ x y : D1ι, dot2(x,y) = dot(x,y) |
| `quoted_inert_d1` | ∀ d : D1ι, d · quoted(y) = p |

All proofs by `decide` over finite types.

### Extension 2: Δ₃ -- Recursive Evaluation

Δ₃ extends Δ₂ with recursive EVAL: evaluating a quoted application node recursively evaluates both subterms, then applies the results. This is the boundary between algebra and interpreter.

The mutual recursion between eval and dot is resolved via a fuel parameter: `interp (fuel : Nat) (mode : Bool) (a b : T3) → T3`, structurally recursive on fuel. For any finite term, sufficient fuel exists for complete evaluation.

Key theorems in `Delta3.lean`:

| Theorem | What it proves |
|---------|---------------|
| `eval_quote_all_atoms` | All 21 atoms roundtrip through QUOTE/EVAL |
| `flat_eval_eD_k` | eval(app(e_D, k)) = d_K |
| `flat_eval_eM_i` | eval(app(e_M, i)) = m_I |
| `flat_eval_eSigma_sC` | eval(app(e_Sigma, s_C)) = e_Delta |
| `nested_eval_mI` | eval(app(m_I, app(e_I, i))) = top (recursive!) |
| `eval_quoted_nested` | EVAL · quote(app(m_I, app(e_I, i))) = top |
| `triple_nesting` | eval(app(e_M, app(e_D, app(e_I, i)))) = p (3 levels) |
| `d1_preserved` | All 17x17 Δ₁ atom pairs compute correctly |
| `full_app_unapp_roundtrip` | APP → UNAPP → bundle query roundtrip |

All proofs by `native_decide` on concrete fuel values.

---

## The Progression

| Level | Elements | Operation | Key capability | Carrier | Lean file |
|-------|----------|-----------|---------------|---------|-----------|
| Δ₀ | 16 | Σ (symmetric) | Self-modeling | Finite | `Delta0.lean` |
| Δ₁ | 17 | · (directed) | Discoverable self-modeling | Finite | `Delta1.lean` |
| Δ₂ | 21 | · + QUOTE/EVAL | Flat quoting (name without executing) | Finite | `Delta2.lean` |
| Δ₃ | 21 | · + recursive EVAL | Recursive evaluation (execute nested terms) | Unbounded | `Delta3.lean` |

Each step adds exactly one capability. The formalizability boundary falls between Δ₂ (finite, fully decidable) and Δ₃ (unbounded terms, fuel-bounded proofs). Both are machine-verified.

---

## What Is Not Proved

- **Minimality.** We do not prove that 16 (resp. 17) is the minimum element count. The models are upper bound witnesses.
- **Symmetric impossibility.** The symmetric synthesis barrier is demonstrated by construction but not proved as a general impossibility theorem.
- **Categorical formalization.** The category-theoretic perspective is discussed in the document but not formalized in Lean.
- **Δ₃ termination.** The fuel parameter makes Δ₃ total, but we do not prove that for every finite term there exists sufficient fuel (this is true but requires a separate well-foundedness argument).

## Empirical Testing

The `delta2_true_blackbox.py` script implements the full Δ₃ interpreter in Python with true black-box recovery of all 21 elements across 1000 random permutations (all pass). The `ai_interpretability/` directory contains neural network experiments testing whether the recovery procedure transfers to learned approximations of the algebra.

## Background Document

The full mathematical and philosophical development is in [`docs/Distinction_Structures.md`](docs/Distinction_Structures.md). It covers the four concepts (Distinction, Context, Actuality, Synthesis), both existence proofs, the recovery procedure, the symmetric synthesis barrier, epistemological implications, and the path to computation.

## License

MIT

## Citation

If you use this work, please cite:

```
@software{distinction_structures_2026,
  author = {Stefano Palmieri},
  title = {Distinction Structures: A Minimal Self-Modeling Framework},
  year = {2026},
  note = {Lean 4 formalization, 0 sorry. Five machine-checked results: existence (Δ₀, Δ₁), discoverability (8 recovery lemmas), actuality irreducibility, flat quoting (Δ₂), and recursive evaluation (Δ₃).}
}
```

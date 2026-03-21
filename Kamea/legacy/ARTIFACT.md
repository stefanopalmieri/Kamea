# Artifact Guide

## What Is Proved and How

This document maps between the informal proofs in the main document and the Lean 4 formalizations, explains the proof methodology, and clarifies what is and is not mechanically verified.

---

## Proof Methodology

All theorems in this formalization are proved by **exhaustive finite computation** using Lean 4's `decide` and `native_decide` tactics. This is appropriate because:

1. **The carrier types are finite.** `D1ι` has 17 constructors; `Dι` has 14. Both derive `Fintype` and `DecidableEq`.
2. **The operations are total computable functions.** `dot` is defined by pattern matching with no recursion or partiality.
3. **All properties are decidable.** Universal quantification over finite types, existential quantification over finite types, and equality of elements in types with `DecidableEq` are all decidable.

When `decide` is used, Lean's kernel evaluates the proposition to `True` by checking every case. This is not "brute force" in the pejorative sense — it is the *correct and complete* proof method for decidable properties of finite structures. The finite model is small enough that computation terminates quickly.

### Why not "human-readable" proofs?

For a 17-element algebra, a human-readable proof of (say) Ext would require exhibiting 136 witness pairs (one for each pair of distinct elements). Writing these out adds length without adding insight. The `decide` tactic checks all 136 cases and certifies correctness. We include human-readable explanations in the main document for the *ideas* behind each result, and rely on mechanical verification for the *case analysis*.

One exception worth noting informally: the Ext fix for passive elements (Block E, Rules 20–25) is the most conceptually important repair in the construction. Without these rules, six elements (i, k, a, b, d_I, s_C) have identical left-behavior (all produce `p` for every right-argument via the default). The fix `x · ⊤ = x` gives each passive element a unique left-output, restoring behavioral separability at the cost of zero new elements.

---

## Theorem Map

### Delta0.lean — Symmetric Model Δ₀

| Lean theorem | Informal claim | Document section |
|-------------|---------------|-----------------|
| `ext_Dι` | Ext: ∀ x ≠ y ∈ D(ι), ∃ z, Σ({x,z}) ≠ Σ({y,z}) | §8, Axiom verification |
| `h1_iota` | Σ({e_D, e_ι}) = r_Dι | §8, IR3 |
| `h1_kappa` | Σ({e_D, e_κ}) = r_Dκ | §8, IR3 |
| `h2_iota` | Σ({e_M, e_ι}) = r_Mι | §8, IR3 |
| `h2_kappa` | Σ({e_M, e_κ}) = r_Mκ | §8, IR3 |
| `h3` | Σ({e_Σ, r_S}) = e_Δ | §8, IR3 |
| `ir1` | Encoders are pairwise distinct | §8, IR1 |
| `ir2` | All encoders ∈ M(ι) | §8, IR2 |
| `ir4` | Σ({e_𝐈, e_D, e_M, e_Σ}) = e_Δ | §8, IR4 |
| `ir5` | p, q ∉ range(ρ) | §8, IR5 |
| `a7'` | e_Δ has distinct interaction profile from components | §8, A7′ |

### Delta1.lean — Directed Model Δ₁

| Lean theorem | Informal claim | Document section |
|-------------|---------------|-----------------|
| `ext_D1ι` | Directed Ext: ∀ x ≠ y, ∃ z, x·z ≠ y·z | §23, Directed Ext |
| `h1_iota` | e_D · i = d_I | §25 |
| `h1_kappa` | e_D · k = d_K | §25 |
| `h2_iota` | e_M · i = m_I | §25 |
| `h2_kappa` | e_M · k = m_K | §25 |
| `h3` | e_Σ · s_C = e_Δ | §25 |
| `ir1` | Encoders pairwise distinct | §25 |
| `ir2` | All encoders ∈ M(ι) (none is p) | §25 |
| `ir4` | e_Σ · s_C = e_Δ and e_Δ ∉ component set | §25 |
| `ir5` | p not in encoding range | §25 |
| `a7'` | e_Δ · e_D = d_I, distinct from all component behaviors | §25 |
| `delta1_IR` | Complete DirectedIR structure witness | §25 |

### Discoverable.lean — Recovery Procedure

| Lean theorem | Recovery step | What it proves |
|-------------|--------------|---------------|
| `boolean_uniqueness` | Step 1 | ⊤ and ⊥ are the only left-absorbers: x·y = x for all y iff x ∈ {⊤, ⊥} |
| `tester_characterization` | Step 2 | e_I, d_K, m_K, m_I are the only non-booleans with Im_L ⊆ {⊤, ⊥} |
| `tester_cardinality_mI` | Step 3a | \|{y : m_I·y = ⊤}\| = 16 |
| `tester_cardinality_eI` | Step 3b | \|{y : e_I·y = ⊤}\| = 2 |
| `tester_cardinality_dK` | Step 3c | \|{y : d_K·y = ⊤}\| = 2 |
| `tester_cardinality_mK` | Step 3d | \|{y : m_K·y = ⊤}\| = 1 |
| `rich_vs_inert` | Step 4 | Dec(e_I) contains productive right-arguments; Dec(d_K) does not |
| `encoder_asymmetry` | Step 5 | e_M maps both context tokens to testers; e_D maps to a mixed pair |
| `context_token_discrimination` | Step 6 | \|Dec(m_I)\| = 16 ≠ 1 = \|Dec(m_K)\|, distinguishing i from k |
| `junk_identification` | Step 7 | p is the unique element with m_I·p = ⊥ |
| `triple_identification` | Step 8 | (e_Σ, s_C, e_Δ) is the unique triple with f·g = h and h·e_D = d_I |

---

## What Is Not Mechanically Verified

| Claim | Status | Why not formalized |
|-------|--------|-------------------|
| Symmetric synthesis barrier | Demonstrated by construction in document | Would require formalizing "for all possible boolean embeddings in symmetric Σ" — a universally quantified statement over all symmetric DS, not just one model |
| Categorical type separation | Discussed in document §12–13 | Requires topos-theoretic infrastructure not present in this development |
| Minimality (16 and 17 are optimal) | Not claimed | Would require proving nonexistence of smaller models — feasible in Lean but computationally expensive |
| Δ₂ properties | Python implementation only | Δ₂ involves recursive evaluation on unbounded terms, requiring different formalization techniques (partial functions, well-founded recursion) |
| Four-role necessity | Conjectured | Open problem; requires distinguishing behavioral self-modeling from syntactic self-reference |

---

## Reproducing the Results

### Lean formalization

```bash
# Install Lean 4.28.0 via elan
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Clone and build
git clone <repo-url>
cd Kamea
lake build

# Verify zero sorry
grep -r "sorry" Kamea/ && echo "FOUND SORRY" || echo "No sorry found"
```

Expected: clean build, no warnings, no sorry.

### Δ₂ interpreter

```bash
cd python
python delta2_interpreter.py
```

Expected output: recovery of all 21 atoms from shuffled labels, followed by correct execution of two example programs.

---

## Design Decisions

### Why `Finset` for Δ₀ but direct pattern matching for Δ₁?

Δ₀ uses symmetric synthesis (Σ operates on sets), so `Finset Dι → Dι` is the natural type. Δ₁ uses directed synthesis (binary operation), so `D1ι → D1ι → D1ι` with pattern matching is cleaner and more efficient for `decide`.

### Why derive `Fintype` and `DecidableEq`?

These instances are required for `decide` to work. `Fintype` tells Lean the type is finite (so universal quantifiers can be checked exhaustively). `DecidableEq` tells Lean equality is computable (so `≠` comparisons can be evaluated).

### Why are recovery lemmas in a separate file?

Separation of concerns: `Delta1.lean` establishes that the model exists and satisfies axioms. `Discoverable.lean` establishes that the model's self-encoding is recoverable. These are logically independent properties — a model could satisfy all axioms without being discoverable (Δ₀ is an example).

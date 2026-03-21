# Lean 4 Formalization of Distinction Structures

## Project Goal

Build a Lean 4 formalization that machine-checks the core results of "Distinction Structures: A Minimal Self-Modeling Framework for Relational Description." The proofs are constructive and finite, so most verification should be dischargeable by `decide` or `native_decide`. The goal is a clean, well-documented Lean project that a mathematician can clone, build, and verify.

## Project Structure

```
Kamea/
  lakefile.lean
  Kamea/
    Basic.lean            -- Abstract definition of Distinction Structures + axioms
    Delta0.lean           -- Δ₀ construction (16 elements, symmetric Σ) + intrinsic reflexivity proof
    Directed.lean         -- Directed DS definition (binary operation replacing set-based Σ)
    Delta1.lean           -- Δ₁ construction (17 elements, directed ·) + axiom verification
    Discoverable.lean     -- Recovery procedure: each step as a uniqueness lemma
    SymmetricBarrier.lean -- (Optional) The boolean contradiction in symmetric Σ
```

## What to Formalize

### Phase 1: Definitions (Basic.lean)

Define the abstract notion of a Distinction Structure. A DS is a quadruple ⟨𝐈, D, M, Σ⟩ where:
- 𝐈 is a nonempty collection of Contexts
- D assigns to each I ∈ 𝐈 a set of Distinctions D(I)  
- M assigns to each I ∈ 𝐈 a subset M(I) ⊆ D(I) of actual Distinctions
- Σ_I is a total function from finite nonempty subsets of D(I) to D(I)

Axioms to define as propositions:
- A1 (Existence): 𝐈 ≠ ∅
- A2 (Sustenance): ∀ I, M(I) ≠ ∅
- A3 (Containment): ∀ I, M(I) ⊆ D(I)
- A4 (Contextuality): ∀ I ≠ J, D(I) ∩ D(J) = ∅
- A5 (Selectivity): ∃ I, M(I) ⊊ D(I)
- A6 (Total Synthesis): Σ_I total on Fin*(D(I))
- A7′ (Structural Novelty): ∃ I, S ⊆ M(I) with |S| ≥ 2 such that δ* = Σ_I(S) ∉ S and ∃ t with Σ_I({δ*,t}) ≠ Σ_I({δ,t}) for all δ ∈ S
- Ext (Behavioral Separability): ∀ I, ∀ x ≠ x′ ∈ D(I), ∃ y with Σ_I({x,y}) ≠ Σ_I({x′,y})

Define intrinsic reflexivity conditions:
- IR1 (Presence): Component encoders e_𝐈, e_D, e_M, e_Σ are pairwise distinct
- IR2 (Actuality): All encoding elements ∈ M(ι)
- IR3 (Homomorphism): H1, H2, H3 hold (see below)
- IR4 (Closure): Σ_ι({e_𝐈, e_D, e_M, e_Σ}) = e_Δ with e_Δ ∉ {e_𝐈, e_D, e_M, e_Σ}
- IR5 (Non-exhaustion): ∃ elements in D(ι) not in range of encoding

Homomorphism conditions:
- H1: ∀ K ∈ 𝐈, Σ_ι({e_D, e_K}) = ρ(D(K))
- H2: ∀ K ∈ 𝐈, Σ_ι({e_M, e_K}) = ρ(M(K))
- H3: Σ_ι({e_Σ, ρ(S₀)}) = ρ(Δ) where S₀ is the component set

### Phase 2: Δ₀ Construction (Delta0.lean)

This is the main existence proof. Build a CONCRETE model.

**Contexts:** 𝐈 = {ι, κ} — define as an inductive type with two constructors.

**Distinctions in ι (14 elements):** Define as an inductive type:

```
inductive Dι where
  | e_I | e_D | e_M | e_Sigma  -- component encoders
  | e_iota | e_kappa            -- context encoders
  | r_Di | r_Dk | r_Mi | r_Mk  -- set encoders
  | e_Delta                     -- whole structure encoder
  | r_S                         -- component set encoder
  | p | q                       -- surplus (non-actual)
  deriving DecidableEq, Repr, Fintype
```

**Distinctions in κ (2 elements):**

```
inductive Dk where
  | alpha | beta
  deriving DecidableEq, Repr, Fintype
```

**Actuality:** M(ι) = all of Dι except p and q. M(κ) = {alpha}.

**Synthesis Σ_ι** operates on `Finset Dι → Dι` with these priority rules:

| # | Input | Output | Purpose |
|---|-------|--------|---------|
| 1 | {x} (singleton) | x | Identity |
| 2 | {e_D, e_iota} | r_Di | H1 for ι |
| 3 | {e_D, e_kappa} | r_Dk | H1 for κ |
| 4 | {e_M, e_iota} | r_Mi | H2 for ι |
| 5 | {e_M, e_kappa} | r_Mk | H2 for κ |
| 6 | {e_Sigma, r_S} | e_Delta | H3 |
| 7 | {e_I, e_D, e_M, e_Sigma} | e_Delta | IR4 |
| 8 | {e_Delta, e_D} | r_Di | A7′ witness |
| 9 | {x, q} for non-special x | x | Ext discriminator |
| 10 | all other S | p | Default |

IMPORTANT: Rule 9 means Σ_ι({x, q}) = x for any x where {x, q} isn't already caught by rules 2–8. This is what makes Ext work: for any a ≠ b, Σ({a,q}) = a ≠ b = Σ({b,q}).

For Σ_ι, the cleanest Lean approach is probably to define it as a function on Finset Dι, pattern-matching on the set contents. Since the domain is finite (14 elements), Finset Dι is finite and everything is decidable. You may want to represent Σ as a function and verify properties computationally.

**Σ_κ:** {alpha} ↦ alpha, {beta} ↦ beta, {alpha, beta} ↦ alpha.

**What to prove:**

1. A1–A6 satisfaction (should be trivial/computational)
2. A7′: with S = {e_I, e_D, e_M, e_Sigma}, δ* = Σ(S) = e_Delta.
   - N1: e_Delta ∉ S
   - N2: test t = e_D: Σ({e_Delta, e_D}) = r_Di, but Σ({e_I, e_D}) = p, Σ({e_D, e_D}) = e_D, Σ({e_M, e_D}) = p, Σ({e_Sigma, e_D}) = p. All differ from r_Di.
3. Ext: ∀ a b, a ≠ b → ∃ y, Σ({a,y}) ≠ Σ({b,y}). Witness: y = q for all pairs.
4. H1: Σ({e_D, e_iota}) = r_Di and Σ({e_D, e_kappa}) = r_Dk
5. H2: Σ({e_M, e_iota}) = r_Mi and Σ({e_M, e_kappa}) = r_Mk
6. H3: Σ({e_Sigma, r_S}) = e_Delta
7. IR1–IR5

Most of these should be provable by `decide` or `native_decide` once the types have `DecidableEq` and `Fintype` instances.

### Phase 3: Directed DS and Δ₁ (Directed.lean + Delta1.lean)

A directed DS replaces set-based Σ with a binary operation: `· : D(I) → D(I) → D(I)`.

**Δ₁ has 17 elements in D(ι):**

```
inductive D1ι where
  | top | bot                        -- booleans
  | i | k                           -- context tokens
  | a | b                           -- κ-element encodings
  | e_I                             -- context tester
  | e_D | e_M | e_Sigma | e_Delta  -- structural encoders
  | d_I | d_K                       -- domain codes
  | m_I | m_K                       -- actuality codes
  | s_C                             -- component-set token
  | p                               -- surplus/default
  deriving DecidableEq, Repr, Fintype
```

**The operation `dot : D1ι → D1ι → D1ι`** is defined by first-match on 26 rules:

Block A — Boolean absorption:
  1. top · y = top (for all y)
  2. bot · y = bot (for all y)

Block B — Testers (boolean-valued):
  3. e_I · i = top
  4. e_I · k = top
  5. e_I · y = bot (for all other y)
  6. d_K · a = top
  7. d_K · b = top
  8. d_K · y = bot (for all other y)
  9. m_K · a = top
  10. m_K · y = bot (for y ≠ a)
  11. m_I · p = bot
  12. m_I · y = top (for y ≠ p)

Block C — Structural encoders:
  13. e_D · i = d_I
  14. e_D · k = d_K
  15. e_M · i = m_I
  16. e_M · k = m_K
  17. e_Sigma · s_C = e_Delta
  18. e_Delta · e_D = d_I

Block D — Absorption breaker:
  19. p · top = top

Block E — Passive self-identification (Ext fix):
  20. i · top = i
  21. k · top = k
  22. a · top = a
  23. b · top = b
  24. d_I · top = d_I
  25. s_C · top = s_C

Block F — Default:
  26. x · y = p (all remaining pairs)

In Lean, define this as a function with pattern matching. The 17-element type is finite, so `match x, y with` covering all 17×17 = 289 pairs (most fall through to default) is feasible. You only need to explicitly list the ~25 non-default cases.

**Actuality:** M(ι) = everything except p. M(κ) = {alpha}.

**What to prove:**

1. All axioms (A1–A6, adapted A7′, directed Ext)
2. Directed Ext: ∀ x y, x ≠ y → ∃ z, dot x z ≠ dot y z
   - This should be decidable by exhaustive search over the finite type
3. Homomorphism conditions:
   - H1: dot e_D i = d_I, dot e_D k = d_K
   - H2: dot e_M i = m_I, dot e_M k = m_K
   - H3: dot e_Sigma s_C = e_Delta
4. IR2: all encoding elements are in M(ι) (i.e., none of them is p)
5. IR5: p is not in the range of the encoding

### Phase 4: Recovery Procedure (Discoverable.lean)

This is the most novel part. Each step of the recovery should be a lemma:

**Lemma 1 (Boolean uniqueness):** top and bot are the only elements x with the property that dot x y = x for all y.
```
∀ x : D1ι, (∀ y, dot x y = x) ↔ (x = top ∨ x = bot)
```

**Lemma 2 (Tester characterization):** e_I, d_K, m_K, m_I are the only non-boolean elements whose left-image is contained in {top, bot}.
```
∀ x : D1ι, x ≠ top → x ≠ bot → 
  (∀ y, dot x y = top ∨ dot x y = bot) ↔ (x = e_I ∨ x = d_K ∨ x = m_K ∨ x = m_I)
```

**Lemma 3 (Tester cardinality signatures):** The testers have distinct decoded-set sizes.
- |{y | dot m_I y = top}| = 16
- |{y | dot e_I y = top}| = 2
- |{y | dot d_K y = top}| = 2
- |{y | dot m_K y = top}| = 1

(You can express cardinality via Finset.card of the appropriate filter.)

**Lemma 4 (Rich vs inert discrimination):** The two 2-element testers (e_I and d_K) are distinguishable because Dec(e_I) = {i,k} contains elements that serve as productive right-arguments for non-testers, while Dec(d_K) = {a,b} does not.
```
-- There exists a non-tester f such that dot f i ∉ {top, bot, p} (or similar characterization)
-- No non-tester f has dot f a ∉ {top, bot, p}
```

**Lemma 5 (Encoder asymmetry):** e_D and e_M are the only elements that map both context tokens to non-trivial non-boolean outputs. They are distinguished because e_M maps both to testers while e_D maps to a mixed pair (d_K is a tester, d_I is not).

**Lemma 6 (Context token discrimination):** i and k are distinguished by the decoded-set sizes of their actuality codes: |Dec(dot e_M i)| = |Dec(m_I)| = 16 ≠ 1 = |Dec(m_K)| = |Dec(dot e_M k)|.

**Lemma 7 (Junk identification):** p is the unique element with dot m_I p = bot.

**Lemma 8 (Triple identification):** Among remaining elements, e_Sigma, s_C, e_Delta are the unique triple (f,g,h) with dot f g = h and dot h e_D = d_I.

All of these should be provable by `decide` or `native_decide` over the finite domain.

## Implementation Advice

1. **Start with Δ₁, not Δ₀.** Δ₁ is the more important result (discoverability) and its directed binary operation is simpler to formalize than Σ on Finsets. Get the 17-element type, the dot function, and the recovery lemmas working first. Then go back and do Δ₀ if time permits.

2. **Use `Fintype` and `DecidableEq` everywhere.** Derive them for all your inductive types. This unlocks `decide` and `Finset.univ` for exhaustive proofs.

3. **For the dot function,** pattern match on the pair (x, y). List the ~25 non-default rules explicitly, then use a wildcard for the default `| _, _ => p`. Example:
```lean
def dot : D1ι → D1ι → D1ι
  | .top, _ => .top
  | .bot, _ => .bot
  | .e_I, .i => .top
  | .e_I, .k => .top
  | .e_I, _ => .bot
  -- ... etc
  | _, _ => .p
```

4. **For proofs, try `decide` first.** If it times out, try `native_decide`. If that's too slow, break the proposition into smaller decidable pieces. For Ext specifically, you might need to provide witnesses explicitly rather than searching:
```lean
theorem ext_d1 : ∀ x y : D1ι, x ≠ y → ∃ z, dot x z ≠ dot y z := by decide
```

5. **Keep the lakefile simple.** Just Lean 4 with Mathlib as a dependency (for Fintype, Finset, Decidable infrastructure). If Mathlib is too heavy, you may be able to get away with just Lean 4 + Batteries.

6. **Document everything.** Each definition and theorem should have a docstring explaining its role in the framework. The Lean file should be readable as a self-contained proof document.

## What Success Looks Like

The minimum viable formalization is:
- D1ι type with 17 constructors ✓
- dot function implementing all 26 rules ✓
- Directed Ext proved (∀ x y, x ≠ y → ∃ z, dot x z ≠ dot y z) ✓
- H1, H2, H3 proved ✓
- All 8 recovery lemmas proved ✓
- Everything compiles with no `sorry` ✓

If that works, extend to Δ₀ (the symmetric case) and then to the symmetric barrier argument.

The full formalization with both Δ₀ and Δ₁ would be roughly 1500–2500 lines of Lean.

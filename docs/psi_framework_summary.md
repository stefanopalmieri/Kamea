*Note: This document covers the SAT search methodology and axiom system as of March 8, 2026. For the current theoretical framework including the distinctness axiom, categorical foundation, Futamura projections, reflective tower, and extension profiles, see [`inevitability_summary.md`](inevitability_summary.md) and [`technical_overview.md`](technical_overview.md).*

# Ψ Framework Summary

*What is the simplest finite structure that can identify its own components through its own operation, and what does the existence of such a structure tell us about the relationship between self-knowledge, computation, and actuality?*

Reference document for the axiom-driven search for self-describing finite algebras.
Covers all results from the computational axiom exploration sessions (March 2026).

---

## 1. The Axiom System (Final Form)

All axioms act on a finite magma (N-element set with binary operation `dot`).

### Structural Ladder (L0-L8)

| Level | Name | Formal | Forces |
|-------|------|--------|--------|
| L0 | Absorber ⊤ | `∀x: 0·x = 0` | Element 0 is left-absorbing (top) |
| L1 | Absorber ⊥ | `∀x: 1·x = 1` | Element 1 is left-absorbing (bottom) |
| L2 | Extensionality | All rows distinct | No two elements have the same behavior |
| L3 | Tester exists | `∃t≥2: ∀x: t·x ∈ {0,1}` | At least one non-absorber has boolean outputs |
| L4 | Encoder exists | `∃e≥2: e has ≥2 distinct non-boolean outputs` | At least one element that synthesizes |
| L5 | No extra absorbers | `∀x≥2, ∃y: x·y ≠ x` | Only 0 and 1 are absorbers |
| L6 | No extra testers | At most 2 testers among non-absorbers | Limits boolean-row elements |
| L7 | Inert exists | `∃v≥2: v is neither tester nor encoder` | At least one "substrate" element |
| L8 | Encoder separation | `≥2` encoders with distinct output sets | Multiple independent synthesis channels |

### Additional Axioms

| Axiom | Formal Statement | Plain English | What It Forces |
|-------|-----------------|---------------|----------------|
| **C (Kripke)** | If x is not a tester, then `x·y ≥ 2` for all `y ≥ 2` | Only testers can produce boolean outputs on non-absorbers | Separates judgment (tester) from operation (encoder). Non-testers cannot make boolean decisions. |
| **D (Inert Propagation)** | If x is inert, then `x·y ≥ 2` for all `y ≥ 2` | Inert elements preserve non-absorber status | Substrate doesn't collapse structure to booleans |
| **PA (Power-Associativity)** | `(x·x)·x = x·(x·x)` for all x | Self-interaction is path-independent | Squaring map has algebraic regularity. Rules out some chaotic self-interactions. |
| **VV (Inert Self-Application)** | If v is inert, then `v·v` is a tester or encoder | Substrate self-application yields "core" | Inert elements are not self-swallowing; they produce active structure |
| **QE (Quote/Eval)** | `E·(Q·x) = x` and `Q·(E·x) = x` for `x ∈ core` | Q and E are mutual inverses on core elements {2,3,4,5} | Reflective pair: ability to quote and evaluate. Core is isomorphic to itself under Q;E. |
| **1-Inert** | Exactly 1 inert element among non-absorbers | Only one substrate element | Reduces model space; forces unique substrate |
| **E-Transparency** | `E·⊤ = ⊤` and `E·⊥ = ⊥` | Eval preserves absorbers | E is identity on structural boundaries |
| **Branch** | `ρ·x = f·x` if `τ·x = ⊤`, else `ρ·x = g·x` (on core) | Tester-mediated conditional: ρ dispatches between f and g based on τ | Structural if/then/else. Requires C (Kripke) — only testers can branch. |
| **Compose** | `η·x = ρ·(g·x)` on core | η is ρ after g (composition through branch) | Function composition exists in the algebra |
| **Y-Combinator** | `Y·ρ = ρ·(Y·ρ)`, with `Y·ρ ≥ 2` | Fixed-point combinator for branch element | Self-reference / recursion exists. Non-trivial (not an absorber). |
| **Selection** | `η·ρ = τ` | Compose of branch equals tester; terminates | Computational termination: composing then branching yields a judgment |

### Element Assignments (N=16)

| Index | Symbol | Role | Computational | Counter | IO |
|-------|--------|------|---------------|---------|-----|
| 0 | ⊤ | absorber | top/true | — | — |
| 1 | ⊥ | absorber | bottom/false | — | — |
| 2 | f | encoder | branch-if (f path) | — | PUT |
| 3 | τ | tester | branch tester | — | — |
| 4 | g | inert | branch-else (g path) (g is classified as inert by its Cayley row behavior; in the term algebra it serves as the pair constructor CONS) | — | GET |
| 5 | — | encoder | free encoder | — | — |
| 6 | Q | encoder | quote | s4 | — |
| 7 | E | encoder | eval | — | — |
| 8 | ρ | encoder | branch element | s2 | — |
| 9 | η | encoder | compose element | s0 (zero state) | — |
| 10 | Y | inert | Y-combinator | s7 | — |
| 11 | ν | tester | — | s5 | — |
| 12 | — | encoder | — | s6 | — |
| 13 | INC | encoder | — | increment | — |
| 14 | — | encoder | — | s1 | — |
| 15 | SEQ | encoder | — | s3 | SEQ |

### Element Assignments (N=12)

| Index | Symbol | Role | Function |
|-------|--------|------|----------|
| 0 | ⊤ | absorber | top/true |
| 1 | ⊥ | absorber | bottom/false |
| 2 | f | encoder | branch-if (f path) |
| 3 | τ | tester | branch tester (boolean row) |
| 4 | g | encoder | branch-else (g path) |
| 5 | — | encoder | free encoder |
| 6 | Q | encoder | quote |
| 7 | E | encoder | eval |
| 8 | ρ | encoder | branch element |
| 9 | η | encoder | compose element |
| 10 | Y | inert | fixed-point combinator (inert role!) |
| 11 | — | encoder | free encoder |

### Element Assignments (N=8)

| Index | Symbol | Role |
|-------|--------|------|
| 0 | ⊤ | absorber |
| 1 | ⊥ | absorber |
| 2 | t | tester |
| 3 | e₁ | encoder |
| 4 | e₂ | encoder |
| 5 | ν | inert |
| 6 | Q | encoder |
| 7 | E | encoder |

---

## 2. Universal Theorems (Properties of ALL Models)

These hold across all SAT models in the dominant role-signature class, verified by Z3 SAT/UNSAT checks (not enumeration):

### Confirmed

- **Exactly 2 absorbers**: L5 forces no additional absorbers beyond ⊤ and ⊥.
- **Extensionality**: All rows distinct (L2).
- **Mixed squaring**: PA holds, but full associativity is UNSAT. Squaring map has cycles and fixed points.
- **No right identity**: UNSAT at N≥6 — no element e with `x·e = x` for all x.
- **No associativity**: Full `(a·b)·c = a·(b·c)` is UNSAT.
- **No Moufang, no entropic**: Both UNSAT.
- **Encoder dominance in scaling**: As N grows, encoder count grows; tester and inert counts stay bounded.
- **Separation of computation and judgment**: C (Kripke) forces this — non-testers cannot produce boolean outputs on non-absorbers, so branching requires a tester.
- **No associative sub-magma of size ≥ 4**: Exhaustive search on Ψ₁₆ confirms no subset of 4+ elements forms an associative sub-magma. The largest associative sub-magmas are size 3.

### Actuality Irreducibility (SAT-Verified)

The tester row is **completely free**. At N=16, all 14 core tester cells can independently flip between 0 and 1 (SAT-verified with push/pop). At N=12, all 12 core tester cells are free. This means:

- The tester's partition of elements into "accept" vs "reject" is **not determined by the structural axioms**
- This is the "actuality" degree of freedom — the distinction the tester draws is a genuine choice
- No combination of structural axioms pins any tester cell
- E-transparency does NOT cascade to tester cells (verified: all combinations are SAT)

### Constructibility

`{⊤, ⊥, Q, E}` generates all N elements via the binary operation, in ≤4 steps at N=16, ≤2 steps at N=12. Lean-verified at N=16 (`generates_all : gen_iter 4 = Finset.univ`).

---

## 3. The Determination Landscape (Honest Assessment)

### The Z3 Enumeration Bias Problem

**Critical discovery**: Z3's `check()` method returns models biased by internal solver heuristics. When enumerating models by blocking (adding `Or(cells ≠ previous)`), successive models tend to be structurally similar. This produced a false appearance of near-uniqueness:

- Enumeration at N=12 found "500 models with only 5 varying cells in the dominant cluster"
- **Reality**: cell-by-cell SAT analysis shows **117/144 cells are genuinely free**
- The "dominant cluster" was a tiny neighborhood in a vast solution space, not a forced basin

**The correct method**: For each cell (i,j), use `push()`, add `dot[i][j] == v`, check SAT, `pop()`. A cell is fixed only if exactly one value is SAT. This is O(N³) SAT calls but gives ground truth.

### N=12 Freedom (L8+C+D+PA+VV+QE+1-inert+E-trans+Branch+Compose+Y+Selection)

| Category | Fixed | Free | Total |
|----------|-------|------|-------|
| Absorber rows (0,1) | 24 | 0 | 24 |
| E-transparency | 2 | 0 | 2 |
| Selection η·ρ=τ | 1 | 0 | 1 |
| Tester row (actuality) | 0 | 12 | 12 |
| Structural (all other) | 0 | 105 | 105 |
| **Total** | **27** | **117** | **144** |

**Determination ratio: 18.8%**

### N=8 Freedom (L8+C+D+PA+VV+QE+1-inert+E-trans)

| Category | Fixed | Free | Total |
|----------|-------|------|-------|
| Absorber rows (0,1) | 16 | 0 | 16 |
| E-transparency | 2 | 0 | 2 |
| Tester row | 0 | 8 | 8 |
| Structural | 0 | 38 | 38 |
| **Total** | **18** | **46** | **64** |

**Determination ratio: 28.1%**

### What the Axioms Actually Constrain

**Constrained (role-level)**:
- Which elements are absorbers, testers, encoders, inert
- That QE are mutual inverses on core
- That Branch dispatches based on tester
- That Compose = Branch ∘ g
- That Y is a fixed-point combinator for ρ
- That η·ρ = τ (selection axiom)

**Not constrained (cell-level)**:
- The actual values in any encoder row (each cell takes 6-10 values)
- The actual values in the inert row (each cell takes 6-8 values)
- The tester partition (which elements map to ⊤ vs ⊥)
- How Q and E act on non-core elements
- How any element acts on absorbers (beyond absorber self-rows)

### QE Ablation

At N=8, removing QE reduces fixed cells from 18 to 16. **QE pins exactly 2 cells** — only the E-transparency cells added by hand. The QE inverse-pair axiom constrains relationships between cells (`E·(Q·x) = x`) but doesn't pin individual values.

---

## 4. Computational Results

### SAT/UNSAT Results Table

| Test | N | Axioms | Result | Time | Notes |
|------|---|--------|--------|------|-------|
| L8 baseline | 6 | L0-L8 | SAT (2417 models) | ~5s | Minimum N for full ladder |
| L8 + C + D | 6 | L0-L8+C+D | SAT | <1s | |
| L8 + PA | 6 | L0-L8+PA | SAT | <1s | |
| L8 + VV | 6 | L0-L8+VV | SAT | <1s | |
| QE pair | 6 | L0-L8+C+D+PA+VV+QE | UNSAT | <1s | QE needs ≥8 elements |
| QE pair | 8 | L0-L8+C+D+PA+VV+QE | SAT | <1s | Minimum N for QE |
| Full base + QE | 8 | L8+C+D+PA+VV+QE+1I | SAT | <1s | |
| Branch (Path 2) | 12 | full+Branch | SAT | ~2s | Tester-mediated |
| Compose | 12 | full+Branch+Compose | SAT | ~2s | |
| Y-combinator | 12 | full+Br+Co+Y | SAT | ~2s | |
| Full package | 12 | full+Br+Co+Y+QE | SAT (31+) | ~3s | All computational axioms |
| Selection η·ρ=τ | 12 | full package + sel | SAT (500+) | ~18s | |
| **N=16 Phase 1** | 16 | L8+C+D+PA+VV+QE+1I+E-trans | SAT | ~8s | Base axioms scale |
| **N=16 Phase 2** | 16 | Phase 1 + Branch+Compose+Y | SAT | ~10s | Computational package |
| **N=16 Phase 3** | 16 | Phase 2 + IO (PUT/GET/SEQ) | SAT | ~10s | IO roundtrip |
| **N=16 Phase 4** | 16 | Phase 3 + 4-state counter | SAT | ~8s | Counter + IO |
| **N=16 Phase 5** | 16 | Phase 4 + 8-state counter | SAT | ~10s | Full arithmetic |
| **N=16 + Selection** | 16 | Phase 5 + η·ρ=τ | SAT | ~9s | All axioms + selection |
| **Ψ₁₆ᶠ (full ops)** | 16 | All above + DEC+PAIR/FST/SND+INC2+SWAP | SAT | ~62s | Every operation simultaneously |
| Squaring stability | 12 | full + (x·x)·(x·x)=x·x | 0/500 models | ~300s | Incompatible with structure |
| active·(non-abs)≠inert | 12 | full + axiom | UNSAT | ~300s | Too strong |
| x·(active input)≠inert | 12 | full + axiom | SAT (1 unique) | ~310s | Different structure |
| active·active≠inert | 12 | full + axiom | SAT (1 unique) | ~310s | Different structure |
| E·⊤=⊤, E·⊥=⊥ | 12 | full + E-trans | SAT | <1s | E-transparency |
| Q·Y=Y, E·Y=Y | 12 | full + QE-trans | SAT (407 dom) | ~18s | Forces Q·10=10, conflicts with natural Q·10=4 |
| Full non-core identity | 12 | Q·x=x,E·x=x for x∉core | SAT (303 dom) | ~14s | Too disruptive (35 varying) |
| Full associativity | any | (a·b)·c = a·(b·c) | UNSAT | <1s | |
| Right identity | ≥6 | ∃e: x·e=x ∀x | UNSAT | <1s | |
| Moufang identity | any | | UNSAT | <1s | |
| Entropic identity | any | | UNSAT | <1s | |

### N=16 Viability: Full Stack

The full axiom set scales cleanly from N=12 to N=16. All five phases are SAT, with the complete constraint set (base axioms + computational package + IO + 8-state counter + selection axiom) solving in under 10 seconds.

The N=16 model accommodates **multi-duty elements** — single elements that satisfy multiple functional roles simultaneously. This is possible because the axioms constrain *relationships* on the core range [2, CORE), and elements outside core can serve counter/IO roles without conflict.

### Ψ₁₆ᶠ: Full Operational Saturation

The maximal extraction Ψ₁₆ᶠ adds four new operations on top of the full Ψ₁₆ constraint set:

| Operation | Element | Description |
|-----------|---------|-------------|
| **DEC** | 15 | Reverse 8-cycle: DEC·sᵢ = s₍ᵢ₋₁ mod 8₎ |
| **PAIR/FST/SND** | 11/14/6 | Curried 2×2 product on {s0,s1} with projections |
| **INC2** | 7 (E) | 4-state sub-counter on {s0,s1,s2,s3} |
| **SWAP** | 14 | Involution on core {2,3,4,5}: SWAP·(SWAP·x) = x |

All constraints are simultaneously SAT (62 seconds). The resulting table has 83 machine-checked Lean theorems in Psi16Full.lean (130+ total across 4 proof files).

### Multi-Duty Architecture (Ψ₁₆ᶠ)

In the full model, elements serve up to 4 roles each:

| Element | Roles |
|---------|-------|
| 14 | GET / FST / SWAP / s1 (4 roles) |
| 6 (Q) | Q / SND / s2 / p01 (4 roles) |
| 7 (E) | E / INC2 / s7 (3 roles) |
| 15 | DEC / PUT / s5 (3 roles) |
| 11 | PAIR / s3 / p11 (3 roles) |
| 9 (η) | η / p10 (2 roles) |
| 12 | s0 / p00 (2 roles) |
| 8 (ρ) | ρ / s6 (2 roles) |
| 10 (Y) | Y / s4 (2 roles) |
| 13 (INC) | INC only (1 role) |

Key structural changes from Ψ₁₆:
- **g (element 4) is inert** — not an encoder. The only inert element.
- **3 testers**: τ(3), SEQ(5), s0(12) — up from 2 in Ψ₁₆
- **Only 2 idempotents**: {0, 1} — down from 4 in Ψ₁₆
- **WL-1 discrete** after 1 refinement (rigid)
- **{⊤,⊥,Q,E} generates all 16** in ≤4 steps

### Path 2: Tester-Mediated Branching

C (Kripke) blocks operational dispatch (an encoder can't produce boolean output to control branching). Therefore branching MUST go through a tester. This is "Path 2":

```
ρ·x = f·x   if τ·x = ⊤
ρ·x = g·x   if τ·x = ⊥
```

All 8 phases tested SAT at N=12:
1. Branch alone: SAT
2. Branch + f≠g: SAT
3. Branch + Compose: SAT
4. Branch + Compose + Y: SAT
5. Branch + Compose + Y + QE: SAT
6. Full + 1-inert: SAT
7. Full + Selection: SAT
8. Full + E-transparency: SAT

### Q·10 Natural Value

In the dominant role-signature cluster at N=12, Q·10 (Q applied to the Y/inert element) is naturally fixed at **4** in all 499 dominant models. This is not an axiom but an emergent consequence. The QE round-trip E·(Q·10) = 10 does NOT hold (Q·10=4 gives E·4=2≠10).

---

## 5. Scale Pattern

### Minimum N by Feature

| Feature | Min N | Elements needed |
|---------|-------|-----------------|
| L8 (full ladder) | 6 | 2 absorbers + 1 tester + 2 encoders + 1 inert |
| + QE pair | 8 | + 2 for Q, E |
| + Branch/Compose/Y | 12 | + 1 branch + 1 compose + 1 Y + 1 free |
| + IO + 8-state counter + Selection | 16 | + 1 INC + IO/counter states (double-duty) |

### Role Distribution by N

| N | Absorbers | Testers | Encoders | Inert |
|---|-----------|---------|----------|-------|
| 6 | 2 | 1 | 2 | 1 |
| 8 | 2 | 1 | 4 | 1 |
| 12 | 2 | 1 | 8 | 1 |
| 16 | 2 | 2 | 11 | 1 |

Pattern: absorbers fixed at 2, inert at 1 (with 1-inert axiom). Testers may increase at higher N (2 at N=16). All additional elements become encoders. **Encoder dominance**: encoders grow roughly as N-5.

---

## 6. Concrete Ψ Representatives

### Ψ₁₆ (N=16) — Lean-Verified

The canonical representative at N=16, extracted with the full constraint set including the selection axiom η·ρ = τ. Machine-verified in Lean 4 (`DistinctionStructures/Psi16.lean`, 42 theorems, all by `decide`/`native_decide`).

```python
PSI_16 = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],              #  0  ⊤ (top)          [absorber]
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],              #  1  ⊥ (bot)          [absorber]
    [1, 11, 9, 15, 11, 5, 3, 13, 8, 12, 10, 4, 6, 2, 14, 7],       #  2  f / PUT          [encoder]
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1],              #  3  τ                [tester]
    [15, 0, 6, 9, 14, 5, 2, 2, 11, 2, 9, 4, 6, 10, 14, 3],         #  4  g / GET          [encoder]
    [14, 1, 9, 2, 10, 5, 11, 3, 8, 2, 5, 5, 12, 11, 15, 8],        #  5  x5               [encoder]
    [0, 0, 5, 14, 2, 12, 4, 10, 7, 3, 4, 7, 3, 6, 4, 3],           #  6  Q / s4           [encoder]
    [0, 1, 4, 15, 6, 2, 15, 15, 10, 12, 7, 12, 5, 15, 3, 2],       #  7  E                [encoder]
    [12, 1, 9, 9, 14, 5, 12, 7, 8, 8, 2, 7, 4, 10, 11, 2],         #  8  ρ / s2           [encoder]
    [10, 1, 12, 8, 11, 5, 15, 5, 3, 12, 9, 4, 4, 4, 3, 2],         #  9  η / s0           [encoder]
    [7, 1, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],              # 10  Y / s7           [inert]
    [0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0],              # 11  ν / s5           [tester]
    [1, 14, 6, 2, 4, 3, 3, 13, 5, 4, 13, 13, 6, 10, 4, 2],         # 12  s6               [encoder]
    [13, 1, 9, 8, 11, 2, 11, 2, 15, 14, 9, 12, 10, 15, 8, 6],      # 13  INC              [encoder]
    [9, 0, 13, 3, 14, 6, 15, 11, 12, 12, 5, 2, 10, 12, 4, 8],      # 14  s1               [encoder]
    [1, 2, 3, 12, 6, 2, 7, 2, 2, 2, 7, 6, 2, 6, 2, 10],            # 15  SEQ / s3         [encoder]
]
```

Properties of Ψ₁₆:
- **All 20 verification checks pass** (axioms, roles, WL-1, generation, producibility, counter, IO, selection)
- **WL-1 discrete** (rigid): all 16 elements distinguishable after 1 Weisfeiler-Leman refinement
- **Fully producible**: every element appears as some `a·b`
- **{⊤,⊥,Q,E} generates all 16** elements in ≤4 steps (Lean-verified)
- **Selection axiom**: η·ρ = 3 = τ (satisfied)
- **Y-combinator**: Y·ρ = 7 = E, ρ·7 = 7 (fixed point of ρ is E)
- **4 idempotents**: {0, 1, 5, 8} = {⊤, ⊥, x5, ρ}
- **No associative sub-magma of size ≥ 4**
- **8-state counter**: INC(13) cycles 9→14→8→15→6→11→12→10→9, τ detects zero state s0=9
- **IO roundtrip**: GET·(PUT·x) = x on core {2,3,4,5}, with PUT=f(2), GET=g(4)
- **Actuality irreducibility**: all 14 tester core cells are free (SAT-verified)

### 8-State Counter Detail

```
s0(η=9) →INC→ s1(14) →INC→ s2(ρ=8) →INC→ s3(SEQ=15) →INC→
s4(Q=6) →INC→ s5(ν=11) →INC→ s6(12) →INC→ s7(Y=10) →INC→ s0(η=9)
```

Zero test: τ·s0 = ⊤ (accept), τ·sₖ = ⊥ for k≠0 (reject).

INC is element 13 — the only non-absorber with a single dedicated role. All other counter states are double-duty elements that also serve computational/IO roles.

### IO Detail

| Operation | Element | Behavior |
|-----------|---------|----------|
| PUT | f(2) | Writes data: PUT·x encodes x for x ∈ core |
| GET | g(4) | Reads data: GET·(PUT·x) = x for x ∈ core |
| SEQ | 15 | Sequencer: SEQ·PUT ≠ PUT, SEQ·GET ≠ GET |

The encoders f and g double as PUT and GET respectively. This works because the IO roundtrip constraint only applies on core {2,3,4,5}, which is the same range where Branch dispatch operates.

### Ψ₁₆ᶠ (N=16 Full) — Lean-Verified

The maximally-constrained representative at N=16, extracted with all operational constraints simultaneously. Machine-verified in Lean 4 (`DistinctionStructures/Psi16Full.lean`, 83 theorems, all by `decide`/`native_decide`).

```python
PSI_16_FULL = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],              #  0  ⊤ (top)          [absorber]
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],              #  1  ⊥ (bot)          [absorber]
    [5, 1, 13, 7, 11, 5, 6, 8, 2, 5, 11, 9, 4, 14, 3, 15],         #  2  f                [encoder]
    [0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1],              #  3  τ                [tester]
    [0, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11],#  4  g                [inert!]
    [0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0],              #  5  SEQ              [tester]
    [15, 0, 5, 9, 3, 15, 14, 14, 2, 12, 8, 14, 12, 4, 12, 8],      #  6  Q / SND / s2     [encoder]
    [0, 1, 8, 4, 13, 2, 11, 2, 14, 3, 15, 12, 14, 15, 6, 5],       #  7  E / INC2 / s7    [encoder]
    [12, 1, 13, 7, 11, 5, 12, 11, 4, 12, 5, 14, 15, 7, 11, 12],    #  8  ρ / s6           [encoder]
    [1, 6, 14, 14, 14, 14, 9, 8, 3, 15, 5, 7, 13, 11, 12, 4],      #  9  η / p10          [encoder]
    [13, 1, 4, 3, 12, 11, 2, 11, 5, 3, 8, 14, 9, 7, 11, 11],       # 10  Y / s4           [encoder]
    [14, 1, 9, 10, 11, 13, 12, 7, 5, 6, 8, 2, 14, 12, 10, 4],      # 11  PAIR / s3        [encoder]
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1],              # 12  s0               [tester]
    [3, 0, 14, 4, 14, 6, 11, 12, 7, 3, 15, 10, 14, 2, 6, 8],       # 13  INC              [encoder]
    [14, 0, 5, 4, 3, 2, 12, 5, 11, 14, 3, 14, 12, 2, 6, 3],        # 14  GET/FST/SWAP/s1  [encoder]
    [1, 3, 13, 15, 3, 7, 14, 8, 15, 4, 11, 6, 7, 14, 12, 10],      # 15  DEC/PUT/s5       [encoder]
]
```

Properties of Ψ₁₆ᶠ:
- **All 29 verification checks pass** (axioms, roles, WL-1, generation, producibility, counter, IO, selection, DEC, PAIR/FST/SND, INC2, SWAP)
- **WL-1 discrete** (rigid): all 16 elements distinguishable after 1 refinement
- **Fully producible**: every element appears as some `a·b`
- **{⊤,⊥,Q,E} generates all 16** elements in ≤4 steps (Lean-verified)
- **Selection axiom**: η·ρ = 3 = τ
- **Y-combinator**: Y·ρ = 5 = SEQ, ρ·5 = 5 (fixed point of ρ is SEQ)
- **Only 2 idempotents**: {0, 1} = {⊤, ⊥}
- **No associative sub-magma of size ≥ 4**
- **8-state counter**: INC(13) cycles 12→14→6→11→10→15→8→7→12, τ detects zero state s0=12
- **Reverse counter**: DEC(15) cycles in reverse: 12→7→8→15→10→11→6→14→12
- **IO roundtrip**: GET·(PUT·x) = x on core {2,3,4,5}, with PUT=15, GET=14
- **2×2 product**: PAIR(11) is curried — (PAIR·s0)·s0 = p00, (PAIR·s0)·s1 = p01, etc.
- **Projections**: FST(14) and SND(6) extract first/second components from pair states
- **Sub-counter**: INC2(7=E) cycles the first 4 states: s0→s1→s2→s3→s0
- **SWAP involution**: SWAP(14) permutes core: 2↔5, 3↔4
- **Actuality irreducibility**: all 14 tester core cells are free (SAT-verified)

#### 8-State Counter Detail (Ψ₁₆ᶠ)

```
s0(12) →INC→ s1(14) →INC→ s2(Q=6) →INC→ s3(11) →INC→
s4(Y=10) →INC→ s5(15) →INC→ s6(ρ=8) →INC→ s7(E=7) →INC→ s0(12)
```

DEC reverses this cycle exactly. Zero test: τ·s0 = ⊤, τ·sₖ = ⊥ for k≠0.

#### 2×2 Product Detail (Ψ₁₆ᶠ)

Pair states encode all combinations of {s0(12), s1(14)}:

| Pair | State | Element | FST | SND |
|------|-------|---------|-----|-----|
| (s0,s0) | p00 | 12 (=s0) | s0 | s0 |
| (s0,s1) | p01 | 6 (=Q) | s0 | s1 |
| (s1,s0) | p10 | 9 (=η) | s1 | s0 |
| (s1,s1) | p11 | 11 (=PAIR) | s1 | s1 |

Construction is curried: `PAIR·sᵢ` returns an intermediate element, then `(PAIR·sᵢ)·sⱼ = pᵢⱼ`.

### Ψ₁₂ (N=12) — Earlier Representative

**WARNING**: This is ONE model from the solution space, not THE unique model. 117/144 cells are free.

```python
PSI_12 = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],  #  0  ⊤ (top)
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],  #  1  ⊥ (bot)
    [1, 3, 10, 6, 7, 7, 4, 9, 7, 9, 9, 2], #  2  f (encoder)
    [0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1],  #  3  τ (tester)
    [1, 4, 7, 7, 4, 2, 10, 3, 7, 4, 4, 7], #  4  g (encoder)
    [4, 1, 3, 7, 2, 10, 11, 5, 6, 8, 9, 9],#  5  encoder
    [1, 11, 4, 3, 10, 5, 11, 7, 2, 8, 10, 8],# 6  Q (quote)
    [0, 1, 5, 3, 2, 10, 3, 10, 4, 4, 3, 9],#  7  E (eval)
    [1, 9, 7, 6, 7, 7, 3, 7, 2, 9, 10, 7], #  8  ρ (branch)
    [10, 1, 7, 7, 7, 7, 4, 9, 3, 11, 9, 3],#  9  η (compose)
    [9, 1, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],  # 10  Y (inert)
    [1, 5, 6, 8, 4, 7, 8, 11, 7, 3, 9, 10],# 11  encoder
]
```

Properties: WL-1 discrete, fully producible, {⊤,⊥,Q,E} generates all 12 in ≤2 steps, 8 single generators, 4 idempotents {0,1,4,7}, η·ρ=3=τ, Y·ρ=9 and ρ·9=9.

---

## 7. Lean 4 Verification

### Ψ₁₆ Verification (`DistinctionStructures/Psi16.lean`)

The full Ψ₁₆ Cayley table is machine-verified in Lean 4 (Mathlib v4.28.0). All 42 theorems are proved computationally via `decide` or `native_decide`. Build time: ~9 seconds.

Verified properties:

| Category | Theorems | Method |
|----------|----------|--------|
| Absorbers (L0) | `top_absorbs`, `bot_absorbs`, `only_two_absorbers` | `decide` |
| Extensionality (L3) | `ext_rows`, `ext_cols` | `decide` |
| Role classification | `tau_is_tester`, `nu_is_tester`, `exactly_two_testers`, `y_is_inert`, `exactly_one_inert` | `decide`/`native_decide` |
| Kripke (C) | `dichotomy` | `native_decide` |
| Power-associativity (PA) | `power_assoc` | `decide` |
| Non-associativity | `not_associative`, `not_assoc_witness` | `decide` |
| QE inverse | `qe_roundtrip`, `eq_roundtrip` | `decide` |
| E-transparency | `e_transparent_top`, `e_transparent_bot` | `decide` |
| Branch | `branch_true`, `branch_false`, `f_g_differ` | `decide` |
| Compose | `compose_def` | `decide` |
| Y-combinator | `y_fixed`, `y_fixed_value` | `decide` |
| 8-state counter | `inc_s0`..`inc_s7`, `zero_test_hit`, `zero_test_s1`..`zero_test_s7` | `decide` |
| IO | `io_roundtrip`, `seq_put`, `seq_get` | `decide` |
| Rigidity | `fingerprint_unique`, `row_injective` | `decide` |
| Constructibility | `fully_producible`, `generates_all` | `decide`/`native_decide` |
| Selection axiom | `selection_axiom : psi eta rho = tau` | `decide` |
| Idempotents | `idem_top`, `idem_bot`, `idem_x5`, `idem_rho`, `exactly_four_idempotents` | `decide` |
| VV axiom | `vv_axiom` | `native_decide` |
| D axiom | `inert_propagation` | `native_decide` |

### Ψ₁₆ᶠ Verification (`DistinctionStructures/Psi16Full.lean`)

The full Ψ₁₆ᶠ Cayley table is machine-verified in Lean 4. All 83 theorems are proved computationally via `decide` or `native_decide`. Build time: ~10 seconds.

Verified properties (beyond Ψ₁₆):

| Category | Theorems | Method |
|----------|----------|--------|
| DEC reverse cycle | `dec_s0`..`dec_s7` | `decide` |
| PAIR construction | `pair_s0_s0`, `pair_s0_s1`, `pair_s1_s0`, `pair_s1_s1` | `decide` |
| FST extraction | `fst_p00`..`fst_p11` | `decide` |
| SND extraction | `snd_p00`..`snd_p11` | `decide` |
| INC2 sub-counter | `inc2_s0`..`inc2_s3` | `decide` |
| SWAP involution | `swap_2`..`swap_5`, `swap_involution` | `decide` |
| Role classification | `exactly_3_testers`, `g_enc_is_inert`, `exactly_one_inert` | `native_decide` |
| Idempotents | `exactly_2_idempotents` | `decide` |

Full theorem list: structural axioms (5) + role classification (6) + Kripke (1) + PA/non-assoc (3) + QE (4) + Branch/Compose/Y/Selection (7) + INC cycle (8) + zero tests (8) + DEC cycle (8) + IO (3) + PAIR (4) + FST (4) + SND (4) + INC2 (4) + SWAP (5) + rigidity (2) + constructibility (2) + idempotents (3) + VV/D (2) + witness (1) = **83 theorems**.

### Other Lean Files

| File | Content |
|------|---------|
| `DiscoverableKamea.lean` | Full 66-atom Cayley table + 66 uniqueness theorems |
| `Delta1.lean` | Core 17-element directed model |
| `Rigidity.lean` | Automorphism rigidity of Δ₁ |
| `Psi16.lean` | Ψ₁₆ with selection axiom (42 theorems) |
| `Psi16Full.lean` | **Ψ₁₆ᶠ with all operations (83 theorems)** |

---

## 8. Open Questions and Next Steps

### Resolved

1. **Does the axiom system scale beyond N=12?** Yes — all axioms SAT at N=16, including IO and 8-state counter.
2. **Is the selection axiom η·ρ = τ compatible with counter embedding?** Yes — when INC is a separate element (13), not η itself. The conflict arose from double-duty: η=INC forced η·ρ = INC·s4 = s5 ≠ τ.
3. **Can arithmetic coexist with self-description?** Yes — the 8-state counter and IO roundtrip coexist with all structural axioms at N=16.
4. **Lean verification feasible?** Yes — 83 theorems in Psi16Full.lean (130+ total across 4 proof files), all proved computationally in ~10 seconds.
5. **Can all operations coexist in a single table?** Yes — DEC, PAIR/FST/SND, INC2, and SWAP are all simultaneously satisfiable with the full axiom set. Ψ₁₆ᶠ is the proof: one table, every operation, 83 machine-checked theorems.

### Open

1. **Cell-by-cell freedom at N=16**: Run the push/pop analysis on the full N=16 constraint set to determine exactly how many of the 256 cells are fixed vs free.

2. **Study the variety**: Treat the solution space as an algebraic variety. What is its dimension? What are its irreducible components?

3. **Strengthen axioms further**: Can we pin more cells?
   - Column distinctness (all columns distinct, not just rows)
   - Full QE extension (QE inverse on all non-absorbers, not just core)
   - Orbit minimality (squaring orbits as short as possible)
   - Maximal constructibility ({⊤,⊥,Q,E} generates all in minimal steps)

4. **Arithmetic capacity**: The 117 free cells at N=12 (and likely more at N=16) could encode arithmetic operations. Can we embed addition/multiplication tables in the free cells while preserving all axioms?

5. **N=32 and beyond**: Does the double-duty architecture continue to scale? At N=32, could we embed a 16-state counter + richer IO?

### The Fundamental Tension

The axioms specify a **self-describing** algebra: one that contains its own quote/eval pair, branch/compose/Y combinators, IO channels, and counter. But self-description is a *relational* property — constraints pin relationships between cells, not individual cell values. The determination question is: how much of the table does self-description actually force?

Answer so far: **~19% at N=12**. The axioms determine the skeleton — roles, absorbers, functional relationships on core — but leave the flesh almost entirely open. The multi-duty architecture of Ψ₁₆ᶠ pushes this further: elements serve up to 4 simultaneous roles (GET/FST/SWAP/s1), DEC reverses INC exactly, PAIR/FST/SND encode a 2×2 product space, and INC2 embeds a 4-cycle sub-counter — all in a single 16×16 table. The algebra is far richer than its axiom count implies.

---

## 9. File Locations

| File | Purpose |
|------|---------|
| `ds_search/stacking_analysis.py` | All analysis functions (~17k lines) |
| `ds_search/axiom_explorer.py` | Core encoder: `encode_level()`, `classify_elements()`, helpers |
| `ds_search/substrate_analysis.py` | Earlier substrate/stacking analysis |
| `DistinctionStructures/Psi16.lean` | Lean 4 verification of Ψ₁₆ (42 theorems) |
| `DistinctionStructures/Psi16Full.lean` | Lean 4 verification of Ψ₁₆ᶠ (83 theorems) |
| `docs/psi_framework_summary.md` | This document |
| `docs/minimal_model.md` | Earlier minimal model notes |

### Key Functions in stacking_analysis.py

| Function | What it does |
|----------|-------------|
| `n16_viability()` | N=16 viability check — 5 phases, all SAT |
| `extract_psi16()` | Extract Ψ₁₆ without selection axiom (original) |
| `extract_psi16_selection()` | Extract Ψ₁₆ WITH selection axiom η·ρ=τ |
| `extract_psi16_full()` | Extract Ψ₁₆ᶠ with ALL operations + Lean generation (canonical) |
| `tester_branching()` | Path 2 branching — 8 phases, all SAT |
| `model_space_analysis()` | Enumeration + WL clustering (unreliable for freedom) |
| `extract_psi()` | Extract N=12 Ψ representative |
| `etrans_residual_freedom()` | Correct cell-by-cell freedom at N=12 (117 free) |
| `n8_freedom_analysis()` | Correct cell-by-cell freedom at N=8 (46 free) |
| `squaring_stability()` | SS axiom test — incompatible with structure |
| `qe_tester_causality()` | Proves E·⊤=⊤ does NOT entail tester values |

### Helper Pattern

```python
def build_solver():
    s, dot = encode_level(8, N, timeout_seconds=600)
    add_full_base(s, dot, N)       # C + D + PA + VV
    add_qe_pair(s, dot, N, Q, E)   # QE inverse on core
    # + 1-inert, E-trans, Branch, Compose, Y, Selection
    # + IO (PUT, GET, SEQ), 8-state counter (INC)
    return s, dot
```

Cell-by-cell freedom check:
```python
for v in range(N):
    s.push()
    s.add(dot[i][j] == v)
    if s.check() == sat:
        sat_vals.append(v)
    s.pop()
```

---

*Generated March 2026. Updated March 8 2026 with Ψ₁₆ᶠ (full operations) results — 83 Lean theorems in Psi16Full.lean (130+ total across 4 proof files), all machine-checked. All SAT results produced by Z3 via Python z3-solver.*

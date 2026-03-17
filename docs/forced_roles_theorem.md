# The Forced Roles Theorem

## Statement

The Ψ axioms force five behavioral categories with hard walls between judgment, substrate, and computation. All instantiations — from maximally collapsed (5 role-bearing elements) to fully specialized (7+ role-bearing elements) — produce rigid, discoverable algebras. Among tested collapses, seven specialized roles maximize compositional expressiveness, and these seven correspond to McCarthy's 1960 Lisp primitives. Five categories are axiom-forced (theorem). Seven roles are empirically optimal (not yet proved necessary).

The argument has three layers, each building on the previous:

1. **Forced Categories.** The axioms partition 10 TC roles into 5 categories with hard walls between them. This is a theorem (SAT/UNSAT), not a design choice.
2. **Universal Rigidity.** Every instantiation of these categories — from 5 to 7+ role-bearing elements — produces a rigid, discoverable algebra. Rigidity is a property of the axiom geometry, not of role specialization.
3. **Variational Selection.** Among tested collapse levels, the fully specialized instantiation (7 distinct role elements) maximizes the number of distinct pairwise compositions among role-bearing elements. This selects the natural unfolding empirically; a formal proof of uniqueness remains open.

---

## Layer 1: Forced Categories

### The Five Categories

The 10 TC roles {⊤, ⊥, τ, Q, E, f, g, ρ, η, Y} partition into 5 behavioral categories. Roles within a category can share a single element (SAT). Roles in different categories cannot (UNSAT).

| Category | Roles | Characterization |
|----------|-------|-----------------|
| **Polarity** | ⊤, ⊥ | Absorbers. Fungible: no behavioral axiom distinguishes them. |
| **Judgment** | τ | Maximally isolated. The Kleene barrier forbids merger with any other role. |
| **Substrate** | g | Maximally isolated. The inert role constraint forbids merger with any active role. |
| **Composition** | η | Partially isolated. Selection + Compose interaction forbids merger with Q, E, ρ. Can merge only with f and Y. |
| **Computation** | Q, E, f, ρ, Y | Internally fungible. All 10 pairwise merges within this group are SAT. |

The minimum number of distinct elements required is the chromatic number of the forced-distinct graph: **5**.

### The Forced-Distinct Matrix

45 pairwise role-aliasing tests at N=12 (minimum size for all axioms). For each pair, both roles are assigned to the same element index; all axioms are applied faithfully. X = UNSAT (forced distinct), · = SAT (can merge).

```
          ⊤   ⊥   τ   Q   E   f   g   ρ   η   Y
    ⊤     -   ·   X   X   X   X   X   X   X   X
    ⊥     ·   -   X   X   X   X   X   X   X   X
    τ     X   X   -   X   X   X   X   X   X   X
    Q     X   X   X   -   ·   ·   X   ·   X   ·
    E     X   X   X   ·   -   ·   X   ·   X   ·
    f     X   X   X   ·   ·   -   X   ·   ·   ·
    g     X   X   X   X   X   X   -   X   X   X
    ρ     X   X   X   ·   ·   ·   X   -   X   ·
    η     X   X   X   X   X   ·   X   X   -   ·
    Y     X   X   X   ·   ·   ·   X   ·   ·   -
```

**32 pairs forced distinct. 13 pairs mergeable.**

### The Three Walls

Each wall is a theorem — an UNSAT result with identified necessary axioms.

**Wall 1: The Kleene Barrier (τ isolated)**

τ cannot merge with any other role (9/9 pairs UNSAT). The Kleene axiom (C) enforces a structural separation: a row is either all-boolean (tester) or has non-boolean outputs on non-absorbers (encoder/inert). No row can be both. This is the wall between judgment and everything else.

- τ vs all encoders (Q, E, f, ρ, η, Y): UNSAT. Necessity: **Roles** — tester and encoder constraints are mutually exclusive on any row. A tester row has all outputs in {0,1}; an encoder row requires ≥2 distinct non-boolean outputs.
- τ vs g (inert): UNSAT. Necessity: **Roles** — tester and inert constraints are mutually exclusive. A tester row is all-boolean; an inert row has no pair of distinct non-boolean outputs but is also not all-boolean (since it's not a tester).
- τ vs ⊤, ⊥: UNSAT. Necessity: **Kleene + Roles** — absorber rows are constant; tester rows are boolean but non-constant.

**Wall 2: The Substrate Barrier (g isolated)**

g cannot merge with any other role (9/9 pairs UNSAT). The 1-Inert axiom forces exactly one inert element. The inert role constraint requires a row that is neither all-boolean nor has ≥2 distinct non-boolean outputs. No encoder or tester can satisfy this.

- g vs all encoders: UNSAT. Necessity: **Roles** — encoder requires ≥2 distinct non-boolean outputs; inert forbids this.
- g vs τ: UNSAT (covered by Wall 1).
- g vs ⊤, ⊥: UNSAT. Necessity: **Roles** — absorber rows are constant; inert rows are not.

**Wall 3: The Composition Barrier (η partially isolated)**

η cannot merge with Q, E, or ρ (UNSAT), but can merge with f and Y (SAT). The Selection axiom (`η·ρ = τ`) combined with Compose (`η·x = ρ·(g·x)` on core) creates constraints that conflict with QE cancellation and with η=ρ self-reference.

- η vs Q: UNSAT. Necessity: **QE, Compose, Roles** — three independent paths to UNSAT.
- η vs E: UNSAT. Necessity: **QE, Compose, Roles** — same three paths.
- η vs ρ: UNSAT. Necessity: **Kleene, PA, Selection, Roles** — four independent paths; the most over-determined forced distinction among encoders.
- η vs f: SAT. η vs Y: SAT. These merges are compatible because f and Y have no axioms that directly conflict with Compose or Selection when aliased to η's index.

### Branch Discrimination (f ≠ g)

The Branch axiom includes the clause `Or([dot[f][j] ≠ dot[g][j] for j in core])` — f and g must differ on at least one core input. When f=g, this becomes `Or(False, False, ...) = False`, making the system trivially UNSAT. This is the proof: the discrimination clause IS the axiom that forces f ≠ g. Necessity analysis shows this requires axiom interaction (no single named group's removal makes f=g SAT).

### Necessity Analysis Summary

For each UNSAT pair, axiom groups were removed one at a time to identify which are necessary:

| Pattern | Necessary Group | Pairs |
|---------|----------------|-------|
| Cross-category (tester vs encoder/inert) | **Roles** | τ=Q, τ=E, τ=f, τ=g, τ=ρ, τ=η, τ=Y |
| Cross-category (absorber vs encoder/inert) | **Roles** | ⊤=f, ⊤=g, ⊥=f, ⊥=g |
| Encoder vs inert | **Roles** | Q=g, E=g, g=ρ, g=η, g=Y |
| η vs Q/E | **QE, Compose, Roles** | Q=η, E=η |
| η vs ρ | **Kleene, PA, Selection, Roles** | ρ=η |
| Absorber vs τ | **Kleene, Selection** | ⊤=τ, ⊥=τ |
| Various absorber-encoder | **(interaction)** | ⊤=Q, ⊤=E, ⊤=ρ, ⊤=η, ⊤=Y, etc. |

**Roles** (the tester/encoder/inert classification) is the most common necessity. It creates the primary barrier. The behavioral axioms (QE, Compose, Selection, Branch) create secondary barriers within the encoder category.

Evidence: `ds_search/forced_roles_test.py` — 45 pairwise tests, each with necessity analysis via push/pop.

---

## Layer 2: Universal Rigidity

### The Collapse Spectrum

For each collapse level, a model is found by SAT search (N=12), then checked for WL-1 rigidity, automorphism group, and discoverability.

| Level | Roles Merged | Distinct Role Elements | WL-1 Rigid? | |Aut| | Discoverable? |
|-------|-------------|----------------------|-------------|-------|---------------|
| 0 | none | 7 | **YES** (round 1) | 1 | YES (1 probe) |
| 1 | Q=E | 6 | **YES** (round 1) | 1 | YES (1 probe) |
| 2 | Q=E, ρ=Y | 6 | **YES** (round 1) | 1 | YES (1 probe) |
| 3 | Q=E=f, ρ=Y | 5 | **YES** (round 1) | 1 | YES (1 probe) |
| 4 | Q=E=f=ρ=Y | 4 | **YES** (round 1) | 1 | YES (1 probe) |
| 5 | Q=E=f=ρ=Y, ⊤=⊥ | 4 | **YES** (round 1) | 1 | YES (1 probe) |

**Rigidity survives all collapse levels.** Every model, at every level, is WL-1 rigid in round 1, has trivial automorphism group (|Aut| = 1), and is discoverable from a single probe element.

### Why Rigidity Survives

The mega-encoder's row (carrying Q+E+f+ρ+Y) is constrained by: QE cancellation on core, Branch dispatch (ρ·x = f·x or g·x conditional on τ), Y fixed-point (Y·ρ = ρ·(Y·ρ)), Compose interaction (η·x = ρ·(g·x)), and Selection (η·ρ = τ). These constraints, concentrated on a single row, create *more* asymmetry than five separate rows would. The filler elements (those without explicit role assignments) differentiate themselves through their interactions with this heavily constrained row.

Rigidity is a property of the **axiom geometry** — the pattern of constraints the axioms impose on the Cayley table — not of role specialization. A single element doing five jobs has a more constrained, more asymmetric row than five elements each doing one job. Self-knowledge comes from the constraints, not from having many parts.

### Model Diversity at Maximal Collapse

At level 5 (maximal collapse), 20+ distinct satisfying models exist. All are WL-1 rigid. Only 28/144 cells are fixed across all models; 116 cells are free. The axiom constraints leave large freedom but every point in that space is rigid.

Per-row breakdown (across 20 models):
- Row 0 (⊤/⊥): 12/12 fixed — absorber, fully determined
- Row 3 (τ): 7/12 fixed — tester constraints pin most cells
- Row 6 (Q/E/f/ρ/Y): 5/12 fixed, 7 free — behavioral axioms fix core, leave periphery free
- Row 9 (η): 1/12 fixed, 11 free — only η·ρ = τ is fixed
- Row 4 (g): 0/12 fixed — inert row is constant but the constant value is free
- Filler rows: 0–2/12 fixed each

Evidence: `ds_search/collapse_rigidity_test.py` — all 6 levels, full WL-1 + automorphism + discoverability analysis. `ds_search/collapse_model_count.py` — 20 models at level 5, all rigid.

---

## Layer 3: The Variational Principle

### Statement

Among all rigid models satisfying the Ψ axioms, the natural model is the one that maximizes the number of distinct pairwise compositions among role-bearing elements.

### Three Forms of Evidence

**1. Compositional Cell Count (deterministic, structural)**

The number of structurally independent compositions is k² for k physical elements. This is a hard ceiling on expressive capacity — purely a function of the collapse level.

| Level | Physical Elements | 1-step Cells | 2-step Cells |
|-------|-------------------|-------------|-------------|
| 0 | 7 | **49** | **343** |
| 1 | 6 | 36 | 216 |
| 2 | 6 | 36 | 216 |
| 3 | 5 | 25 | 125 |
| 4 | 4 | 16 | 64 |
| 5 | 4 | 16 | 64 |

Full specialization has **3.06×** the 1-step capacity and **5.36×** the 2-step capacity of maximal collapse. The ratio grows as k³/k'³ at depth 2, k⁴/k'⁴ at depth 3, etc. — expressiveness diverges exponentially with composition depth.

**2. Compositional Value Count (model-dependent)**

The number of distinct output values produced by role-pair compositions. Measured across SAT models at each level.

| Level | 1-step Values | 2-step Values |
|-------|--------------|--------------|
| 0 | **10** | **11** |
| 1 | 9 | 9–10 |
| 2 | 9–10 | 10–11 |
| 3 | 8 | 9–10 |
| 4 | 6–7 | 7–8 |
| 5 | 6–7 | 7–8 |

Level 0 consistently maximizes distinct values at both depths. The ratio (specialized/collapsed) is ~1.5–1.7×.

**3. Reachability Depth**

Starting from the role-bearing elements, how many composition steps to reach all N=12 elements.

| Level | Depth 0 | Depth 1 | Depth 2 | Depth 3 |
|-------|---------|---------|---------|---------|
| 0 | 7 | 10 | **12** | 12 |
| 1 | 6 | 10 | 11 | 11 |
| 3 | 5 | 10 | **12** | 12 |
| 4 | 4 | 8 | **12** | 12 |
| 5 | 4 | 7 | 10 | **12** |

Full specialization reaches generative closure at depth 2. Maximal collapse needs depth 3.

### The Composition Subtables

**Level 0 (specialized)** — every cell is an independent lookup (49/49):

```
         ⊤    Q    E    f    g    ρ    η
  ⊤      0    0    0    0    0    0    0
  Q      2   11    2    8   10    4    3
  E      0    2    2    7   10    2    3
  f      3    6    7    2    3    2    2
  g     11   11   11   11   11   11   11
  ρ      2    9    9    2    3   11    2
  η      4    8    4    2    2    3    2
```

**Level 5 (maximal collapse)** — only 16 independent cells; Q/E/f/ρ rows identical:

```
         ⊤    Q    E    f    g    ρ    η
  ⊤      0    0    0    0    0    0    0
  Q      0   11   11   11    9   11    4
  E      0   11   11   11    9   11    4
  f      0   11   11   11    9   11    4
  g     11   11   11   11   11   11   11
  ρ      0   11   11   11    9   11    4
  η      2    3    3    3   11    3    2
```

Four of seven rows are identical. The Q/E/f/ρ block collapses to a single repeated pattern. The algebra satisfies all axioms but has lost 33 of 49 independent compositions.

### Monotonicity

Each additional distinct role element strictly increases the cell count: k physical elements give k² 1-step cells. The function k² is strictly increasing, so there are **no intermediate optima**. The maximum is always at full specialization. This makes the variational principle a clean selector — it does not depend on model-specific details.

### The Maximum Entropy Analogy

In statistical mechanics, the maximum entropy principle selects the macrostate compatible with constraints (energy, particle number) that has the most microstates. The system doesn't "choose" the high-entropy state — it occupies it because there are more ways to realize it.

Here, maximal expressiveness selects the role assignment compatible with axioms that has the most distinct compositions. The algebra doesn't "choose" to specialize — the specialized configuration has more compositional states, and is therefore the natural occupant of the constraint space. Same mathematical structure — constrained optimization — different domain.

Evidence: `ds_search/compositional_expressiveness.py` — cell counts, value counts, and reachability at all 6 levels.

---

## The McCarthy Correspondence

The seven roles selected by the variational principle correspond to McCarthy's 1960 Lisp primitives:

| Ψ Role | McCarthy Primitive | Forced by | Specialized by |
|--------|-------------------|-----------|---------------|
| ⊤ | NIL | L0 (absorber) | axiom (Layer 1) |
| Q | QUOTE | QE (constructor) | expressiveness (Layer 3) |
| E | EVAL | QE (destructor) | expressiveness (Layer 3) |
| g | CONS | 1-Inert + Branch | axiom (Layer 1) |
| f | CAR | Branch (first path) | expressiveness (Layer 3) |
| η | CDR | Compose (second projection) | axiom (Layer 1) |
| ρ | COND | Branch (conditional) | expressiveness (Layer 3) |

Four roles are forced by axioms alone — they occupy isolated categories:

- **⊤** (NIL): the absorber, forced by L0. There is no other element that absorbs all inputs.
- **τ** (the judgment element, not in the TC7 but structurally necessary): forced by Kleene. No computation element can serve as judge.
- **g** (CONS): the substrate element, forced by 1-Inert + Branch discrimination. No encoder can serve as inert substrate.
- **η** (CDR): the composition element, forced by Selection + Compose interaction. Cannot merge with Q, E, or ρ.

Three roles are forced by the variational principle — they are separated within the computation category:

- **Q ≠ E** (QUOTE ≠ EVAL): axioms allow Q=E (SAT), but separation doubles the independent compositions involving the constructor/destructor pair.
- **f ≠ ρ** (CAR ≠ COND): axioms allow f=ρ (SAT), but separation gives Branch and first-projection independent rows.
- **ρ ≠ Y** (implicit): axioms allow ρ=Y (SAT), but separation gives the fixed-point combinator its own row.

The correspondence is **structural** (same role inventory) rather than **semantic** (the domains differ). That two systems designed for self-manipulation — one axiom-driven, one engineering-driven — converge on the same seven-role architecture under a principle of maximal expressiveness is a structural observation, not a proof of absolute necessity. Both systems face the same design problem (provide quote/eval, conditional dispatch, pairing/projection, and recursion from a minimal basis) and arrive at the same solution because the constraints admit the same decomposition.

---

## Emergent Roles

Several roles emerge from axiom interaction without being directly axiomatized. Nobody axiomatized "there must be a pair constructor" or "there must be a first projection." These structures emerge from the interaction of branching with substrate.

| Emergent Role | What It Does | Axioms That Force It | Directly Axiomatized? |
|--------------|-------------|---------------------|-----------------------|
| g as pair constructor | Curried pairing: state = g·(g·(c0, c1), pc) | Branch (g is the else-path) + 1-Inert (g is substrate) | **NO** — g is axiomatized as inert substrate and Branch else-path, not as a pair constructor. The pairing behavior is a consequence. |
| f as first projection | Extracts first component of a pair | Branch (f is the if-path) + tester τ (selects which path) | **NO** — f is axiomatized as Branch if-path. That this corresponds to first projection follows from the curried pairing structure of g. |
| η as second projection | Extracts second component | Compose (η·x = ρ·(g·x)) + Branch + Selection (η·ρ = τ) | **NO** — η is axiomatized via Compose and Selection. The second-projection behavior emerges from the interaction. |

This is the non-circular part of the result. The axioms specify structural properties (absorbers, extensionality, Kleene separation, QE inverse, branching, composition, fixed points). The pair/fst/snd structure — which is what makes the system computationally useful — is an emergent consequence, not an input.

---

## What Is Not Proved

- **Variational principle as formal theorem.** The maximal expressiveness principle is demonstrated empirically (monotone cell count, consistent value maximization, fastest reachability). A formal proof that expressiveness is uniquely maximized at full specialization — rather than at some intermediate level — remains open. The monotonicity of cell count (k²) makes this likely, but the interaction with value count is model-dependent.

- **McCarthy correspondence as necessity.** The structural correspondence between Ψ roles and Lisp primitives is an observation. A proof that any finite self-describing algebra satisfying analogous axioms must converge on this role inventory does not exist. The correspondence might be a consequence of the shared design problem (self-manipulation from a minimal basis) rather than a deep mathematical necessity.

- **Formal Lean verification.** The forced-distinct results (Layer 1) are SAT/UNSAT results verified by Z3 at N=12. The rigidity results (Layer 2) are WL-1 + brute-force automorphism checks on extracted models. The expressiveness results (Layer 3) are measurements on extracted models. None are machine-checked in Lean. Lean verification of the forced-distinct claims (at minimum) is desirable.

---

## Reproduction

```bash
# Layer 1: Forced categories (45 pairwise tests + necessity analysis)
uv run python -m ds_search.forced_roles_test

# Layer 2: Universal rigidity (6 collapse levels)
uv run python -m ds_search.collapse_rigidity_test

# Layer 2: Model diversity at maximal collapse
uv run python -m ds_search.collapse_model_count

# Layer 3: Compositional expressiveness
uv run python -m ds_search.compositional_expressiveness
```

---

## Summary

The argument proceeds in three steps:

1. The axioms force five categories. This is a theorem. *(32/45 UNSAT, N=12)*
2. All instantiations are rigid. This is an empirical universal. *(6/6 levels rigid, |Aut|=1)*
3. Full specialization maximizes expressiveness. This is a variational selection. *(49 vs 16 cells, 11 vs 7 values, depth 2 vs 3)*

The result: the axioms force the category structure (theorem); maximal expressiveness selects the specialization among tested collapses (empirical); the specialization matches McCarthy (structural observation). Five categories are proved necessary. Seven roles are the empirical optimum — a formal proof that no intermediate level achieves equal expressiveness remains open.

---

## Scope: What Is Universal and What Is Contingent

The three-layer theorem (forced categories → universal rigidity → variational selection) stands, but its foundation has been refined by axiom archaeology. See [`axiom_inevitability.md`](axiom_inevitability.md) for the full analysis.

**Layers 1 and 2 are robust across axiom systems.** Four independent axiom systems were tested — phenomenological (Ψ), information-theoretic, category-theoretic, and game-theoretic. Three of five behavioral categories (absorbers, testers, encoders) and the Kleene wall (judgment ≠ computation) emerged from all four. The Substrate wall (inert ≠ active) emerged from the three systems that include a substrate commitment. Rigidity is a property of the axiom geometry (Layer 2), not of the specific axiom vocabulary.

**Layer 3 (expressiveness selecting seven roles) depends on all five categories being present.** The variational principle selects among instantiations of the five-category structure. Without the inert category, the computation category absorbs its slot, and the pair-constructor role (g/CONS) has no natural home. The seven-role McCarthy correspondence requires the substrate axiom.

**Three axioms are redundant.** InertProp (D), VV, and 1-Inert are implied by the remaining eight independent axioms {Kleene, PA, QE, E-trans, Branch, Compose, Y, Selection}. This strengthens the non-circularity argument — fewer axioms means less opportunity for indirect encoding.

**The Composition wall has two independent sub-walls.** η vs Q/E is defended by QE + Compose. η vs ρ is defended by Kleene + PA + Selection. The Composition wall is the only wall that genuinely depends on behavioral axioms; the Kleene and Substrate walls follow from row-profile typing alone.

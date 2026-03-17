# Forced Roles Theorem — Honest Characterization

*See also: [`axiom_inevitability.md`](axiom_inevitability.md) for which parts of the forced-roles result are structurally universal and which are axiom-contingent.*

## Summary

The axioms force **partial** distinctness among TC roles, not total. Of the C(10,2) = 45 pairwise role-aliasing tests at N=12, **32 are UNSAT** (forced distinct) and **13 are SAT** (can share one element). The minimum number of distinct elements required by the axioms is **5**, not 7 or 10.

This corrects the previous claim of "21/21 pairs UNSAT" in `tc_merge_test.py`, which tested extensionality (forcing two different indices to have identical rows) rather than role-forcing (assigning both roles to the same index).

## Methodology

For each pair (R1, R2) of the 10 TC roles {⊤, ⊥, τ, Q, E, f, g, ρ, η, Y}:

1. Assign both roles to **the same element index** (R2 gets R1's default index)
2. Apply **all** base axioms faithfully: L0–L8, C (Kleene), D (Inert Propagation), PA, VV, QE, E-transparency, 1-Inert, Branch, Compose, Y, Selection
3. Apply **both** role constraints to the shared index (e.g., if one role is a tester and the other is an encoder, the shared index must satisfy both — which is impossible)
4. Check SAT/UNSAT at N=12 (minimum size for all axioms)

If a clause becomes trivially False under aliasing (e.g., Branch's `f≠g` discrimination clause when f=g), that **is** the proof — the solver correctly keeps this clause.

## Why the Previous Test Was Wrong

`tc_merge_test.py` tested merging by forcing `dot[a][j] == dot[b][j]` and `dot[i][a] == dot[i][b]` for two different indices a, b. This is UNSAT for **any** two distinct indices due to the Ext axiom (all rows must be distinct), regardless of any role axioms. Confirmed: merging indices 2 and 3 under Level 0 alone (absorbers + Ext, zero role axioms) is already UNSAT.

## Results

### Forced-Distinct Matrix

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

X = forced distinct (UNSAT), · = can merge (SAT)

### Mergeable Pairs (13 SAT)

| Pair | Notes |
|------|-------|
| ⊤=⊥ | Both absorbers — no behavioral axiom distinguishes them |
| Q=E | QE cancellation still works when both roles on same index |
| Q=f | Q as branch-if — compatible roles |
| Q=ρ | Q as branch element |
| Q=Y | Q as Y-combinator |
| E=f | E as branch-if |
| E=ρ | E as branch element |
| E=Y | E as Y-combinator |
| f=ρ | Branch-if as branch element |
| f=η | Branch-if as compose element |
| f=Y | Branch-if as Y-combinator |
| ρ=Y | Branch element as Y-combinator |
| η=Y | Compose element as Y-combinator |

### Layer-by-Layer Analysis

**Layer 0: Absorbers (⊤, ⊥)**
- ⊤ ≠ ⊥: **SAT** — the absorber axioms (`dot[0][j]=0`, `dot[1][j]=1`) are index-based, not role-based. No behavioral axiom explicitly requires ⊥ to differ from ⊤. When aliased, ⊥ simply refers to the same absorber row.
- ⊤ ≠ {all non-absorbers}: **UNSAT** — absorber rows are constant; non-absorber role constraints (tester/encoder/inert) require non-constant behavior.
- ⊥ ≠ {all non-absorbers}: **UNSAT** — same reason.

**Layer 1: Tester (τ)**
- τ ≠ {⊤, ⊥}: UNSAT — tester requires boolean row but non-absorber.
- τ ≠ {all encoders}: UNSAT — Kleene barrier: a row cannot be simultaneously all-boolean (tester) and have ≥2 distinct non-boolean outputs (encoder).
- τ ≠ g: UNSAT — tester vs inert role constraints are incompatible.
- τ is forced distinct from **all** other roles.

**Layer 2: Encoder/Inert Separation (Q, E vs g)**
- Q ≠ g, E ≠ g: UNSAT — encoder requires ≥2 distinct non-boolean outputs; inert has no such pair. The Kleene barrier applies.
- Q=E: **SAT** — QE cancellation (`E·(Q·x)=x` and `Q·(E·x)=x` on core) is satisfiable with a single element acting as its own inverse.
- g ≠ {all encoders}: UNSAT — g is forced into its own category.

**Layer 3: Branch Discrimination (f vs g)**
- f ≠ g: UNSAT — the Branch axiom includes `Or([dot[f][j] ≠ dot[g][j] for j in core])`. When f=g this becomes `Or(False...)` = False → trivially UNSAT.
- f can merge with Q, E, ρ, η, Y — all encoder-type roles.

**Layer 4: Compose/Selection Constraints (η)**
- η ≠ Q: UNSAT — Selection forces `η·ρ = τ`. Combined with Compose (`η·x = ρ·(g·x)`) and QE, this creates constraints Q cannot satisfy when aliased to η.
- η ≠ E: UNSAT — same interaction.
- η ≠ ρ: UNSAT — if η=ρ, then Compose becomes `ρ·x = ρ·(g·x)` on core, which combined with Selection `ρ·ρ = τ` creates contradictions.
- η can merge with f and Y only.

### Minimum Distinct Elements

The forced-distinct graph has chromatic number **5**. One valid partition:

| Abstract Element | Roles |
|-----------------|-------|
| Element 0 | ⊤, ⊥ |
| Element 1 | τ |
| Element 2 | Q, E, f, ρ, Y |
| Element 3 | g |
| Element 4 | η |

This means a valid Ψ algebra could in principle implement all 10 TC roles using only 5 distinct elements (plus additional elements to fill out the table to N≥12).

### Necessity Analysis (which axiom group forces each distinction?)

For each UNSAT pair, removing axiom groups one at a time identifies which are necessary:

| Pair | Necessary Group(s) | Notes |
|------|-------------------|-------|
| ⊤=τ | Kleene, Selection, Roles | Multiple groups each sufficient |
| ⊤=Q | (interaction) | No single group — requires combination |
| ⊤=E | (interaction) | No single group |
| ⊤=f | Roles | Absorber can't be encoder |
| ⊤=g | Roles | Absorber can't be inert |
| ⊤=ρ | (interaction) | No single group |
| ⊤=η | (interaction) | No single group |
| ⊤=Y | (interaction) | No single group |
| ⊥=τ | Kleene, Selection | |
| ⊥=Q | (interaction) | |
| ⊥=E | (interaction) | |
| ⊥=f | Roles | |
| ⊥=g | Roles | |
| ⊥=ρ | (interaction) | |
| ⊥=η | (interaction) | |
| ⊥=Y | (interaction) | |
| τ=Q | Roles | Tester can't be encoder |
| τ=E | Roles | |
| τ=f | Roles | |
| τ=g | Roles | Tester can't be inert |
| τ=ρ | Roles | |
| τ=η | Roles | |
| τ=Y | Roles | |
| Q=g | Roles | Encoder can't be inert |
| Q=η | QE, Compose, Roles | Three independent paths |
| E=g | Roles | |
| E=η | QE, Compose, Roles | Three independent paths |
| f=g | (interaction) | Branch discrimination + role interaction |
| g=ρ | Roles | |
| g=η | Roles | |
| g=Y | Roles | |
| ρ=η | Kleene, PA, Selection, Roles | Four independent paths |

Key observations:
- **Roles** is the most common necessity — the tester/encoder/inert classification creates a hard barrier
- **f=g** requires interaction (the Branch discrimination clause `Or(f·j ≠ g·j)` becomes False when f=g, but removing Branch alone doesn't help because other constraints also force distinctness)
- **Q=η and E=η** have three independent reasons: QE cancellation, Compose, and Roles
- **ρ=η** has four independent reasons: the most over-determined forced distinction among encoders

## Implications

1. **The canonical 7-element TC construction is one point in a space.** The axioms don't force 7 distinct elements — they force 5. Alternative constructions with role-sharing are possible.

2. **The inert element (g) is maximally isolated.** It cannot merge with any other role. This reflects its unique algebraic status: the only non-absorber whose row has no pair of distinct non-boolean values.

3. **τ (tester) is also maximally isolated.** The Kleene barrier creates an absolute wall between tester and encoder/inert roles.

4. **Encoder roles are highly fungible.** {Q, E, f, ρ, Y} can all potentially share a single element, with η being the only encoder forced somewhat apart (can only merge with f or Y).

5. **⊤ and ⊥ are interchangeable** from the behavioral axioms' perspective. No axiom explicitly references ⊥ by index — it's just "the other absorber."

## Reproduction

```bash
uv run python -m ds_search.forced_roles_test          # full analysis with necessity
uv run python -m ds_search.forced_roles_test --quick   # skip necessity analysis
```

## Further Reading

This document presents the raw SAT data (Layer 1 of the argument). The complete three-layer argument — forced categories → universal rigidity → distinctness axiom (with expressiveness justification) → McCarthy correspondence — is in [`forced_roles_theorem.md`](forced_roles_theorem.md).

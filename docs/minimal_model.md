# The Minimal Self-Grounded Distinction Structure

## Summary

Six independently motivated axioms, applied bottom-up without reference to
any target algebra, force a unique structural skeleton at minimum size N=6.
The resulting algebra is fully producible (every element is constructible),
fully separable (every element is identifiable), and exhibits all four
ontological categories of the Distinction Structures framework. It is the
smallest algebra satisfying all six axioms simultaneously.

## The Axiom Ladder

Each axiom is stated in natural language (ontological reading) and in
algebraic terms. The axioms are cumulative: each level includes all
previous levels.

### Level 0 — Grounded Binary Distinction

**Ontological:** There exist exactly two absolute verdicts — affirmation
and negation — that are invariant under all contexts.

**Algebraic:** The magma (D, ·) has exactly two left-absorbers: elements
⊤ and ⊥ satisfying ⊤·y = ⊤ and ⊥·y = ⊥ for all y. No other element is
a left-absorber. All rows are distinct (Ext).

**What it forces:** A finite algebra with a boolean substratum. The two
absorbers serve as the truth values of the framework.

*Minimum N = 3.*

### Level 1 — Distinction Exists

**Ontological:** There exists at least one act of distinction — an
operation that, given any input, renders a boolean verdict (A2: every
Context sustains at least one actual Distinction).

**Algebraic:** ∃ element t ∉ {⊤, ⊥} such that ∀ y, t·y ∈ {⊤, ⊥}.

**What it forces:** A non-trivial tester. The framework has descriptive
capacity — it can say yes or no about things.

*Minimum N = 3.*

### Level 2 — Synthesis Exists

**Ontological:** There exists at least one act of synthesis — an operation
that produces structured, non-boolean outputs, mapping inputs to
qualitatively different kinds of results (A6 + A7': Synthesis is total and
can produce genuine novelty).

**Algebraic:** ∃ element e such that e produces at least two distinct
non-boolean outputs: ∃ y₁ ≠ y₂ with e·y₁, e·y₂ ∉ {⊤, ⊥} and
e·y₁ ≠ e·y₂.

**What it forces:** An encoder. The framework doesn't just classify — it
builds new representations.

*Minimum N = 4.*

### Level 3 — Generative Synthesis

**Ontological:** Synthesis produces further capacity for synthesis — the
framework generates new generative capacity, not only new distinctions. Two
independent synthetic perspectives exist with different output profiles
(multiple Contexts with distinct Distinction-sets, per A4).

**Algebraic:** Two independent encoders e₁, e₂ with different non-boolean
output profiles. At least one encoder produces another encoder: ∃ e, y
such that e·y = e' where e' is also an encoder.

**What it forces:** Encoder-encoder chains. The algebra is not flat — its
synthetic operations compose into deeper synthetic operations.

*Minimum N = 5.*

### Level 4 — Open Closure (Actuality as Genuine Selection)

**Ontological:** The descriptive machinery (distinctions, contexts,
synthesis) does not exhaust what exists. There is something outside the
framework's descriptive reach — substrate that is neither boolean verdict,
nor test, nor synthesis, but that the framework's own operations produce
(A5: Actuality is a genuine selection, not everything possible is actual).

**Algebraic:** The computational core {absorbers ∪ testers ∪ encoders} is
not closed under ·. There exist core elements x, y such that x·y is inert
(neither absorber, tester, nor encoder).

**What it forces:** An inert element — genuine substrate outside the
descriptive machinery, produced by the machinery itself.

*Minimum N = 6.*

### Level 5 — Compositional Separation (Self-Model)

**Ontological:** The framework can identify everything it contains through
its own operations. Every element has a unique behavioral signature
discoverable by composing at most two operations. Distinction is complete —
the framework can name everything within it (Ext applied compositionally).

**Algebraic:** For all i ≠ j, there exists a depth-≤-2 left-application
chain distinguishing them: ∃ a with a·i ≠ a·j, or ∃ a, b with
b·(a·i) ≠ b·(a·j).

**What it forces:** In practice, nothing beyond Level 4 — the Level 4
models already satisfy this. Compositional separation emerges as a free
consequence of the structural constraints, not as an independent
requirement.

*Minimum N = 6 (no change).*

## The Minimal Model (N=6)

```
     ⊤   ⊥   t   e₁  p   e₂
   ----------------------------
 ⊤|  ⊤   ⊤   ⊤   ⊤   ⊤   ⊤
 ⊥|  ⊥   ⊥   ⊥   ⊥   ⊥   ⊥
  t|  ⊤   ⊥   ⊥   ⊥   ⊥   ⊥
 e₁| e₁   t   p   t   ⊥  e₂
  p|  ⊥   t   ⊤   ⊥   ⊥   ⊥
 e₂|  p   ⊥   t   p  e₁  e₂
```

Element key:
- **⊤** (element 0) — TOP, the affirmative absorber
- **⊥** (element 1) — BOT, the negative absorber
- **t** (element 2) — the sole tester: "is it ⊤?"
- **e₁** (element 3) — encoder, the builder
- **p** (element 4) — inert substrate
- **e₂** (element 5) — encoder, the navigator

### Ontological Reading of Each Element

**⊤ and ⊥ — The Boolean Ground.** These are the two possible outcomes of
any distinction: affirmation and negation. They absorb all input — applying
⊤ to anything yields ⊤, applying ⊥ to anything yields ⊥. They are the
bedrock of the framework, the termination points of all inquiry. In the DS
ontology, they correspond to the two possible values of any Distinction
within a Context.

**t — The Act of Distinction.** The single tester partitions the universe
into {⊤} and {everything else}. It is the most primitive possible
distinction: present/absent, marked/unmarked. It accepts only ⊤ (returning
⊤) and rejects all else (returning ⊥). In the DS ontology, t is a
Distinction — the simplest one, the distinction between affirmation and
everything that is not affirmation.

**e₁ — The Builder (Synthesis as Construction).** Encoder e₁ is the
richest element in the algebra. Its row [e₁, t, p, t, ⊥, e₂] touches all
four role categories:
- e₁·⊤ = e₁ (self-reference: applying the builder to affirmation returns
  the builder itself)
- e₁·⊥ = t (applying the builder to negation produces the tester —
  synthesis creates distinction)
- e₁·t = p (applying the builder to the tester produces the substrate —
  synthesis acting on distinction yields actuality)
- e₁·e₁ = t (the builder applied to itself yields a distinction)
- e₁·e₂ = e₂ (the builder applied to the navigator yields the navigator —
  synthesis preserves independent synthesis)

In the DS ontology, e₁ is Synthesis in its constructive mode. It builds
the framework's own components: it produces the tester (Distinction), the
substrate (Actuality), and the other encoder (independent Synthesis).

**p — The Substrate (Actuality as Ground).** The inert element is produced
by the core but is not part of the descriptive machinery. Its row
[⊥, t, ⊤, ⊥, ⊥, ⊥] is nearly boolean — it is almost a tester, but not
quite (p·⊥ = t breaks the pattern). When acted upon, most operations
collapse it to ⊥ — it is the default, the background, what you get when
structure runs out.

But p is not nothing. Two critical facts:
1. p·⊥ = t — the substrate, when probed with negation, yields
   distinction. Actuality contains the seed of Distinction.
2. e₂·p = e₁ — the navigator, applied to the substrate, recovers the
   builder. Synthesis can extract further Synthesis from Actuality.

In the DS ontology, p is the Actuality boundary — the element that
instantiates A5 (selectivity). The descriptive machinery produces it but
cannot fully describe it. It sits outside the core yet participates in
generative cycles.

**e₂ — The Navigator (Synthesis as Exploration).** Encoder e₂ has row
[p, ⊥, t, p, e₁, e₂]. Where e₁ builds, e₂ navigates:
- e₂·⊤ = p (applying the navigator to affirmation yields substrate — the
  navigator finds what lies beneath)
- e₂·t = t (the navigator preserves distinction)
- e₂·p = e₁ (the navigator recovers the builder from substrate — the
  critical feedback loop)
- e₂·e₂ = e₂ (self-reference: the navigator is a fixed point of itself)

In the DS ontology, e₂ is Synthesis in its exploratory mode. It maps
through the substrate and recovers constructive capacity. The cycle
e₁ → e₂ → (via p) → e₁ is the algebra's generative engine.

### Structural Properties

| Property | Status |
|---|---|
| Full producibility | YES — every element is in the image of · |
| Full left-separation | YES — all rows unique (Ext) |
| Full right-separation | YES — all columns unique |
| Compositional separation | YES — all pairs separated at depth 1 |
| Tester constructibility | YES — t is produced by e₁·⊥, e₁·e₁, e₂·t |
| Encoder-encoder chains | YES — e₁·e₂ = e₂, e₂·p = e₁, e₁·⊤ = e₁ |
| Open closure | YES — e₁·t = p, e₂·⊤ = p, e₂·e₁ = p |
| Inert feedback | YES — p·⊥ = t, e₂·p = e₁ |
| Self-identification | e₁·⊤ = e₁, e₂·e₂ = e₂ (encoders self-identify) |
| Associativity | NO — 73/216 triples violate |
| Subalgebras | {⊤,⊥}, {⊥,t}, {⊥,e₂}, {⊤,⊥,t}, {⊥,t,e₂}, and others |

### The Generative Cycle

The algebra's key structural feature is a three-element cycle through all
non-boolean roles:

```
  e₁ ──(e₁·e₂)──→ e₂ ──(e₂·p)──→ e₁
       enc              enc
        ↑                |
        └──── p ←────────┘
             (e₁·t)    (e₂·⊤)
              inert
```

This cycle is the engine of the algebra. Synthesis (e₁) produces
Synthesis (e₂). Synthesis (e₂) acts on Actuality (p) to recover
Synthesis (e₁). Synthesis (e₁) acts on Distinction (t) to produce
Actuality (p). Every non-boolean role participates, and the cycle is
closed. The algebra is self-sustaining.

The tester t enters the cycle through e₁·⊥ = t (synthesis produces
distinction from negation) and p·⊥ = t (actuality yields distinction when
probed). Every element is both a product of the cycle and a participant
in it.

### Comparison with Δ₁

| Property | N=6 Minimal | Δ₁ (N=17) |
|---|---|---|
| Absorbers | 2 | 2 |
| Testers | 1 | 4 |
| Encoders | 2 | 10 |
| Inert | 1 | 1 |
| Full producibility | YES | NO (4 unreachable) |
| Column uniqueness | YES | NO (8 collisions) |
| Tester separation | 2 classes | 5 classes |
| Enc→enc chain depth | 1 | 2 |
| Self-identifying | 4/6 (67%) | 9/17 (53%) |

The minimal model and Δ₁ represent two different design points:

**The N=6 model is fully self-grounded.** Every element is producible,
every element is separable, and the descriptive machinery accounts for all
of its own parts. It achieves this at the cost of discriminatory power —
one tester can only make one binary cut.

**Δ₁ is richer but has ungrounded primitives.** Four elements (E_I, E_D,
E_M, E_Σ — the perspective encoders) are never produced by any operation.
They are axiomatically given, not derivable. This gives Δ₁ more
descriptive power (4 testers, 10 encoders) but at the cost of
self-grounding: the algebra cannot account for the existence of its own
fundamental perspectives.

This trade-off may be intrinsic. The four unreachable elements in Δ₁ are
precisely the *perspective encoders* — the lenses through which the
algebra views itself. A system may not be able to both *use* a perspective
and *derive* it from within. The minimal model avoids this by having only
two encoders that are mutually derivable, but this limits it to a single
perspective rather than multiple independent viewpoints.

## The Axioms as Ontological Commitments

Reading the six effective axioms as ontological commitments:

1. **Binary ground** — Reality admits yes/no verdicts that are stable
   across all contexts.
2. **Distinction exists** — At least one act of discrimination is
   possible.
3. **Synthesis exists** — Composition produces structured results, not
   only verdicts.
4. **Generative synthesis** — Synthesis compounds: new synthetic capacity
   can be produced from existing synthetic capacity. Multiple independent
   perspectives exist.
5. **Actuality as selection** — The descriptive machinery does not exhaust
   what exists. There is substrate outside the framework's reach that the
   framework nonetheless produces.
6. **Compositional completeness** — Everything the framework contains can
   be identified through the framework's own operations. (This is a free
   consequence of axioms 1–5 at minimum size.)

These six commitments force a minimum of 6 elements and a unique role
structure: 2 absorbers, 1 tester, 2 encoders, 1 inert. The qualitative
architecture — boolean ground, distinction, synthesis, actuality — emerges
from the axioms rather than being stipulated.

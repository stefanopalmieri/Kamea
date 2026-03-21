---

**Explore whether the Ψ axiom system is missing something — or whether alternative axiom paths converge on the same structure.**

This is the hardest open question in the project. The current axioms produce seven roles matching McCarthy's Lisp primitives. But a critic can ask: did the axioms encode Lisp indirectly? Are the roles forced by self-description, or by the particular axiom vocabulary chosen?

You have full access to the repo. Read `docs/forced_roles_theorem.md`, `docs/psi_framework_summary.md`, and the README thoroughly before starting. Understand the current axiom system, what it forces, and what it leaves free.

**Three directions to explore. Do whichever ones seem most productive.**

**Direction 1: Axiom archaeology — which axioms are doing the real work?**

The current system has ~15 axioms (L0-L8, C, D, PA, VV, QE, 1-Inert, E-Transparency, Branch, Compose, Y, Selection). Some of these might be redundant — derivable from others. Some might be doing more work than they appear to.

For each axiom: remove it, run the SAT search at N=12, and characterize what changes. Not just "is it still SAT?" but: do the five forced categories survive? Do the three hard walls (Kripke, inert, Selection+Compose) survive? Does rigidity survive? Which role merges become newly possible?

Build a dependency graph: which axioms depend on which others for their consequences? Are there axioms that are consequences of combinations of other axioms?

The goal: find the MINIMAL axiom set that still forces the five categories and three walls. If you can get the same forced structure from fewer axioms, the remaining axioms are engineering choices, not structural necessities. That sharpens the boundary between "what self-description requires" and "what this particular formalization adds."

**Direction 2: Alternative axiom systems — different paths to the same destination?**

Design a DIFFERENT axiom system for self-describing finite algebras. Don't start from the Ψ axioms. Start from a different intuition entirely.

Some starting points to try:

Approach A — Information-theoretic: Instead of roles (absorber, tester, encoder, inert), axiomatize in terms of information flow. An element's row is a function from N to N. Some functions are constant (information-destroying). Some are injective (information-preserving). Some are surjective (information-covering). Require that the algebra contains at least one of each type, plus an inverse pair. See what structure emerges.

Approach B — Category-theoretic: Think of the Cayley table as a single-object category where elements are morphisms. Require that the category has a retraction pair (Q/E), a product with projections, and an initial/terminal object. These are standard categorical concepts that have nothing to do with Lisp. See if the resulting algebra has the same role structure.

Approach C — Game-theoretic: Think of elements as strategies in a game. An absorber is a dominant strategy. A tester is a strategy that classifies opponents into two types. An encoder is a strategy that transforms opponents. Require that the game has enough strategic diversity for one player to identify all strategies from interaction alone (discoverability). See what falls out.

For each approach: encode the axioms in Z3 at N=12. Check SAT. If SAT, classify the elements into roles. Do the same five categories appear? Do the same three walls hold? Do seven roles emerge under expressiveness maximization?

If YES for any approach: that's strong evidence the roles are structurally inevitable, not axiom-dependent. Document which roles appeared, which walls held, and how the alternative axioms relate to the Ψ axioms.

If NO: that's equally valuable. Document what's different. What roles appear instead? What walls are absent? What does self-description look like under different axioms? The divergence tells you which aspects of the Ψ result are universal and which are axiom-specific.

**Direction 3: What's missing — axioms the current system might need.**

The current system has 192/256 free cells at N=16. That's a lot of freedom. Maybe the axioms are UNDER-constraining. What additional axioms would be natural and independently motivated?

Some candidates to test:

Associativity of composition: does `dot(a, dot(b, c)) = dot(dot(a, b), c)` hold for any interesting subset of elements? Full associativity is UNSAT (known). But associativity restricted to encoders, or to the QE pair, might be SAT and might pin additional cells.

Distributivity: does `dot(a, dot(b, c))` relate to `dot(dot(a, b), dot(a, c))` for any elements? If so, for which? This would connect the algebra to ring-like or lattice-like structure.

Idempotent completion: for each idempotent element (x·x = x), does it act as a local identity or projection on some subset? This would give the algebra more categorical flavor.

Absorption laws: do any pairs (a, b) satisfy `dot(a, dot(b, a)) = a` or `dot(b, dot(a, b)) = b`? These are lattice absorption laws. Their presence or absence tells you whether the algebra has lattice-like substructure.

For each candidate: check SAT at N=12 and N=16. If SAT, how many cells does it pin? Does it reduce the model count? Does it change the forced categories or the wall structure? If UNSAT, that's a new universal theorem — document it.

**What to report:**

For each direction, produce a summary document with:

1. What you tried (axiom removals, alternative systems, new axioms)
2. What happened (SAT/UNSAT results, role classifications, wall survival)
3. What it means (which aspects of the current result are robust, which are fragile)
4. Surprises (anything unexpected — new walls, unexpected merges, alternative role structures)

The honest finding might be: "the current axioms are one of several paths to the same structure" (strengthens inevitability). Or: "the current axioms are the only path — alternatives produce different structures" (weakens inevitability but clarifies what's axiom-specific). Or: "the current axioms are missing something — adding X produces a cleaner, more constrained system" (improves the axiom system). All three outcomes are valuable.

**Don't try to confirm the existing result. Try to break it.** The strongest evidence for inevitability comes from failing to find alternatives, not from succeeding in confirming what we already have.

---

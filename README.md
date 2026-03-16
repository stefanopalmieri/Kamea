# Kamea

**Seven axiom-forced elements. One Turing-complete term algebra. 130+ Lean theorems. Zero `sorry`.**

*The axioms force seven algebraic roles whose term algebra — like combinatory logic over {S, K} — is Turing complete. The boundary between what the axioms determine and what they leave free is precisely the boundary between structure and actuality.*

<p align="center">
  <img src="melencolia.png" width="250" alt="Albrecht Dürer — Melencolia I (1514)" />
</p>
<p align="center"><sub>In loving memory of Boba</sub></p>

## Quick Start

```bash
git clone https://github.com/stefanopalmieri/Kamea.git && cd Kamea

python3 psi_lisp.py examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp
```

```
=== PSI REFLECTIVE TOWER (Defunctionalized CPS) ===
Layer 3: User programs (fib, fact)
Layer 2: CPS meta-circular evaluator (psi_metacircular.lisp)
Layer 1: Base evaluator (psi_lisp.py)
Layer 0: Cayley table (256 bytes)

--- Level 0: Computation (meta-evaluated) ---
Defining fib and computing fib(8)... 21
Defining fact and computing fact(10)... 3628800

--- Level 1: Ground Verification (Cayley table probes) ---
Absorber laws (TOP/BOT): ALL HOLD
Table health: ALL INVARIANTS HOLD

--- Level 2b: Continuation Chain Inspection ---
Reify inside (let ((x (reify))) x):
  Chain depth: 3
  Frame 0 tag = k-let-bind? YES
  Frame 1 tag = k-let-body? YES
  Frame 2 tag = k-id? YES

--- Level 2c: Continuation Modification (rewriting the future) ---
K-IF BRANCH SWAP — the definitive 3-Lisp demo:
  Without modification: (if 1 42 99) → 42
  With branch swap: (if 1 42 99) → 99
  CONFIRMED: Program rewrote its own if-branches.
```

A program that can inspect its own continuation, where the continuation is data built from algebraically verified atoms, running on a table whose rigidity, discoverability, and actuality irreducibility are Lean-proved, implementing a Lisp whose seven primitive roles are axiom-forced and whose term algebra is Turing complete.

Smith's 3-Lisp (1984) had the reflective tower but no ground. The levels went down forever — interpreter interpreting interpreter interpreting interpreter. There was no bottom. Each level's meaning depended on the level below, and there was no foundation. Here, the tower terminates at a 16×16 Cayley table — 256 bytes whose algebraic properties are machine-checked. The program verifies the table before trusting the evaluator. There is nothing beneath the table to worry about. It IS the algebra, not an implementation of it.

The demo: a defunctionalized CPS meta-circular evaluator — Ψ-Lisp interpreting itself with inspectable continuations — computes fibonacci, verifies the Cayley table it runs on, then reifies its own continuation as walkable data, navigates to a pending `k-if` frame, swaps the then/else branches, reflects, and takes the opposite branch from what the source code says. The program rewrites its own future. Everything below — axioms, theorems, phenomenology — is context for understanding what you just saw.

```bash
python3 psi_repl.py                                        # interactive REPL
python3 examples/psi16_corrupted_host_demo.py               # watch one wizard heal another
cd kamea-rs && cargo run --release -- repl                   # Rust REPL (~25x faster)
cd kamea-rs && cargo run --release -- run \                  # Rust reflective tower
  examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp
```

### Compile to Native

```bash
python3 psi_supercompile.py examples/psi_counter_known.psi > /tmp/opt.psi
python3 psi_transpile.py /tmp/opt.psi > /tmp/counter.c
gcc -O2 -I. -o /tmp/counter /tmp/counter.c
/tmp/counter                                               # native speed, zero table lookups
```

---

Seven axiom-forced elements — ⊤, Q, E, f, g, η, ρ — generate a term algebra Ψ∗ (finite binary trees with these atoms as leaves) that simulates 2-counter machines and is therefore Turing complete (Minsky 1961). The finite algebra itself is decidable; the computational universality lives in the term algebra over it, as with combinatory logic or lambda calculus. These elements exist in every model of the Ψ axiom class: they are not specific to one table but forced by the axioms themselves. A stepped 2-counter machine simulation using only these elements matches a reference interpreter trace-for-trace on all test programs (`psi_star.py`). The structural proofs (rigidity, discoverability, actuality irreducibility, no right identity, card ≥ 4) are machine-checked in Lean 4 with zero `sorry`. Formal Lean verification of the TC simulation remains open.

The full 16×16 table Ψ₁₆ᶠ adds counter arithmetic, IO, and a Y-combinator — all verified by 130+ Lean theorems. But the computational core is 7 elements, not 16.

These seven roles — ground element, constructor/destructor pair, pair-builder with two projections, and conditional — correspond closely to the minimal symbolic manipulation primitives identified by McCarthy (1960):

| Ψ | Lisp | Role |
|---|------|------|
| ⊤ | NIL | Empty / base case |
| Q | QUOTE | Freeze a term (constructor) |
| E | EVAL | Unwrap / interpret (destructor) |
| g | CONS | Build a pair |
| f | CAR | First projection |
| η | CDR | Second projection |
| ρ | COND | Conditional branch |

The correspondence is structural (same role inventory) rather than semantic (the domains differ: Ψ operates on magma elements, Lisp on symbolic lists). That two systems designed for self-manipulation — one axiom-driven, one engineering-driven — converge on the same seven-role architecture is a noteworthy observation, not a proof of necessity.

---

## Why It Matters

Any system that can inspect and modify its own components needs a representation layer: some way to quote a piece of itself, examine it, and act on the result. In practice this is a runtime, a reflection API, a JIT compiler — machinery bolted on top, with no guarantee that the representation is faithful or complete.

The Ψ framework asks whether that machinery can be *intrinsic*. Can a finite algebraic structure — nothing but a set of elements and a binary operation — contain its own quote/eval pair, conditional branching, recursion, arithmetic, and IO, all realized within a single binary operation table? And can the language that emerges from this table interpret itself — can a program written in it verify the table, capture its own continuation, and modify its own future, all within the same algebra?

The answer is yes, and it fits in a 16×16 table. A 350-line defunctionalized CPS meta-circular evaluator runs fibonacci through a Lisp written in itself, after verifying the 256-byte table it runs on — and a program running inside it can inspect its own continuation chain, swap the branches of a pending `if`, and take the opposite path from what the source code says.

The primary contribution is methodological: a demonstration that axiom-driven SAT search combined with Lean verification can systematically explore the space of self-describing finite structures, producing both universal theorems about the axiom class and specific verified models. The specific algebra Ψ₁₆ᶠ is one output of this methodology. The universal theorems — forced rigidity, actuality irreducibility, separation of judgment and synthesis — are the more durable results. Whether these properties translate to practical self-verifying systems is an open question.

**Formally established:**
- A 16-element model exists satisfying all axioms simultaneously `[Lean]`
- The axiom class forces exactly 2 absorbers, Kleene separation, WL-1 rigidity, and 4-element constructibility `[Lean]`
- Automorphism rigidity: every injective endomorphism is the identity `[Lean]`
- All 16 elements behaviorally identifiable from 4 probes (discoverability) `[Lean]`
- Actuality irreducibility: twin models agree on structure, disagree on tester assignment `[Lean]`
- No right identity in any model satisfying role axioms L0–L3 `[Lean]`
- Card ≥ 4 from role axioms (tight: 4-element countermodel exists) `[Lean]`
- Tester cells are completely free across all tested sizes `[SAT]`
- Defunctionalized CPS meta-circular evaluator: Ψ-Lisp interpreting Ψ-Lisp with inspectable tagged continuations (14 continuation types, zero lambdas in control flow), handles arithmetic, conditionals, lambda, let, defun, cond, progn, recursive closures `[Empirical]`
- Reify captures continuation (tagged data structure) + environment as first-class inspectable Ψ-Lisp value; reflect installs modified state including modified continuations `[Empirical]`
- Continuation chain walkable as data: `k-walk`, `k-depth`, `k-next`, `describe-continuation` `[Empirical]`
- K-IF branch swap: program reifies, navigates to k-if frame, swaps then/else branches, reflects — if takes opposite branch from source code `[Empirical]`
- 3-level reflective tower: compute → verify ground → inspect/modify continuations → branch swap `[Empirical]`
- All 16 elements recoverable from shuffled oracle, 3 methods, 100% on 1000 seeds `[Empirical]`
- Pure Ψ-Lisp recovery spell: ~62 probes, IO-only, identifies all 16 elements `[Empirical]`
- Term algebra Ψ∗ over 7 axiom-forced elements generates a TC system (stepped 2CM simulation matches reference interpreter on all test programs). The finite algebra is decidable; TC lives in the term algebra + evaluation semantics, as with combinatory logic over {S, K} `[Empirical]` — formal Lean verification open
- TC minimality (canonical construction): all 7 TC roles pairwise forced distinct (21/21 merge attempts UNSAT); alternative constructions with fewer elements remain open `[SAT]`

**Not formally established:**
- Uniqueness or optimality of Ψ₁₆ᶠ among satisfying models `[Open]`
- Symmetric impossibility as a general theorem `[Open]`

Claim status is tracked in [`CLAIMS.md`](CLAIMS.md) (`Lean-proved`, `Empirical`, `Conjecture/Open`).

### How to Read This Repo

1. [`psi_repl.py`](psi_repl.py) — Interactive Ψ-Lisp REPL
2. [`examples/psi_metacircular.lisp`](examples/psi_metacircular.lisp) — Defunctionalized CPS meta-circular evaluator with inspectable continuations
3. [`examples/psi_reflective_tower.lisp`](examples/psi_reflective_tower.lisp) — Three-level reflective tower: compute → verify table → inspect/modify continuations → branch swap
4. [`examples/psi_recovery_spell.lisp`](examples/psi_recovery_spell.lisp) — Black-box recovery as pure Ψ-Lisp (the "spell" cast by the wizard)
5. [`examples/psi16_corrupted_host_demo.py`](examples/psi16_corrupted_host_demo.py) — Animated TUI: watch one wizard heal another using the spell
6. [`psi_star.py`](psi_star.py) — Turing-completeness proof: 2CM simulation via 7 axiom-forced elements (run it)
7. [`psi_lisp.py`](psi_lisp.py) — Mini-Lisp → Ψ∗ transpiler (McCarthy 1960 conventions)
8. [`kamea-rs/`](kamea-rs/) — Rust emulator + WASM browser debugger (~25x faster than Python)
9. [`docs/psi_framework_summary.md`](docs/psi_framework_summary.md) — full axiom search results and Cayley tables
10. [`DistinctionStructures/Psi16Full.lean`](DistinctionStructures/Psi16Full.lean) — 83 operational theorems + rigidity/discoverability/irreducibility proofs
11. [`psi_blackbox.py`](psi_blackbox.py) — Black-box recovery (3 methods, 100% on 1M seeds)
12. [`CLAIMS.md`](CLAIMS.md) — what is proved, what is empirical, what is open
13. [`psi_supercompile.py`](psi_supercompile.py) — Partial evaluator: constant folding + QE cancellation + branch elimination + let propagation + lambda inlining
14. [`psi_transpile.py`](psi_transpile.py) — Supercompiled Ψ∗ → C transpiler
15. [`psi_runtime.h`](psi_runtime.h) — C runtime: 256-byte Cayley table + inline dot function

---

## 1. The Ψ Framework

What is the simplest finite structure that can identify its own components through its own operation?

The Ψ framework answers this by stacking axioms on a finite magma (N-element set with binary operation `dot`). Each axiom forces a specific capability — absorbers for boundaries, testers for judgment, encoders for synthesis, quote/eval for reflection, branching for control flow — until the structure is self-describing: it contains enough internal structure to encode, decode, and operationally recover its components. (Here "self-describing" means the algebra contains distinguished elements behaving as an internal representation and evaluation interface for elements of the same algebra.)

### The Axiom System

**Structural Ladder (L0–L8)** — forces the basic role architecture:

| Level | Name | What It Forces |
|-------|------|----------------|
| L0 | Absorber ⊤ | `∀x: 0·x = 0` |
| L1 | Absorber ⊥ | `∀x: 1·x = 1` |
| L2 | Extensionality | All rows distinct |
| L3 | Tester exists | At least one non-absorber has boolean outputs |
| L4 | Encoder exists | At least one element synthesizes (≥2 distinct non-boolean outputs) |
| L5 | No extra absorbers | Only ⊤ and ⊥ are absorbers |
| L6 | No extra testers | At most 2 testers among non-absorbers |
| L7 | Inert exists | At least one "substrate" element |
| L8 | Encoder separation | ≥2 encoders with distinct output sets |

**Operational Axioms** — force specific computational capabilities:

| Axiom | What It Forces |
|-------|----------------|
| **C (Kleene)** | Only testers can produce boolean outputs on non-absorbers |
| **D (Inert Propagation)** | Inert elements preserve non-absorber status |
| **PA (Power-Associativity)** | `(x·x)·x = x·(x·x)` for all x |
| **VV (Inert Self-Application)** | Inert self-application yields a tester or encoder |
| **QE (Quote/Eval)** | `E·(Q·x) = x` and `Q·(E·x) = x` on core — mutual inverses |
| **1-Inert** | Exactly 1 inert element |
| **E-Transparency** | `E·⊤ = ⊤` and `E·⊥ = ⊥` |
| **Branch** | `ρ·x = f·x` if `τ·x = ⊤`, else `ρ·x = g·x` — tester-mediated conditional |
| **Compose** | `η·x = ρ·(g·x)` — function composition through branch |
| **Y-Combinator** | `Y·ρ = ρ·(Y·ρ)`, with `Y·ρ ≥ 2` — fixed-point combinator |
| **Selection** | `η·ρ = τ` — composing then branching yields a judgment |

### Scale

| Feature | Min N |
|---------|-------|
| L8 (full ladder) | 6 |
| + QE pair | 8 |
| + Branch/Compose/Y | 12 |
| + IO + 8-state counter + Selection | 16 |

The axiom stack admits models of size 12 supporting quote/eval, branching, and fixed points — enough for Turing completeness. The specific model Ψ₁₆ᶠ adds efficient counters, IO, product encodings, and a Y-combinator at size 16. The computational core is 7 axiom-forced elements; the rest is infrastructure.

### Result Categories

Results in this repository fall into four tiers:

- **Universal results** — properties proved for *every* model satisfying the axiom class, not just one table. Tagged `[Lean]` or `[SAT]`.
- **Model-specific results** — properties proved for the particular table Ψ₁₆ᶠ. Tagged `[Lean]`.
- **Empirical search results** — SAT satisfiability, minimality bounds, freedom analysis, recovery observations. Tagged `[SAT]` or `[Empirical]`.
- **Open claims** — not yet formalized. Tagged `[Open]`.

Full registry with reproduction commands: [`CLAIMS.md`](CLAIMS.md).

### Universal Theorems

These hold for **all** models of the axiom system — not just Ψ₁₆ᶠ, but any satisfying algebra:

- **Exactly 2 absorbers.** `[Lean]` L5 forces no additional absorbers beyond ⊤ and ⊥.
- **Separation of judgment and operation.** `[Lean]` Kleene (C) makes this structural: non-testers *cannot* produce boolean outputs on non-absorbers. Branching must go through a tester. There is no shortcut.
- **Actuality irreducibility.** `[Lean]` The tester row is structurally underdetermined. A twin-model construction on Fin 17 proves that two valid extensions of Ψ₁₆ᶠ can agree on all structural axioms yet disagree on tau's assignment to the surplus element. SAT analysis confirms all 40 tester free cells at N=16 can independently flip (push/pop verified at N=8, 12, 16).
- **Rigidity.** `[Lean]` Every injective endomorphism of Ψ₁₆ᶠ is the identity (Aut = {id}). Proved via a 16-step fixing chain: idempotent constraints pin ⊤ and ⊥, then products of fixed elements propagate through the generation tree.
- **Discoverability.** `[Lean]` All 16 elements are behaviorally identifiable. Four probes suffice: the map a ↦ (psi a ⊤, psi a ⊥, psi a τ, psi a Q) is injective on Fin 16. Testers, encoders, and the inert element are each uniquely characterized by structural properties.
- **Chirality.** `[SAT]` E-transparency (E·⊤ = ⊤, E·⊥ = ⊥) does *not* cascade to tester cells. Eval preserves structural boundaries but cannot determine what the tester accepts — the information flows one way.
- **Encoder-tester non-commutativity.** `[SAT]` Encoders and testers cannot commute in general. The Kleene barrier enforces an asymmetry: testers judge, encoders synthesize, and no element can do both.
- **No right identity.** `[Lean]` Universal algebraic proof: tester boolean constraint contradicts identity on tau. Proved in `PsiUniversalBounds.lean`.
- **Card ≥ 4 from role axioms.** `[Lean]` The four distinguished roles (⊤, ⊥, τ, encoder) must be pairwise distinct. Tight: 4-element countermodel in `PsiCountermodels.lean`.
- **No full associativity.** `[SAT]` UNSAT. No associative sub-magma of size ≥ 4.
- **Encoder dominance.** `[Empirical]` As N grows, encoder count grows; tester and inert counts stay bounded.
- **Constructibility.** `[Lean]` {⊤, ⊥, Q, E} generates all N elements in ≤4 steps at N=16.
- **Turing-completeness of Ψ∗.** `[Empirical]` The term algebra Ψ∗ over any Ψ model, equipped with constructor/destructor evaluation semantics and a stepped machine, simulates 2-counter machines (Minsky 1961) using 7 axiom-forced elements: ⊤ (zero), Q (successor), E (predecessor), g (pair), f (fst), η (snd), ρ (branch). The finite algebra is decidable; TC lives in the term algebra + eval, as with combinatory logic over {S, K}. The contribution is that the basis elements are axiom-forced rather than chosen. Universal — holds for every model of the axiom class, not just Ψ₁₆ᶠ. Formal Lean verification remains open. See below.
- **Equational minimality.** `[Empirical]` Among the 4,694 equational laws cataloged by the [Equational Theories Project](https://github.com/teorth/equational_theories) (Tao et al., 2024), Ψ₁₆ᶠ satisfies exactly one non-trivial law: power-associativity (ETP Equation 4380). All other equational regularities — associativity, commutativity, idempotency, and 4,690 others — are violated. The structure that makes the algebra interesting (absorbers, role separation, Kleene barrier, actuality irreducibility, QE inverse pair) lives entirely in a richer logical fragment that the equational framework cannot express.

### The Decidability Boundary and Turing Completeness

The axiom stack crosses a sharp boundary between decidable and undecidable self-description, and the crossing is exactly one axiom.

Without Y, the algebra has QE (quote/eval) and Branch (tester-mediated conditional dispatch). This is analogous to flat eval — like Datalog, or a first-order term rewriter with no recursion. Every branch eventually bottoms out at an absorber. You can enumerate all reachable states; the system always terminates.

Adding the single Y-combinator axiom (`Y·ρ = ρ·(Y·ρ)`) introduces a fixed point: the branch element can now apply itself to its own output indefinitely. This is the same structural move that separates Datalog from Prolog, or primitive recursion from general recursion.

**This crossing is not merely non-termination — it is Turing completeness.** The term algebra Ψ∗ (finite binary trees with Ψ atoms as leaves) simulates 2-counter machines using 7 axiom-forced elements:

| Element | Role in TC simulation |
|---------|----------------------|
| ⊤ | Zero (base case) |
| Q | Successor (wraps one layer — lazy constructor) |
| E | Predecessor (unwraps Q — destructor, via QE inverse) |
| g | Pair constructor (curried: state = pair(pair(c0, c1), pc)) |
| f | First projection (fst) |
| η | Second projection (snd) |
| ρ | Structural branch (atom = zero-path, compound = nonzero-path) |

The simulation (`psi_star.py`) matches a reference 2CM interpreter trace-for-trace on all test programs, including looping programs with JZ/GOTO that exercise both counters. Three aspects documented honestly:

1. **The step loop is the machine, not a gap.** Every TC system has an execution substrate. The Python loop is ours — small, fixed, program-independent. The Rust emulator will implement the same cycle.
2. **The machine provides implicit duplication.** Non-destructive heap reads let the step function project c0, c1, and pc from the same state. This is the standard separation: the instruction set is combinational, the machine adds state.
3. **The structural branch is a semantic design choice.** ρ dispatching on atom-vs-compound at the Ψ∗ level is the natural lifting of τ's boolean dispatch at the algebra level, but it is a choice in the evaluation semantics, not a direct axiom consequence.

This is structurally identical to how {S, K} supports Turing completeness in combinatory logic — the combinators provide the instruction set, the evaluation semantics provides the machine. The contribution here is not TC per se (many finite bases generate TC term algebras) but that the basis elements are *axiom-forced* rather than chosen, and that the same elements also serve as the algebra's self-description mechanism.

Because only axiom-forced elements are used, TC is a property of every Ψ algebra — any model satisfying the axiom class supports the same simulation. The free cells (192/256 at N=16) provide efficiency (fast counter arithmetic, IO), not capability. Formal Lean verification of the TC simulation remains open.

**TC Minimality (canonical construction).** The 7 roles used in the 2CM construction — ground (⊤), quote (Q), eval (E), branch (ρ), pair constructor (g), first projection (f), second projection (η) — are pairwise forced distinct. 21 satisfiability checks (`ds_search/tc_merge_test.py`), each asserting that one element satisfies both role axioms simultaneously, return UNSAT — all instantaneously, indicating shallow contradictions `[SAT]`. The canonical construction cannot be done with fewer than 7 elements. Whether an alternative TC construction in Ψ∗ exists using fewer elements remains open.

**Mini-Lisp.** `psi_lisp.py` is a McCarthy 1960-style Lisp interpreter where all data flows through the Ψ∗ algebra — numbers are Q-chains rooted at ⊤, pairs are g-applications, car/cdr use f/η via `psi_eval`. NIL = ⊥ (false/empty list), T = ⊤ (true). Example programs:

| Program | Key results |
|---------|-------------|
| `psi_fibonacci.lisp` | `(fib 8)` → 21, `(fib-iter 30)` → 832040, `(fib-list 10)` → (0 1 1 2 3 5 8 13 21 34) |
| `psi_higher.lisp` | `(mapcar add1 '(1 2 3))` → (2 3 4), filter, reduce, reverse |
| `psi_recursion.lisp` | `(fact 10)` → 3628800, `(power 2 10)` → 1024, `(gcd 100 75)` → 25 |
| `psi_functions.lisp` | `(square 12)` → 144, closures, composition |
| `psi_types.lisp` | `(null NIL)` → T, `(null 0)` → NIL, `(zerop 0)` → T, `(zerop NIL)` → NIL |

```bash
python3 psi_lisp.py examples/psi_fibonacci.lisp     # run a file
python3 psi_lisp.py --show-term examples/psi_basic.lisp  # show Ψ∗ terms
python3 psi_repl.py                                  # interactive REPL

# Rust (native, ~25x faster than Python)
cd kamea-rs && cargo run --release -- run examples/psi_fibonacci.lisp

# Rust reflective tower (multiple files share one machine)
cd kamea-rs && cargo run --release -- run examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp

# Browser debugger (WASM)
cd kamea-rs/crates/psi-web && python3 -m http.server 8080 --directory www
# → open http://localhost:8080
```

### The Reflective Tower (Boba's Tower)

**The defunctionalized CPS evaluator.** [`examples/psi_metacircular.lisp`](examples/psi_metacircular.lisp) is a CPS Lisp interpreter written in Ψ-Lisp — approximately 350 lines. Every evaluation step takes an explicit continuation `k`, but unlike a standard CPS interpreter, `k` is never a lambda. Every continuation is a **tagged data structure** — a cons-list with a tag symbol and captured values. This is Reynolds' (1972) definitional interpreters combined with Danvy & Nielsen's (2001) defunctionalization: the evaluator contains zero lambdas in its control flow. A dispatch function `apply-k` pattern-matches on 14 continuation types (`k-id`, `k-if`, `k-cond`, `k-let-body`, `k-let-bind`, `k-seq`, `k-apply-fn`, `k-do-apply`, `k-args-head`, `k-args-tail`, `k-reflect-state`, `k-reflect-jump`, `k-top-wrap`, `k-program-step`) and performs what each lambda would have done.

**Inspectable continuations.** Because continuations are data, the program can examine them with `car`/`cdr`/`nth`:

- `(k-walk k)` — returns the chain of tags from a continuation to `k-id` (e.g., `(k-let-bind k-let-body k-id)`)
- `(k-depth k)` — counts frames in the continuation chain
- `(k-next k)` — follows the chain to the next frame
- `(describe-continuation k)` — human-readable description of what `k` will do next

This is the architecture of Smith's 3-Lisp (1984): reified state is fully inspectable, not an opaque closure. The program can walk the continuation chain, see what computation is pending, modify any of it, and reflect into an altered future.

**Reify and reflect.** These are cases in `meval`, not builtins. `(reify)` packages the current continuation `k` (a tagged data structure) and environment (a cons-list alist) as a Lisp value — the program receives its own future as inspectable data. `(reflect state value)` extracts a (possibly modified) continuation from a reified state and jumps to it, abandoning the current future. The program can inspect and rewrite the continuation between reify and reflect — not just the environment, but the control flow itself.

**The grounded tower.** Unlike 3-Lisp's infinite tower of interpreters resting on nothing, this tower terminates at the Cayley table. The demo ([`examples/psi_reflective_tower.lisp`](examples/psi_reflective_tower.lisp)) runs three levels in a single program:

```
Layer 3: User programs (fib, fact)
Layer 2: CPS meta-circular evaluator (psi_metacircular.lisp)
Layer 1: Base evaluator (psi_lisp.py / kamea-rs)
Layer 0: Cayley table (256 bytes, verified by Level 1)
```

- **Level 0: Computation.** The meta-circular evaluator interprets fibonacci and factorial — Ψ-Lisp running inside Ψ-Lisp through explicit continuations. Each evaluation step is a continuation-passing call built from the seven axiom-forced atoms.
- **Level 1: Ground verification.** The program shifts up and probes the Cayley table directly, checking algebraic invariants: absorber laws (`⊤·x = ⊤`), tester boolean output (`τ·x ∈ {⊤,⊥}`), QE round-trips (`E·(Q·x) = x`), idempotent classification. These are actual table lookups via the `dot` builtin — if any cell were wrong, the check would fail.
- **Level 2: Inspectable reification.** The program reifies its evaluator state via CPS. `(reify)` captures the continuation as a tagged data structure and the environment as an alist — both fully inspectable with `car`/`cdr`. The demo verifies: reify + reflect produces 99, reify + reflect + compute produces 92.
- **Level 2b: Continuation chain inspection.** The program walks the continuation chain as a linked list of frames. Inside `(let ((x (reify))) x)`, the chain is `k-let-bind → k-let-body → k-id` — three frames, each verified by tag comparison.
- **Level 2c: Continuation modification — the branch swap.** The definitive 3-Lisp demo. A program reifies inside the test position of an `(if TEST 42 99)`. It navigates the continuation chain (`k-let-bind → k-let-body → k-if`), finds the `k-if` frame, swaps the then/else branches, rebuilds the chain, and reflects. The if receives `1` (truthy) as the test value — which would normally select the then-branch (42) — but because the branches were swapped in the continuation, it returns 99 instead. **The program rewrote its own control flow from the meta-level.**

Level 1 verifies the table before Level 2 trusts the evaluator. There is nothing beneath the table to worry about — it IS the algebra, not an implementation of it.

### The Recovery Spell

The recovery algorithm is written as a pure Ψ-Lisp program ([`examples/psi_recovery_spell.lisp`](examples/psi_recovery_spell.lisp)) — approximately 120 lines that identify all 16 elements of a corrupted table using only ~62 dot-oracle probes. The program communicates exclusively through the algebra's IO atoms: `(put x)` to emit a value and `(get)` to read one. No Python builtins, no foreign function calls. The IO protocol:

```
PROBE:  (put 0) (put a) (put b) (get) → dot(a,b)
REPORT: (put 1) (put idx) (put label)
```

The corrupted host demo loads the spell into a healthy Kamea and casts it on a scrambled copy — the animated TUI visualizes the recovery in real time. The recovery algorithm, the language it's written in, and the IO channel it communicates through are all elements of the same 16×16 table.

```bash
python3 examples/psi16_corrupted_host_demo.py           # animated TUI
python3 examples/psi16_corrupted_host_demo.py --plain    # plain text
```

### Phenomenological Interpretation

*The following correspondences are interpretive, not part of the formal theorem set.*

The structural constraints have precise phenomenological counterparts. Judgment cannot commute with synthesis (Kleene barrier) — that is a theorem, not an analogy. Tester values are axiomatically unconstrained (actuality irreducibility) — also a theorem. Eval preserves boundaries but cannot determine what the tester accepts (chirality) — again, proved. Whether these correspondences with receptivity/spontaneity, the irreducibility of givenness, and the asymmetry of observation reflect something deeper about self-description is an open question — but the structural facts themselves are theorems, not interpretations.

---

## 2. Ψ₁₆ᶠ: The Specific Algebra

The canonical representative: a single 16×16 Cayley table with **130+ machine-checked Lean theorems** `[Lean]` across `Psi16Full.lean`, `Psi16Discoverable.lean`, `Psi16Rigidity.lean`, and `Psi16ActualityIrreducibility.lean`, covering every operational constraint, discoverability, automorphism rigidity, and actuality irreducibility. All proofs compile with **zero `sorry`** on Lean 4.28.0 / Mathlib v4.28.0.

This table is one model from the solution space — the axioms constrain roles and relationships but leave many cells free (192/256 at N=16, 117/144 at N=12). The universal theorems above hold for all models; the properties below are verified for this specific table.

### Element Assignments

The "Role" column describes each element's classification by its Cayley row behavior (absorber, tester, encoder, inert). This is distinct from its role in the Ψ∗ term algebra — for example, g is classified as *inert* because its Cayley row has the signature of a substrate element, but in Ψ∗ evaluation semantics it serves as the pair constructor (CONS). The Cayley role and the TC role are different slices of the same element: one describes what `dot(g, x)` produces across all x, the other describes what `eval(App(g, t))` does.

| Index | Symbol | Role | Computational | Counter | IO | Product |
|-------|--------|------|---------------|---------|----|---------|
| 0 | ⊤ | absorber | top/true | — | — | — |
| 1 | ⊥ | absorber | bottom/false | — | — | — |
| 2 | f | encoder | branch-if (f path) | — | — | — |
| 3 | τ | tester | branch tester | — | — | — |
| 4 | g | inert | branch-else (g path) / pair constructor | — | — | — |
| 5 | SEQ | tester | — | — | SEQ | — |
| 6 | Q | encoder | quote | s2 | — | SND/p01 |
| 7 | E | encoder | eval | s7 | — | INC2 |
| 8 | ρ | encoder | branch element | s6 | — | — |
| 9 | η | encoder | compose element | — | — | p10 |
| 10 | Y | encoder | Y-combinator | s4 | — | — |
| 11 | PAIR | encoder | — | s3 | — | PAIR/p11 |
| 12 | s0 | tester | — | s0 (zero) | — | p00 |
| 13 | INC | encoder | increment | — | — | — |
| 14 | GET | encoder | — | s1 | GET/FST | SWAP |
| 15 | DEC | encoder | decrement | s5 | PUT/DEC | — |

### Multi-Duty Architecture

Elements serve up to 4 roles each. The Cayley table encodes all pairwise interactions, so an element's role depends on what it's composed with, not on a fixed assignment — element 14 acts as GET when composed after PUT, as FST when composed after a pair, as SWAP when composed with a core element, and as counter state s1 when operated on by INC or DEC. There is no overloading; every role is a different slice of the same row.

| Element | Roles |
|---------|-------|
| 14 (GET) | GET / FST / SWAP / s1 (4 roles) |
| 6 (Q) | Q / SND / s2 / p01 (4 roles) |
| 7 (E) | E / INC2 / s7 (3 roles) |
| 15 (DEC) | DEC / PUT / s5 (3 roles) |
| 11 | PAIR / s3 / p11 (3 roles) |

### Operations

**8-State Counter:**
```
s0(12) →INC→ s1(14) →INC→ s2(Q=6) →INC→ s3(11) →INC→
s4(Y=10) →INC→ s5(15) →INC→ s6(ρ=8) →INC→ s7(E=7) →INC→ s0(12)
```
DEC reverses this cycle exactly. Zero test: `τ·s0 = ⊤`, `τ·sₖ = ⊥` for k≠0.

**IO Roundtrip:** `GET·(PUT·x) = x` on core {2,3,4,5}, with PUT=15, GET=14.

**2×2 Product:** Pairing encodes structured data, enabling the algebra to represent tuples for multi-argument operations. Four elements encode the four states of a 2-bit register, with FST and SND as projections:

| Pair | State | Element | FST | SND |
|------|-------|---------|-----|-----|
| (s0,s0) | p00 | 12 (=s0) | s0 | s0 |
| (s0,s1) | p01 | 6 (=Q) | s0 | s1 |
| (s1,s0) | p10 | 9 (=η) | s1 | s0 |
| (s1,s1) | p11 | 11 (=PAIR) | s1 | s1 |

**1-Bit Logic (AND, OR, XOR):** `[SAT]` The axiom class admits models where all three Boolean gates embed via curried dispatch on {s0, s1}. Each gate is a single element whose action on a first bit selects a function, which is then applied to the second bit — two table lookups per gate, no new elements. SAT-verified with all existing constraints; model stays WL-1 rigid.

| Gate | Dispatch | dot(gate, s0) → | dot(gate, s1) → | Behavior |
|------|----------|-----------------|-----------------|----------|
| AND | Y(10) | f(2) = zero | s1(14) = id | 0∧x = 0, 1∧x = x |
| OR | INC(13) | s1(14) = id | Q(6) = one | 0∨x = x, 1∨x = 1 |
| XOR | η(9) | s1(14) = id | ρ(8) = not | 0⊕x = x, 1⊕x = ¬x |

Four functional elements, each an existing element in a new role:

| Function | Element | dot(elem, s0) | dot(elem, s1) |
|----------|---------|---------------|---------------|
| id (identity) | s1(14) | s0 | s1 |
| not (negation) | ρ(8) | s1 | s0 |
| zero (const 0) | f(2) | s0 | s0 |
| one (const 1) | Q(6) | s1 | s1 |

The specific element assignments are model-dependent — the axiom class leaves 192/256 cells free at N=16, and different models assign different elements to each role. In one SAT-feasible model, Q(6) acts as NOT (bit negation) — its fifth role alongside quote, SND, s2, and p01. The gate and function assignments shown above are from a different SAT-feasible model; both satisfy all axioms simultaneously. This is the same multi-duty architecture: different columns of the same row, different operational slices of the same element.

### Worked Example

All operations below are lookups in the same 16×16 Cayley table.

```
# Quote/Eval round-trip: Q encodes τ, E decodes it back
Q · τ  = 9  (η)          -- quote the tester: get a code for it
E · 9  = 3  (τ)          -- eval the code: recover the original

# Branch dispatch: ρ routes through f when τ accepts
τ · f  = 0  (⊤)          -- tester accepts f
ρ · f  = 13 (INC)        -- branch element computes f·f = 13  (took the f-path)

τ · g  = 0  (⊤)          -- tester also accepts g
ρ · g  = 11 (PAIR)       -- branch computes f·g = 11

# Counter step: INC advances the 8-state counter
INC · s0 = 14 (s1)       -- increment from zero
INC · s1 = 6  (Q = s2)   -- increment again: counter state 2 is Q
τ · s0   = 0  (⊤)        -- zero test: tester accepts s0
τ · s1   = 1  (⊥)        -- non-zero: tester rejects s1
```

### Extension Profiles

Ψ₁₆ᶠ is the **hardware profile** — designed for FPGA and embedded targets where every operation is a single table lookup. Its extensions (8-state counter, IO roundtrip, 2×2 product) pack maximum functionality into 256 bytes of ROM.

Ψ₁₆ᶜ is the **software profile** — designed for conventional hosts via supercompile → transpile → C. Its extensions (4-cycle counter on core {2,3,4,5}, INV involution) have arithmetic interpretations (`INC(x) = ((x-1)&3)+2`, `INV(x) = 7-x`) that make three additional cancellation rules sound:

| Rule | Identity | Sound because |
|------|----------|---------------|
| INC·(DEC·x) → x | mutual inverses on core | 4-cycle + reverse 4-cycle |
| DEC·(INC·x) → x | mutual inverses on core | same |
| INV·(INV·x) → x | full involution | SAT-enforced on all 16 elements |

After supercompilation, Ψ₁₆ᶜ eliminates 50–67% more residual operations than Ψ₁₆ᶠ. An 8-operation chain of paired INV and INC/DEC operations supercompiles to the identity function — zero runtime cost. The arithmetic row interpretations exist to make the cancellation rules sound; the cancellation rules eliminate the code.

Both profiles share the same base axioms, the same universal theorems, and the same evaluation semantics. They differ only in the free cells — different fillings of the extension space, optimized for different targets. The analogy to RISC-V ISA extensions (RV32I base + M/F/V/... extensions) is deliberate.

Actuality irreducibility holds across both profiles: 48/48 free tester cells in Ψ₁₆ᶜ, 40/48 in Ψ₁₆ᶠ (8 fixed by counter-zero-test coupling). Full details: [`docs/extension_profiles.md`](docs/extension_profiles.md).

---

## 3. Black-Box Recovery

All 16 elements can be identified from a shuffled, opaque dot oracle — no ground truth, no labels. Three methods (`psi_blackbox.py`), all 100% on 1,000,000 seeds `[Empirical]`:

| Method | Mean dot calls | Min | Max | Strategy |
|--------|---------------|-----|-----|----------|
| **Behavioral** | 756.9 | 653 | 861 | 12-step axiom-driven probing (full row reads) |
| **Generation** | 659.4 | 543 | 776 | Steps 1–7, then depth-2 generation from {⊤,⊥,Q,E} |
| **Adaptive** | **62.5** | 59 | 66 | Absorber-probe signatures + Kleene/QE targeting + generation |

The adaptive method never reads a full row. The 2-probe absorber signature `(x·⊤, x·⊥)` partitions all 14 non-absorbers into 5 disjoint classes:

| Signature | Elements | What it reveals |
|-----------|----------|-----------------|
| full-preserver | τ, SEQ, E, s0 | E is here (Kleene separates it from testers) |
| semi(⊤) | g | **unique** — orients ⊤ |
| semi(⊥) | f, ρ, Y, PAIR | — |
| swap(⊥→⊤) | Q, INC, s1 | Q is here (QE round-trip on E identifies it) |
| swap(⊤→⊥) | η, DEC | — |

Once ⊤, ⊥, Q, E are found (~50 probes), 12 generation calls produce all remaining elements via the depth-2 generation tree.

```bash
uv run python psi_blackbox.py --method adaptive              # single demo
uv run python psi_blackbox.py --method adaptive --seeds 1000  # batch
uv run python psi_blackbox.py --seeds 1000 --compare          # cost comparison
```

---

## 4. What Is Not Proved

- **Uniqueness of Ψ₁₆ᶠ.** The Cayley table is one model from the solution space. The axioms constrain roles and relationships but leave 192/256 cells free at N=16 (25.0% determination). Cell-by-cell freedom analysis (`ds_search/n16_freedom.py`) confirms: absorber rows fully fixed (32), counter/INC/DEC pinned (24), E-transparency + INC2 fix 6 E-cells, selection fixes η·ρ, Y fixed-point fixes Y·ρ. Scale: N=8 → 28.1%, N=12 → 18.8%, N=16 → 25.0% (increase from N=12 due to additional operational constraints).
- **Minimality from base axioms.** Abstract axiom limitation theorems show base DirectedDS axioms imply only `card ≥ 2` (tight). What forcing conditions derive the full structure from first principles remains open.
- **Symmetric impossibility.** The symmetric synthesis barrier is demonstrated by construction but not proved as a general impossibility theorem.
- **Necessity of self-modeling.** Empirical evidence (`ds_search/counterexample_search.py`) strongly suggests self-modeling is not required for efficient scramble-resilience — nearly all structureless rigid magmas are WL-1 discriminable. Self-modeling provides interpretability, not computational necessity.
- **Extension profile optimality.** Ψ₁₆ᶠ and Ψ₁₆ᶜ are two points in the extension design space. Whether either is optimal for its target — or whether better profiles exist — is unexplored. The methodology (SAT search with target-specific constraints) can find other profiles, but the space has not been systematically enumerated.

## 5. Supercompiler and Compilation Pipeline

The Cayley table is a specification. You don't have to interpret it at runtime — you can compile against it.

`psi_supercompile.py` is a partial evaluator written in Ψ-Lisp itself. It walks a Ψ-Lisp expression and applies five optimization passes, each justified by algebraic properties of the table:

| Pass | Rule | Justification |
|------|------|---------------|
| Constant folding | `(dot A B)` → table lookup when both atoms known | Cayley table is total |
| QE cancellation | `E·(Q·x)` → `x`, `Q·(E·x)` → `x` | QE inverse axiom `[Lean]` |
| INC/DEC cancellation | `INC·(DEC·x)` → `x`, `DEC·(INC·x)` → `x` | Mutual inverses on core (Ψ₁₆ᶜ only) |
| INV cancellation | `INV·(INV·x)` → `x` | Full involution (Ψ₁₆ᶜ only) |
| Dead branch elimination | `(if ⊤ then else)` → `then` | Tester output determines branch |
| Let propagation | `(let ((x KNOWN)) body)` → substitute and fold | Standard substitution |
| Lambda inlining | `((λ (x) body) KNOWN)` → beta reduce and fold | Standard beta reduction |

All five passes cascade: a let binding feeds a dot fold, which feeds a branch elimination, which eliminates dead code. For fully known inputs, the supercompiler resolves every operation at compile time — zero table lookups remain at runtime.

`psi_transpile.py` takes supercompiled output and emits C. The translation is mechanical:

| Ψ∗ pattern | C output |
|------------|----------|
| Known atom | `(uint8_t)N` — constant |
| `(dot A x)`, A known | `psi_dot(A, x)` — one array lookup |
| `(dot x y)`, both unknown | `psi_dot(x, y)` — one array lookup |
| `(if test then else)` | ternary with `psi_dot(TAU, test)` |
| `(let ((x val)) body)` | `{ uint8_t x = val; ... }` |
| `(lambda (x) body)` | C function |

The C runtime is the Cayley table as a 256-byte constant array and a one-line inline function. The entire Ψ runtime fits in `psi_runtime.h`.

**End-to-end pipeline:**

```bash
python3 psi_supercompile.py program.psi > optimized.psi    # supercompile
python3 psi_transpile.py optimized.psi > program.c          # emit C
gcc -O2 -o program program.c                                # compile
./program                                                    # native speed
```

Example: three counter increments from a known base.

```
Ψ-Lisp:         (let ((x s0)) (dot INC (dot INC (dot INC x))))
Supercompiled:   11                          — 3 lets, 3 dots eliminated
C output:        uint8_t result = 11;        — zero runtime lookups
```

With unknown inputs, the supercompiler leaves residual operations:

```
Ψ-Lisp:         (defun double-inc (x) (dot INC (dot INC x)))
Supercompiled:   (lambda (x) (dot INC (dot INC x)))    — can't fold
C output:        uint8_t double_inc(uint8_t x) {
                     return psi_dot(13, psi_dot(13, x));
                 }                           — two array lookups
```

Both cases verified: all 16 inputs produce identical results through the interpreter and the compiled C `[Empirical]`.

`psi_transpile.py` also handles full Ψ-Lisp programs directly — arithmetic, recursive `defun`, nested functions (lambda-lifted), cons/car/cdr, if/cond/let/progn. Programs with closures or higher-order functions (passing functions as arguments) are not yet supported.

### Performance

Each row runs the same five computations: fib(8), fib-iter(30), fact(10), power(2,10), gcd(100,75). These are pure arithmetic — `(+)`, `(-)`, `(*)`, `(if)` — with zero `psi_dot()` calls. The compiled C is identical under both Ψ₁₆ᶠ and Ψ₁₆ᶜ. Single invocation = wall-clock time including process startup. Amortized = per-iteration in a tight loop (10M iterations for C/Rust, 100K for Python).

| Implementation | Single invocation | Amortized/iter | vs Ψ-Lisp Python |
|----------------|------------------|---------------|-----------------|
| **Ψ-Lisp (Python interpreter)** | ~2,000 ms | — | 1x |
| **Ψ-Lisp (Rust interpreter)** | ~200 ms | — | 10x |
| **Native Python** | ~30 ms (startup), 5 µs compute | 5 µs | 400,000x |
| **Compiled Ψ-Lisp** (both profiles, gcc -O2) | ~2.4 ms (startup) | 0.01 µs | 200,000,000x |
| **Native Rust** (LLVM -O) | ~1 ms (startup) | 0.003 µs | ~700,000,000x |

The Ψ-Lisp interpreters are slow because of triple indirection: the host language runs an evaluator, which walks S-expressions, which encodes numbers as Q-chains (nested `App(Q, App(Q, ...))` trees). Every `(+ a b)` decodes two Q-chains, adds, and re-encodes. The transpiler eliminates all of that — `(+ a b)` becomes a single `add` instruction.

The compiled output is within **4x of hand-written Rust compiled with LLVM** — and faster than native Python. The entire compilation pipeline is ~1,100 lines: a 312-line supercompiler, a 640-line transpiler, and a 121-line C runtime whose core is a 256-byte array. A language designed for algebraic self-description, not performance, compiles to near-native speed through a pipeline small enough to audit in an afternoon.

### Extension Profile Comparison (Ψ₁₆ᶠ vs Ψ₁₆ᶜ)

Programs that use `(dot ...)` operations — where the table choice matters. Supercompilation residual = AST nodes after optimization. Compiled C = 100M iterations, `gcc -O2`.

| Benchmark | Ψ₁₆ᶠ residual | Ψ₁₆ᶜ residual | Ψ₁₆ᶠ C (ns/iter) | Ψ₁₆ᶜ C (ns/iter) |
|-----------|--------------|--------------|------------------|------------------|
| `INV·INV·INC·DEC·x` (4 ops) | 4 dots | **0 dots** (identity) | 0.9 | **0.5** |
| `INV·INV·(INC·DEC)³·x` (8 ops) | 8 dots | **0 dots** (identity) | 1.6 | **0.6** |
| `E·Q·INC·DEC·x` (mixed) | 2 dots | **0 dots** (identity) | 0.9 | **0.5** |

Ψ₁₆ᶠ table lookups are fast (sub-nanosecond, L1-cached 256-byte array). But Ψ₁₆ᶜ supercompilation eliminates the lookups entirely. The gap widens with chain depth — 8 operations that survive Ψ₁₆ᶠ supercompilation cost 1.6 ns; the same 8 operations under Ψ₁₆ᶜ cost 0 ns because the supercompiler proved they cancel. Details: [`docs/extension_profiles.md`](docs/extension_profiles.md).

### Claim Matrix

| Claim | Scope | Status | Evidence |
|-------|-------|--------|----------|
| Ψ₁₆ᶠ satisfies all listed operations | specific model | `[Lean]` | `Psi16Full.lean` (83 theorems) |
| Ψ₁₆ᶠ is WL-1 rigid and fully producible | specific model | `[Lean]` | `Psi16Full.lean` |
| Ψ₁₆ᶠ automorphism rigidity (Aut = {id}) | specific model | `[Lean]` | `Psi16Rigidity.lean` |
| Ψ₁₆ᶠ discoverability (4-probe injectivity) | specific model | `[Lean]` | `Psi16Discoverable.lean` |
| Actuality irreducibility (twin-model proof) | structural | `[Lean]` | `Psi16ActualityIrreducibility.lean` |
| Base axioms imply only card ≥ 2 (tight) | universal | `[Lean]` | `BaseAxiomDerivation.lean` |
| QE exists at N ≥ 8 | universal / min-size | `[SAT]` | `stacking_analysis.py` |
| Branch/Compose/Y require N ≥ 12 | universal / min-size | `[SAT]` | `stacking_analysis.py` |
| Tester cells completely free | universal / all sizes tested | `[SAT]` | `n16_freedom.py` (N=8, 12, 16) |
| No right identity (any PsiStructure) | universal | `[Lean]` | `PsiUniversalBounds.lean` |
| Card ≥ 4 from L0–L3 (tight) | universal | `[Lean]` | `PsiUniversalBounds.lean`, `PsiCountermodels.lean` |
| N=16 determination: 64/256 fixed (25.0%) | size-specific | `[SAT]` | `n16_freedom.py` |
| Black-box recovery (3 methods, 100%) | specific model | `[Empirical]` | `psi_blackbox.py` |
| Encoder dominance as N grows | trend | `[Empirical]` | `stacking_analysis.py` |
| Ψ∗ Turing-completeness (term algebra + eval over 7 axiom-forced elements) | universal | `[Empirical]` | `psi_star.py` — 2CM trace-matching on 4 test programs |
| TC minimality — canonical construction (7 roles pairwise distinct) | universal | `[SAT]` | `tc_merge_test.py` — 21/21 pairs UNSAT |
| 1-bit logic (AND/OR/XOR) via curried dispatch | universal | `[SAT]` | SAT-verified at N=16 with all constraints; model stays WL-1 rigid |
| Defunctionalized CPS evaluator (14 continuation types, zero lambdas) | specific model | `[Empirical]` | `psi_metacircular.lisp` + `psi_reflective_tower.lisp` |
| Inspectable continuations: k-walk, k-depth, k-next, describe-continuation | specific model | `[Empirical]` | `psi_reflective_tower.lisp` — chain tags verified by comparison |
| Reify/reflect with continuation modification | specific model | `[Empirical]` | `psi_reflective_tower.lisp` — reify + reflect, value injection, branch swap |
| K-IF branch swap: program rewrites own control flow | specific model | `[Empirical]` | `psi_reflective_tower.lisp` — `(if 1 42 99)` → 99 after swap |
| Reflective tower (3-level + continuation inspection/modification) | specific model | `[Empirical]` | `examples/psi_reflective_tower.lisp` |
| Recovery spell (pure Ψ-Lisp, IO-only) | specific model | `[Empirical]` | `examples/psi_recovery_spell.lisp` |
| Recovery spell: 62-probe adaptive, 100% on 1M seeds | specific model | `[Empirical]` | `psi_blackbox.py --seeds 1000000` |
| Symmetric impossibility (general) | universal | `[Open]` | demonstrated, not proved |
| Supercompiler: 5-pass partial evaluator (fold, QE, branch, let, lambda) | universal | `[Empirical]` | `psi_supercompile.py` — all optimizations algebraically justified |
| C transpiler: supercompiled Ψ∗ → C with 256-byte runtime | specific model | `[Empirical]` | `psi_transpile.py` — verified against interpreter for all 16 inputs |
| End-to-end compilation: Ψ-Lisp → supercompile → C → native binary | specific model | `[Empirical]` | Full pipeline tested on counter arithmetic and branching programs |
| Ψ₁₆ᶜ extension: INV involution + modular INC/DEC + 5 cancellation rules | specific model | `[Empirical]` | `ds_search/n16_c_interop.py` + `psi_star_c.py` |
| Ψ₁₆ᶜ actuality irreducibility (48/48 free tester cells) | specific model | `[Empirical]` | `ds_search/n16_c_interop.py --freedom` |
| Ψ₁₆ᶜ supercompilation: 50–67% residual reduction vs Ψ₁₆ᶠ | specific model | `[Empirical]` | `bench_c_interop.py` — cancel_chain, deep_cancel, mixed, branch |
| Extension profile modularity: same core theorems, different extension cells | architectural | `[Empirical]` | Both profiles satisfy all base axioms, differ only in free cells |

Full registry with reproduction commands: [`CLAIMS.md`](CLAIMS.md).

---

## Repository Structure

```
├── DistinctionStructures/
│   ├── Basic.lean                    # Abstract DS definitions and axioms
│   ├── BaseAxiomDerivation.lean      # Base axioms imply only card ≥ 2 (tight)
│   ├── BasePlusA7Derivation.lean     # Adding generic A7′ still doesn't force card ≥ 17
│   ├── OntologicalSchema.lean        # Abstract four-lift schema theorem
│   ├── Psi16.lean                    # Ψ₁₆ with selection axiom (42 theorems)
│   ├── Psi16Full.lean               # Ψ₁₆ᶠ full operations (83 theorems)
│   ├── Psi16Discoverable.lean       # Behavioral discoverability (4-probe injectivity)
│   ├── Psi16Rigidity.lean           # Automorphism rigidity (Aut = {id})
│   ├── Psi16ActualityIrreducibility.lean  # Twin-model actuality irreducibility
│   ├── PsiStructure.lean               # Abstract Ψ role axioms (L0–L3)
│   ├── PsiUniversalBounds.lean          # No right identity + card ≥ 4 (algebraic)
│   └── PsiCountermodels.lean            # Tight 4-element countermodel
├── kamea-rs/                             # Rust emulator + WASM browser debugger
│   ├── crates/
│   │   ├── psi-core/                     # The algebra — #![no_std], zero deps
│   │   │   └── src/
│   │   │       ├── table.rs              # 16×16 Cayley table as const array
│   │   │       ├── term.rs               # Term enum + arena allocator
│   │   │       └── eval.rs               # Explicit-stack Ψ∗ evaluator
│   │   ├── psi-runtime/                  # The machine — heap, IO, Mini-Lisp
│   │   │   └── src/
│   │   │       ├── machine.rs            # Lisp evaluator, builtins, environment
│   │   │       ├── lisp.rs               # S-expression parser
│   │   │       └── io.rs                 # IO channel abstraction
│   │   ├── psi-cli/                      # Native CLI — runner, REPL, benchmark
│   │   │   └── src/main.rs
│   │   └── psi-web/                      # WASM target + browser debugger
│   │       ├── src/lib.rs                # wasm-bindgen exports
│   │       └── www/
│   │           ├── index.html            # Debugger UI
│   │           ├── debugger.js           # UI logic (computation in Web Worker)
│   │           ├── worker.js             # WASM Web Worker
│   │           └── style.css
│   └── examples/
│       └── psi_*.lisp                    # Lisp test programs (copied from examples/)
├── examples/
│   ├── psi16_corrupted_host_demo.py  # Animated TUI: dual-wizard corrupted-host bootstrap
│   ├── psi16_bijection_designer.py   # Interactive bijection designer for wiz2 sprite
│   ├── psi16_wizard_sprites.py       # Sprite rendering utilities
│   ├── wiz2.json                     # Hand-designed bijective sprite mapping
│   ├── psi_metacircular.lisp         # Defunctionalized CPS evaluator (~350 lines, 14 continuation types)
│   ├── psi_reflective_tower.lisp     # Three-level reflective tower + branch swap demo
│   ├── psi_recovery_spell.lisp       # Black-box recovery as pure Ψ-Lisp
│   ├── psi_hello_world.lisp          # Ψ-Lisp hello world example
│   ├── psi_counter_known.psi          # Supercompiler test: known-base counter increments
│   ├── psi_counter_free.psi           # Supercompiler test: free-variable counter
│   ├── psi_branch_test.psi            # Supercompiler test: branch elimination
│   ├── psi_fold_constants.lisp        # Supercompiler test: constant folding
│   └── psi_*.lisp                    # Mini-Lisp test programs (fibonacci, recursion, etc.)
├── ds_search/
│   ├── axiom_explorer.py             # Core encoder: encode_level(), classify_elements()
│   ├── stacking_analysis.py          # All Ψ analysis functions (~17k lines)
│   ├── substrate_analysis.py         # Substrate/stacking analysis
│   ├── n16_freedom.py                # Ψ₁₆ᶠ cell-by-cell SAT freedom analysis
│   ├── n16_c_interop.py              # Ψ₁₆ᶜ SAT search + freedom analysis
│   ├── tc_merge_test.py              # TC minimality: 21 pairwise merge checks (all UNSAT)
│   ├── counterexample_search.py      # WL-1 discrimination tests
│   ├── rigid_census.py               # Small rigid magma census
│   └── counterexamples/              # Saved counterexample tables (.npy)
├── docs/
│   ├── psi_framework_summary.md      # Comprehensive Ψ framework reference
│   ├── extension_profiles.md         # Ψ₁₆ᶠ vs Ψ₁₆ᶜ: modular extension architecture
│   ├── continuation_protocol.md      # Continuation protocol documentation
│   └── minimal_model.md              # Minimal model notes
├── psi_star.py                       # Ψ∗ TC proof: 2CM simulation via 7 axiom-forced elements
├── psi_star_c.py                     # Ψ∗ term algebra over Ψ₁₆ᶜ (C-interop table)
├── psi_lisp.py                       # Mini-Lisp → Ψ∗ transpiler (McCarthy 1960 conventions)
├── psi_supercompile.py               # Partial evaluator: 2–5 pass supercompiler (table-dependent)
├── psi_transpile.py                  # Supercompiled Ψ∗ → C transpiler (INC/DEC/INV specialization)
├── psi_runtime.h                     # C runtime for Ψ₁₆ᶠ: 256-byte table + inline dot
├── psi_runtime_c.h                   # C runtime for Ψ₁₆ᶜ: table + arithmetic helpers
├── bench_c_interop.py                # Benchmark: Ψ₁₆ᶜ vs Ψ₁₆ᶠ comparison
├── psi_blackbox.py                   # Ψ₁₆ᶠ black-box recovery (3 methods)
├── psi_repl.py                       # Interactive Ψ-Lisp REPL
├── CLAIMS.md                         # Claim status registry
└── README.md
```

## Building

```bash
# Lean (requires Lean 4.28.0 / Mathlib v4.28.0)
lake build

# Python (requires uv)
uv run python psi_lisp.py examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp  # reflective tower
uv run python psi_repl.py                                     # interactive REPL
uv run python examples/psi16_corrupted_host_demo.py           # TUI demo
uv run python examples/psi16_corrupted_host_demo.py --plain   # plain narrative
python3 psi_repl.py --algebraic                              # Q-chain number representation
python3 psi_lisp.py --algebraic examples/psi_fibonacci.lisp  # verify: same results, algebraic encoding

# Rust (requires rustup — https://rustup.rs)
cd kamea-rs
cargo test                                                     # run all tests (40 total)
cargo run --release -- run examples/psi_fibonacci.lisp         # run a Lisp program (~25x faster)
cargo run --release -- repl                                    # interactive REPL
cargo run --release -- bench examples/psi_fibonacci.lisp       # benchmark with timing

# WASM browser debugger (requires wasm-pack — https://rustwasm.github.io/wasm-pack/)
cd kamea-rs/crates/psi-web
wasm-pack build --target web                                   # build WASM (124KB)
python3 -m http.server 8080 --directory www                    # serve debugger UI
# → open http://localhost:8080
```

All Lean theorems are checked by `decide` or `native_decide`, appropriate and complete for finite carrier types with decidable equality. Zero sorry.

All Mini-Lisp test programs produce identical output in Python, Rust, and WASM.

---


## License

MIT

## Citation

If you use this work, please cite:

```bibtex
@software{palmieri2025kamea,
  author = {Palmieri, Stefano},
  title = {Kamea: Axiom-Driven Self-Describing Finite Algebras with Machine-Checked Proofs},
  year = {2025},
  url = {https://github.com/stefanopalmieri/Kamea}
}
```

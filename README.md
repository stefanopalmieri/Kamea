# Kamea

**Seven axiom-forced elements. One Turing-complete term algebra. 130+ Lean theorems. Zero `sorry`.**

*Seven algebraic elements, forced by axioms alone, are sufficient for Turing-complete self-describing computation — and the boundary between what the axioms determine and what they leave free is precisely the boundary between structure and actuality.*

<p align="center">
  <img src="https://upload.wikimedia.org/wikipedia/commons/thumb/7/7a/Albrecht_D%C3%BCrer_-_Melencolia_I_-_Google_Art_Project_%28_AGDdr3EHmNGyA%29.jpg/1280px-Albrecht_D%C3%BCrer_-_Melencolia_I_-_Google_Art_Project_%28_AGDdr3EHmNGyA%29.jpg" width="250" alt="Albrecht Dürer — Melencolia I (1514)" />
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

A program that can inspect its own continuation, where the continuation is data built from algebraically verified atoms, running on a table whose rigidity, discoverability, and actuality irreducibility are Lean-proved, implementing a Lisp whose seven primitive roles are axiom-forced and provably sufficient for Turing completeness.

Smith's 3-Lisp (1984) had the reflective tower but no ground. The levels went down forever — interpreter interpreting interpreter interpreting interpreter. There was no bottom. Each level's meaning depended on the level below, and there was no foundation. Here, the tower terminates at a 16×16 Cayley table — 256 bytes whose algebraic properties are machine-checked. The program verifies the table before trusting the evaluator. There is nothing beneath the table to worry about. It IS the algebra, not an implementation of it.

The demo: a defunctionalized CPS meta-circular evaluator — Ψ-Lisp interpreting itself with inspectable continuations — computes fibonacci, verifies the Cayley table it runs on, then reifies its own continuation as walkable data, navigates to a pending `k-if` frame, swaps the then/else branches, reflects, and takes the opposite branch from what the source code says. The program rewrites its own future. Everything below — axioms, theorems, phenomenology — is context for understanding what you just saw.

```bash
python3 psi_repl.py                                        # interactive REPL
python3 examples/psi16_corrupted_host_demo.py               # watch one wizard heal another
cd kamea-rs && cargo run --release -- repl                   # Rust REPL (~25x faster)
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
- Term algebra Ψ∗ over 7 axiom-forced elements is Turing complete: stepped 2CM simulation matches reference interpreter on all test programs (INC/DEC, transfer loop, clear loop) `[Empirical]` — formal Lean verification open
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
- **Turing-completeness of Ψ∗.** `[Empirical]` The term algebra Ψ∗ over any Ψ model simulates 2-counter machines (Minsky 1961) using 7 axiom-forced elements: ⊤ (zero), Q (successor), E (predecessor), g (pair), f (fst), η (snd), ρ (branch). A stepped simulation matches a reference interpreter trace-for-trace on all test programs. This is universal — it holds for every model of the axiom class, not just Ψ₁₆ᶠ. The free cells provide efficiency, not capability. Formal Lean verification remains open. See below.

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

# Browser debugger (WASM)
cd kamea-rs/crates/psi-web && python3 -m http.server 8080 --directory www
# → open http://localhost:8080
```

### The Reflective Tower

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
| Ψ∗ Turing-completeness (7 axiom-forced elements) | universal | `[Empirical]` | `psi_star.py` — 2CM trace-matching on 4 test programs |
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
│   └── psi_*.lisp                    # Mini-Lisp test programs (fibonacci, recursion, etc.)
├── ds_search/
│   ├── axiom_explorer.py             # Core encoder: encode_level(), classify_elements()
│   ├── stacking_analysis.py          # All Ψ analysis functions (~17k lines)
│   ├── substrate_analysis.py         # Substrate/stacking analysis
│   ├── n16_freedom.py                # N=16 cell-by-cell SAT freedom analysis
│   ├── tc_merge_test.py              # TC minimality: 21 pairwise merge checks (all UNSAT)
│   ├── counterexample_search.py      # WL-1 discrimination tests
│   ├── rigid_census.py               # Small rigid magma census
│   └── counterexamples/              # Saved counterexample tables (.npy)
├── docs/
│   ├── psi_framework_summary.md      # Comprehensive Ψ framework reference
│   └── minimal_model.md              # Minimal model notes
├── psi_star.py                       # Ψ∗ TC proof: 2CM simulation via 7 axiom-forced elements
├── psi_lisp.py                       # Mini-Lisp → Ψ∗ transpiler (McCarthy 1960 conventions)
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

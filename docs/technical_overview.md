# Kamea — Technical Overview

This document contains the full technical details of the Ψ framework. For an introduction, see the [README](../README.md).

---

## 1. The Decidability Boundary and Turing Completeness

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

**The Forced Roles Theorem.** The axioms force five behavioral categories: polarity (⊤/⊥), judgment (τ), substrate (g), composition (η), and computation (Q/E/f/ρ/Y). The Kleene barrier and inert role constraints create hard walls — judgment cannot merge with computation, substrate cannot merge with anything active (32/45 role pairs forced distinct at N=12) `[SAT]`. All instantiations of these categories, from maximally collapsed (5 role-bearing elements) to fully specialized (7+ elements), produce rigid discoverable algebras with trivial automorphism groups (verified at all 6 collapse levels) `[SAT]`. Among tested collapses, full specialization to seven roles maximizes compositional expressiveness (49 vs 16 1-step cells, 343 vs 64 2-step cells) `[Empirical]`. These seven roles correspond to McCarthy's 1960 Lisp primitives — a structural observation, not a proof of necessity. Four roles (⊤, τ, g, η) are forced by axioms alone; three (Q≠E, f≠ρ, ρ≠Y) are selected by the expressiveness principle. A formal proof that seven is uniquely optimal remains open. Full argument in [`forced_roles_theorem.md`](forced_roles_theorem.md).

---

## 2. The Reflective Tower (Boba's Tower)

**The defunctionalized CPS evaluator.** [`examples/psi_metacircular.lisp`](../examples/psi_metacircular.lisp) is a CPS Lisp interpreter written in Ψ-Lisp — approximately 350 lines. Every evaluation step takes an explicit continuation `k`, but unlike a standard CPS interpreter, `k` is never a lambda. Every continuation is a **tagged data structure** — a cons-list with a tag symbol and captured values. This is Reynolds' (1972) definitional interpreters combined with Danvy & Nielsen's (2001) defunctionalization: the evaluator contains zero lambdas in its control flow. A dispatch function `apply-k` pattern-matches on 14 continuation types (`k-id`, `k-if`, `k-cond`, `k-let-body`, `k-let-bind`, `k-seq`, `k-apply-fn`, `k-do-apply`, `k-args-head`, `k-args-tail`, `k-reflect-state`, `k-reflect-jump`, `k-top-wrap`, `k-program-step`) and performs what each lambda would have done.

**Inspectable continuations.** Because continuations are data, the program can examine them with `car`/`cdr`/`nth`:

- `(k-walk k)` — returns the chain of tags from a continuation to `k-id` (e.g., `(k-let-bind k-let-body k-id)`)
- `(k-depth k)` — counts frames in the continuation chain
- `(k-next k)` — follows the chain to the next frame
- `(describe-continuation k)` — human-readable description of what `k` will do next

This is the architecture of Smith's 3-Lisp (1984): reified state is fully inspectable, not an opaque closure. The program can walk the continuation chain, see what computation is pending, modify any of it, and reflect into an altered future.

**Reify and reflect.** These are cases in `meval`, not builtins. `(reify)` packages the current continuation `k` (a tagged data structure) and environment (a cons-list alist) as a Lisp value — the program receives its own future as inspectable data. `(reflect state value)` extracts a (possibly modified) continuation from a reified state and jumps to it, abandoning the current future. The program can inspect and rewrite the continuation between reify and reflect — not just the environment, but the control flow itself.

**The grounded tower.** Unlike 3-Lisp's infinite tower of interpreters resting on nothing, this tower terminates at the Cayley table. The demo ([`examples/psi_reflective_tower.lisp`](../examples/psi_reflective_tower.lisp)) runs three levels in a single program:

```
Layer 3: User programs (fib, fact)
Layer 2: CPS meta-circular evaluator (psi_metacircular.lisp)
Layer 1: Base evaluator (psi_lisp.py / kamea-rs)
Layer 0: Cayley table (256 bytes, verified by Level 1)
```

- **Level 0: Computation.** The meta-circular evaluator interprets fibonacci and factorial — Ψ-Lisp running inside Ψ-Lisp through explicit continuations. Each evaluation step is a continuation-passing call built from seven role-bearing atoms (five categories axiom-forced, seven specializations empirically optimal).
- **Level 1: Ground verification.** The program shifts up and probes the Cayley table directly, checking algebraic invariants: absorber laws (`⊤·x = ⊤`), tester boolean output (`τ·x ∈ {⊤,⊥}`), QE round-trips (`E·(Q·x) = x`), idempotent classification. These are actual table lookups via the `dot` builtin — if any cell were wrong, the check would fail.
- **Level 2: Inspectable reification.** The program reifies its evaluator state via CPS. `(reify)` captures the continuation as a tagged data structure and the environment as an alist — both fully inspectable with `car`/`cdr`. The demo verifies: reify + reflect produces 99, reify + reflect + compute produces 92.
- **Level 2b: Continuation chain inspection.** The program walks the continuation chain as a linked list of frames. Inside `(let ((x (reify))) x)`, the chain is `k-let-bind → k-let-body → k-id` — three frames, each verified by tag comparison.
- **Level 2c: Continuation modification — the branch swap.** The definitive 3-Lisp demo. A program reifies inside the test position of an `(if TEST 42 99)`. It navigates the continuation chain (`k-let-bind → k-let-body → k-if`), finds the `k-if` frame, swaps the then/else branches, rebuilds the chain, and reflects. The if receives `1` (truthy) as the test value — which would normally select the then-branch (42) — but because the branches were swapped in the continuation, it returns 99 instead. **The program rewrote its own control flow from the meta-level.**

Level 1 verifies the table before Level 2 trusts the evaluator. There is nothing beneath the table to worry about — it IS the algebra, not an implementation of it.

---

## 3. The Recovery Spell

The recovery algorithm is written as a pure Ψ-Lisp program ([`examples/psi_recovery_spell.lisp`](../examples/psi_recovery_spell.lisp)) — approximately 120 lines that identify all 16 elements of a corrupted table using only ~62 dot-oracle probes. The program communicates exclusively through the algebra's IO atoms: `(put x)` to emit a value and `(get)` to read one. No Python builtins, no foreign function calls. The IO protocol:

```
PROBE:  (put 0) (put a) (put b) (get) → dot(a,b)
REPORT: (put 1) (put idx) (put label)
```

The corrupted host demo loads the spell into a healthy Kamea and casts it on a scrambled copy — the animated TUI visualizes the recovery in real time. The recovery algorithm, the language it's written in, and the IO channel it communicates through are all elements of the same 16×16 table.

```bash
python3 examples/psi16_corrupted_host_demo.py           # animated TUI
python3 examples/psi16_corrupted_host_demo.py --plain    # plain text
```

---

## 4. Phenomenological Interpretation

*The following correspondences are interpretive, not part of the formal theorem set.*

The structural constraints have precise phenomenological counterparts. Judgment cannot commute with synthesis (Kleene barrier) — that is a theorem, not an analogy. Tester values are axiomatically unconstrained (actuality irreducibility) — also a theorem. Eval preserves boundaries but cannot determine what the tester accepts (chirality) — again, proved. Whether these correspondences with receptivity/spontaneity, the irreducibility of givenness, and the asymmetry of observation reflect something deeper about self-description is an open question — but the structural facts themselves are theorems, not interpretations.

---

## 5. Ψ₁₆ᶠ: The Specific Algebra

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

Actuality irreducibility holds across both profiles: 48/48 free tester cells in Ψ₁₆ᶜ, 40/48 in Ψ₁₆ᶠ (8 fixed by counter-zero-test coupling). Full details: [`extension_profiles.md`](extension_profiles.md).

### Extension Profile Comparison (Ψ₁₆ᶠ vs Ψ₁₆ᶜ)

Programs that use `(dot ...)` operations — where the table choice matters. Supercompilation residual = AST nodes after optimization. Compiled C = 100M iterations, `gcc -O2`.

| Benchmark | Ψ₁₆ᶠ residual | Ψ₁₆ᶜ residual | Ψ₁₆ᶠ C (ns/iter) | Ψ₁₆ᶜ C (ns/iter) |
|-----------|--------------|--------------|------------------|------------------|
| `INV·INV·INC·DEC·x` (4 ops) | 4 dots | **0 dots** (identity) | 0.9 | **0.5** |
| `INV·INV·(INC·DEC)³·x` (8 ops) | 8 dots | **0 dots** (identity) | 1.6 | **0.6** |
| `E·Q·INC·DEC·x` (mixed) | 2 dots | **0 dots** (identity) | 0.9 | **0.5** |

Ψ₁₆ᶠ table lookups are fast (sub-nanosecond, L1-cached 256-byte array). But Ψ₁₆ᶜ supercompilation eliminates the lookups entirely. The gap widens with chain depth — 8 operations that survive Ψ₁₆ᶠ supercompilation cost 1.6 ns; the same 8 operations under Ψ₁₆ᶜ cost 0 ns because the supercompiler proved they cancel. Details: [`extension_profiles.md`](extension_profiles.md).

---

## 6. Futamura Projections

The supercompiler is a specializer. Applying it to an interpreter paired with a known program produces a compiled version of that program — the first Futamura projection (1971). This works on the Ψ algebra because the Cayley table is total and known: every operation the interpreter performs on known data resolves at compile time.

A minimal opcode interpreter written in .psi IR — a lambda that takes an opcode and an argument, then applies the opcode via `dot` — produces identical results to direct computation when supercompiled:

```
Direct:      INC(INC(INC(f)))           → 5
Evaluator:   eval([INC,INC,INC], f)     → 5  (supercompiled)

Direct:      DEC(INV(INC(τ)))           → f
Evaluator:   eval([DEC,INV,INC], τ)     → f  (supercompiled)

Direct:      INC(DEC(INV(INC(f))))      → g
Evaluator:   eval([INC,DEC,INV,INC], f) → g  (supercompiled)
```

Five test cases (10 programs), all matching. The supercompiler traces through the interpreter's dispatch, resolves every `dot` call on known arguments, applies cancellation rules (QE, INC/DEC, INV/INV where sound), and produces the same constant as direct compilation. The interpreter is eliminated entirely — zero residual operations.

**All three Futamura projections are demonstrated**, using two tools that share the same tagged-pair expression encoding:

| Projection | Input | Output | Tool |
|------------|-------|--------|------|
| 1. Specialization = compilation | interpreter + program | compiled program | `psi_specialize.lisp` |
| 2. Specializer(interpreter) = compiler | specializer + interpreter | compiler (residual Ψ-Lisp) | `psi_specialize.lisp` |
| 3. Fixed point | transpiler compiled by Python transpiler vs. transpiler run by interpreter | byte-identical Rust output | `psi_transpile.lisp` + `psi_transpile.py` |

The self-hosted transpiler (`psi_transpile.lisp`) is a Ψ-Lisp program that takes tagged-pair expression trees and streams Rust code via `write-string`/`write-char`. It uses the same IR encoding as the specializer, so the specializer can pre-process expressions before the transpiler emits code — specialize then transpile yields constant-folded Rust with zero runtime lookups:

```
specialize(INC(INC(INC(f))))  →  Atom(5)
transpile(Atom(5))            →  "5_i64"       // zero table lookups in output
```

The fixed-point test: compile the transpiler test program via two independent paths and diff the output.

```bash
# Path A: Ψ-Lisp interpreter runs the transpiler directly
python3 psi_lisp.py --table=c examples/psi_transpile_test.lisp | sed '1d;$d' > /tmp/path_a.rs

# Path B: Python transpiler compiles the Lisp transpiler to a Rust binary,
#          then that binary runs and emits Rust code
python3 psi_transpile.py --target rust examples/psi_transpile_test.lisp > /tmp/compiled.rs
rustc -O -o /tmp/compiled /tmp/compiled.rs
/tmp/compiled | grep -v '^NIL$' > /tmp/path_b.rs

diff /tmp/path_a.rs /tmp/path_b.rs    # identical
```

```bash
python3 psi_supercompile.py --table=c examples/psi_futamura.psi    # projection 1: all 10 pairs match
python3 psi_lisp.py --table=c examples/psi_specialize.lisp         # projections 1 & 2
python3 psi_lisp.py --table=c examples/psi_transpile_test.lisp     # projection 3: self-hosted transpiler

# Rust interpreter (~25x faster — supports both tables)
kamea-rs/target/release/kamea --table=c run examples/psi_specialize.lisp     # projections 1 & 2 (Ψ₁₆ᶜ)
kamea-rs/target/release/kamea --table=c run examples/psi_transpile_test.lisp # projection 3
```

---

## 7. Universal Theorems

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
- **Turing-completeness of Ψ∗.** `[Empirical]` The term algebra Ψ∗ over any Ψ model, equipped with constructor/destructor evaluation semantics and a stepped machine, simulates 2-counter machines (Minsky 1961) using 7 axiom-forced elements: ⊤ (zero), Q (successor), E (predecessor), g (pair), f (fst), η (snd), ρ (branch). The finite algebra is decidable; TC lives in the term algebra + eval, as with combinatory logic over {S, K}. The contribution is that the basis elements are axiom-forced rather than chosen. Universal — holds for every model of the axiom class, not just Ψ₁₆ᶠ. Formal Lean verification remains open. See above.
- **Equational minimality.** `[Empirical]` Among the 4,694 equational laws cataloged by the [Equational Theories Project](https://github.com/teorth/equational_theories) (Tao et al., 2024), Ψ₁₆ᶠ satisfies exactly one non-trivial law: power-associativity (ETP Equation 4380). All other equational regularities — associativity, commutativity, idempotency, and 4,690 others — are violated. The structure that makes the algebra interesting (absorbers, role separation, Kleene barrier, actuality irreducibility, QE inverse pair) lives entirely in a richer logical fragment that the equational framework cannot express.

---

## 8. Black-Box Recovery

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

## 9. Supercompiler and Compilation Pipeline

The Cayley table is a specification. You don't have to interpret it at runtime — you can compile against it.

`psi_supercompile.py` is a partial evaluator written in Ψ-Lisp itself. It walks a Ψ-Lisp expression and applies five optimization passes, each justified by algebraic properties of the table:

| Pass | Rule | Justification |
|------|------|---------------|
| Constant folding | `(dot A B)` → table lookup when both atoms known | Cayley table is total |
| QE cancellation | `E·(Q·x)` → `x`, `Q·(E·x)` → `x` | QE inverse axiom `[Lean]`; verified on 9/16 elements; fires only when x is known valid atom |
| INC/DEC cancellation | `INC·(DEC·x)` → `x`, `DEC·(INC·x)` → `x` | Mutual inverses; fires only when x is known core element ∈ {2,3,4,5} (Ψ₁₆ᶜ only) |
| INV cancellation | `INV·(INV·x)` → `x` | Full involution, verified on all 16 elements (Ψ₁₆ᶜ only) |
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

---

## 10. Performance

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

---

## 11. Claim Matrix

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
| Five behavioral categories forced (32/45 pairs UNSAT, min 5 elements) | universal | `[SAT]` | `forced_roles_test.py` — role-aliasing at N=12 |
| Kleene wall: τ cannot merge with any encoder or inert role | universal | `[SAT]` | `forced_roles_test.py` — τ vs all 9 others UNSAT |
| Inert wall: g cannot merge with any other role | universal | `[SAT]` | `forced_roles_test.py` — g vs all 9 others UNSAT |
| Rigidity survives all collapse levels (5→7 role elements) | universal | `[SAT]` | `collapse_rigidity_test.py` — all 6 levels: |Aut|=1, WL-1 rigid |
| Distinctness axiom adds 13 requirements (32/45 already forced) | universal | `[SAT]` | `ds_search/distinctness_test.py` |
| Distinctness axiom compatible with both Ψ₁₆ᶠ and Ψ₁₆ᶜ | specific models | `[SAT]` | `ds_search/distinctness_test.py` |
| Expressiveness independently justifies distinctness (49 vs 16 cells, monotone) | structural | `[Empirical]` | `ds_search/compositional_expressiveness.py` |
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
| Ψ₁₆ᶜ satisfies all listed operations (table, roles, QE, branch, INC/DEC/INV) | specific model | `[Lean]` | `Psi16C.lean` |
| Ψ₁₆ᶜ cancellation laws (INC∘DEC, DEC∘INC, INV∘INV on core) | specific model | `[Lean]` | `Psi16C.lean` |
| Ψ₁₆ᶜ rigidity (fingerprint uniqueness, row injectivity) | specific model | `[Lean]` | `Psi16C.lean` |
| Ψ₁₆ᶜ constructibility ({⊤,⊥,Q,E} generates all 16) | specific model | `[Lean]` | `Psi16C.lean` |
| Ψ₁₆ᶜ actuality irreducibility (48/48 free tester cells) | specific model | `[Empirical]` | `ds_search/n16_c_interop.py --freedom` |
| Ψ₁₆ᶜ supercompilation: 50–67% residual reduction vs Ψ₁₆ᶠ | specific model | `[Empirical]` | `bench_c_interop.py` — cancel_chain, deep_cancel, mixed, branch |
| Extension profile modularity: same core theorems, different extension cells | architectural | `[Empirical]` | Both profiles satisfy all base axioms, differ only in free cells |
| Futamura projection 1: supercompile(interpreter, program) = supercompile(program) | universal | `[Empirical]` | `examples/psi_futamura.psi` — 10/10 pairs match under Ψ₁₆ᶜ |
| Futamura projection 2: specializer + interpreter = compiler | universal | `[Empirical]` | `examples/psi_specialize.lisp` — beta reduction eliminates interpreter |
| Futamura projection 3 (fixed point): compiled transpiler = interpreted transpiler | tooling | `[Empirical]` | `psi_transpile.lisp` compiled via `psi_transpile.py` → byte-identical Rust output |
| Self-hosted transpiler: Ψ-Lisp → Rust (6 expression types, INC/INV/DEC specialization) | tooling | `[Empirical]` | `examples/psi_transpile.lisp` — all 6 tests compile and match |
| Cancellation rule soundness: partial rules restricted to verified domain | universal | `[Empirical]` | Exhaustive 16-element check; counterexample: INC(DEC(12))=13≠12 |
| Ψ-Lisp → C/Rust transpiler (output matches interpreter) | tooling | `[Empirical]` | `psi_transpile.py --target c\|rust` — fibonacci, recursion verified |
| MMTk GC: 10M allocs in 4MB heap (MarkSweep + shadow stack roots) | tooling | `[Empirical]` | `HEAP_MB=4 cargo run -p wispy-stress --release` |

Full registry with reproduction commands: [`CLAIMS.md`](../CLAIMS.md).

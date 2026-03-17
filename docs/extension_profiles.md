# Extension Profiles

The Ψ framework separates **core** from **extension**. The core — seven role-bearing elements (⊤, Q, E, f, g, η, ρ) from five axiom-forced categories, plus the tester τ and Y-combinator — is pinned by the base axioms (L0–L8, C, D, PA, VV, QE, Branch, Compose, Y, Selection). These axioms fix ~18% of the 16×16 Cayley table: absorber rows, E-transparency, QE round-trip on core, the Selection identity η·ρ = τ, and the Y fixed-point Y·ρ = ρ·(Y·ρ). The remaining ~82% is the **extension space** — 209 free cells at N=16 under Ψ₁₆ᶜ, 192 under Ψ₁₆ᶠ.

Different fillings of the extension space serve different deployment targets. All fillings share the same universal theorems: WL-1 rigidity (Ext axiom), actuality irreducibility (tester rows unconstrained by structural axioms), Kleene separation, no right identity, constructibility, and Turing completeness of Ψ∗.

The analogy to ISA extensions is deliberate:

```
RISC-V:  RV32I (base) + M (multiply) + F (float) + V (vector) + ...
Ψ:       Core (axiom-forced elements) + Counter + IO + INV + ...
```

The base instruction set is universal. The extensions are optimized for specific deployment targets. Both are found by constrained search within a design space.

---

## Ψ₁₆ᶠ — Hardware Profile

**Target:** FPGA, embedded, self-verifying hardware.

**Extensions:** 8-state counter (INC/DEC cycling through 8 elements), IO roundtrip (GET/PUT inverse pair on core), 2×2 product (PAIR/FST/SND on {s0, s1}), SWAP involution, 1-bit logic gates (AND/OR/XOR via curried dispatch).

**Design principle:** every operation is a table lookup. No arithmetic interpretation — the hardware IS the table. An FPGA implements Ψ₁₆ᶠ as a 256-byte ROM with a single clock-cycle lookup. The 8-state counter gives a compact state machine. The product encoding enables structured data within the table itself.

**Supercompiler cancellations:** 2 (QE, EQ). INC and DEC are not mutual inverses on any fixed domain — INC cycles through 8 states, touching Q, E, ρ, η, Y, and other structural elements in the counter path. No cancellation identity is available.

**Compiled C:** residual `dot` operations emit `psi_dot(a, b)` — a single array lookup into the 256-byte table. The table is the runtime.

**Determination:** 64/256 cells fixed (25.0%). The counter cycle, IO roundtrip, product encoding, and zero-detection test collectively pin 32 non-absorber cells.

**Tester freedom:** 40/48 tester cells free. The counter-zero-test axiom (τ·s0 = ⊤, τ·sₖ = ⊥ for k≠0) fixes 8 cells in the τ row. The tester's role as zero-detector couples it to the counter extension.

**130+ Lean theorems** verify every operational constraint, with zero `sorry`.

---

## Ψ₁₆ᶜ — Software Profile

**Target:** conventional hosts via supercompile → transpile → C.

**Extensions:** 4-cycle counter on core {2,3,4,5} (modular increment/decrement), INV involution (7−x on core, full involution on all 16 elements), SEQ tester (boolean predicate).

**Design principle:** every extension row has an arithmetic interpretation that `gcc -O2` can optimize. The cycle states are contiguous (2,3,4,5), enabling single-expression C:

| Operation | Algebraic | C expression | Instructions |
|-----------|-----------|-------------|-------------|
| INC(x) | 4-cycle: 2→3→4→5→2 | `((x - 1) & 3) + 2` | 3 ops |
| DEC(x) | reverse: 2→5→4→3→2 | `((x - 3) & 3) + 2` | 3 ops |
| INV(x) | involution: 2↔5, 3↔4 | `7 - x` | 1 op |

No switch statements, no lookup tables. The contiguity of the core indices is what makes this possible — it was a consequence of the revised design (the original plan used non-contiguous states and was UNSAT due to a power-associativity conflict).

**Supercompiler cancellations:** 5 (QE, EQ, INC/DEC, DEC/INC, INV/INV). Each cancellation rule is sound because the corresponding algebraic identity holds:
- INC·(DEC·x) = x on core (follows from cycle definitions)
- DEC·(INC·x) = x on core (same)
- INV·(INV·x) = x on all 16 elements (full involution, enforced by SAT constraint)

**Compiled C:** residual `dot` operations with known INC/DEC/INV first argument emit inline arithmetic helpers (`psi_inc()`, `psi_dec()`, `psi_inv()`) instead of table lookups. After supercompilation, many operations are eliminated entirely.

**Determination:** 47/256 cells fixed (18.4%). Fewer constraints than Ψ₁₆ᶠ — a 4-element cycle pins fewer cells than an 8-state counter with IO and product encoding.

**Tester freedom:** 48/48 tester cells free. The extension constraints do not touch tester rows at all. Actuality irreducibility is fully preserved — the base-axiom theorem holds without any erosion from the extension.

**SAT-verified** (`ds_search/n16_c_interop.py`). All base axioms satisfied, plus non-idempotent constraint (only absorbers are idempotent, preserving recovery algorithm compatibility).

---

## Benchmark Comparison

### Supercompilation: Residual AST Size

Programs with paired INC/DEC and INV/INV chains — the patterns that the cancellation rules target.

| Benchmark | Pattern | Ψ₁₆ᶠ nodes | Ψ₁₆ᶜ nodes | Reduction |
|-----------|---------|-----------|-----------|-----------|
| cancel_chain | `INV·(INV·(INC·(DEC·x)))` | 16 | 8 | 50% |
| deep_cancel | `INV·INV·(INC·DEC)³·x` | 24 | 8 | 67% |
| mixed_cancel | `E·(Q·(INC·(DEC·x)))` | 12 | 8 | 33% |
| branch_cancel | `if τ·x then INC·DEC·x else INV·INV·x` | 21 | 13 | 38% |

Under Ψ₁₆ᶠ, `(defun deep x ...)` with 8 nested operations survives supercompilation unchanged — all 8 `dot` nodes remain as residual code. Under Ψ₁₆ᶜ, the same function supercompiles to `(defun deep x x)` — the identity function. Zero residual operations.

### Compiled C: Runtime Performance

100M iterations, `gcc -O2`, each iteration applies the operation to `(i & 15)`.

| Configuration | cancel_chain (4 ops) | deep_cancel (8 ops) |
|---------------|---------------------|---------------------|
| Ψ₁₆ᶠ generic `psi_dot()` | 0.9 ns/iter | 1.6 ns/iter |
| Ψ₁₆ᶜ inline helpers (no supercomp) | 2.0 ns/iter | 4.1 ns/iter |
| Ψ₁₆ᶜ supercompiled | **0.5 ns/iter** | **0.6 ns/iter** |

The inline helpers *alone* are slower than table lookup — the branch (`if (x >= 2 && x <= 5)`) costs more than indexing a 256-byte array that fits in L1 cache. This is the wrong comparison. The arithmetic interpretations exist to make the cancellation rules *sound*, and the cancellation rules eliminate the code. The fastest operation is the one that doesn't exist.

After supercompilation:
- Ψ₁₆ᶜ is **2–3x faster** than Ψ₁₆ᶠ on cancellable patterns
- The gap grows with chain depth (8 ops: 2.7x, 4 ops: 1.8x)
- For non-cancellable patterns (no paired operations), both tables produce identical residual code

---

## Actuality Irreducibility Across Profiles

| Profile | Tester cells | Free | Fixed | Notes |
|---------|-------------|------|-------|-------|
| Ψ₁₆ᶠ | 48 (3 testers × 16) | 40 | 8 | Counter-zero-test couples τ to counter states |
| Ψ₁₆ᶜ | 48 (3 testers × 16) | 48 | 0 | No tester coupling — full irreducibility preserved |
| Base axioms only | 48 | 48 | 0 | Universal theorem: structural axioms never constrain testers |

The 8 fixed tester cells in Ψ₁₆ᶠ are all in the τ row at counter-state positions — the zero-detection capability requires τ to distinguish s0 from s1–s7. This is a deliberate trade: Ψ₁₆ᶠ sacrifices 8 tester cells for the ability to test counter zero within the table. Ψ₁₆ᶜ doesn't need this because C has native comparison.

Both profiles confirm that the tester's freedom is not an accident of the specific table but a structural consequence of the axiom architecture.

---

## Design Methodology

The extension space is not undetermined — it is a **design surface**. Each profile is found by SAT search with target-specific constraints added to the base axiom set:

1. **Define target semantics.** What operations does the deployment target need?
2. **Express as SAT constraints.** Counter cycles, involutions, IO pairs, role assignments.
3. **Search.** Z3 finds a model satisfying all base axioms plus extension constraints, or reports UNSAT (the constraints are incompatible — the original Ψ₁₆ᶜ design was UNSAT due to a PA conflict and was redesigned).
4. **Verify.** Cell-by-cell freedom analysis confirms determination percentage. Cancellation identities are checked empirically. WL-1 rigidity is verified (both profiles are rigid in round 0).
5. **Build toolchain.** Runtime header, supercompiler rules, transpiler specialization — all derived mechanically from the verified table.

The base axioms guarantee structural properties. The extensions are optimized for specific deployment targets. The SAT search is the moment of truth: either the extension constraints are compatible with the axioms and a valid rigid table exists, or they conflict and the design needs adjustment.

---

## Files

| File | Description |
|------|-------------|
| `ds_search/n16_c_interop.py` | Ψ₁₆ᶜ SAT search + freedom analysis |
| `ds_search/n16c_expressiveness_search.py` | Ψ₁₆ᶜ table search (maximally expressive model) |
| `ds_search/n16_freedom.py` | Ψ₁₆ᶠ SAT search + freedom analysis |
| `psi_star.py` | Ψ∗ term algebra over Ψ₁₆ᶠ |
| `psi_star_c.py` | Ψ∗ term algebra over Ψ₁₆ᶜ |
| `psi_runtime.h` | C runtime for Ψ₁₆ᶠ (256-byte table + inline dot) |
| `psi_runtime_c.h` | C runtime for Ψ₁₆ᶜ (table + arithmetic helpers) |
| `psi_supercompile.py` | Supercompiler (2 or 5 rules, table-dependent) |
| `psi_transpile.py` | Transpiler (specializes INC/DEC/INV for Ψ₁₆ᶜ) |
| `bench_c_interop.py` | Benchmark: Ψ₁₆ᶜ vs Ψ₁₆ᶠ comparison |

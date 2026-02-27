<p align="center">
  <img src="https://upload.wikimedia.org/wikipedia/commons/thumb/7/7a/Albrecht_D%C3%BCrer_-_Melencolia_I_-_Google_Art_Project_%28_AGDdr3EHmNGyA%29.jpg/1280px-Albrecht_D%C3%BCrer_-_Melencolia_I_-_Google_Art_Project_%28_AGDdr3EHmNGyA%29.jpg" width="250" alt="Albrecht Dürer — Melencolia I (1514)" />
</p>

# Kamea

**A minimal self-modeling framework for relational description, with machine-checked proofs in Lean 4.**

---

## Three Theorems, Five Extensions, and a OISC Hardware Emulator

This repository contains Lean 4 formalizations of five results about finite algebraic structures that model themselves, plus a Python implementation extending the algebra to 66 atoms with a full 74181 ALU, 32-bit wide arithmetic, 16-bit multiply, byte-level IO, and a QUALE symmetry-breaker — all uniquely recoverable from a scrambled Cayley ROM by a dedicated hardware scanner.

All Lean proofs compile with **zero `sorry`** on Lean 4.28.0 / Mathlib v4.28.0.

**Theorem 1 (Existence).** Intrinsically reflexive Distinction Structures exist. A 16-element symmetric algebra (Δ₀) and a 17-element directed algebra (Δ₁) each satisfy axioms A1--A7', Ext, and contain behavioral self-models: internal encodings whose elements, when composed by the structure's own operation, reproduce the behavior of the structure's own components.

**Theorem 2 (Discoverability).** Discoverably reflexive Distinction Structures exist. The 17-element directed model Δ₁ has a self-model that is recoverable from black-box probing alone, with each of the 8 recovery steps proved unique. An observer with no prior knowledge can identify every structural component purely from the operation table.

**Theorem 3 (Irreducibility).** Actuality is not determined by structure. Two models (Δ₁ and Δ₁') on the same 18-element carrier share 322 out of 324 operation table entries, both satisfy all axioms and reflexivity conditions, yet differ in actuality assignment. No structural predicate resolves the difference. The only way to determine which elements are actual is to query the actuality tester directly.

**Extension 1 (Δ₂ -- Flat Quoting).** Δ₁ extended with QUOTE, EVAL, APP, UNAPP restricted to flat (one-level) evaluation. The carrier is finite, the operation is total, and all properties are proved by `decide`. This is the Datalog-level extension: naming without executing, inspecting without reducing.

**Extension 2 (Δ₃ -- Recursive Evaluation).** Δ₂ extended with recursive EVAL via a fuel-bounded interpreter. Evaluating a quoted application node recursively evaluates both subterms, then applies the results. Proved in Lean using a combined eval/dot function structurally recursive on fuel. Concrete computations (flat eval, nested eval, triple nesting, QUOTE/EVAL roundtrips) verified by `native_decide`.

**Extension 3 (74181 ALU + IO).** Δ₂ extended with 26 new atoms: 16 nibble data values (N0–NF), 3 ALU dispatch atoms, 2 ALU predicates, 1 nibble successor (N_SUCC), and 4 IO atoms (IO_PUT, IO_GET, IO_RDY, IO_SEQ). Total: 47 atoms.

**Extension 4 (W32 + MUL).** 18 additional atoms for 32-bit wide arithmetic (W_ADD, W_SUB, W_CMP, W_XOR, W_AND, W_OR, W_NOT, W_SHL, W_SHR, W_ROTL, W_ROTR, W_PACK8, W_LO, W_HI, W_MERGE, W_NIB) and 16-bit multiply (MUL16, MAC16). Total: 65 atoms.

**Extension 5 (QUALE).** A single symmetry-breaking atom that makes the algebra *rigid*. The 26 opaque atoms (D2 + IO + W32 + MUL) all have identical all-p Cayley rows; QUALE gives each a unique structurally-identifiable target in its column. All 66 atoms are now uniquely identifiable from the Cayley table alone — no term-level probing required. A dedicated hardware scanner (`CayleyScanner`) reads the Cayley ROM directly at boot, recovering the complete atom identity map in ~7,300 ROM reads.

Six machine-checked results, plus a computationally complete extension with hardware emulator. Self-description is possible. Communication is possible. Computation is possible. But the question of what's real cannot be settled by structure alone.

---

## Why It Matters

Many systems can represent themselves (Godel numbering, quines, metacircular evaluators). Fewer do so *behaviorally* -- where the encoding elements don't just name components but act like them under the system's own operation. Fewer still are *discoverable* -- where an external observer can recover the self-model with no documentation.

Δ₁ achieves all three: self-representation, behavioral fidelity, and black-box recoverability. The recovery procedure is not a heuristic -- each step is a uniqueness lemma, machine-checked over the finite domain.

The irreducibility result shows what the framework *cannot* do. Given a complete structural description of a self-modeling system, the question "which elements are actual?" has multiple valid answers, and the structure alone does not select among them. Two fully valid self-modeling Distinction Structures can agree on every compositional fact and disagree only on actuality. The actuality tester carries irreducible information: there is no structural back door. This is "existence is not a predicate" as a machine-checked theorem.

The extensions (Δ₂, Δ₃) show the path from algebra to computation: Δ₂ adds data representation (quoting without executing), Δ₃ adds recursive evaluation (executing quoted terms). Both are machine-verified. The boundary between finite decidable algebra and recursive interpretation is precisely located.

The QUALE extension addresses a fundamental obstruction: as the algebra grows, groups of atoms become structurally indistinguishable (identical Cayley rows), creating an automorphism group (S₂₆ for the 26 opaque atoms). QUALE trivializes this symmetry with a single column of unique values, making the algebra *rigid* — every atom uniquely identifiable from the operation table alone. A dedicated hardware scanner reads the Cayley ROM at boot to recover the complete identity map in ~7,300 ROM reads.

---

## Repository Structure

```
DistinctionStructures/
├── lakefile.lean                                # Build configuration
├── lean-toolchain                               # Lean version pin
├── DistinctionStructures/
│   ├── Basic.lean                               # Abstract DS definitions and axioms
│   ├── Delta0.lean                              # Δ₀: 16-element symmetric model
│   ├── Delta1.lean                              # Δ₁: 17-element directed model
│   ├── Discoverable.lean                        # 8 recovery lemmas (discoverability)
│   ├── ActualityIrreducibility.lean             # Actuality irreducibility theorem
│   ├── Delta2.lean                              # Δ₂: flat quoting (finite, decidable)
│   └── Delta3.lean                              # Δ₃: recursive eval (fuel-bounded)
├── kamea.py                                     # Core 66-atom algebra (D1+D2+74181+IO+W32+MUL+QUALE)
├── kamea_blackbox.py                            # Black-box recovery (48-atom subset)
├── ds_repl.py                                   # Interactive REPL with all 66 atoms
├── emulator/
│   ├── __init__.py
│   ├── chips.py                                 # Hardware primitives (EEPROM, IC74181, SRAM, Register, FIFO)
│   ├── cayley.py                                # Cayley ROM builder (66×66 byte array)
│   ├── machine.py                               # Clocked eval/apply state machine (64-bit words)
│   ├── host.py                                  # High-level interface (term loading, decoding)
│   ├── scanner.py                               # CayleyScanner: boot-time hardware recovery module
│   ├── recovery.py                              # Black-box recovery via dispatch unit + scanner
│   ├── debugger.py                              # Textual TUI debugger for the emulator
│   └── test_machine.py                          # Verification suite (4356 atom pairs, 768 ALU ops)
├── examples/
│   ├── io_demo.ds                               # IO atoms demo (prints "Hi!")
│   └── alu_74181_demo.ds                        # ALU operations demo
├── ai_interpretability/                         # ML interpretability experiments
├── docs/
│   ├── Distinction_Structures.md                # Full document with proofs and philosophy
│   └── Distinction_Structures_Complete.md       # Complete version
└── README.md
```

## Building

```bash
# Requires Lean 4.28.0 and Mathlib v4.28.0
lake build
```

All theorems are checked by `decide` or `native_decide`, which is appropriate and complete for finite carrier types with decidable equality. The full project is ~1630 lines of Lean across 7 files. Zero sorry.

---

## The Five Results in Detail

### Theorem 1: Existence (Δ₀ and Δ₁)

| Property | Δ₀ (Symmetric) | Δ₁ (Directed) |
|----------|----------------|----------------|
| Elements in D(ι) | 14 (+ 2 in D(κ)) | 17 (+ 2 in D(κ)) |
| Operation | Σ : Finset D(ι) → D(ι) | · : D(ι) → D(ι) → D(ι) |
| Rules | Priority-based on Finset | 26 first-match rules |
| Self-model | 12 encoding elements | Encoding elements with H1--H3 |
| Reflexivity | Intrinsic | Discoverable |
| Lean files | `Delta0.lean` | `Delta1.lean` + `Discoverable.lean` |

Both models satisfy A1--A7', Ext, H1--H3, and IR1--IR5. The switch from symmetric to directed composition costs one additional element but unlocks discoverability.

### Theorem 2: Discoverability (Recovery Lemmas)

An observer with access only to the operation `dot : D → D → D` (no documentation, no labels) can recover every structural component of Δ₁:

| Step | What is recovered | Lean theorem |
|------|-------------------|-------------|
| 1 | Booleans (top, bot) -- the only left-absorbers | `boolean_uniqueness` |
| 2 | Testers (e_I, d_K, m_K, m_I) -- non-booleans with boolean-valued output | `tester_characterization` |
| 3 | Tester signatures by decoded-set size (16, 2, 2, 1) | `tester_card_m_I`, `tester_card_e_I`, `tester_card_d_K`, `tester_card_m_K` |
| 4 | Context tester vs domain tester -- rich vs inert decoded elements | `rich_context_tokens`, `inert_kappa_tokens` |
| 5 | e_D vs e_M -- encoder asymmetry | `encoder_pair`, `encoder_asymmetry` |
| 6 | i vs k -- context token discrimination | `context_token_discrimination` |
| 7 | p (non-actual element) -- unique m_I reject | `junk_identification` |
| 8 | e_Sigma, s_C, e_Delta -- unique triple with synthesis property | `triple_identification`, `triple_uniqueness` |

Each step has exactly one solution. The recovery is not heuristic -- it is mechanically verified.

### Theorem 3: Actuality Irreducibility

Two models, Δ₁ and Δ₁', are constructed on the same 18-element carrier (the 17 elements of Δ₁ plus a second surplus element q). They differ in exactly two entries of the 18x18 operation table -- both in the m_I row:

| | Δ₁ | Δ₁' |
|---|---|---|
| m_I · p | bot (rejects p) | top (accepts p) |
| m_I · q | top (accepts q) | bot (rejects q) |
| All other 322 entries | identical | identical |
| Actuality set | M = D \ {p} | M' = D \ {q} |

Both models independently satisfy Ext, H1--H3, IR1--IR4, A2, A5, A7'.

Key theorems in `ActualityIrreducibility.lean`:

| Theorem | What it proves |
|---------|---------------|
| `ops_agree_non_mI` | ∀ x y, x ≠ m_I → dot1 x y = dot1' x y |
| `ops_differ_only_mI` | The only disagreements are at (m_I, p) and (m_I, q) |
| `right_image_same_dot1` | ∀ x ≠ m_I, dot1 x p = dot1 x q |
| `cross_model_right_image` | ∀ x ≠ m_I, dot1 x p = dot1' x q |
| `mI_is_unique_discriminator` | m_I is the only element that classifies p and q differently |
| `no_universal_actuality_predicate` | No predicate matches actualM in Δ₁ and actualM' in Δ₁' |
| `actuality_irreducibility` | Combined 7-conjunct theorem |

### Extension 1: Δ₂ -- Flat Quoting

Δ₂ adds QUOTE, EVAL, APP, UNAPP to Δ₁'s 17 atoms (21 total). Evaluation is flat: EVAL on a quoted application node looks up Δ₁'s dot table once. No recursion, no unbounded terms. The carrier includes atoms, quoted atoms, application nodes, bundles, and partial applications -- all finite.

Key theorems in `Delta2.lean`:

| Theorem | What it proves |
|---------|---------------|
| `eval_quote_inverse` | ∀ x, EVAL · (QUOTE · x) = x |
| `unapp_app_roundtrip` | ∀ f x, UNAPP · (APP · f · x) = bundle(f, x) |
| `bundle_query_top/bot` | ∀ f x, bundle(f,x) · top = f, bundle(f,x) · bot = x |
| `eval_appnode` | ∀ f x : D1ι, EVAL · app(f,x) = dot(f,x) |
| `eval_app_computes` | ∀ f x : D1ι, EVAL · (APP · f · x) = dot(f,x) |
| `d1_fragment_preserved` | ∀ x y : D1ι, dot2(x,y) = dot(x,y) |
| `quoted_inert_d1` | ∀ d : D1ι, d · quoted(y) = p |

All proofs by `decide` over finite types.

### Extension 2: Δ₃ -- Recursive Evaluation

Δ₃ extends Δ₂ with recursive EVAL: evaluating a quoted application node recursively evaluates both subterms, then applies the results. This is the boundary between algebra and interpreter.

The mutual recursion between eval and dot is resolved via a fuel parameter: `interp (fuel : Nat) (mode : Bool) (a b : T3) → T3`, structurally recursive on fuel. For any finite term, sufficient fuel exists for complete evaluation.

Key theorems in `Delta3.lean`:

| Theorem | What it proves |
|---------|---------------|
| `eval_quote_all_atoms` | All 21 atoms roundtrip through QUOTE/EVAL |
| `flat_eval_eD_k` | eval(app(e_D, k)) = d_K |
| `flat_eval_eM_i` | eval(app(e_M, i)) = m_I |
| `flat_eval_eSigma_sC` | eval(app(e_Sigma, s_C)) = e_Delta |
| `nested_eval_mI` | eval(app(m_I, app(e_I, i))) = top (recursive!) |
| `eval_quoted_nested` | EVAL · quote(app(m_I, app(e_I, i))) = top |
| `triple_nesting` | eval(app(e_M, app(e_D, app(e_I, i)))) = p (3 levels) |
| `d1_preserved` | All 17x17 Δ₁ atom pairs compute correctly |
| `full_app_unapp_roundtrip` | APP → UNAPP → bundle query roundtrip |

All proofs by `native_decide` on concrete fuel values.

### Extensions 3–5: 74181 ALU + IO + W32 + MUL + QUALE (Python)

The full algebra extends Δ₂'s 21 atoms to 66 total. The design maps the classic 74181 4-bit ALU chip's control interface directly onto the algebra: the 4-bit function selector IS a nibble atom, the mode select IS the choice of dispatch atom. No translation layer — the algebra speaks the chip's native language.

**Atom inventory (66 total):**

| Group | Count | Atoms | Role |
|-------|-------|-------|------|
| Δ₁ core | 17 | ⊤, ⊥, p, i, k, a, b, e_I, e_D, e_M, e_Σ, e_Δ, d_I, d_K, m_I, m_K, s_C | Self-modeling primitives |
| Δ₂ extensions | 4 | QUOTE, EVAL, APP, UNAPP | Term construction and evaluation |
| Nibbles | 16 | N0–NF | 4-bit data values / ALU selectors |
| ALU dispatch | 3 | ALU_LOGIC, ALU_ARITH, ALU_ARITHC | 74181 mode select (logic / arith / arith+carry) |
| ALU predicates | 2 | ALU_ZERO, ALU_COUT | Zero-detect and carry-out testers |
| N_SUCC | 1 | N_SUCC | Nibble successor (16-cycle) |
| IO | 4 | IO_PUT, IO_GET, IO_RDY, IO_SEQ | Byte-level stdin/stdout |
| W32 | 16 | W_PACK8, W_LO, W_HI, W_MERGE, W_NIB, W_ADD, W_SUB, W_CMP, W_XOR, W_AND, W_OR, W_NOT, W_SHL, W_SHR, W_ROTL, W_ROTR | 32-bit wide arithmetic |
| MUL | 2 | MUL16, MAC16 | 16-bit multiply / multiply-accumulate |
| QUALE | 1 | QUALE | Symmetry breaker — makes all atoms uniquely identifiable |

**Recovery via QUALE (single phase, Cayley-only):**

The 26 opaque atoms (D2 + IO + W32 + MUL) have identical all-p Cayley rows and are structurally indistinguishable at the atom-atom level. QUALE breaks this S₂₆ symmetry: each opaque atom maps to a unique structurally-identifiable target in the QUALE column (e.g., `dot(QUOTE, QUALE) = k`, `dot(W_ADD, QUALE) = N_SUCC`).

| Phase | Method | Atoms recovered |
|-------|--------|----------------|
| Phase 1a | Cayley-level | 17 D1 atoms (absorbers, testers, encoders, synthesis triple) |
| Phase 1b | Cayley-level | 22 atoms (predicates, nibble Z/16Z, N_SUCC, dispatch, QUALE) |
| Phase 1c | QUALE column | 27 opaque atoms (one ROM read each via `dot(u, QUALE)`) |

All 66 atoms identified from the 66×66 Cayley table alone. No term-level probing required. Verified across 1000+ random permutations at 100% recovery rate.

### Emulator: Kamea Machine

A cycle-accurate emulator of the hardware architecture: Cayley ROM, IC74181 ALU, SRAM heap, hardware stack, UART FIFOs, a microcode-driven eval/apply state machine, and a dedicated boot-time recovery scanner. One dispatch unit handles all term-level operations — both normal evaluation and black-box recovery use the same code path.

**Architecture:**

| Component | Model | Role |
|-----------|-------|------|
| Cayley ROM | EEPROM (16-bit addr, 8-bit data) | 66×66 atom-level dot lookup (4,356 bytes) |
| ALU | IC74181 (pin-accurate) | 32 operations via 3 mode atoms × 16 selectors |
| Heap | SRAM (64-bit words) | Term storage (tag + left + right + meta) |
| Stack | SRAM (64-bit words) | Eval/apply continuation stack |
| UART | 16-byte TX/RX FIFOs | Byte-level IO |
| Scanner | CayleyScanner | Boot-time atom identity recovery from ROM |

**Word format:** 64 bits — 4-bit tag, 24-bit left, 24-bit right, 12-bit meta. 17 tag types covering atoms, quoted terms, applications, ALU partials, IO partials, bundles, W32 values, W16 values, pack state, W32/MUL operation partials, and extended operations.

**State machine:** FETCH → DECODE → EVAL_R → APPLY → dispatch → RETURN. The dispatch unit routes based on tag and atom index, handles Cayley ROM lookup, ALU firing, partial application building, IO operations, W32/MUL wide arithmetic, and quote/eval/app/unapp.

**CayleyScanner (boot-time recovery):** A hardware module that reads the Cayley ROM directly to identify all 66 atoms — no heap, no stack, no eval/apply. Runs at boot before the dispatch unit starts. Three phases: D1 recovery (absorbers/testers/encoders), nibble/ALU/QUALE identification, and QUALE column resolution of all 27 opaque atoms. Avg ~7,300 ROM reads per scrambled ROM.

**Recovery comparison:**

| Method | Atoms | Heap | Stack | Avg time (10 seeds) |
|--------|-------|------|-------|---------------------|
| CayleyScanner (hardware) | 66/66 | 0 | 0 | 0.02s |
| Dispatch unit (eval/apply) | 66/66 | ~600 words | yes | 0.05s |

```bash
# Run emulator tests (4356 atom pairs + ALU + IO + W32 + MUL)
uv run python -m emulator.test_machine

# Run black-box recovery through the emulator (10 seeds)
uv run python -m emulator.recovery --seeds 10

# Run hardware scanner recovery (10 seeds)
uv run python -m emulator.recovery --seeds 10 --scanner

# Launch TUI debugger
uv run python -m emulator.debugger

# Run emulator CLI demo
uv run python -m emulator.host
```

**Usage (REPL):**

```bash
# ALU: 3 XOR 5 = 6
uv run ds_repl.py -e '(((ALU_LOGIC :N6) :N3) :N5)'

# ALU: 7 + 5 = 12
uv run ds_repl.py -e '(((ALU_ARITH :N9) :N7) :N5)'

# IO: print "Hi" followed by newline
uv run ds_repl.py -e '((:IO_SEQ ((:IO_PUT :N4) :N8)) ((:IO_PUT :N6) :N9))'

# QUALE: identity check
uv run ds_repl.py -e '(:QUALE :QUALE)'

# Run verification suite (200 seeds)
uv run python kamea.py
```

---

## The Progression

| Level | Elements | Operation | Key capability | Carrier | Source |
|-------|----------|-----------|---------------|---------|--------|
| Δ₀ | 16 | Σ (symmetric) | Self-modeling | Finite | `Delta0.lean` |
| Δ₁ | 17 | · (directed) | Discoverable self-modeling | Finite | `Delta1.lean` |
| Δ₂ | 21 | · + QUOTE/EVAL | Flat quoting (name without executing) | Finite | `Delta2.lean` |
| Δ₃ | 21 | · + recursive EVAL | Recursive evaluation (execute nested terms) | Unbounded | `Delta3.lean` |
| Kamea | 47 | · + ALU + IO | 74181 arithmetic + byte I/O | Unbounded | `kamea.py` |
| Kamea+W32 | 65 | · + W32 + MUL | 32-bit wide arithmetic + 16-bit multiply | Unbounded | `kamea.py` |
| Kamea+QUALE | 66 | · + QUALE | Rigid algebra (all atoms Cayley-identifiable) | Unbounded | `kamea.py` |

Each step adds exactly one capability. The formalizability boundary falls between Δ₂ (finite, fully decidable) and Δ₃ (unbounded terms, fuel-bounded proofs). Both are machine-verified. The Kamea extensions (Python) add computational completeness: 32 ALU operations, 32-bit wide arithmetic, 16-bit multiply, byte I/O, and a QUALE symmetry-breaker that makes the entire algebra rigid — every atom uniquely identifiable from the Cayley table alone.

---

## What Is Not Proved

- **Minimality.** We do not prove that 16 (resp. 17) is the minimum element count. The models are upper bound witnesses.
- **Symmetric impossibility.** The symmetric synthesis barrier is demonstrated by construction but not proved as a general impossibility theorem.
- **Categorical formalization.** The category-theoretic perspective is discussed in the document but not formalized in Lean.
- **Δ₃ termination.** The fuel parameter makes Δ₃ total, but we do not prove that for every finite term there exists sufficient fuel (this is true but requires a separate well-foundedness argument).
- **Kamea Lean formalization.** The 66-atom extension is verified empirically in Python (1000+ seeds, 100% recovery via QUALE). Lean proofs for the extension atoms' uniqueness theorems are planned but not yet implemented.

## Empirical Testing

The `kamea.py` module implements the full 66-atom algebra with verification suite and black-box recovery. Running `kamea.py` directly executes the complete test suite including Cayley table verification, D1 recovery, nibble/ALU/QUALE identification, and QUALE-based opaque atom resolution across 1000+ random permutations (all pass).

The `kamea_blackbox.py` module implements term-level black-box recovery for a 48-atom subset (D1 + D2 + nibbles + ALU + N_SUCC + IO + QUALE), demonstrating that QUALE eliminates the need for term-level Phase 2/3 probing.

The hardware `CayleyScanner` (`emulator/scanner.py`) recovers all 66 atoms from a scrambled Cayley ROM using only ROM reads — no heap, no stack, no eval/apply. Verified across 100+ seeds.

The `ds_repl.py` interactive REPL provides an eval/apply interpreter for the full 66-atom algebra with real IO effects (stdout/stdin).

The `ai_interpretability/` directory contains neural network experiments testing whether the recovery procedure transfers to learned approximations of the algebra.

## Background Document

The full mathematical and philosophical development is in [`docs/Distinction_Structures.md`](docs/Distinction_Structures.md). It covers the four concepts (Distinction, Context, Actuality, Synthesis), both existence proofs, the recovery procedure, the symmetric synthesis barrier, epistemological implications, and the path to computation.

## License

MIT

## Citation

If you use this work, please cite:

```
@software{kamea_2026,
  author = {Stefano Palmieri},
  title = {Kamea: A Minimal Self-Modeling Framework},
  year = {2026},
  note = {Lean 4 formalization (0 sorry) of five machine-checked results: existence (Δ₀, Δ₁), discoverability (8 recovery lemmas), actuality irreducibility, flat quoting (Δ₂), recursive evaluation (Δ₃). Python extension: 66-atom Kamea algebra with 74181 ALU, W32 wide arithmetic, MUL16 multiply, IO, and QUALE symmetry-breaker. Hardware emulator with CayleyScanner boot-time recovery. 100\% black-box recovery across 1000+ seeds.}
}
```

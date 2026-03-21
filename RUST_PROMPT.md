---

**Build the Ψ∗ Rust emulator with WASM target and web debugger.**

**Context:**

Ψ₁₆ᶠ is a 16-element self-describing algebra. Ψ∗ is the term algebra over it — Turing complete using 7 axiom-forced elements corresponding to McCarthy's 1960 Lisp primitives. We have a working Python implementation (`psi_star.py` for the algebra, `psi_lisp.py` for the Ψ-Lisp transpiler). The Rust emulator is the production runtime.

The reference implementations are the source of truth:
- `psi_star.py` — term representation, evaluation semantics, the Cayley table
- `psi_lisp.py` — Ψ-Lisp parser, translator, evaluator, builtins

**Read both files carefully before writing any Rust.** The evaluation semantics are subtle — constructor laziness, rule priority, structural dispatch. The Rust implementation must match the Python behavior exactly. Run the Python test suite (`examples/psi_*.lisp`) and understand what each test exercises before reimplementing.

**Crate structure:**

```
kamea-rs/
├── Cargo.toml                    # workspace
├── crates/
│   ├── psi-core/                 # The algebra — #![no_std], zero dependencies
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── table.rs          # 16×16 Cayley table as const array
│   │       ├── term.rs           # Term enum + arena allocator
│   │       └── eval.rs           # Ψ∗ evaluator (pure function)
│   ├── psi-runtime/              # The machine — heap, IO, step loop
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── heap.rs           # Arena-based term storage
│   │       ├── io.rs             # IO channel abstraction
│   │       └── machine.rs        # Step loop, builtins, environment
│   ├── psi-cli/                  # Native CLI — runner, REPL, debugger
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── main.rs
│   └── psi-web/                  # WASM target + browser debugger
│       ├── Cargo.toml
│       ├── src/
│       │   └── lib.rs            # wasm-bindgen exports
│       └── www/
│           ├── index.html
│           ├── debugger.js
│           └── style.css
├── tests/
│   ├── eval_tests.rs             # Port of Python eval tests
│   └── lisp_tests.rs             # Port of psi_*.lisp test suite
└── examples/
    └── *.lisp                    # Copy from Python examples
```

**Phase 1: psi-core (the algebra)**

This crate is `#![no_std]`. No heap allocation. No IO. No system calls. It compiles to ANY target — WASM, ARM bare metal, x86, embedded, FPGA soft core.

`table.rs`:
```rust
/// The Ψ₁₆ᶠ Cayley table. 256 bytes. Fits in L1 cache.
/// Copy this exactly from psi_star.py's PSI_FULL constant.
pub const TABLE: [[u8; 16]; 16] = [
    // ... extract from psi_star.py ...
];

/// Element names for debugging
pub const NAMES: [&str; 16] = [
    "⊤", "⊥", "f", "τ", "g", "SEQ", "Q", "E",
    "ρ", "η", "Y", "PAIR", "s0", "INC", "GET", "DEC",
];

/// Role constants
pub const TOP: u8 = 0;
pub const BOT: u8 = 1;
pub const Q: u8 = 6;
pub const E: u8 = 7;
pub const F_ENC: u8 = 2;
pub const G_ENC: u8 = 4;
pub const ETA: u8 = 9;
pub const RHO: u8 = 8;
pub const TAU: u8 = 3;
pub const Y_COMB: u8 = 10;

/// One dot operation — the entire algebra.
#[inline(always)]
pub fn dot(a: u8, b: u8) -> u8 {
    TABLE[a as usize][b as usize]
}
```

`term.rs`:
```rust
/// Term representation. Arena-allocated for cache friendliness.
/// Atoms are indices 0-15 stored inline. App nodes reference arena slots.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Term {
    Atom(u8),
    App { fun: u32, arg: u32 },  // indices into Arena
}

/// Fixed-size arena for term allocation.
/// Grows from index 0. No deallocation (arena-style).
pub struct Arena {
    nodes: Vec<Term>,  // use alloc::vec::Vec for no_std + alloc
}

impl Arena {
    pub fn new(capacity: usize) -> Self { ... }
    pub fn alloc(&mut self, term: Term) -> u32 { ... }
    pub fn get(&self, idx: u32) -> Term { ... }
    pub fn app(&mut self, fun: u32, arg: u32) -> u32 {
        self.alloc(Term::App { fun, arg })
    }
    pub fn atom(&mut self, a: u8) -> u32 {
        self.alloc(Term::Atom(a))
    }
}
```

Note: for `no_std` compatibility, use `alloc::vec::Vec` with a feature flag, or accept a `&mut [Term]` slice from the caller. The arena should work with both heap-allocated (native/WASM) and static (embedded) backing storage.

`eval.rs`:

This is the critical file. **Port the evaluation rules from `psi_star.py` exactly.** The rule priority order must match:

```
1. Atom self-evaluation:     eval(Atom(x)) = Atom(x)
2. Q (quote/lazy):           eval(App(Q, t)) = App(Q, t)        — do NOT eval t
3. Constructor rules:        eval(App(g, t)) = App(g, eval(t))   — g evaluates arg
4. Destructor rules:
     eval(App(E, App(Q, t))) = eval(t)                           — E unwraps Q
     eval(App(f, App(App(g, a), b))) = eval(a)                   — car of pair
     eval(App(η, App(App(g, a), b))) = eval(b)                   — cdr of pair
5. Control:
     eval(App(ρ, t)):
       let v = eval(t)
       if v is Atom: eval(App(f_enc, t))                         — base case path
       if v is App:  eval(App(g_enc, t))                         — recursive case path
6. Y-combinator:
     eval(App(Y, f)) = eval(App(f, App(Y, f)))                  — fixed-point unfold
7. Default:
     eval(App(a, b)):
       let va = eval(a), vb = eval(b)
       if both atoms: Atom(dot(va, vb))                          — table lookup
       else: App(va, vb)                                         — irreducible
```

**Critical details to get right:**
- Q is LAZY. `App(Q, t)` returns `App(Q, t)` without evaluating `t`. This is what gives unbounded data nesting. Get this wrong and numbers break.
- Rule matching must check for specific atom values in function position BEFORE falling through to default. Pattern: `App(Atom(Q), _)`, `App(Atom(E), App(Atom(Q), _))`, etc.
- The evaluator needs a fuel/depth limit to prevent infinite recursion on diverging terms. The Python version may handle this via Python's stack limit. Rust needs an explicit counter.
- The arena grows during evaluation (constructors allocate). The evaluator takes `&mut Arena`.

Add a configurable evaluation limit:
```rust
pub struct EvalConfig {
    pub max_depth: usize,     // default 10_000
    pub max_allocs: usize,    // default 1_000_000
}

pub fn eval(arena: &mut Arena, term: u32, config: &EvalConfig) -> Result<u32, EvalError> {
    eval_inner(arena, term, config, 0)
}
```

**Phase 1 tests:** Port the core eval tests from `psi_star.py`. At minimum:
- `dot(Q, x)` for all 16 atoms matches Python table
- `eval(App(Q, Atom(3)))` = `App(Q, Atom(3))` (quote is lazy)
- `eval(App(E, App(Q, Atom(3))))` = `Atom(3)` (E unwraps Q)
- `eval(App(App(G, Atom(3)), Atom(5)))` = pair (g constructs)
- `eval(App(F, pair))` = first element (car)
- `eval(App(ETA, pair))` = second element (cdr)
- Nested Q-chains for number encoding/decoding
- 2-counter machine simulation matches Python traces

**Phase 2: psi-runtime (the machine)**

This crate adds everything the evaluator needs to run real programs.

`heap.rs`:
```rust
/// Wraps Arena with growth policy and GC hooks (future).
pub struct Heap {
    arena: Arena,
    // GC metadata if needed later
}
```

`io.rs`:
```rust
/// IO channel abstraction.
/// Native: stdin/stdout.
/// WASM: buffer that JS reads/writes.
pub trait IoChannel {
    fn put(&mut self, byte: u8);
    fn get(&mut self) -> Option<u8>;
    fn ready(&self) -> bool;
}

pub struct StdIo;      // Native: wraps stdin/stdout
pub struct BufferIo {   // WASM: ring buffer, JS-accessible
    input: VecDeque<u8>,
    output: Vec<u8>,
}
```

`machine.rs`:
```rust
/// The Ψ∗ machine. Holds heap, IO, environment, step counter.
pub struct Machine<I: IoChannel> {
    pub heap: Heap,
    pub io: I,
    pub steps: u64,
    pub eval_config: EvalConfig,
}

impl<I: IoChannel> Machine<I> {
    /// Evaluate a Ψ∗ term to normal form.
    pub fn eval(&mut self, term: u32) -> Result<u32, EvalError> { ... }
    
    /// Encode an integer as Q-chain rooted at ⊤
    pub fn encode_int(&mut self, n: u64) -> u32 { ... }
    
    /// Decode a Q-chain to integer
    pub fn decode_int(&self, term: u32) -> Option<u64> { ... }
    
    /// Build a cons pair
    pub fn cons(&mut self, car: u32, cdr: u32) -> u32 { ... }
    
    /// Step counter and performance stats
    pub fn stats(&self) -> MachineStats { ... }
}
```

**Phase 2 tests:** Run all `psi_*.lisp` examples through the Rust machine and verify outputs match Python. Use the Python test outputs as golden files.

**Phase 3: psi-cli (native runner)**

```
Usage:
  kamea run file.lisp              # run a file
  kamea repl                       # interactive REPL
  kamea debug file.lisp            # TUI debugger (stretch goal)
  kamea bench file.lisp            # benchmark with timing
```

The REPL should match `psi_lisp.py`'s behavior — same prompt, same display format, same builtins. A user should be able to switch between Python and Rust and get identical results.

For the initial version, the CLI can accept pre-translated Ψ∗ terms (serialized from Python) rather than including a full Lisp parser. Adding a Rust Lisp parser is Phase 5.

Alternatively, include a minimal S-expression parser in Rust. The parser from `psi_lisp.py` is ~60 lines — the Rust version won't be much larger. This would make the CLI self-contained from day one.

**Phase 4: psi-web (WASM + browser debugger)**

`lib.rs` — wasm-bindgen exports:
```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct PsiDebugger {
    machine: Machine<BufferIo>,
    // Current state for stepping
}

#[wasm_bindgen]
impl PsiDebugger {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self { ... }
    
    /// Load a Ψ∗ term (serialized or from Lisp source)
    pub fn load(&mut self, source: &str) { ... }
    
    /// Execute one evaluation step. Returns JSON state snapshot.
    pub fn step(&mut self) -> String { ... }
    
    /// Run to completion. Returns result as display string.
    pub fn run(&mut self) -> String { ... }
    
    /// Get the Cayley table as JSON (for grid display)
    pub fn table(&self) -> String { ... }
    
    /// Get current term as JSON tree (for visualization)
    pub fn current_term(&self) -> String { ... }
    
    /// Get eval stack as JSON (for stack display)
    pub fn eval_stack(&self) -> String { ... }
    
    /// Write input byte (for IO simulation)
    pub fn input(&mut self, byte: u8) { ... }
    
    /// Read output bytes (for IO display)
    pub fn output(&mut self) -> Vec<u8> { ... }
    
    /// Get machine stats
    pub fn stats(&self) -> String { ... }
}
```

`www/index.html` — the debugger UI:

```
┌──────────────────────────────────────────────────────────────┐
│  Ψ∗ Debugger                     [Step] [Run] [Reset] [Load]│
├────────────────────┬─────────────────────────────────────────┤
│                    │                                         │
│   Cayley Table     │   Current Term                          │
│   16×16 grid       │   (tree visualization, collapsible)     │
│                    │                                         │
│   Highlight:       │   Atoms as colored nodes                │
│   - current dot    │   App nodes as branches                 │
│     lookup in      │   Q-chains shown as [n] shorthand       │
│     yellow         │   g-pairs shown as (a . b) shorthand    │
│   - result cell    │                                         │
│     in green       │                                         │
│                    │                                         │
├────────────────────┼─────────────────────────────────────────┤
│                    │                                         │
│   Eval Trace       │   Output                                │
│   (scrollable)     │   (terminal-style, monospace)           │
│                    │                                         │
│   Each step shows: │   Shows:                                │
│   - rule applied   │   - print output                        │
│   - term before    │   - IO bytes                            │
│   - term after     │   - final result                        │
│   - dot(a,b)=c     │                                         │
│     when table     │                                         │
│     is consulted   │                                         │
│                    │                                         │
├────────────────────┴─────────────────────────────────────────┤
│                                                              │
│   Source Editor (Ψ-Lisp)                                     │
│   (textarea with syntax highlighting, monospace)             │
│                                                              │
│   Preloaded examples: [fibonacci] [factorial] [list ops]     │
│                                                              │
├──────────────────────────────────────────────────────────────┤
│   Stats: steps=1234  allocs=5678  depth=12  time=0.3ms      │
└──────────────────────────────────────────────────────────────┘
```

**Cayley table visualization details:**
- 16×16 grid, cells show atom index or symbol
- Row and column headers show element names (⊤, ⊥, f, τ, ...)
- Color-code by role: absorbers gray, tester blue, encoders green, inert yellow
- When a `dot(a, b)` happens during evaluation, highlight row `a` header, column `b` header, and cell `(a,b)` with a flash animation
- The table is static data but the highlighting makes it alive — the user sees every table lookup as it happens

**Term tree visualization:**
- Render as a collapsible tree (like a JSON viewer)
- Atoms are leaf nodes colored by role
- App nodes show `(fun arg)` with children
- Q-chains detected and shown as integer shorthand: `App(Q, App(Q, App(Q, ⊤)))` displays as `3`
- g-pairs detected and shown as list shorthand: `(1 2 3)` instead of nested pairs
- The currently-being-evaluated subterm is highlighted
- Nodes expand/collapse on click for deep terms

**Eval trace:**
- Scrollable log, most recent at bottom
- Each entry: `[step N] rule: <name> | <term_before> → <term_after>`
- When a dot lookup happens: `dot(Q, τ) = η` with the cell reference
- Color-code by rule type: constructors green, destructors red, control blue, table lookup yellow

**Build with wasm-pack:**
```bash
cd crates/psi-web
wasm-pack build --target web
# Serve www/ with any static file server
```

**Tech stack for web UI:**
- Vanilla HTML/CSS/JS. No React, no framework, no build step beyond wasm-pack.
- CSS grid for the layout.
- The Cayley table is a `<table>` element with 16×16 `<td>` cells.
- Term tree uses nested `<details>` elements for collapse/expand.
- Eval trace is a `<pre>` element with appended lines.
- Source editor is a `<textarea>` with monospace font.
- All state comes from the WASM module via the `PsiDebugger` API.

**Phase 5 (stretch): Rust Lisp parser**

Port `psi_lisp.py`'s parser and evaluator to Rust so the CLI and WASM targets can run `.lisp` files directly without Python. The parser is ~100 lines (tokenize + recursive descent). The evaluator is ~300 lines (translate + apply + builtins). This makes the system fully self-contained.

**Correctness requirement:**

The Python implementation is the reference. For every test program:
```
python3 psi_lisp.py examples/psi_fibonacci.lisp > expected.txt
kamea run examples/psi_fibonacci.lisp > actual.txt
diff expected.txt actual.txt  # must be empty
```

Create a test harness that runs all examples through both Python and Rust and verifies identical output.

**Performance target:**

Benchmark `(fib 30)` in both implementations:
```
python3 -c "import time; t=time.time(); exec(open('run_fib30.py').read()); print(f'{time.time()-t:.3f}s')"
kamea bench examples/psi_fibonacci.lisp
```

Target: Rust should be at least 10x faster than Python on `(fib 30)`. If the arena is cache-friendly and the evaluator is tight, 50-100x is realistic.

**Deliverables in order:**

1. `psi-core` with table, terms, evaluator. All eval tests passing.
2. `psi-runtime` with machine, IO. 2CM simulation matching Python.
3. `psi-cli` running `.lisp` files. All 6 test programs matching Python output.
4. `psi-web` with WASM build. Debugger UI showing table, term tree, eval trace. Same test programs running in browser.
5. Performance benchmark: Rust vs Python on `(fib 30)`.

**Do not:**
- Change the Cayley table. It's from the Lean-verified `Psi16Full.lean`.
- Change the evaluation semantics. They're from the TC-proved `psi_star.py`.
- Add dependencies to `psi-core` beyond `core`/`alloc`. It must stay `no_std`-compatible.
- Use `unsafe` in the evaluator. The arena can use `unsafe` for performance if needed, but the eval logic must be safe Rust.
- Over-engineer the web UI. Vanilla JS, no framework. The debugger is a visualization tool, not a web app.

---

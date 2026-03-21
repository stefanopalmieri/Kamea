# Related Work

*Where Boba's Tower sits in the landscape of reflective systems.*

---

## The Architectural Fork

Reflective language design faces a structural choice: does the tower terminate? This choice forces everything else.

An **infinite tower** (Smith 1984) has no bottom. Each level is interpreted by the level below, forever. Continuations are higher-order closures — opaque, invocable, composable, but not inspectable. You can't walk a continuation frame by frame because the frames are closures at the next level down, which are closures at the level below that, ad infinitum.

A **grounded tower** has a bottom: a finite structure whose properties are verifiable. Continuations must be defunctionalized — tagged data structures with finite type — because there is no infinite hierarchy of closure types to hide behind. You *can* walk a continuation frame by frame because each frame is a data constructor with inspectable fields.

This fork is not a design preference. It's a logical consequence:

- **Grounded → finite continuation types → defunctionalization → transparency → the branch swap.** The bottom forces continuations to be data. Data can be walked and modified. Modified data can be reflected. That's the branch swap.

- **Infinite → infinite continuation types → closures → opacity → live meta-modification.** The absence of a bottom means closures can capture arbitrary depth. You can't inspect them, but you can replace the interpreter that creates them. That's `set! base-eval`.

Neither side is better. They solve different problems with different tradeoffs.

---

## System Comparison

| System | Tower | Continuations | Headline result |
|--------|-------|---------------|-----------------|
| Smith (1984) | Infinite | — | Reflective tower concept |
| Wand & Friedman (1986) | Fixed-point | — | Demystifying Smith: the tower is a Y combinator |
| Danvy & Malmkjær (1988) | Semantically stratified | — | Separating intension from extension |
| Black/Brown/Blond | Infinite | Opaque closures | Live `set! base-eval` |
| Amin & Rompf (POPL 2018) | Collapsible | Opaque closures | Compile user programs *through* the tower |
| **Boba's Tower (Kamea)** | **Grounded (256 bytes)** | **Tagged data** | **Compile the tower itself** |

---

## Detailed Comparison: LMS-Black vs Boba's Tower

Amin and Rompf's "Collapsing Towers of Interpreters" (POPL 2018) is the closest system in ambition. Both compile reflective towers. The difference is what gets compiled and what the compiled code can do.

|                              | LMS-Black (POPL 2018)          | Boba's Tower (Kamea)           |
|------------------------------|--------------------------------|--------------------------------|
| What's compiled              | User programs through tower    | The tower itself               |
| Tower at runtime             | Scala data structures          | Compiled away — all Rust       |
| Compilation latency          | Seconds (runtime Scala compiler)| One-time rustc                |
| Generated code               | 6-7 nested CPS levels          | Flat Rust functions           |
| Meta-modification in compiled| Yes — the headline result      | No                            |
| Continuation inspection      | No — closures are opaque       | Yes — tagged data, walkable   |
| Branch swap                  | No                             | Yes                           |
| Formal verification          | No                             | 102 Lean theorems             |
| Runtime substrate verification | No                           | Yes — Cayley table checked    |

LMS-Black's headline result: compile a user program that was being interpreted by a meta-interpreter that was being interpreted by another meta-interpreter, and collapse all the interpretation overhead via stage polymorphism. The compiled code runs at the speed of a hand-written interpreter.

Boba's Tower's headline result: compile the meta-circular evaluator itself — including continuation reification, frame walking, table verification, and branch swap — into a single native binary. 2.2 ms vs ~43 s interpreted. The compiled tower is Futamura projection 1 applied to the meta-circular evaluator.

---

## The Blond Swap vs The Branch Swap

Blond (Asai & Masuhara, 2016) implements a form of reflective modification: `swap!` permutes the reflective levels, changing which interpreter interprets which. This is a whole-level operation — you swap entire interpreters.

Boba's Tower's branch swap is a single-frame field edit. The program reifies its continuation (a linked list of tagged frames), walks to a specific `k-if` frame, swaps the `then` and `else` fields, and reflects. The `if` expression takes the branch it wouldn't normally take.

The difference: Blond's swap is coarser (whole levels) but applies to the meta-interpreter itself. Boba's Tower's swap is finer (individual fields within a single frame) but operates only on the program's own continuation, not the meta-interpreter's structure.

---

## Historical Context

| System | The tower is... | The bottom is... | Reflection is for... |
|--------|----------------|-----------------|---------------------|
| Smith (1984) | infinite | nonexistent | understanding meaning |
| Wand & Friedman (1986) | a fixed point | a Y combinator | demystifying Smith |
| Danvy & Malmkjær (1988) | semantically stratified | a precise formalism | separating intension from extension |
| Amin & Rompf (2018) | collapsible overhead | generated code | compilation |
| Black/Brown/Blond | a programmable runtime | Scheme/Racket | modifying your own semantics |
| **Boba's Tower (Kamea)** | **grounded** | **a verified algebra** | **inspecting and rewriting your own future** |

---

## What They Have That We Don't

1. **Live meta-interpreter modification** (`set! base-eval`). In Black/Blond, you can change how `if` works at the meta-level, affecting all future computation. In Boba's Tower, `meval`'s special forms are hardcoded — you can inspect and modify your continuation, but not the evaluator that creates it.

2. **Infinite tower levels.** Smith's tower has no inherent depth limit. Boba's Tower has 3 fixed levels (user program → meta-circular evaluator → base evaluator → Cayley table). Adding a fourth level is possible but would require writing a meta-meta-evaluator.

3. **Compilation under modified semantics.** LMS-Black can compile a program whose interpreter was modified at a higher level. In Boba's Tower, compilation is a separate offline step — the compiled binary has fixed semantics.

4. **`reify` as live meta-access.** In 3-Lisp, `reify` gives access to the running meta-interpreter's state. In Boba's Tower, `reify` gives a snapshot of the current continuation — inspectable data, not live meta-state. The difference: you can read the continuation but not the evaluator.

---

## What We Have That None Of Them Do

1. **Walkable continuations.** The branch swap: reify the continuation, walk to a `k-if` frame, swap the `then`/`else` fields, reflect. No other reflective system in this lineage provides frame-by-frame inspection and field-level modification of continuations.

2. **A compiled tower.** The meta-circular evaluator, continuation reification, frame walking, table verification, and branch swap all compile to a single native binary (2.2 ms). LMS-Black compiles *through* the tower; Boba's Tower compiles *the tower itself*.

3. **Formal verification.** 102 Lean theorems, zero `sorry`. Rigidity, discoverability, actuality irreducibility, the Kripke wall, the asymmetry theorem — all machine-checked. No other reflective system in this lineage has formal verification of its substrate.

4. **Runtime substrate verification.** The compiled tower verifies the 256-byte Cayley table at runtime before trusting the evaluator. The algebra isn't assumed — it's checked.

5. **A ground.** Smith's tower has no bottom. This one does: a 16×16 Cayley table whose algebraic properties are Lean-proved. The program verifies the table before trusting the evaluator. There is nothing beneath the table to worry about. It IS the algebra, not an implementation of it.

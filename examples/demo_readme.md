# The Recovery Spell: A Self-Healing Algebra

## What You're About to See

Two small computers — represented as wizards — each running the same 16-element algebra. One gets corrupted: its internal lookup table is scrambled, so it no longer knows what its own components are. The other wizard loads a short program, written in the algebra's own programming language, and casts it as a "recovery spell." Through 62 carefully chosen questions sent over a simple communication channel, the spell identifies every element of the corrupted table and restores it. The corrupted wizard heals, pixel by pixel, as each element is recognized.

The whole thing takes about 120 lines of code and a few seconds.

## Why This Is Interesting

The recovery program isn't written in Python or C or any external language. It's written in a Lisp dialect that runs on the algebra itself. Every list operation, every conditional branch, every recursive call is evaluated using the same 16×16 multiplication table that defines the algebra. The seven atoms that make the language work — a ground element, a constructor/destructor pair, a pair-builder with two projections, and a conditional — are elements of the algebra. The IO channel that carries the 62 probe questions and their answers uses two more elements from the same algebra.

So what you're watching is: a structure recovering a corrupted copy of itself, using a program written in its own language, communicating through its own IO primitives. Nothing outside the algebra touches the computation.

## The Algebra in 30 Seconds

Imagine a 16×16 grid where every cell contains a number from 0 to 15. That's the entire algebra — one binary operation, `dot(x, y)`, defined by table lookup. No addition, no multiplication, no floating point. Just: look up row x, column y, read the result.

From this single operation, specific elements emerge with specific behaviors:

- **Two absorbers** (⊤ and ⊥) — like true and false. Their rows are constant: `dot(⊤, anything) = ⊤`.
- **A tester** (τ) — its row contains only ⊤ and ⊥. It judges.
- **Encoders** — their rows contain many distinct values. They transform.
- **A quote/eval pair** (Q and E) — mutual inverses. Q wraps, E unwraps. Together they give the algebra the ability to represent and inspect its own elements.

These roles aren't assigned by convention. They're forced by the axioms — mathematical constraints that any valid table must satisfy. If you search for all 16×16 tables satisfying the axioms, every single one has exactly these roles, in exactly this configuration. The structure is rigid: every element is distinguishable from every other element by its row alone.

## How the Recovery Works

The spell doesn't know which element is which — the table has been shuffled. All it can do is ask "what is `dot(x, y)`?" for specific x and y, and observe the answer. From 62 such questions, it reconstructs the identity of all 16 elements:

1. **Find the absorbers** (16 questions): Scan for elements where `dot(x, x) = x`. Only ⊤ and ⊥ are idempotent.

2. **Classify by absorber signature** (28 questions): For each remaining element, ask `dot(x, ⊤)` and `dot(x, ⊥)`. The answers partition all 14 non-absorbers into five structurally distinct groups.

3. **Orient the ground** (0 questions): One group has exactly one element. That element's signature reveals which absorber is ⊤ and which is ⊥.

4. **Find the eval element** (1–4 questions): Among the elements that preserve both absorbers, one produces non-boolean outputs on non-absorbers. That's E — the destructor.

5. **Find the quote element** (2–6 questions): Among the elements that swap absorbers, one satisfies the round-trip property: `dot(E, dot(Q, x)) = x`. That's Q — the constructor.

6. **Generate the rest** (12 questions): The four elements {⊤, ⊥, Q, E} generate all 16 elements through composition. Twelve targeted dot-calls produce the remaining twelve elements via a known generation tree.

Each identification is reported back through the IO channel. On screen, each report restores part of the corrupted wizard's sprite.

## What Makes This Different from Normal Error Correction

Standard error correction (checksums, ECC memory, redundant voting) detects that something is wrong and either corrects bit patterns or overrules a disagreeing copy. It doesn't know *what* the components mean. It doesn't diagnose. It doesn't reason about the structure.

The recovery spell reasons algebraically. It exploits the fact that the algebra's axioms force every element into a unique structural role. The spell doesn't compare against a known-good copy. It deduces what each element must be from the algebraic relationships between elements. Even if you scramble the entire table, the relationships survive — because they're properties of the algebra, not properties of the labeling.

This is possible because the algebra is *rigid* — every element is uniquely determined by its structural fingerprint — and *constructible* — every element can be built from just four seeds. These properties are mathematical theorems, proved in the Lean 4 theorem prover with zero unfinished proofs.

## Running It

```bash
git clone https://github.com/stefanopalmieri/Kamea.git && cd Kamea

# Animated TUI version (recommended)
python3 examples/psi16_corrupted_host_demo.py

# Plain text narration
python3 examples/psi16_corrupted_host_demo.py --plain
```

## Further Reading

- The algebra and its axioms: [README.md](../README.md)
- The recovery algorithm in detail: [psi_blackbox.py](../psi_blackbox.py)
- The spell source code: [psi_recovery_spell.lisp](psi_recovery_spell.lisp)
- The Lean proofs: [DistinctionStructures/](../DistinctionStructures/)
- The Ψ-Lisp language: [psi_lisp.py](../psi_lisp.py)

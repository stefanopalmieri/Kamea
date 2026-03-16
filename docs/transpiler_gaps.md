# Transpiler Gaps: Reflective Tower Compilation

Status: **identified, not yet fixed**

The Python transpiler (`psi_transpile.py --target rust`) successfully compiles arithmetic programs, the specializer, and the self-hosted transpiler. It fails on the reflective tower (`psi_metacircular.lisp` + `psi_reflective_tower.lisp`) — 504 lines of Rust generated, 180 compile errors.

## The Fundamental Gap: Quoted Symbol Encoding

The reflective tower is a meta-circular evaluator. It builds Lisp programs as cons-cell data structures:

```lisp
(cons 'defun (cons 'fib (cons (list 'n) (cons body NIL))))
```

The transpiler has no mechanism to encode quoted symbols (`'defun`, `'if`, `'lambda`, `'car`, etc.) as integer values. It emits them as bare Rust identifiers:

```rust
arena.cons(defun, arena.cons(fib, ...))  // ERROR: `defun` not in scope
```

In `psi_lisp.py`, quoted symbols go through `_symbol_to_term`, which assigns each unique symbol a stable integer ID (starting at 100) and encodes it as a Q-chain. The transpiler would need an equivalent: a compile-time symbol table that maps each quoted symbol to a unique `PsiVal` constant.

This affects every quoted symbol in the tower: `defun`, `if`, `cond`, `lambda`, `let`, `progn`, `quote`, `car`, `cdr`, `cons`, `null`, `+`, `*`, `<`, `=`, `and`, `or`, `not`, `list`, `setq`, `reify`, `reflect`, `fib`, `fact`, `n`, `x`, etc.

Operator symbols are further mangled: `+` → `_plus`, `*` → `_star`, `<` → `_lt`, `=` → `_eq` — then used as variable names that don't exist.

## Secondary Gaps

### Arena threading for display functions

Functions that call `psi_print_val` or `atom_name` need `arena: &mut Arena` but the transpiler's `uses_arena` check only looks for `cons`/`car`/`cdr`/`list`/`print`/`display`. Functions calling other arena-needing user functions are detected (via `_calls_arena_fn`), but builtins like `psi_print_val` used in `write-string` output are not.

### Global `setq` variables

The tower defines globals via `setq`:

```lisp
(setq TOP 0)
(setq BOT 1)
(setq QQ 6)
(setq EE 7)
```

The transpiler emits these as `let mut` declarations in `main()`, but references to them from within compiled functions see bare identifiers (`TOP`, `BOT`, `QQ`, `EE`) that are not in scope. These need to be either function parameters, global statics, or inlined constants.

### `_` as expression

`(setq _ (some-side-effect))` emits `_ = ...` in Rust. The identifier `_` is not valid in expression position in Rust — only on the left-hand side of `let _ = ...`.

### Mismatched types from `cond` fallthrough

Some `cond` clauses in the metacircular evaluator have complex nesting that produces Rust type mismatches — the `if/else if/else` chain doesn't always resolve to the same type in all branches.

## What Would Fix It

The quoted-symbol encoding requires:

1. **Symbol table pass**: walk all `(quote sym)` forms before code generation, assign each unique symbol a stable integer ID.

2. **Emit symbol constants**: at the top of the generated Rust, emit `const SYM_DEFUN: PsiVal = 101; const SYM_IF: PsiVal = 102;` etc.

3. **Encode as Q-chains at runtime**: symbols are Q-chain integers in psi_lisp.py (`encode_int(id)`). The transpiler would need to either:
   - Emit the Q-chain construction at startup (call `arena.encode_int(id)` for each symbol), or
   - Use raw integer IDs directly (faster, but changes the representation)

4. **Handle operator symbols**: `+`, `*`, `<`, `=` as quoted data must map to symbol IDs, not be name-mangled.

The secondary gaps (arena threading, globals, `_`) are straightforward once the symbol encoding is in place.

## Performance Expectation

If compiled, the reflective tower would run at roughly:

| Mode | fib(8) | Notes |
|------|--------|-------|
| Python interpreting Lisp-in-Lisp | ~44,000 ms | triple interpretation |
| Rust interpreter (kamea) running tower | ~4,000 ms | compiled interpreter, interpreted meta-evaluator |
| **Compiled tower (estimated)** | **~400–800 ms** | compiled meta-evaluator, interpreted fib |
| Directly compiled fib | ~0.06 ms | no interpretation overhead |

The compiled tower is not about speed — it's about having the meta-circular evaluator as compiled Rust that can switch between native execution and reflective interpretation via `(reify)`/`(reflect)`, with continuations as MMTk-managed cons cells in a single binary.

# Transpiler Gaps: Reflective Tower Compilation

Status: **symbol encoding fixed, tower compiles and runs**

The Python transpiler (`psi_transpile.py --target rust`) now successfully compiles the reflective tower (`psi_metacircular.lisp` + `psi_reflective_tower.lisp`). The compiled binary produces output matching the interpreter.

## What Was Fixed

### Quoted Symbol Encoding (fundamental gap — resolved)

The transpiler now performs a symbol table pass before code generation:

1. **Symbol collection**: walks all `(quote ...)` forms (including nested data within quoted lists) and assigns each unique symbol a stable integer ID starting at 100.

2. **Constant emission**: emits `const SYM_DEFUN: PsiVal = 101;` etc. at module level.

3. **Datum emission**: `emit_rust_datum` uses symbol constants for symbols and builds cons-list data using temporaries to avoid Rust borrow conflicts.

4. **Operator symbols**: `+` → `SYM__PLUS`, `*` → `SYM__STAR`, etc. — properly mangled and mapped to integer IDs.

### Global `setq` Variables (resolved)

Integer-valued `setq` (e.g., `(setq TOP 0)`, `(setq QQ 6)`) now emit as `const` at module level, making them visible to all functions. Complex-valued globals remain `let mut` in `main()`.

### Arena Threading (resolved)

- `uses_arena` now detects: `atom-name`, `numberp`, `atom`, `write-string` with variable arguments, `quote` with list data, and string literals as PsiVal.
- All `cons` calls use temporaries to prevent nested mutable borrow conflicts.
- `car`/`cdr` with arena-using arguments use temporaries.
- `list` emission evaluates all items into temps before building the cons chain.

### Missing Builtins (resolved)

- `numberp`: `!is_nil(x) && !is_cons(x)`
- `atom`: `!is_cons(x)`
- `atom-name`: new `psi_atom_name` runtime function returns cons-list of char codes
- `write-string` with variable args: new `psi_write_string` runtime function
- String literals as PsiVal: compiled to cons-lists of ASCII char codes

### Other Fixes

- Multiple input files supported (e.g., `psi_transpile.py file1.lisp file2.lisp`)
- `--table f|c` flag: selects Ψ₁₆ᶠ (default) or Ψ₁₆ᶜ runtime
- `_` identifier handled (emitted as temp variable)
- Top-level IO statements no longer auto-print NIL return values

## What Remains

The transpiler handles the full reflective tower. Remaining limitations:

- **Closures as values**: `lambda` as a stored value (not directly applied) is not supported. The tower doesn't need this — closures are represented as tagged lists within the meta-circular evaluator.
- **Higher-order functions**: passing functions as arguments requires a closure representation. Not needed by the tower.
- **C backend for tower**: only the Rust backend has been tested with the tower. The C backend would need similar symbol encoding (straightforward).

## Usage

```bash
# Compile the reflective tower (default table: Ψ₁₆ᶠ)
python3 psi_transpile.py --target rust \
  examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp > /tmp/tower.rs
cp psi_runtime_f.rs /tmp/
rustc -O -o /tmp/tower /tmp/tower.rs
/tmp/tower

# With Ψ₁₆ᶜ table
python3 psi_transpile.py --target rust --table=c \
  examples/psi_metacircular.lisp examples/psi_reflective_tower.lisp > /tmp/tower_c.rs
cp psi_runtime.rs /tmp/
rustc -O -o /tmp/tower_c /tmp/tower_c.rs
/tmp/tower_c
```

#!/usr/bin/env python3
"""
Ψ-Lisp → C/Rust transpiler.

Reads Ψ-Lisp source (.lisp) or .psi IR and emits C or Rust code.

Handles: defun (recursive, multi-arg), nested defun (lifted), arithmetic,
if/cond, let, progn, cons/car/cdr/null/list, print/display/terpri/write-string,
and/or/not, lambda in direct application, setq, quote (including quoted lists
and nested symbol data — compiles the full reflective tower).

Does NOT handle: closures (lambda as value), higher-order functions (passing
functions as arguments), function values in setq. These require a closure
representation that neither backend natively supports.

Usage:
  python3 psi_transpile.py program.lisp > program.c                     # C (default, Ψ₁₆ᶠ)
  python3 psi_transpile.py --target rust program.lisp > program.rs       # Rust (Ψ₁₆ᶠ)
  python3 psi_transpile.py --target rust --table=c program.lisp > p.rs   # Rust (Ψ₁₆ᶜ)
  python3 psi_transpile.py --target rust f1.lisp f2.lisp > out.rs        # multiple files

  gcc -O2 -I. -o program program.c
  cp psi_runtime_f.rs /tmp/ && rustc -O -o program program.rs
"""

import sys
import re

# ═══════════════════════════════════════════════════════════════════════
# S-expression parser (handles both .lisp and .psi)
# ═══════════════════════════════════════════════════════════════════════

def tokenize(s):
    tokens = []
    i = 0
    while i < len(s):
        c = s[i]
        if c in ' \t\n\r':
            i += 1
        elif c == ';':
            while i < len(s) and s[i] != '\n':
                i += 1
        elif c in '()':
            tokens.append(c)
            i += 1
        elif c == "'":
            tokens.append("'")
            i += 1
        elif c == '"':
            j = i + 1
            while j < len(s) and s[j] != '"':
                if s[j] == '\\':
                    j += 1
                j += 1
            tokens.append(s[i:j+1])
            i = j + 1
        else:
            j = i
            while j < len(s) and s[j] not in ' \t\n\r();':
                j += 1
            tokens.append(s[i:j])
            i = j
    return tokens

def parse_one(tokens, pos):
    if pos >= len(tokens):
        raise SyntaxError("unexpected end")
    tok = tokens[pos]
    if tok == "'":
        expr, pos = parse_one(tokens, pos + 1)
        return ['quote', expr], pos
    if tok == '(':
        pos += 1
        items = []
        while pos < len(tokens) and tokens[pos] != ')':
            item, pos = parse_one(tokens, pos)
            items.append(item)
        if pos >= len(tokens):
            raise SyntaxError("missing )")
        return items, pos + 1
    if tok == ')':
        raise SyntaxError("unexpected )")
    # String literal
    if tok.startswith('"') and tok.endswith('"'):
        return tok, pos + 1
    # Number
    try:
        return int(tok), pos + 1
    except ValueError:
        pass
    # Symbol
    return tok, pos + 1

def parse_all(source):
    tokens = tokenize(source)
    forms = []
    pos = 0
    while pos < len(tokens):
        form, pos = parse_one(tokens, pos)
        forms.append(form)
    return forms

# ═══════════════════════════════════════════════════════════════════════
# Compiler state
# ═══════════════════════════════════════════════════════════════════════

BUILTINS = {'+', '-', '*', '<', '>', '<=', '>=', '=', 'eq', 'equal',
            'mod', 'zerop', 'null', 'numberp', 'atom',
            'cons', 'car', 'cdr', 'list',
            'print', 'display', 'terpri', 'write-string', 'write-char',
            'dot', 'atom-name', '1+', '1-', 'not',
            'env-size', 'env-keys', 'bound?'}

SPECIAL_FORMS = {'if', 'cond', 'let', 'progn', 'begin', 'defun', 'define',
                 'setq', 'lambda', 'quote', 'and', 'or', 'not'}

class Compiler:
    def __init__(self):
        self.functions = []        # [(name, params, body_sexpr)]
        self.globals = []          # [(name, init_sexpr)]
        self.constants = {}        # name → int  (setq with integer literal → const)
        self.main_stmts = []       # [sexpr]  — bare expressions to evaluate
        self.known_fns = set()     # all known function names
        self.tmp_count = 0
        self.errors = []           # constructs we couldn't handle
        self.symbol_table = {}     # symbol_name → integer ID
        self._next_symbol_id = 100
        self.table = 'f'           # default table: Ψ₁₆ᶠ

    def fresh(self, prefix='_t'):
        self.tmp_count += 1
        return f'{prefix}{self.tmp_count}'

    # ── Top-level processing ──────────────────────────────────────────

    def process(self, forms):
        for form in forms:
            if isinstance(form, list) and len(form) >= 1:
                head = form[0]
                if head == 'defun' and len(form) >= 4:
                    self.process_defun(form, prefix='')
                    continue
                elif head == 'define' and len(form) >= 3 and isinstance(form[1], list):
                    name = form[1][0]
                    params = form[1][1:]
                    body = form[2] if len(form) == 3 else ['progn'] + form[2:]
                    self.process_defun(['defun', name, params, body], prefix='')
                    continue
                elif head == 'setq' and len(form) == 3:
                    # Integer-valued setq → module-level const
                    if isinstance(form[2], int):
                        self.constants[form[1]] = form[2]
                    else:
                        self.globals.append((form[1], form[2]))
                    continue
            self.main_stmts.append(form)
        # Build symbol table from all quoted symbols in the program
        self._collect_symbols(forms)

    def _collect_symbols(self, forms):
        """Walk all forms to find (quote ...) and assign integer IDs to all symbols within."""
        def intern_sym(sym):
            if isinstance(sym, str):
                up = sym.upper()
                if up not in ('NIL', 'T') and sym not in self.symbol_table:
                    self.symbol_table[sym] = self._next_symbol_id
                    self._next_symbol_id += 1

        def walk_datum(datum):
            """Walk inside a quoted datum to find all symbols."""
            if isinstance(datum, str):
                intern_sym(datum)
            elif isinstance(datum, list):
                for item in datum:
                    walk_datum(item)

        def walk(sexpr):
            if isinstance(sexpr, list) and len(sexpr) >= 2:
                if sexpr[0] == 'quote':
                    walk_datum(sexpr[1])
                for item in sexpr:
                    walk(item)
        for form in forms:
            walk(form)

    def _sym_const_name(self, sym):
        """Return the Rust constant name for an interned symbol."""
        s = sym.replace('-', '_').replace('?', '_p').replace('!', '_b')
        s = s.replace('+', '_plus').replace('*', '_star').replace('/', '_slash')
        s = s.replace('<', '_lt').replace('>', '_gt').replace('=', '_eq')
        return f'SYM_{s.upper()}'

    def process_defun(self, form, prefix):
        name = form[1]
        params = form[2] if isinstance(form[2], list) else [form[2]]
        # Skip docstring if present (string literal as first body form)
        body_forms = form[3:]
        if len(body_forms) > 1 and isinstance(body_forms[0], str) and body_forms[0].startswith('"'):
            body_forms = body_forms[1:]
        body = body_forms[0] if len(body_forms) == 1 else ['progn'] + body_forms

        full_name = f'{prefix}{name}' if prefix else name
        self.known_fns.add(full_name)

        # Lift nested defuns
        body = self.lift_nested(body, full_name)

        self.functions.append((full_name, params, body))

    def lift_nested(self, sexpr, parent_name):
        """Walk sexpr, lift any nested (defun ...) to top level."""
        if not isinstance(sexpr, list) or len(sexpr) == 0:
            return sexpr
        if sexpr[0] == 'defun' and len(sexpr) >= 4:
            name = sexpr[1]
            params = sexpr[2] if isinstance(sexpr[2], list) else [sexpr[2]]
            body = sexpr[3] if len(sexpr) == 4 else ['progn'] + sexpr[3:]
            lifted_name = f'{c_ident(parent_name)}__{c_ident(name)}'
            # Register before processing body (for self-recursive calls)
            self.known_fns.add(name)
            self.known_fns.add(lifted_name)
            body = self.lift_nested(body, lifted_name)
            # Detect captured variables (name itself is known, not captured)
            free = find_free_vars(body, set(params), self.known_fns | BUILTINS | SPECIAL_FORMS | {name})
            extra_params = sorted(free)
            all_params = params + extra_params
            # Rewrite self-calls in body: name → lifted_name (with extra params)
            body = rewrite_calls(body, {name: (lifted_name, extra_params)})
            self.functions.append((lifted_name, all_params, body))
            # Return a marker so the parent knows this name was lifted
            return ('__lifted__', name, lifted_name, extra_params)
        # Recurse into sub-expressions, handling lifted markers
        result = []
        lifted_map = {}  # original_name → (lifted_name, extra_params)
        for item in sexpr:
            processed = self.lift_nested(item, parent_name)
            if isinstance(processed, tuple) and processed[0] == '__lifted__':
                _, orig_name, lifted_name, extra = processed
                lifted_map[orig_name] = (lifted_name, extra)
                # Don't add the defun to the result — it's been lifted
            else:
                result.append(processed)
        # Rewrite calls to lifted functions
        if lifted_map:
            result = rewrite_calls(result, lifted_map)
        return result

    # ── C emission ────────────────────────────────────────────────────

    def emit_c(self):
        lines = []
        lines.append('/* Generated by psi_transpile.py — Ψ-Lisp → C transpiler */')
        lines.append('#include "psi_runtime.h"')
        lines.append('')

        # Forward declarations
        for name, params, _ in self.functions:
            cname = c_ident(name)
            cparams = ', '.join(f'psi_val {c_ident(p)}' for p in params)
            lines.append(f'psi_val {cname}({cparams});')
        if self.functions:
            lines.append('')

        # Function definitions
        for name, params, body in self.functions:
            cname = c_ident(name)
            cparams = ', '.join(f'psi_val {c_ident(p)}' for p in params)
            lines.append(f'psi_val {cname}({cparams}) {{')
            lines.extend(self.emit_return(body, indent=1))
            lines.append('}')
            lines.append('')

        # Main
        lines.append('int main(void) {')
        for name, init in self.globals:
            lines.append(f'    psi_val {c_ident(name)};')
        for name, init in self.globals:
            lines.extend(self.emit_assign(c_ident(name), init, indent=1))
        for stmt in self.main_stmts:
            is_io = (isinstance(stmt, list) and len(stmt) >= 1 and
                     isinstance(stmt[0], str) and stmt[0] in
                     ('print', 'display', 'terpri', 'write-string', 'write-char'))
            tmp = self.fresh()
            lines.append(f'    psi_val {tmp};')
            lines.extend(self.emit_assign(tmp, stmt, indent=1))
            if not is_io:
                lines.append(f'    psi_println({tmp});')
        lines.append('    return 0;')
        lines.append('}')
        return '\n'.join(lines) + '\n'

    # ── Rust emission ─────────────────────────────────────────────────

    def emit_rust(self):
        table = getattr(self, 'table', 'f')
        runtime_file = 'psi_runtime_f.rs' if table == 'f' else 'psi_runtime.rs'
        lines = []
        lines.append('// Generated by psi_transpile.py — Ψ-Lisp → Rust transpiler')
        lines.append('#![allow(non_snake_case, unused_parens, unused_variables, unused_mut)]')
        lines.append(f'#[path = "{runtime_file}"]')
        lines.append('mod psi_runtime;')
        lines.append('use psi_runtime::*;')
        lines.append('')

        # Emit integer-valued setq as module-level constants
        if self.constants:
            for name, val in self.constants.items():
                rname = rust_ident(name)
                lines.append(f'const {rname}: PsiVal = {val}_i64;')
            lines.append('')

        # Emit symbol table constants
        if self.symbol_table:
            lines.append('// Interned symbol constants (quoted symbols → integer IDs)')
            for sym, sid in sorted(self.symbol_table.items(), key=lambda x: x[1]):
                cname = self._sym_const_name(sym)
                lines.append(f'const {cname}: PsiVal = {sid}_i64;')
            lines.append('')

        # Determine which functions need arena
        self._fn_needs_arena = {}
        # First pass: direct usage
        for name, params, body in self.functions:
            self._fn_needs_arena[c_ident(name)] = uses_arena(body)
        # Also check main stmts and globals
        main_needs = any(uses_arena(s) for s in self.main_stmts)
        main_needs = main_needs or any(uses_arena(init) for _, init in self.globals)
        # Second pass: propagate — if a function calls an arena-using function, it needs arena too
        changed = True
        while changed:
            changed = False
            for name, params, body in self.functions:
                cname = c_ident(name)
                if not self._fn_needs_arena.get(cname):
                    if self._calls_arena_fn(body):
                        self._fn_needs_arena[cname] = True
                        changed = True
        # Main also needs arena if it calls arena-using functions
        for stmt in self.main_stmts + [init for _, init in self.globals]:
            if self._calls_arena_fn(stmt):
                main_needs = True

        # Function definitions
        for name, params, body in self.functions:
            rname = rust_ident(name)
            cname = c_ident(name)
            needs_arena = self._fn_needs_arena.get(cname, False)
            rparams = []
            if needs_arena:
                rparams.append('arena: &mut Arena')
            for p in params:
                rparams.append(f'{rust_ident(p)}: PsiVal')
            param_str = ', '.join(rparams)
            lines.append(f'fn {rname}({param_str}) -> PsiVal {{')
            # Inside a function, arena is already &mut Arena — use 'arena' for passing
            self._rust_arena_ref = 'arena'
            lines.extend(self.emit_rust_return(body, indent=1))
            lines.append('}')
            lines.append('')

        # Main — arena is owned, pass &mut arena
        self._rust_arena_ref = '&mut arena'
        lines.append('fn main() {')
        # Always create arena — psi_println needs &Arena
        if main_needs:
            lines.append('    let mut arena = Arena::new();')
        else:
            lines.append('    let arena = Arena::new();')
        for name, init in self.globals:
            rname = rust_ident(name)
            if rname == '_':
                # _ can't be declared as mutable or read back in Rust
                continue
            lines.append(f'    let mut {rname}: PsiVal;')
        for name, init in self.globals:
            rname = rust_ident(name)
            if rname == '_':
                # Emit as side-effect only: let _ = expr;
                tmp = self.fresh()
                lines.append(f'    let {tmp}: PsiVal;')
                lines.extend(self.emit_rust_assign(tmp, init, indent=1))
            else:
                lines.extend(self.emit_rust_assign(rname, init, indent=1))
        for stmt in self.main_stmts:
            tmp = self.fresh()
            lines.append(f'    let {tmp}: PsiVal;')
            lines.extend(self.emit_rust_assign(tmp, stmt, indent=1))
            # Print result unless NIL (matching interpreter's _VOID suppression)
            lines.append(f'    if !is_nil({tmp}) {{ psi_println(&arena, {tmp}); }}')
        lines.append('}')
        return '\n'.join(lines) + '\n'

    def _calls_arena_fn(self, sexpr):
        """Check if sexpr calls any function that needs arena."""
        if isinstance(sexpr, (int, str)):
            return False
        if isinstance(sexpr, list) and len(sexpr) >= 1:
            head = sexpr[0]
            if isinstance(head, str):
                cname = c_ident(head)
                if self._fn_needs_arena.get(cname, False):
                    return True
            return any(self._calls_arena_fn(item) for item in sexpr)
        return False

    def _needs_rust_temps(self, sexpr):
        """Check if a call needs temporaries to avoid borrow conflicts."""
        if not isinstance(sexpr, list) or len(sexpr) < 1:
            return False
        head = sexpr[0]
        if not isinstance(head, str) or head in SPECIAL_FORMS:
            return False
        cname = c_ident(head)
        needs_arena = self._fn_needs_arena.get(cname, False)
        if not needs_arena:
            return False
        # Does any argument use arena (directly or via function calls)?
        return any(uses_arena(a) or self._calls_arena_fn(a) for a in sexpr[1:])

    def emit_rust_return(self, sexpr, indent=1):
        """Emit Rust statements that return the value of sexpr."""
        pad = '    ' * indent
        if self._needs_rust_temps(sexpr):
            return self._emit_rust_temped_call_return(sexpr, indent)
        if self.is_simple_expr(sexpr):
            return [f'{pad}{self.emit_rust_expr(sexpr)}']
        return self.emit_rust_stmt_return(sexpr, indent)

    def _arg_needs_temp(self, a):
        """Check if an argument to an arena-using function needs a temporary."""
        return uses_arena(a) or self._needs_rust_temps(a) or self._calls_arena_fn(a)

    def _emit_rust_temped_call_return(self, sexpr, indent):
        """Emit a function call with arena args pulled into temporaries."""
        pad = '    ' * indent
        lines = []
        head = sexpr[0]
        rname = rust_ident(head)
        cname = c_ident(head)
        args = [self._rust_arena_ref]
        for a in sexpr[1:]:
            if self._arg_needs_temp(a):
                tmp = self.fresh()
                lines.append(f'{pad}let {tmp}: PsiVal;')
                lines.extend(self.emit_rust_assign(tmp, a, indent))
                args.append(tmp)
            else:
                args.append(self.emit_rust_expr(a))
        lines.append(f'{pad}{rname}({", ".join(args)})')
        return lines

    def _emit_rust_temped_call_assign(self, target, sexpr, indent):
        """Emit a function call with arena args pulled into temporaries, assigning to target."""
        pad = '    ' * indent
        lines = []
        head = sexpr[0]
        rname = rust_ident(head)
        cname = c_ident(head)
        args = [self._rust_arena_ref]
        for a in sexpr[1:]:
            if self._arg_needs_temp(a):
                tmp = self.fresh()
                lines.append(f'{pad}let {tmp}: PsiVal;')
                lines.extend(self.emit_rust_assign(tmp, a, indent))
                args.append(tmp)
            else:
                args.append(self.emit_rust_expr(a))
        lines.append(f'{pad}{target} = {rname}({", ".join(args)});')
        return lines

    def emit_rust_stmt_return(self, sexpr, indent):
        pad = '    ' * indent
        lines = []
        if isinstance(sexpr, list) and len(sexpr) >= 1:
            head = sexpr[0]
            if head == 'if':
                test, then_b = sexpr[1], sexpr[2]
                else_b = sexpr[3] if len(sexpr) >= 4 else 'NIL'
                if self.is_simple_expr(test):
                    lines.append(f'{pad}if is_true({self.emit_rust_expr(test)}) {{')
                else:
                    tmp = self.fresh()
                    lines.append(f'{pad}let {tmp}: PsiVal;')
                    lines.extend(self.emit_rust_assign(tmp, test, indent))
                    lines.append(f'{pad}if is_true({tmp}) {{')
                lines.extend(self.emit_rust_return(then_b, indent + 1))
                lines.append(f'{pad}}} else {{')
                lines.extend(self.emit_rust_return(else_b, indent + 1))
                lines.append(f'{pad}}}')
                return lines
            if head == 'cond':
                first = True
                for clause in sexpr[1:]:
                    test, val = clause[0], clause[1]
                    if isinstance(test, str) and test.upper() == 'T':
                        if not first:
                            lines.append(f'{pad}}} else {{')
                        else:
                            lines.append(f'{pad}{{')
                        lines.extend(self.emit_rust_return(val, indent + 1))
                        lines.append(f'{pad}}}')
                        return lines
                    if first:
                        if self.is_simple_expr(test):
                            lines.append(f'{pad}if is_true({self.emit_rust_expr(test)}) {{')
                        else:
                            tmp = self.fresh()
                            lines.append(f'{pad}let {tmp}: PsiVal;')
                            lines.extend(self.emit_rust_assign(tmp, test, indent))
                            lines.append(f'{pad}if is_true({tmp}) {{')
                        first = False
                    else:
                        if self.is_simple_expr(test):
                            lines.append(f'{pad}}} else if is_true({self.emit_rust_expr(test)}) {{')
                        else:
                            lines.append(f'{pad}}} else {{')
                            tmp = self.fresh()
                            lines.append(f'{pad}    let {tmp}: PsiVal;')
                            lines.extend(self.emit_rust_assign(tmp, test, indent + 1))
                            lines.append(f'{pad}    if is_true({tmp}) {{')
                    lines.extend(self.emit_rust_return(val, indent + 1))
                if not first:
                    lines.append(f'{pad}}} else {{')
                    lines.append(f'{pad}    PSI_NIL')
                    lines.append(f'{pad}}}')
                else:
                    lines.append(f'{pad}PSI_NIL')
                return lines
            if head == 'let':
                bindings = sexpr[1]
                body = sexpr[2] if len(sexpr) == 3 else ['progn'] + sexpr[2:]
                for binding in bindings:
                    vname = rust_ident(binding[0])
                    lines.append(f'{pad}let {vname}: PsiVal;')
                    lines.extend(self.emit_rust_assign(vname, binding[1], indent))
                lines.extend(self.emit_rust_return(body, indent))
                return lines
            if head in ('progn', 'begin'):
                for expr in sexpr[1:-1]:
                    tmp = self.fresh()
                    lines.append(f'{pad}let {tmp}: PsiVal;')
                    lines.extend(self.emit_rust_assign(tmp, expr, indent))
                if len(sexpr) >= 2:
                    lines.extend(self.emit_rust_return(sexpr[-1], indent))
                else:
                    lines.append(f'{pad}PSI_NIL')
                return lines
        return [f'{pad}{self.emit_rust_expr(sexpr)}']

    def emit_rust_assign(self, target, sexpr, indent=1):
        pad = '    ' * indent
        lines = []
        if isinstance(sexpr, list) and len(sexpr) >= 1:
            head = sexpr[0]
            if head == 'if':
                test, then_b = sexpr[1], sexpr[2]
                else_b = sexpr[3] if len(sexpr) >= 4 else 'NIL'
                if self.is_simple_expr(test):
                    lines.append(f'{pad}{target} = if is_true({self.emit_rust_expr(test)}) {{')
                else:
                    tmp = self.fresh()
                    lines.append(f'{pad}let {tmp}: PsiVal;')
                    lines.extend(self.emit_rust_assign(tmp, test, indent))
                    lines.append(f'{pad}{target} = if is_true({tmp}) {{')
                # then branch
                if self.is_simple_expr(then_b):
                    lines.append(f'{pad}    {self.emit_rust_expr(then_b)}')
                else:
                    then_tmp = self.fresh()
                    lines.append(f'{pad}    let {then_tmp}: PsiVal;')
                    lines.extend(self.emit_rust_assign(then_tmp, then_b, indent + 1))
                    lines.append(f'{pad}    {then_tmp}')
                lines.append(f'{pad}}} else {{')
                # else branch
                if self.is_simple_expr(else_b):
                    lines.append(f'{pad}    {self.emit_rust_expr(else_b)}')
                else:
                    else_tmp = self.fresh()
                    lines.append(f'{pad}    let {else_tmp}: PsiVal;')
                    lines.extend(self.emit_rust_assign(else_tmp, else_b, indent + 1))
                    lines.append(f'{pad}    {else_tmp}')
                lines.append(f'{pad}}};')
                return lines
            if head == 'cond':
                # Emit as chain of if/else if
                first = True
                for clause in sexpr[1:]:
                    test, val = clause[0], clause[1]
                    if isinstance(test, str) and test.upper() == 'T':
                        if not first:
                            lines.append(f'{pad}}} else {{')
                        else:
                            lines.append(f'{pad}{{')
                        lines.extend(self.emit_rust_assign(target, val, indent + 1))
                        if not first:
                            lines.append(f'{pad}}}')
                        else:
                            lines.append(f'{pad}}}')
                        return lines
                    if first:
                        if self.is_simple_expr(test):
                            lines.append(f'{pad}if is_true({self.emit_rust_expr(test)}) {{')
                        else:
                            tmp = self.fresh()
                            lines.append(f'{pad}let {tmp}: PsiVal;')
                            lines.extend(self.emit_rust_assign(tmp, test, indent))
                            lines.append(f'{pad}if is_true({tmp}) {{')
                        first = False
                    else:
                        if self.is_simple_expr(test):
                            lines.append(f'{pad}}} else if is_true({self.emit_rust_expr(test)}) {{')
                        else:
                            tmp = self.fresh()
                            lines.append(f'{pad}}} else {{')
                            lines.append(f'{pad}    let {tmp}: PsiVal;')
                            lines.extend(self.emit_rust_assign(tmp, test, indent + 1))
                            lines.append(f'{pad}    if is_true({tmp}) {{')
                    lines.extend(self.emit_rust_assign(target, val, indent + 1))
                if not first:
                    lines.append(f'{pad}}} else {{')
                    lines.append(f'{pad}    {target} = PSI_NIL;')
                    lines.append(f'{pad}}}')
                else:
                    lines.append(f'{pad}{target} = PSI_NIL;')
                return lines
            if head == 'let':
                bindings = sexpr[1]
                body = sexpr[2] if len(sexpr) == 3 else ['progn'] + sexpr[2:]
                lines.append(f'{pad}{{')
                for binding in bindings:
                    vname = rust_ident(binding[0])
                    lines.append(f'{pad}    let {vname}: PsiVal;')
                    lines.extend(self.emit_rust_assign(vname, binding[1], indent + 1))
                lines.extend(self.emit_rust_assign(target, body, indent + 1))
                lines.append(f'{pad}}}')
                return lines
            if head in ('progn', 'begin'):
                for expr in sexpr[1:-1]:
                    tmp = self.fresh()
                    lines.append(f'{pad}let {tmp}: PsiVal;')
                    lines.extend(self.emit_rust_assign(tmp, expr, indent))
                if len(sexpr) >= 2:
                    lines.extend(self.emit_rust_assign(target, sexpr[-1], indent))
                else:
                    lines.append(f'{pad}{target} = PSI_NIL;')
                return lines
            if head == 'lambda':
                self.errors.append(f"lambda-as-value: {sexpr}")
                lines.append(f'{pad}{target} = PSI_NIL; // ERROR: lambda as value not supported')
                return lines
        # Check for borrow conflicts
        if self._needs_rust_temps(sexpr):
            return self._emit_rust_temped_call_assign(target, sexpr, indent)
        lines.append(f'{pad}{target} = {self.emit_rust_expr(sexpr)};')
        return lines

    def _emit_rust_string_as_charlist(self, s):
        """Emit a string literal as a cons-list of ASCII char codes."""
        chars = s.replace('\\n', '\n').replace('\\t', '\t').replace('\\\\', '\\')
        if not chars:
            return 'PSI_NIL'
        # Use a block with temps to avoid nested mutable borrow
        stmts = []
        result = 'PSI_NIL'
        for c in reversed(chars):
            tmp = self.fresh('_s')
            stmts.append(f'let {tmp} = arena.cons({ord(c)}_i64, {result});')
            result = tmp
        return '{ ' + ' '.join(stmts) + f' {result} }}'

    def emit_rust_expr(self, sexpr):
        """Emit a Rust expression for a simple S-expression."""
        if isinstance(sexpr, int):
            return f'{sexpr}_i64'
        if isinstance(sexpr, str):
            if sexpr.startswith('"') and sexpr.endswith('"'):
                inner = sexpr[1:-1]
                return self._emit_rust_string_as_charlist(inner)
            up = sexpr.upper()
            if up == 'NIL':
                return 'PSI_NIL'
            if up == 'T':
                return '1_i64'
            return rust_ident(sexpr)
        if not isinstance(sexpr, list) or len(sexpr) == 0:
            return 'PSI_NIL'

        head = sexpr[0]

        # Arithmetic
        if head == '+' and len(sexpr) == 3:
            return f'{self.emit_rust_expr(sexpr[1])} + {self.emit_rust_expr(sexpr[2])}'
        if head == '-' and len(sexpr) == 3:
            a, b = self.emit_rust_expr(sexpr[1]), self.emit_rust_expr(sexpr[2])
            return f'{{ let _a = {a}; let _b = {b}; if _a >= _b {{ _a - _b }} else {{ 0_i64 }} }}'
        if head == '*' and len(sexpr) == 3:
            return f'{self.emit_rust_expr(sexpr[1])} * {self.emit_rust_expr(sexpr[2])}'
        if head == '/' and len(sexpr) == 3:
            return f'{self.emit_rust_expr(sexpr[1])} / {self.emit_rust_expr(sexpr[2])}'
        if head == 'mod' and len(sexpr) == 3:
            return f'{self.emit_rust_expr(sexpr[1])} % {self.emit_rust_expr(sexpr[2])}'
        if head == '1+' and len(sexpr) == 2:
            return f'{self.emit_rust_expr(sexpr[1])} + 1'
        if head == '1-' and len(sexpr) == 2:
            a = self.emit_rust_expr(sexpr[1])
            return f'{{ let _a = {a}; if _a > 0 {{ _a - 1 }} else {{ 0_i64 }} }}'

        # Comparison
        if head == '<' and len(sexpr) == 3:
            return f'if {self.emit_rust_expr(sexpr[1])} < {self.emit_rust_expr(sexpr[2])} {{ 1_i64 }} else {{ PSI_NIL }}'
        if head == '>' and len(sexpr) == 3:
            return f'if {self.emit_rust_expr(sexpr[1])} > {self.emit_rust_expr(sexpr[2])} {{ 1_i64 }} else {{ PSI_NIL }}'
        if head == '<=' and len(sexpr) == 3:
            return f'if {self.emit_rust_expr(sexpr[1])} <= {self.emit_rust_expr(sexpr[2])} {{ 1_i64 }} else {{ PSI_NIL }}'
        if head == '>=' and len(sexpr) == 3:
            return f'if {self.emit_rust_expr(sexpr[1])} >= {self.emit_rust_expr(sexpr[2])} {{ 1_i64 }} else {{ PSI_NIL }}'
        if head in ('=', 'eq', 'equal') and len(sexpr) == 3:
            return f'if {self.emit_rust_expr(sexpr[1])} == {self.emit_rust_expr(sexpr[2])} {{ 1_i64 }} else {{ PSI_NIL }}'

        # Predicates
        if head == 'zerop' and len(sexpr) == 2:
            return f'if {self.emit_rust_expr(sexpr[1])} == 0 {{ 1_i64 }} else {{ PSI_NIL }}'
        if head == 'null' and len(sexpr) == 2:
            return f'if is_nil({self.emit_rust_expr(sexpr[1])}) {{ 1_i64 }} else {{ PSI_NIL }}'
        if head == 'not' and len(sexpr) == 2:
            return f'if is_nil({self.emit_rust_expr(sexpr[1])}) {{ 1_i64 }} else {{ PSI_NIL }}'
        if head == 'numberp' and len(sexpr) == 2:
            return f'{{ let _np = {self.emit_rust_expr(sexpr[1])}; if !is_nil(_np) && !is_cons(_np) {{ 1_i64 }} else {{ PSI_NIL }} }}'
        if head == 'atom' and len(sexpr) == 2:
            return f'if !is_cons({self.emit_rust_expr(sexpr[1])}) {{ 1_i64 }} else {{ PSI_NIL }}'

        # List operations — thread arena
        if head == 'cons' and len(sexpr) == 3:
            a_expr = self.emit_rust_expr(sexpr[1])
            b_expr = self.emit_rust_expr(sexpr[2])
            # Always use temps to avoid nested mutable borrow issues
            return f'{{ let _ca = {a_expr}; let _cb = {b_expr}; arena.cons(_ca, _cb) }}'
        if head == 'car' and len(sexpr) == 2:
            arg = self.emit_rust_expr(sexpr[1])
            if uses_arena(sexpr[1]) or self._calls_arena_fn(sexpr[1]):
                return f'{{ let _cr = {arg}; arena.car(_cr) }}'
            return f'arena.car({arg})'
        if head == 'cdr' and len(sexpr) == 2:
            arg = self.emit_rust_expr(sexpr[1])
            if uses_arena(sexpr[1]) or self._calls_arena_fn(sexpr[1]):
                return f'{{ let _cr = {arg}; arena.cdr(_cr) }}'
            return f'arena.cdr({arg})'
        if head == 'list':
            if len(sexpr) == 1:
                return 'PSI_NIL'
            # Evaluate all items into temps first, then build cons list
            stmts = []
            item_vars = []
            for item in sexpr[1:]:
                item_expr = self.emit_rust_expr(item)
                tmp = self.fresh('_li')
                stmts.append(f'let {tmp} = {item_expr};')
                item_vars.append(tmp)
            result = 'PSI_NIL'
            for var in reversed(item_vars):
                tmp = self.fresh('_l')
                stmts.append(f'let {tmp} = arena.cons({var}, {result});')
                result = tmp
            return '{ ' + ' '.join(stmts) + f' {result} }}'

        # IO — evaluate into temp to avoid arena borrow conflicts
        if head == 'print' and len(sexpr) == 2:
            return f'{{ let _pv = {self.emit_rust_expr(sexpr[1])}; psi_println(&arena, _pv); PSI_NIL }}'
        if head == 'display' and len(sexpr) == 2:
            return f'{{ let _pv = {self.emit_rust_expr(sexpr[1])}; psi_print_val(&arena, _pv); PSI_NIL }}'
        if head == 'terpri':
            return '{ println!(); PSI_NIL }'
        if head == 'write-string' and len(sexpr) == 2:
            arg = sexpr[1]
            if isinstance(arg, str) and arg.startswith('"'):
                inner = arg[1:-1].replace('\\', '\\\\').replace('\n', '\\n')
                # Escape { and } for Rust format strings
                inner = inner.replace('{', '{{').replace('}', '}}')
                return f'{{ print!("{inner}"); PSI_NIL }}'
            return f'{{ let _ws = {self.emit_rust_expr(arg)}; psi_write_string(&arena, _ws); PSI_NIL }}'
        if head == 'write-char' and len(sexpr) == 2:
            return f'{{ print!("{{}}", ({self.emit_rust_expr(sexpr[1])}) as u8 as char); PSI_NIL }}'

        # Cayley table
        if head == 'dot' and len(sexpr) == 3:
            first = sexpr[1]
            first_idx = None
            if isinstance(first, str) and first in ('INC', 'INV', 'DEC'):
                first_idx = {'INC': 13, 'INV': 14, 'DEC': 15}[first]
            elif isinstance(first, int) and first in (13, 14, 15):
                first_idx = first
            if first_idx == 13:
                return f'(psi_inc({self.emit_rust_expr(sexpr[2])} as u8) as PsiVal)'
            if first_idx == 14:
                return f'(psi_inv({self.emit_rust_expr(sexpr[2])} as u8) as PsiVal)'
            if first_idx == 15:
                return f'(psi_dec({self.emit_rust_expr(sexpr[2])} as u8) as PsiVal)'
            return f'(psi_dot({self.emit_rust_expr(sexpr[1])} as u8, {self.emit_rust_expr(sexpr[2])} as u8) as PsiVal)'

        if head == 'atom-name' and len(sexpr) == 2:
            return f'psi_atom_name({self._rust_arena_ref}, {self.emit_rust_expr(sexpr[1])})'

        # Logical
        if head == 'and':
            if len(sexpr) == 1:
                return '1_i64'
            parts = [self.emit_rust_expr(a) for a in sexpr[1:]]
            result = parts[-1]
            for p in reversed(parts[:-1]):
                result = f'if is_true({p}) {{ {result} }} else {{ PSI_NIL }}'
            return result
        if head == 'or':
            if len(sexpr) == 1:
                return 'PSI_NIL'
            parts = [self.emit_rust_expr(a) for a in sexpr[1:]]
            result = parts[-1]
            for p in reversed(parts[:-1]):
                result = f'{{ let _v = {p}; if is_true(_v) {{ _v }} else {{ {result} }} }}'
            return result

        # Quote
        if head == 'quote' and len(sexpr) == 2:
            return self.emit_rust_datum(sexpr[1])

        # If as expression (parens needed so it can appear in +, * etc.)
        if head == 'if' and len(sexpr) >= 3:
            test = self.emit_rust_expr(sexpr[1])
            then_e = self.emit_rust_expr(sexpr[2])
            else_e = self.emit_rust_expr(sexpr[3]) if len(sexpr) >= 4 else 'PSI_NIL'
            return f'(if is_true({test}) {{ {then_e} }} else {{ {else_e} }})'

        # Direct lambda application
        if isinstance(head, list) and len(head) >= 3 and head[0] == 'lambda':
            params = head[1]
            body = head[2]
            if len(params) == 1 and len(sexpr) == 2:
                return self.emit_rust_expr(['let', [[params[0], sexpr[1]]], body])

        # Function call
        if isinstance(head, str) and head not in SPECIAL_FORMS:
            rname = rust_ident(head)
            cname = c_ident(head)
            needs_arena = self._fn_needs_arena.get(cname, False)
            # If call needs arena AND any arg uses arena, pull into temps
            # to avoid multiple mutable borrows of arena.
            if needs_arena and any(uses_arena(a) or self._calls_arena_fn(a) for a in sexpr[1:]):
                temps = []
                lets = []
                for a in sexpr[1:]:
                    if uses_arena(a) or self._calls_arena_fn(a):
                        tmp = self.fresh()
                        lets.append(f'let {tmp} = {self.emit_rust_expr(a)};')
                        temps.append(tmp)
                    else:
                        temps.append(self.emit_rust_expr(a))
                args = [self._rust_arena_ref] + temps
                return '{ ' + ' '.join(lets) + f' {rname}({", ".join(args)})' + ' }'
            args = []
            if needs_arena:
                args.append(self._rust_arena_ref)
            for a in sexpr[1:]:
                args.append(self.emit_rust_expr(a))
            return f'{rname}({", ".join(args)})'

        self.errors.append(f"unhandled expression: {sexpr}")
        return f'PSI_NIL /* unhandled: {head} */'

    def emit_rust_datum(self, datum):
        """Emit a Rust expression for a simple (non-list) datum."""
        if isinstance(datum, int):
            return f'{datum}_i64'
        if isinstance(datum, str):
            up = datum.upper()
            if up == 'NIL':
                return 'PSI_NIL'
            if up == 'T':
                return '1_i64'
            if datum in self.symbol_table:
                return self._sym_const_name(datum)
            return rust_ident(datum)
        if isinstance(datum, list):
            if len(datum) == 0:
                return 'PSI_NIL'
            # For lists, use a block with temporaries to avoid nested arena borrows
            stmts = []
            result_var = self._emit_rust_datum_list(datum, stmts)
            block = '{ ' + ' '.join(stmts) + f' {result_var} }}'
            return block
        return 'PSI_NIL'

    def _emit_rust_datum_list(self, datum, stmts):
        """Build a cons-list datum using temp variables. Returns the final var name."""
        if isinstance(datum, list):
            if len(datum) == 0:
                return 'PSI_NIL'
            # Build tail-first
            result = 'PSI_NIL'
            for item in reversed(datum):
                item_var = self._emit_rust_datum_item(item, stmts)
                tmp = self.fresh('_d')
                stmts.append(f'let {tmp} = arena.cons({item_var}, {result});')
                result = tmp
            return result
        return self._emit_rust_datum_item(datum, stmts)

    def _emit_rust_datum_item(self, datum, stmts):
        """Emit a single datum item, returning a var name or simple expression."""
        if isinstance(datum, int):
            return f'{datum}_i64'
        if isinstance(datum, str):
            up = datum.upper()
            if up == 'NIL':
                return 'PSI_NIL'
            if up == 'T':
                return '1_i64'
            if datum in self.symbol_table:
                return self._sym_const_name(datum)
            return rust_ident(datum)
        if isinstance(datum, list):
            if len(datum) == 0:
                return 'PSI_NIL'
            return self._emit_rust_datum_list(datum, stmts)
        return 'PSI_NIL'

    # ── C emission (original) ──────────────────────────────────────────

    def emit_return(self, sexpr, indent=1):
        """Emit statements that return the value of sexpr."""
        pad = '    ' * indent
        # Check if we can emit as a simple expression
        if self.is_simple_expr(sexpr):
            return [f'{pad}return {self.emit_expr(sexpr)};']
        # Complex forms need statement-level emission
        return self.emit_stmt_return(sexpr, indent)

    def emit_stmt_return(self, sexpr, indent):
        """Emit complex forms as statements, ending with a return."""
        pad = '    ' * indent
        lines = []
        if isinstance(sexpr, list) and len(sexpr) >= 1:
            head = sexpr[0]
            if head == 'if':
                test, then_b = sexpr[1], sexpr[2]
                else_b = sexpr[3] if len(sexpr) >= 4 else 'NIL'
                if self.is_simple_expr(test):
                    lines.append(f'{pad}if (IS_TRUE({self.emit_expr(test)})) {{')
                else:
                    tmp = self.fresh()
                    lines.append(f'{pad}psi_val {tmp};')
                    lines.extend(self.emit_assign(tmp, test, indent))
                    lines.append(f'{pad}if (IS_TRUE({tmp})) {{')
                lines.extend(self.emit_return(then_b, indent + 1))
                lines.append(f'{pad}}} else {{')
                lines.extend(self.emit_return(else_b, indent + 1))
                lines.append(f'{pad}}}')
                return lines
            if head == 'cond':
                for clause in sexpr[1:]:
                    test, val = clause[0], clause[1]
                    if isinstance(test, str) and test.upper() == 'T':
                        lines.extend(self.emit_return(val, indent))
                        return lines
                    if self.is_simple_expr(test):
                        lines.append(f'{pad}if (IS_TRUE({self.emit_expr(test)})) {{')
                    else:
                        tmp = self.fresh()
                        lines.append(f'{pad}psi_val {tmp};')
                        lines.extend(self.emit_assign(tmp, test, indent))
                        lines.append(f'{pad}if (IS_TRUE({tmp})) {{')
                    lines.extend(self.emit_return(val, indent + 1))
                    lines.append(f'{pad}}}')
                lines.append(f'{pad}return PSI_NIL;')
                return lines
            if head == 'let':
                bindings = sexpr[1]
                body = sexpr[2] if len(sexpr) == 3 else ['progn'] + sexpr[2:]
                for binding in bindings:
                    vname = c_ident(binding[0])
                    lines.append(f'{pad}psi_val {vname};')
                    lines.extend(self.emit_assign(vname, binding[1], indent))
                lines.extend(self.emit_return(body, indent))
                return lines
            if head in ('progn', 'begin'):
                for expr in sexpr[1:-1]:
                    tmp = self.fresh()
                    lines.append(f'{pad}psi_val {tmp};')
                    lines.extend(self.emit_assign(tmp, expr, indent))
                if len(sexpr) >= 2:
                    lines.extend(self.emit_return(sexpr[-1], indent))
                else:
                    lines.append(f'{pad}return PSI_NIL;')
                return lines
        # Fallback: treat as expression
        return [f'{pad}return {self.emit_expr(sexpr)};']

    def emit_assign(self, target, sexpr, indent=1):
        """Emit statements that assign value of sexpr to target."""
        pad = '    ' * indent
        lines = []
        if isinstance(sexpr, list) and len(sexpr) >= 1:
            head = sexpr[0]
            if head == 'if':
                test, then_b = sexpr[1], sexpr[2]
                else_b = sexpr[3] if len(sexpr) >= 4 else 'NIL'
                if self.is_simple_expr(test):
                    lines.append(f'{pad}if (IS_TRUE({self.emit_expr(test)})) {{')
                else:
                    tmp = self.fresh()
                    lines.append(f'{pad}psi_val {tmp};')
                    lines.extend(self.emit_assign(tmp, test, indent))
                    lines.append(f'{pad}if (IS_TRUE({tmp})) {{')
                lines.extend(self.emit_assign(target, then_b, indent + 1))
                lines.append(f'{pad}}} else {{')
                lines.extend(self.emit_assign(target, else_b, indent + 1))
                lines.append(f'{pad}}}')
                return lines
            if head == 'cond':
                for clause in sexpr[1:]:
                    test, val = clause[0], clause[1]
                    if isinstance(test, str) and test.upper() == 'T':
                        lines.extend(self.emit_assign(target, val, indent))
                        return lines
                    if self.is_simple_expr(test):
                        lines.append(f'{pad}if (IS_TRUE({self.emit_expr(test)})) {{')
                    else:
                        tmp = self.fresh()
                        lines.append(f'{pad}psi_val {tmp};')
                        lines.extend(self.emit_assign(tmp, test, indent))
                        lines.append(f'{pad}if (IS_TRUE({tmp})) {{')
                    lines.extend(self.emit_assign(target, val, indent + 1))
                    lines.append(f'{pad}}}')
                lines.append(f'{pad}{target} = PSI_NIL;')
                return lines
            if head == 'let':
                bindings = sexpr[1]
                body = sexpr[2] if len(sexpr) == 3 else ['progn'] + sexpr[2:]
                lines.append(f'{pad}{{')
                for binding in bindings:
                    vname = c_ident(binding[0])
                    lines.append(f'{pad}    psi_val {vname};')
                    lines.extend(self.emit_assign(vname, binding[1], indent + 1))
                lines.extend(self.emit_assign(target, body, indent + 1))
                lines.append(f'{pad}}}')
                return lines
            if head in ('progn', 'begin'):
                for expr in sexpr[1:-1]:
                    tmp = self.fresh()
                    lines.append(f'{pad}psi_val {tmp};')
                    lines.extend(self.emit_assign(tmp, expr, indent))
                if len(sexpr) >= 2:
                    lines.extend(self.emit_assign(target, sexpr[-1], indent))
                else:
                    lines.append(f'{pad}{target} = PSI_NIL;')
                return lines
            if head == 'lambda':
                self.errors.append(f"lambda-as-value: {sexpr}")
                lines.append(f'{pad}{target} = PSI_NIL; /* ERROR: lambda as value not supported */')
                return lines
        # Simple expression
        lines.append(f'{pad}{target} = {self.emit_expr(sexpr)};')
        return lines

    def is_simple_expr(self, sexpr):
        """Can this be emitted as a single C expression (no statements)?"""
        if isinstance(sexpr, (int, str)):
            return True
        if isinstance(sexpr, list) and len(sexpr) >= 1:
            head = sexpr[0]
            if head in ('if', 'cond', 'let', 'progn', 'begin', 'lambda',
                        'defun', 'define', 'setq'):
                return False
            return all(self.is_simple_expr(a) for a in sexpr[1:])
        return True

    def emit_expr(self, sexpr):
        """Emit a C expression for a simple S-expression."""
        if isinstance(sexpr, int):
            return f'(psi_val){sexpr}'
        if isinstance(sexpr, str):
            if sexpr.startswith('"') and sexpr.endswith('"'):
                # String literal for write-string — handle at call site
                return f'"{sexpr[1:-1]}"'
            up = sexpr.upper()
            if up == 'NIL':
                return 'PSI_NIL'
            if up == 'T':
                return '(psi_val)1'  # T = truthy non-NIL
            return c_ident(sexpr)
        if not isinstance(sexpr, list) or len(sexpr) == 0:
            return 'PSI_NIL'

        head = sexpr[0]

        # Arithmetic
        if head == '+' and len(sexpr) == 3:
            return f'({self.emit_expr(sexpr[1])} + {self.emit_expr(sexpr[2])})'
        if head == '-' and len(sexpr) == 3:
            a, b = self.emit_expr(sexpr[1]), self.emit_expr(sexpr[2])
            return f'(({a}) >= ({b}) ? ({a}) - ({b}) : (psi_val)0)'
        if head == '*' and len(sexpr) == 3:
            return f'({self.emit_expr(sexpr[1])} * {self.emit_expr(sexpr[2])})'
        if head == 'mod' and len(sexpr) == 3:
            return f'({self.emit_expr(sexpr[1])} % {self.emit_expr(sexpr[2])})'
        if head == '1+' and len(sexpr) == 2:
            return f'({self.emit_expr(sexpr[1])} + 1)'
        if head == '1-' and len(sexpr) == 2:
            a = self.emit_expr(sexpr[1])
            return f'(({a}) > 0 ? ({a}) - 1 : (psi_val)0)'

        # Comparison (return 1 for true, PSI_NIL for false)
        if head == '<' and len(sexpr) == 3:
            return f'({self.emit_expr(sexpr[1])} < {self.emit_expr(sexpr[2])} ? (psi_val)1 : PSI_NIL)'
        if head == '>' and len(sexpr) == 3:
            return f'({self.emit_expr(sexpr[1])} > {self.emit_expr(sexpr[2])} ? (psi_val)1 : PSI_NIL)'
        if head == '<=' and len(sexpr) == 3:
            return f'({self.emit_expr(sexpr[1])} <= {self.emit_expr(sexpr[2])} ? (psi_val)1 : PSI_NIL)'
        if head == '>=' and len(sexpr) == 3:
            return f'({self.emit_expr(sexpr[1])} >= {self.emit_expr(sexpr[2])} ? (psi_val)1 : PSI_NIL)'
        if head in ('=', 'eq', 'equal') and len(sexpr) == 3:
            return f'({self.emit_expr(sexpr[1])} == {self.emit_expr(sexpr[2])} ? (psi_val)1 : PSI_NIL)'

        # Predicates
        if head == 'zerop' and len(sexpr) == 2:
            return f'({self.emit_expr(sexpr[1])} == 0 ? (psi_val)1 : PSI_NIL)'
        if head == 'null' and len(sexpr) == 2:
            return f'(IS_NIL({self.emit_expr(sexpr[1])}) ? (psi_val)1 : PSI_NIL)'
        if head == 'not' and len(sexpr) == 2:
            return f'(IS_NIL({self.emit_expr(sexpr[1])}) ? (psi_val)1 : PSI_NIL)'

        # List operations
        if head == 'cons' and len(sexpr) == 3:
            return f'psi_cons({self.emit_expr(sexpr[1])}, {self.emit_expr(sexpr[2])})'
        if head == 'car' and len(sexpr) == 2:
            return f'psi_car({self.emit_expr(sexpr[1])})'
        if head == 'cdr' and len(sexpr) == 2:
            return f'psi_cdr({self.emit_expr(sexpr[1])})'
        if head == 'list':
            if len(sexpr) == 1:
                return 'PSI_NIL'
            # Build cons chain right-to-left
            result = 'PSI_NIL'
            for item in reversed(sexpr[1:]):
                result = f'psi_cons({self.emit_expr(item)}, {result})'
            return result

        # IO
        if head == 'print' and len(sexpr) == 2:
            return f'(psi_println({self.emit_expr(sexpr[1])}), PSI_NIL)'
        if head == 'display' and len(sexpr) == 2:
            return f'(psi_print_val({self.emit_expr(sexpr[1])}), PSI_NIL)'
        if head == 'terpri':
            return '(printf("\\n"), PSI_NIL)'
        if head == 'write-string' and len(sexpr) == 2:
            arg = sexpr[1]
            if isinstance(arg, str) and arg.startswith('"'):
                inner = arg[1:-1].replace('\\', '\\\\').replace('\n', '\\n')
                return f'(printf("%s", "{inner}"), PSI_NIL)'
            return f'(psi_print_val({self.emit_expr(arg)}), PSI_NIL)'

        # Cayley table — specialize INC/DEC/INV for Ψ₁₆ᶜ inline helpers
        if head == 'dot' and len(sexpr) == 3:
            first = sexpr[1]
            # Check if first arg is a known atom (string name or integer)
            first_idx = None
            if isinstance(first, str) and first in ('INC', 'INV', 'DEC'):
                first_idx = {'INC': 13, 'INV': 14, 'DEC': 15}[first]
            elif isinstance(first, int) and first in (13, 14, 15):
                first_idx = first
            if first_idx == 13:
                return f'(psi_val)psi_inc((uint8_t){self.emit_expr(sexpr[2])})'
            if first_idx == 14:
                return f'(psi_val)psi_inv((uint8_t){self.emit_expr(sexpr[2])})'
            if first_idx == 15:
                return f'(psi_val)psi_dec((uint8_t){self.emit_expr(sexpr[2])})'
            return f'(psi_val)psi_dot((uint8_t){self.emit_expr(sexpr[1])}, (uint8_t){self.emit_expr(sexpr[2])})'

        # Logical (short-circuit — only works as simple expr if args are simple)
        if head == 'and':
            if len(sexpr) == 1:
                return '(psi_val)1'
            parts = [self.emit_expr(a) for a in sexpr[1:]]
            # Chain: check each, return last truthy or first falsy
            result = parts[-1]
            for p in reversed(parts[:-1]):
                result = f'(IS_TRUE({p}) ? {result} : PSI_NIL)'
            return result
        if head == 'or':
            if len(sexpr) == 1:
                return 'PSI_NIL'
            parts = [self.emit_expr(a) for a in sexpr[1:]]
            result = parts[-1]
            for p in reversed(parts[:-1]):
                result = f'(IS_TRUE({p}) ? {p} : {result})'
            return result

        # Quote
        if head == 'quote' and len(sexpr) == 2:
            return self.emit_datum(sexpr[1])

        # If as ternary (simple case)
        if head == 'if' and len(sexpr) >= 3:
            test = self.emit_expr(sexpr[1])
            then_e = self.emit_expr(sexpr[2])
            else_e = self.emit_expr(sexpr[3]) if len(sexpr) >= 4 else 'PSI_NIL'
            return f'(IS_TRUE({test}) ? {then_e} : {else_e})'

        # Direct lambda application: ((lambda (x) body) arg)
        if isinstance(head, list) and len(head) >= 3 and head[0] == 'lambda':
            params = head[1]
            body = head[2]
            if len(params) == 1 and len(sexpr) == 2:
                # Inline as let
                return self.emit_expr(['let', [[params[0], sexpr[1]]], body])

        # Function call
        if isinstance(head, str) and head not in SPECIAL_FORMS:
            cname = c_ident(head)
            args = ', '.join(self.emit_expr(a) for a in sexpr[1:])
            return f'{cname}({args})'

        self.errors.append(f"unhandled expression: {sexpr}")
        return f'PSI_NIL /* unhandled: {head} */'

    def emit_datum(self, datum):
        """Emit a quoted datum as a C expression."""
        if isinstance(datum, int):
            return f'(psi_val){datum}'
        if isinstance(datum, str):
            up = datum.upper()
            if up == 'NIL':
                return 'PSI_NIL'
            if up == 'T':
                return '(psi_val)1'
            return c_ident(datum)
        if isinstance(datum, list):
            if len(datum) == 0:
                return 'PSI_NIL'
            result = 'PSI_NIL'
            for item in reversed(datum):
                result = f'psi_cons({self.emit_datum(item)}, {result})'
            return result
        return 'PSI_NIL'


# ═══════════════════════════════════════════════════════════════════════
# Utilities
# ═══════════════════════════════════════════════════════════════════════

def c_ident(name):
    """Sanitize a name for C."""
    if isinstance(name, int):
        return str(name)
    s = str(name)
    s = s.replace('-', '_').replace('?', '_p').replace('!', '_b')
    s = s.replace('+', '_plus').replace('*', '_star').replace('/', '_slash')
    s = s.replace('<', '_lt').replace('>', '_gt').replace('=', '_eq')
    if s in ('int', 'float', 'double', 'char', 'void', 'return', 'if',
             'else', 'for', 'while', 'do', 'switch', 'case', 'break',
             'continue', 'struct', 'typedef', 'const', 'static', 'main'):
        s = 'psi_' + s
    return s


def rust_ident(name):
    """Sanitize a name for Rust."""
    if isinstance(name, int):
        return str(name)
    s = str(name)
    s = s.replace('-', '_').replace('?', '_p').replace('!', '_b')
    s = s.replace('+', '_plus').replace('*', '_star').replace('/', '_slash')
    s = s.replace('<', '_lt').replace('>', '_gt').replace('=', '_eq')
    # Rust reserved words
    if s in ('fn', 'let', 'mut', 'ref', 'if', 'else', 'for', 'while', 'loop',
             'match', 'return', 'break', 'continue', 'struct', 'enum', 'impl',
             'trait', 'type', 'const', 'static', 'pub', 'mod', 'use', 'self',
             'super', 'crate', 'where', 'as', 'in', 'move', 'main', 'true',
             'false', 'str', 'bool', 'i64', 'u8', 'box'):
        s = 'psi_' + s
    return s


def uses_arena(sexpr):
    """Check if an S-expression uses list operations (cons/car/cdr/list/print/atom-name)."""
    if isinstance(sexpr, (int, str)):
        # String literals as PsiVal become cons-lists of char codes
        if isinstance(sexpr, str) and sexpr.startswith('"') and sexpr.endswith('"') and len(sexpr) > 2:
            return True
        return False
    if isinstance(sexpr, list) and len(sexpr) >= 1:
        head = sexpr[0]
        if isinstance(head, str) and head in ('cons', 'car', 'cdr', 'list',
                                               'print', 'display', 'atom-name',
                                               'numberp', 'atom'):
            return True
        # quote with a list datum needs arena to build cons cells
        if head == 'quote' and len(sexpr) == 2:
            if isinstance(sexpr[1], list) and len(sexpr[1]) > 0:
                return True
        # write-string with a non-literal argument needs arena for psi_write_string
        if isinstance(head, str) and head == 'write-string' and len(sexpr) == 2:
            arg = sexpr[1]
            if not (isinstance(arg, str) and arg.startswith('"')):
                return True
        return any(uses_arena(item) for item in sexpr)
    return False

def find_free_vars(sexpr, bound, known):
    """Find variables in sexpr that are not in bound or known."""
    if isinstance(sexpr, str):
        up = sexpr.upper()
        if up in ('NIL', 'T'):
            return set()
        if sexpr in bound or sexpr in known:
            return set()
        if sexpr.startswith('"'):
            return set()
        return {sexpr}
    if isinstance(sexpr, int):
        return set()
    if isinstance(sexpr, list) and len(sexpr) >= 1:
        head = sexpr[0]
        if head == 'let' and len(sexpr) >= 3:
            free = set()
            new_bound = set(bound)
            for binding in sexpr[1]:
                free |= find_free_vars(binding[1], bound, known)
                new_bound.add(binding[0])
            for b in sexpr[2:]:
                free |= find_free_vars(b, new_bound, known)
            return free
        if head == 'lambda' and len(sexpr) >= 3:
            params = set(sexpr[1]) if isinstance(sexpr[1], list) else {sexpr[1]}
            return find_free_vars(sexpr[2], bound | params, known)
        if head == 'defun' and len(sexpr) >= 4:
            # Skip nested defuns — handled by lifting
            return set()
        if head == 'quote':
            return set()
        free = set()
        for i, item in enumerate(sexpr):
            if i == 0 and isinstance(item, str) and item in (SPECIAL_FORMS | BUILTINS):
                continue
            free |= find_free_vars(item, bound, known)
        return free
    return set()

def rewrite_calls(sexpr, lifted_map):
    """Rewrite calls to lifted functions, adding extra args."""
    if isinstance(sexpr, str):
        return sexpr
    if isinstance(sexpr, int):
        return sexpr
    if isinstance(sexpr, list):
        if len(sexpr) >= 1 and isinstance(sexpr[0], str) and sexpr[0] in lifted_map:
            lifted_name, extra = lifted_map[sexpr[0]]
            new_call = [lifted_name] + [rewrite_calls(a, lifted_map) for a in sexpr[1:]] + list(extra)
            return new_call
        return [rewrite_calls(item, lifted_map) for item in sexpr]
    return sexpr

# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    # Parse args
    target = 'c'
    table = 'f'  # default: Ψ₁₆ᶠ
    paths = []
    args = sys.argv[1:]
    i = 0
    while i < len(args):
        if args[i] == '--target' and i + 1 < len(args):
            target = args[i + 1].lower()
            i += 2
        elif args[i].startswith('--target='):
            target = args[i].split('=', 1)[1].lower()
            i += 1
        elif args[i] == '--table' and i + 1 < len(args):
            table = args[i + 1].lower()
            i += 2
        elif args[i].startswith('--table='):
            table = args[i].split('=', 1)[1].lower()
            i += 1
        elif not args[i].startswith('-'):
            paths.append(args[i])
            i += 1
        else:
            print(f"Unknown option: {args[i]}", file=sys.stderr)
            sys.exit(1)

    if not paths:
        print("Usage: psi_transpile.py [--target c|rust] [--table f|c] program.lisp [...]", file=sys.stderr)
        sys.exit(1)
    if target not in ('c', 'rust'):
        print(f"Unknown target: {target}. Use 'c' or 'rust'.", file=sys.stderr)
        sys.exit(1)
    if table not in ('f', 'c'):
        print(f"Unknown table: {table}. Use 'f' (Ψ₁₆ᶠ, default) or 'c' (Ψ₁₆ᶜ).", file=sys.stderr)
        sys.exit(1)

    source = ''
    for path in paths:
        with open(path) as f:
            source += f.read() + '\n'

    forms = parse_all(source)
    compiler = Compiler()
    compiler.table = table
    compiler.process(forms)

    if target == 'rust':
        code = compiler.emit_rust()
    else:
        code = compiler.emit_c()
    print(code, end='')

    comment = '//' if target == 'rust' else '/*'
    end_comment = '' if target == 'rust' else ' */'
    if compiler.errors:
        print(f'{comment} TRANSPILER WARNINGS:', file=sys.stderr)
        for e in compiler.errors:
            print(f'{comment}   {e}', file=sys.stderr)
        if end_comment:
            print(end_comment, file=sys.stderr)


if __name__ == '__main__':
    main()

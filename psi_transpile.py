#!/usr/bin/env python3
"""
Ψ-Lisp → C transpiler.

Reads Ψ-Lisp source (.lisp) or .psi IR and emits C code using psi_runtime.h.

Handles: defun (recursive, multi-arg), nested defun (lifted), arithmetic,
if/cond, let, progn, cons/car/cdr/null/list, print/display/terpri/write-string,
and/or/not, lambda in direct application, setq, quote.

Does NOT handle: closures (lambda as value), higher-order functions (passing
functions as arguments), function values in setq. These require a closure
representation that C doesn't natively support.

Usage:
  python3 psi_transpile.py program.lisp > program.c
  gcc -O2 -I. -o program program.c
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
        self.main_stmts = []       # [sexpr]  — bare expressions to evaluate
        self.known_fns = set()     # all known function names
        self.tmp_count = 0
        self.errors = []           # constructs we couldn't handle

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
                    self.globals.append((form[1], form[2]))
                    continue
            self.main_stmts.append(form)

    def process_defun(self, form, prefix):
        name = form[1]
        params = form[2] if isinstance(form[2], list) else [form[2]]
        body = form[3] if len(form) == 4 else ['progn'] + form[3:]

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
            tmp = self.fresh()
            lines.append(f'    psi_val {tmp};')
            lines.extend(self.emit_assign(tmp, stmt, indent=1))
            lines.append(f'    psi_println({tmp});')
        lines.append('    return 0;')
        lines.append('}')
        return '\n'.join(lines) + '\n'

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
    if len(sys.argv) < 2:
        print("Usage: psi_transpile.py program.lisp", file=sys.stderr)
        sys.exit(1)

    path = sys.argv[1]
    with open(path) as f:
        source = f.read()

    forms = parse_all(source)
    compiler = Compiler()
    compiler.process(forms)

    c_code = compiler.emit_c()
    print(c_code, end='')

    if compiler.errors:
        print(f'/* TRANSPILER WARNINGS:', file=sys.stderr)
        for e in compiler.errors:
            print(f'   {e}', file=sys.stderr)
        print(f'*/', file=sys.stderr)


if __name__ == '__main__':
    main()

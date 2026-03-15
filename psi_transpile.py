#!/usr/bin/env python3
"""
Ψ∗ → C transpiler.

Reads a .psi intermediate representation (output of psi_supercompile.py)
and emits C code that uses psi_runtime.h for Cayley table lookups.

Usage:
  python3 psi_transpile.py input.psi > output.c
"""

import sys

# ═══════════════════════════════════════════════════════════════════════
# Same IR and parser as psi_supercompile.py
# ═══════════════════════════════════════════════════════════════════════

ATOM_NAMES = {
    'TOP': 0, 'BOT': 1, 'f': 2, 'TAU': 3, 'g': 4, 'SEQ': 5,
    'Q': 6, 'E': 7, 'RHO': 8, 'ETA': 9, 'Y': 10, 'PAIR': 11,
    's0': 12, 'INC': 13, 'GET': 14, 'DEC': 15,
    's1': 14, 's2': 6, 's3': 11, 's4': 10, 's5': 15, 's6': 8, 's7': 7,
}

ATOM_COMMENTS = {
    0: 'TOP', 1: 'BOT', 2: 'f', 3: 'TAU', 4: 'g', 5: 'SEQ',
    6: 'Q', 7: 'E', 8: 'RHO', 9: 'ETA', 10: 'Y', 11: 'PAIR',
    12: 's0', 13: 'INC', 14: 'GET/s1', 15: 'DEC',
}

class Atom:
    __slots__ = ['idx']
    def __init__(self, idx): self.idx = idx

class Var:
    __slots__ = ['name']
    def __init__(self, name): self.name = name

class Dot:
    __slots__ = ['a', 'b']
    def __init__(self, a, b): self.a = a; self.b = b

class If:
    __slots__ = ['test', 'then_b', 'else_b']
    def __init__(self, test, then_b, else_b):
        self.test = test; self.then_b = then_b; self.else_b = else_b

class Let:
    __slots__ = ['var', 'val', 'body']
    def __init__(self, var, val, body):
        self.var = var; self.val = val; self.body = body

class Lam:
    __slots__ = ['param', 'body']
    def __init__(self, param, body): self.param = param; self.body = body

class App:
    __slots__ = ['fn', 'arg']
    def __init__(self, fn, arg): self.fn = fn; self.arg = arg


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
        else:
            j = i
            while j < len(s) and s[j] not in ' \t\n\r();':
                j += 1
            tokens.append(s[i:j])
            i = j
    return tokens

def parse_tokens(tokens, pos):
    if pos >= len(tokens):
        raise SyntaxError("unexpected end")
    tok = tokens[pos]
    if tok == '(':
        pos += 1
        items = []
        while pos < len(tokens) and tokens[pos] != ')':
            item, pos = parse_tokens(tokens, pos)
            items.append(item)
        return items, pos + 1
    if tok == ')':
        raise SyntaxError("unexpected )")
    return tok, pos + 1

def parse_all_tokens(tokens):
    forms = []
    pos = 0
    while pos < len(tokens):
        form, pos = parse_tokens(tokens, pos)
        forms.append(form)
    return forms

def to_expr(form):
    if isinstance(form, str):
        if form in ATOM_NAMES:
            return Atom(ATOM_NAMES[form])
        try:
            n = int(form)
            if 0 <= n <= 15:
                return Atom(n)
            return Var(form)
        except ValueError:
            pass
        return Var(form)
    if isinstance(form, list) and len(form) >= 1:
        head = form[0]
        if head == 'dot' and len(form) == 3:
            return Dot(to_expr(form[1]), to_expr(form[2]))
        if head == 'if' and len(form) == 4:
            return If(to_expr(form[1]), to_expr(form[2]), to_expr(form[3]))
        if head == 'let' and len(form) == 4:
            return Let(form[1], to_expr(form[2]), to_expr(form[3]))
        if head == 'lam' and len(form) == 3:
            return Lam(form[1], to_expr(form[2]))
        if head == 'app' and len(form) == 3:
            return App(to_expr(form[1]), to_expr(form[2]))
        if head == 'defun' and len(form) == 4:
            return ('defun', form[1], form[2], to_expr(form[3]))
        if head == 'main' and len(form) == 2:
            return ('main', to_expr(form[1]))
    raise SyntaxError(f"bad form: {form}")

def parse_file(source):
    tokens = tokenize(source)
    forms = parse_all_tokens(tokens)
    return [to_expr(f) for f in forms]

# ═══════════════════════════════════════════════════════════════════════
# C code generation
# ═══════════════════════════════════════════════════════════════════════

def c_ident(name):
    """Sanitize a name for C identifier use."""
    return name.replace('-', '_').replace('?', '_p').replace('!', '_b')

def atom_comment(idx):
    return ATOM_COMMENTS.get(idx, '')

def emit_expr(e):
    """Emit a C expression string for an IR node."""
    if isinstance(e, Atom):
        cmt = atom_comment(e.idx)
        if cmt:
            return f'{e.idx} /* {cmt} */'
        return str(e.idx)
    if isinstance(e, Var):
        return c_ident(e.name)
    if isinstance(e, Dot):
        return f'psi_dot({emit_expr(e.a)}, {emit_expr(e.b)})'
    if isinstance(e, If):
        return f'({emit_expr(e.test)} != 1 /* !BOT */ ? {emit_expr(e.then_b)} : {emit_expr(e.else_b)})'
    if isinstance(e, App):
        if isinstance(e.fn, Var):
            return f'{c_ident(e.fn.name)}({emit_expr(e.arg)})'
        return f'({emit_expr(e.fn)})({emit_expr(e.arg)})'
    if isinstance(e, Let):
        # Let in expression context — caller handles the block
        raise ValueError("let in expression context — use emit_stmt")
    if isinstance(e, Lam):
        raise ValueError("lambda in expression context — should be lifted to defun")
    return str(e)

def emit_stmt(e, result_var, indent=1):
    """Emit C statements that compute e and store in result_var."""
    pad = '    ' * indent
    if isinstance(e, Let):
        val_name = c_ident(e.var)
        if isinstance(e.val, Let):
            # Nested let in value position
            emit_stmt(e.val, val_name, indent)
            lines = [f'{pad}/* {val_name} already set above */']
        else:
            lines = [f'{pad}uint8_t {val_name} = {emit_expr(e.val)};']
        body_lines = emit_stmt(e.body, result_var, indent)
        return lines + body_lines
    else:
        return [f'{pad}{result_var} = {emit_expr(e)};']

def has_let(e):
    """Check if expression contains a Let node (needs statement form)."""
    if isinstance(e, Let):
        return True
    if isinstance(e, Dot):
        return has_let(e.a) or has_let(e.b)
    if isinstance(e, If):
        return has_let(e.test) or has_let(e.then_b) or has_let(e.else_b)
    if isinstance(e, App):
        return has_let(e.fn) or has_let(e.arg)
    return False

# ═══════════════════════════════════════════════════════════════════════
# Top-level code generation
# ═══════════════════════════════════════════════════════════════════════

def generate(forms):
    """Generate complete C program from a list of IR forms."""
    lines = []
    lines.append('/* Generated by psi_transpile.py — Ψ∗ → C transpiler */')
    lines.append('/* Cayley table operations verified in Lean. */')
    lines.append('')
    lines.append('#include "psi_runtime.h"')
    lines.append('')

    defuns = []
    main_expr = None

    for form in forms:
        if isinstance(form, tuple) and form[0] == 'defun':
            defuns.append(form)
        elif isinstance(form, tuple) and form[0] == 'main':
            main_expr = form[1]
        # bare expression: treat as main
        elif main_expr is None:
            main_expr = form

    # Emit function definitions
    for _, name, param, body in defuns:
        cname = c_ident(name)
        cparam = c_ident(param)
        if has_let(body):
            lines.append(f'uint8_t {cname}(uint8_t {cparam}) {{')
            lines.append(f'    uint8_t _result;')
            stmts = emit_stmt(body, '_result')
            lines.extend(stmts)
            lines.append(f'    return _result;')
            lines.append(f'}}')
        else:
            lines.append(f'uint8_t {cname}(uint8_t {cparam}) {{')
            lines.append(f'    return {emit_expr(body)};')
            lines.append(f'}}')
        lines.append('')

    # Emit main
    lines.append('int main(int argc, char *argv[]) {')
    if main_expr is None:
        lines.append('    printf("No main expression.\\n");')
        lines.append('    return 0;')
    else:
        # Check if main uses 'input' variable
        if uses_var(main_expr, 'input'):
            lines.append('    if (argc < 2) {')
            lines.append('        fprintf(stderr, "Usage: %s <atom-index-0-15>\\n", argv[0]);')
            lines.append('        return 1;')
            lines.append('    }')
            lines.append('    uint8_t input = (uint8_t)atoi(argv[1]);')
            lines.append('')

        if has_let(main_expr):
            lines.append('    uint8_t result;')
            stmts = emit_stmt(main_expr, 'result')
            lines.extend(stmts)
        elif isinstance(main_expr, Atom):
            lines.append(f'    uint8_t result = {emit_expr(main_expr)};')
        else:
            lines.append(f'    uint8_t result = {emit_expr(main_expr)};')

        lines.append('    printf("%s (%u)\\n", psi_names[result], result);')
        lines.append('    return 0;')
    lines.append('}')
    return '\n'.join(lines) + '\n'

def uses_var(e, name):
    """Check if expression references a variable."""
    if isinstance(e, Var):
        return e.name == name
    if isinstance(e, Atom):
        return False
    if isinstance(e, Dot):
        return uses_var(e.a, name) or uses_var(e.b, name)
    if isinstance(e, If):
        return uses_var(e.test, name) or uses_var(e.then_b, name) or uses_var(e.else_b, name)
    if isinstance(e, Let):
        return uses_var(e.val, name) or (e.var != name and uses_var(e.body, name))
    if isinstance(e, Lam):
        return e.param != name and uses_var(e.body, name)
    if isinstance(e, App):
        return uses_var(e.fn, name) or uses_var(e.arg, name)
    return False

# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    if len(sys.argv) < 2:
        print("Usage: psi_transpile.py input.psi", file=sys.stderr)
        sys.exit(1)

    with open(sys.argv[1]) as f:
        source = f.read()

    forms = parse_file(source)
    print(generate(forms), end='')


if __name__ == '__main__':
    main()

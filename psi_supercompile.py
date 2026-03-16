#!/usr/bin/env python3
"""
Ψ∗ supercompiler — partial evaluator for Cayley table programs.

Reads a .psi source file containing expression trees with (dot ...), (if ...),
(let ...), (lam ...), (app ...) nodes. Applies fold-all: constant folding,
QE cancellation, dead branch elimination, let propagation, and beta reduction.
Outputs the optimized expression tree.

Usage:
  python3 psi_supercompile.py input.psi > output.psi
  python3 psi_supercompile.py input.psi   # prints to stdout
"""

import sys
import os

# Table selection: use Ψ₁₆ᶜ if PSI_TABLE=c or --table=c, else Ψ₁₆ᶠ
_table_mode = os.environ.get('PSI_TABLE', '')
if '--table=c' in sys.argv:
    _table_mode = 'c'
    sys.argv.remove('--table=c')

if _table_mode == 'c':
    from psi_star_c import TABLE
    INC_IDX, DEC_IDX, INV_IDX = 13, 15, 14
else:
    from psi_star import TABLE
    INC_IDX, DEC_IDX, INV_IDX = 13, 15, 14  # same indices, different table

# ═══════════════════════════════════════════════════════════════════════
# Named atom constants
# ═══════════════════════════════════════════════════════════════════════

ATOM_NAMES = {
    'TOP': 0, 'BOT': 1, 'f': 2, 'TAU': 3, 'g': 4, '5': 5,
    'Q': 6, 'E': 7, 'RHO': 8, 'ETA': 9, 'Y': 10, '11': 11,
    'SEQ': 12, 'INC': 13, 'INV': 14, 'DEC': 15,
    # Legacy aliases (Ψ₁₆ᶠ names still accepted)
    'PAIR': 11, 'GET': 14, 's0': 12,
    's1': 14, 's2': 6, 's3': 11, 's4': 10, 's5': 15, 's6': 8, 's7': 7,
}

ATOM_DISPLAY = {
    0: 'TOP', 1: 'BOT', 2: 'f', 3: 'TAU', 4: 'g', 5: '5',
    6: 'Q', 7: 'E', 8: 'RHO', 9: 'ETA', 10: 'Y', 11: '11',
    12: 'SEQ', 13: 'INC', 14: 'INV', 15: 'DEC',
}

# ═══════════════════════════════════════════════════════════════════════
# IR nodes
# ═══════════════════════════════════════════════════════════════════════

class Atom:
    __slots__ = ['idx']
    def __init__(self, idx): self.idx = idx
    def __eq__(self, o): return isinstance(o, Atom) and self.idx == o.idx
    def __repr__(self): return ATOM_DISPLAY.get(self.idx, str(self.idx))

class Var:
    __slots__ = ['name']
    def __init__(self, name): self.name = name
    def __eq__(self, o): return isinstance(o, Var) and self.name == o.name
    def __repr__(self): return self.name

class Dot:
    __slots__ = ['a', 'b']
    def __init__(self, a, b): self.a = a; self.b = b
    def __repr__(self): return f'(dot {self.a} {self.b})'

class If:
    __slots__ = ['test', 'then_b', 'else_b']
    def __init__(self, test, then_b, else_b):
        self.test = test; self.then_b = then_b; self.else_b = else_b
    def __repr__(self): return f'(if {self.test} {self.then_b} {self.else_b})'

class Let:
    __slots__ = ['var', 'val', 'body']
    def __init__(self, var, val, body):
        self.var = var; self.val = val; self.body = body
    def __repr__(self): return f'(let {self.var} {self.val} {self.body})'

class Lam:
    __slots__ = ['param', 'body']
    def __init__(self, param, body): self.param = param; self.body = body
    def __repr__(self): return f'(lam {self.param} {self.body})'

class App:
    __slots__ = ['fn', 'arg']
    def __init__(self, fn, arg): self.fn = fn; self.arg = arg
    def __repr__(self): return f'(app {self.fn} {self.arg})'

Expr = Atom | Var | Dot | If | Let | Lam | App

# ═══════════════════════════════════════════════════════════════════════
# Parser: S-expression → IR
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
        else:
            j = i
            while j < len(s) and s[j] not in ' \t\n\r();':
                j += 1
            tokens.append(s[i:j])
            i = j
    return tokens

def parse_tokens(tokens, pos):
    if pos >= len(tokens):
        raise SyntaxError("unexpected end of input")
    tok = tokens[pos]
    if tok == '(':
        pos += 1
        items = []
        while pos < len(tokens) and tokens[pos] != ')':
            item, pos = parse_tokens(tokens, pos)
            items.append(item)
        if pos >= len(tokens):
            raise SyntaxError("missing )")
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
    """Convert parsed S-expression to IR node."""
    if isinstance(form, str):
        # Named atom?
        if form in ATOM_NAMES:
            return Atom(ATOM_NAMES[form])
        # Integer atom?
        try:
            n = int(form)
            if 0 <= n <= 15:
                return Atom(n)
            return Var(form)  # large int used as variable (symbol ID)
        except ValueError:
            pass
        # Variable
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
            name, param, body = form[1], form[2], form[3]
            return ('defun', name, param, to_expr(body))
        if head == 'main' and len(form) == 2:
            return ('main', to_expr(form[1]))
        raise SyntaxError(f"unknown form: {form}")
    raise SyntaxError(f"bad expression: {form}")

def parse_file(source):
    tokens = tokenize(source)
    forms = parse_all_tokens(tokens)
    return [to_expr(f) for f in forms]

# ═══════════════════════════════════════════════════════════════════════
# Substitution
# ═══════════════════════════════════════════════════════════════════════

def subst(var, val, expr):
    if isinstance(expr, Var) and expr.name == var:
        return val
    if isinstance(expr, (Atom, Var)):
        return expr
    if isinstance(expr, Dot):
        return Dot(subst(var, val, expr.a), subst(var, val, expr.b))
    if isinstance(expr, If):
        return If(subst(var, val, expr.test),
                  subst(var, val, expr.then_b),
                  subst(var, val, expr.else_b))
    if isinstance(expr, Let):
        new_val = subst(var, val, expr.val)
        if expr.var == var:
            return Let(expr.var, new_val, expr.body)  # shadowed
        return Let(expr.var, new_val, subst(var, val, expr.body))
    if isinstance(expr, Lam):
        if expr.param == var:
            return expr  # shadowed
        return Lam(expr.param, subst(var, val, expr.body))
    if isinstance(expr, App):
        return App(subst(var, val, expr.fn), subst(var, val, expr.arg))
    return expr

# ═══════════════════════════════════════════════════════════════════════
# Supercompiler: fold-all
# ═══════════════════════════════════════════════════════════════════════

Q_IDX, E_IDX = 6, 7
CORE = frozenset({2, 3, 4, 5})

# Cancellation rules: (outer, inner, valid_set)
# valid_set = None means total (holds for all 16 elements).
# valid_set = frozenset means partial (only fire when x is a known Atom in the set).
#
# Verified exhaustively over all 16 elements of the Ψ₁₆ᶜ table:
#   INV·(INV·x)=x:   TOTAL  (16/16)
#   E·(Q·x)=x:       PARTIAL ({2,3,4,5,6,7,12,13,15} — 9/16)
#   Q·(E·x)=x:       PARTIAL ({2,3,4,5,6,10,11,13,15} — 9/16)
#   INC·(DEC·x)=x:   PARTIAL ({2,3,4,5,15} — 5/16)
#   DEC·(INC·x)=x:   PARTIAL ({2,3,4,5,14} — 5/16)
CANCEL_RULES = [
    (E_IDX, Q_IDX, frozenset({2,3,4,5,6,7,12,13,15})),   # E·(Q·x) → x
    (Q_IDX, E_IDX, frozenset({2,3,4,5,6,10,11,13,15})),   # Q·(E·x) → x
]
if _table_mode == 'c':
    CANCEL_RULES += [
        (INC_IDX, DEC_IDX, frozenset({2,3,4,5,15})),     # INC·(DEC·x) → x
        (DEC_IDX, INC_IDX, frozenset({2,3,4,5,14})),     # DEC·(INC·x) → x
        (INV_IDX, INV_IDX, None),                          # INV·(INV·x) → x  (TOTAL)
    ]

# Build lookup: outer_idx → [(inner_idx, valid_set), ...]
_CANCEL_MAP = {}
for _o, _i, _valid in CANCEL_RULES:
    _CANCEL_MAP.setdefault(_o, []).append((_i, _valid))


def _can_cancel(outer_idx, inner_idx, x_expr):
    """Check if the cancellation outer·(inner·x) → x is sound for the given x."""
    entries = _CANCEL_MAP.get(outer_idx, [])
    for (inner, valid_set) in entries:
        if inner != inner_idx:
            continue
        if valid_set is None:
            return True  # total rule — always safe
        # Partial rule: only safe if x is a known Atom in the valid set
        if isinstance(x_expr, Atom) and x_expr.idx in valid_set:
            return True
        # x is a variable or non-valid atom — cannot fire
        return False
    return False


def is_value(e):
    """True if e is a fully reduced value (propagatable through let)."""
    return isinstance(e, (Atom, Lam))

def fold_all(e):
    if isinstance(e, (Atom, Var)):
        return e

    if isinstance(e, Dot):
        a = fold_all(e.a)
        b_raw = e.b
        # Cancellation on raw b (pre-fold): outer·(inner·x) → x
        # Only fires if _can_cancel verifies x is in the valid set.
        if isinstance(a, Atom) and isinstance(b_raw, Dot):
            b_head = b_raw.a if isinstance(b_raw.a, Atom) else None
            if b_head and _can_cancel(a.idx, b_head.idx, b_raw.b):
                return fold_all(b_raw.b)
        b = fold_all(b_raw)
        # Table lookup
        if isinstance(a, Atom) and isinstance(b, Atom):
            return Atom(TABLE[a.idx][b.idx])
        # Post-fold cancellation
        if isinstance(a, Atom) and isinstance(b, Dot) and isinstance(b.a, Atom):
            if _can_cancel(a.idx, b.a.idx, b.b):
                return b.b
        return Dot(a, b)

    if isinstance(e, If):
        test = fold_all(e.test)
        if isinstance(test, Atom):
            if test.idx == 1:  # BOT = falsy
                return fold_all(e.else_b)
            return fold_all(e.then_b)
        return If(test, fold_all(e.then_b), fold_all(e.else_b))

    if isinstance(e, Let):
        val = fold_all(e.val)
        if is_value(val):
            return fold_all(subst(e.var, val, e.body))
        return Let(e.var, val, fold_all(e.body))

    if isinstance(e, Lam):
        return Lam(e.param, fold_all(e.body))

    if isinstance(e, App):
        fn = fold_all(e.fn)
        arg = fold_all(e.arg)
        if isinstance(fn, Lam) and is_value(arg):
            return fold_all(subst(fn.param, arg, fn.body))
        return App(fn, arg)

    return e

# ═══════════════════════════════════════════════════════════════════════
# Serializer: IR → S-expression text
# ═══════════════════════════════════════════════════════════════════════

def serialize(e):
    if isinstance(e, Atom):
        return ATOM_DISPLAY.get(e.idx, str(e.idx))
    if isinstance(e, Var):
        return e.name
    if isinstance(e, Dot):
        return f'(dot {serialize(e.a)} {serialize(e.b)})'
    if isinstance(e, If):
        return f'(if {serialize(e.test)} {serialize(e.then_b)} {serialize(e.else_b)})'
    if isinstance(e, Let):
        return f'(let {e.var} {serialize(e.val)} {serialize(e.body)})'
    if isinstance(e, Lam):
        return f'(lam {e.param} {serialize(e.body)})'
    if isinstance(e, App):
        return f'(app {serialize(e.fn)} {serialize(e.arg)})'
    return str(e)

# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    if len(sys.argv) < 2:
        print("Usage: psi_supercompile.py input.psi", file=sys.stderr)
        sys.exit(1)

    with open(sys.argv[1]) as f:
        source = f.read()

    forms = parse_file(source)

    for form in forms:
        if isinstance(form, tuple) and form[0] == 'defun':
            _, name, param, body = form
            optimized = fold_all(body)
            print(f'(defun {name} {param} {serialize(optimized)})')
        elif isinstance(form, tuple) and form[0] == 'main':
            optimized = fold_all(form[1])
            print(f'(main {serialize(optimized)})')
        else:
            optimized = fold_all(form)
            print(serialize(optimized))


if __name__ == '__main__':
    main()

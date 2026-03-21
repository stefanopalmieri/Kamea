#!/usr/bin/env python3
"""
Ψ-Lisp → Ψ∗ transpiler.

Parses a McCarthy 1960-style Lisp subset, translates to Ψ∗ terms, evaluates
via psi_star.py. The 7 axiom-forced elements correspond exactly to McCarthy's
original primitives: ⊤=T, Q=QUOTE, E=EVAL, g=CONS, f=CAR, η=CDR, ρ=COND.

Architecture mirrors the 2CM proof: Python is the machine (control flow,
dispatch, recursion), the algebra is the instruction set (data construction/
destruction via psi_eval).

Encoding conventions:
  NIL   = ⊥                          empty list, false, bottom (the only falsy value)
  T     = ⊤                          true, top, ground
  0     = App(Q, ⊤)                  one Q layer around ⊤
  n     = (n+1) Q layers around ⊤    numbers are Q-chains rooted at ⊤
  Lists are g-pairs terminating at ⊥ (NIL).

Usage:
  python3 psi_lisp.py                           # REPL
  python3 psi_lisp.py file.lisp                 # run file
  python3 psi_lisp.py --show-term file.lisp     # show Ψ∗ terms
  python3 psi_lisp.py --trace file.lisp         # trace evaluation
"""

from __future__ import annotations

import sys
import os
from dataclasses import dataclass, field
from typing import Any

# Table selection: use Ψ₁₆ᶜ if PSI_TABLE=c or --table=c, else Ψ₁₆ᶠ
_table_mode = os.environ.get('PSI_TABLE', '')
if '--table=c' in sys.argv:
    _table_mode = 'c'
    sys.argv.remove('--table=c')

if _table_mode == 'c':
    from psi_star_c import (
        App, Term, psi_eval, EvalError,
        TOP, BOT, Q, E, F_ENC, G_ENC, ETA, RHO, Y_COMB, TAU,
        pair, fst, snd, term_str, NAMES, TABLE,
    )
else:
    from psi_star import (
        App, Term, psi_eval, EvalError,
        TOP, BOT, Q, E, F_ENC, G_ENC, ETA, RHO, Y_COMB, TAU,
        pair, fst, snd, term_str, NAMES, TABLE,
    )

# ═══════════════════════════════════════════════════════════════════════
# Lisp constants mapped to Ψ∗ atoms
# ═══════════════════════════════════════════════════════════════════════

LISP_NIL = BOT   # ⊥ — empty list, false, the only falsy value
LISP_T   = TOP   # ⊤ — true, ground

# Sentinel for REPL output suppression (not a Ψ∗ term — never escapes into user code)
_VOID = object()

# ═══════════════════════════════════════════════════════════════════════
# Integer encoding: Q-chains rooted at ⊤
# ═══════════════════════════════════════════════════════════════════════

def encode_int(n: int) -> Term:
    """Encode integer n as Q layers around ⊤.

    Normal mode: (n+1) layers. 0 = App(Q, ⊤). Numbers and NIL distinct.
    Algebraic mode: n layers. 0 = ⊤. The term algebra's native encoding.
    """
    t: Term = TOP
    for _ in range(n + (0 if ALGEBRAIC else 1)):
        t = App(Q, t)
    return t


def decode_int(t: Term) -> int | None:
    """Decode a Ψ∗ term as an integer. None if not a number.

    Normal mode: counts Q layers, requires ≥ 1, returns count - 1.
    Algebraic mode: counts Q layers, 0 = ⊤ (zero layers), returns count.
    """
    count = 0
    while isinstance(t, App) and t.fun == Q:
        count += 1
        t = t.arg
    if ALGEBRAIC:
        return count if t == TOP else None
    else:
        return count - 1 if t == TOP and count >= 1 else None


# ═══════════════════════════════════════════════════════════════════════
# List utilities (lists terminate at ⊥ = NIL)
# ═══════════════════════════════════════════════════════════════════════

def lisp_cons(a: Term, b: Term) -> Term:
    """CONS — build a pair. Lists terminate at NIL (⊥)."""
    return pair(a, b)


def is_pair_term(t: Term) -> bool:
    """Check if t is a curried pair App(App(g, a), b)."""
    return isinstance(t, App) and isinstance(t.fun, App) and t.fun.fun == G_ENC


def list_elements(t: Term) -> list[Term]:
    """Extract elements from a proper list (NIL-terminated pair chain)."""
    elems: list[Term] = []
    while is_pair_term(t):
        elems.append(t.fun.arg)  # car
        t = t.arg                # cdr
    return elems


def is_proper_list(t: Term) -> bool:
    """Check if t is a NIL-terminated list (terminates at ⊥)."""
    while is_pair_term(t):
        t = t.arg
    return t == BOT


# ═══════════════════════════════════════════════════════════════════════
# S-Expression types + Parser
# ═══════════════════════════════════════════════════════════════════════

SExpr = Any  # str | int | list[SExpr]


def tokenize(source: str) -> list[str]:
    """Tokenize Lisp source into parens, atoms, integers."""
    tokens: list[str] = []
    i = 0
    while i < len(source):
        c = source[i]
        if c in " \t\n\r":
            i += 1
        elif c == ";":
            while i < len(source) and source[i] != "\n":
                i += 1
        elif c in "()":
            tokens.append(c)
            i += 1
        elif c == "'":
            tokens.append("'")
            i += 1
        elif c == '"':
            j = i + 1
            while j < len(source) and source[j] != '"':
                j += 1
            tokens.append(source[i : j + 1])
            i = j + 1
        else:
            j = i
            while j < len(source) and source[j] not in " \t\n\r();":
                j += 1
            tokens.append(source[i:j])
            i = j
    return tokens


def parse(tokens: list[str], pos: int = 0) -> tuple[SExpr, int]:
    """Parse tokens into an S-expression."""
    if pos >= len(tokens):
        raise SyntaxError("unexpected end of input")

    tok = tokens[pos]

    if tok == "'":
        expr, pos = parse(tokens, pos + 1)
        return ["quote", expr], pos

    if tok == "(":
        pos += 1
        items: list[SExpr] = []
        while pos < len(tokens) and tokens[pos] != ")":
            expr, pos = parse(tokens, pos)
            items.append(expr)
        if pos >= len(tokens):
            raise SyntaxError("missing closing )")
        return items, pos + 1

    if tok == ")":
        raise SyntaxError("unexpected )")

    try:
        return int(tok), pos + 1
    except ValueError:
        return tok, pos + 1


def parse_all(source: str) -> list[SExpr]:
    """Parse all top-level expressions from source."""
    tokens = tokenize(source)
    exprs: list[SExpr] = []
    pos = 0
    while pos < len(tokens):
        expr, pos = parse(tokens, pos)
        exprs.append(expr)
    return exprs


def sexpr_str(s: SExpr) -> str:
    """Pretty-print an S-expression."""
    if isinstance(s, list):
        return "(" + " ".join(sexpr_str(x) for x in s) + ")"
    return str(s)


# ═══════════════════════════════════════════════════════════════════════
# Function representation
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class Function:
    params: list[str]
    body: SExpr
    env: dict = field(default_factory=dict)
    name: str | None = None


# ═══════════════════════════════════════════════════════════════════════
# Display: Ψ∗ Term → Lisp-readable string
# ═══════════════════════════════════════════════════════════════════════

def _algebraic_int_display(n: int) -> str:
    """Format a number in algebraic mode: Q·(Q·(⊤)) [= 2]."""
    if n == 0:
        return "⊤ [= 0]"
    s = "⊤"
    for i in range(n):
        s = f"Q·{s}" if i == 0 else f"Q·({s})"
    return f"{s} [= {n}]"


def display(t: Term) -> str:
    """Convert Ψ∗ term to Lisp-readable string.

    Three distinct base values:
      ⊥ (BOT)  → NIL
      ⊤ (TOP)  → T (normal) or ⊤ [= 0] (algebraic)
      Q-chain rooted at ⊤ → integer
    """
    if t == BOT:
        return "NIL"
    if not ALGEBRAIC and t == TOP:
        return "T"
    # Check for integer (Q-chain rooted at ⊤) — before list check
    n = decode_int(t)
    if n is not None:
        if ALGEBRAIC:
            return _algebraic_int_display(n)
        return str(n)
    # Check for list (g-pairs terminating at ⊥)
    if is_proper_list(t) and is_pair_term(t):
        return "(" + " ".join(display(e) for e in list_elements(t)) + ")"
    if is_pair_term(t):
        return f"({display(fst(t))} . {display(snd(t))})"
    if isinstance(t, int):
        return NAMES.get(t, str(t))
    return term_str(t)


# ═══════════════════════════════════════════════════════════════════════
# Evaluator
# ═══════════════════════════════════════════════════════════════════════

SHOW_TERM = False
TRACE = False
ALGEBRAIC = False


def eval_term(t: Term) -> Term:
    """psi_eval with optional --show-term output."""
    if SHOW_TERM:
        print(f"  psi_eval: {term_str(t)}")
    result = psi_eval(t)
    if SHOW_TERM:
        print(f"       → {term_str(result)}")
    return result


def translate_datum(s: SExpr) -> Term:
    """Translate a datum (unevaluated) to a Ψ∗ term."""
    if isinstance(s, int):
        return encode_int(s)
    if isinstance(s, str):
        up = s.upper()
        if up == "NIL":
            return BOT
        if up == "T":
            return TOP
        return _symbol_to_term(s)
    if isinstance(s, list):
        if len(s) == 0:
            return BOT  # () = NIL
        result: Term = BOT
        for item in reversed(s):
            result = lisp_cons(translate_datum(item), result)
        return result
    return BOT


_symbol_table: dict[str, int] = {}
_next_symbol_id = [100]


def _symbol_to_term(name: str) -> Term:
    """Encode a symbol as a unique integer."""
    if name not in _symbol_table:
        _symbol_table[name] = _next_symbol_id[0]
        _next_symbol_id[0] += 1
    return encode_int(_symbol_table[name])


def evaluate(sexpr: SExpr, env: dict) -> Term:
    """Evaluate an S-expression in the given environment.

    Python is the machine: control flow, function application, recursion.
    psi_eval is the algebra: cons, car, cdr, quote, successor, predecessor.
    """
    if TRACE:
        print(f"  evaluate: {sexpr_str(sexpr)}")

    # ── Atoms ──
    if isinstance(sexpr, int):
        return encode_int(sexpr)

    if isinstance(sexpr, str):
        # String literals → list of ASCII codes (Q-chain integers)
        if sexpr.startswith('"') and sexpr.endswith('"'):
            chars = sexpr[1:-1]
            # Handle escape sequences
            chars = chars.replace("\\n", "\n").replace("\\t", "\t").replace("\\\\", "\\")
            result: Term = BOT  # NIL
            for c in reversed(chars):
                result = lisp_cons(encode_int(ord(c)), result)
            return result
        # Check env first — user bindings shadow keywords
        if sexpr in env:
            val = env[sexpr]
            if isinstance(val, Term) or isinstance(val, int):
                return val
            return val  # Function object
        # Keywords (only if not bound in env)
        up = sexpr.upper()
        if up == "NIL":
            return BOT
        if up == "T":
            return TOP
        raise NameError(f"unbound variable: {sexpr}")

    # ── Compound forms ──
    if not isinstance(sexpr, list) or len(sexpr) == 0:
        return BOT  # () = NIL

    head = sexpr[0]

    # (quote x)
    if head == "quote":
        if len(sexpr) != 2:
            raise SyntaxError("quote takes exactly 1 argument")
        return translate_datum(sexpr[1])

    # (if test then else)
    if head == "if":
        if len(sexpr) < 3:
            raise SyntaxError("if requires at least test and then-branch")
        cond_val = evaluate(sexpr[1], env)
        # NIL (⊥) is the ONLY falsy value
        if cond_val == BOT:
            if len(sexpr) >= 4:
                return evaluate(sexpr[3], env)
            return BOT  # no else branch → NIL
        return evaluate(sexpr[2], env)

    # (cond (test1 val1) (test2 val2) ... (T default))
    if head == "cond":
        for clause in sexpr[1:]:
            if not isinstance(clause, list) or len(clause) < 2:
                raise SyntaxError("bad cond clause")
            cond_val = evaluate(clause[0], env)
            if cond_val != BOT:
                return evaluate(clause[1], env)
        return BOT

    # (defun name (args) body)
    if head == "defun":
        if len(sexpr) < 4:
            raise SyntaxError("defun requires name, arg list, and body")
        name = sexpr[1]
        params = sexpr[2]
        body = sexpr[3] if len(sexpr) == 4 else ["progn"] + sexpr[3:]
        fn = Function(params=params, body=body, env=env, name=name)
        env[name] = fn
        return _VOID

    # (setq name expr)
    if head == "setq":
        if len(sexpr) != 3:
            raise SyntaxError("setq requires name and expression")
        name = sexpr[1]
        val = evaluate(sexpr[2], env)
        env[name] = val
        return _VOID

    # Keep (define ...) as alternative syntax
    if head == "define":
        if isinstance(sexpr[1], list):
            name = sexpr[1][0]
            params = sexpr[1][1:]
            body = sexpr[2] if len(sexpr) == 3 else ["progn"] + sexpr[2:]
            fn = Function(params=params, body=body, env=dict(env), name=name)
            env[name] = fn
            fn.env[name] = fn
            return _VOID
        else:
            name = sexpr[1]
            val = evaluate(sexpr[2], env)
            env[name] = val
            return _VOID

    # (let ((x v) ...) body)
    if head == "let":
        bindings = sexpr[1]
        body = sexpr[2] if len(sexpr) == 3 else ["progn"] + sexpr[2:]
        new_env = dict(env)
        for binding in bindings:
            new_env[binding[0]] = evaluate(binding[1], env)
        return evaluate(body, new_env)

    # (progn expr ...) / (begin expr ...)
    if head in ("progn", "begin"):
        result: Term = BOT
        for expr in sexpr[1:]:
            result = evaluate(expr, env)
        return result

    # (lambda (params) body)
    if head == "lambda":
        params = sexpr[1]
        body = sexpr[2] if len(sexpr) == 3 else ["progn"] + sexpr[2:]
        return Function(params=params, body=body, env=dict(env))

    # (and a b ...)
    if head == "and":
        result = TOP
        for expr in sexpr[1:]:
            result = evaluate(expr, env)
            if result == BOT:
                return BOT
        return result

    # (or a b ...)
    if head == "or":
        for expr in sexpr[1:]:
            result = evaluate(expr, env)
            if result != BOT:
                return result
        return BOT

    # (not x)
    if head == "not":
        if len(sexpr) != 2:
            raise SyntaxError("not takes exactly 1 argument")
        val = evaluate(sexpr[1], env)
        return TOP if val == BOT else BOT

    # (env-size) — return number of bindings in current environment
    if head == "env-size":
        return encode_int(len(env))

    # (env-keys) — return list of binding names as char-code strings
    if head == "env-keys":
        result: Term = BOT
        for name in reversed(sorted(env.keys())):
            name_term: Term = BOT
            for c in reversed(name):
                name_term = lisp_cons(encode_int(ord(c)), name_term)
            result = lisp_cons(name_term, result)
        return result

    # (bound? "name") — check if a name is bound
    if head == "bound?":
        if len(sexpr) != 2:
            raise SyntaxError("bound? takes exactly 1 argument")
        name = sexpr[1]
        if isinstance(name, str) and not name.startswith('"'):
            return TOP if name in env else BOT
        return BOT

    # ── Application: (fn args...) ──
    fn = evaluate(head, env)
    args = [evaluate(a, env) for a in sexpr[1:]]

    return apply_fn(fn, args, env)


def apply_fn(fn: Any, args: list, env: dict) -> Term:
    """Apply a function to arguments."""
    if callable(fn):
        return fn(*args)

    if isinstance(fn, Function):
        if len(args) != len(fn.params):
            raise TypeError(
                f"expected {len(fn.params)} args, got {len(args)}"
            )
        call_env = dict(fn.env)
        for p, a in zip(fn.params, args):
            call_env[p] = a
        return evaluate(fn.body, call_env)

    raise TypeError(f"not callable: {display(fn) if isinstance(fn, (int, App)) else fn}")


# ═══════════════════════════════════════════════════════════════════════
# Built-in environment
# ═══════════════════════════════════════════════════════════════════════

def _builtin_add(a, b):
    na, nb = decode_int(a), decode_int(b)
    if na is None or nb is None:
        raise TypeError(f"+ requires numbers, got {display(a)} and {display(b)}")
    return encode_int(na + nb)


def _builtin_sub(a, b):
    na, nb = decode_int(a), decode_int(b)
    if na is None or nb is None:
        raise TypeError(f"- requires numbers, got {display(a)} and {display(b)}")
    return encode_int(max(0, na - nb))


def _builtin_mul(a, b):
    na, nb = decode_int(a), decode_int(b)
    if na is None or nb is None:
        raise TypeError(f"* requires numbers, got {display(a)} and {display(b)}")
    return encode_int(na * nb)


def _builtin_lt(a, b):
    na, nb = decode_int(a), decode_int(b)
    if na is None or nb is None:
        raise TypeError("< requires numbers")
    return TOP if na < nb else BOT


def _builtin_gt(a, b):
    na, nb = decode_int(a), decode_int(b)
    if na is None or nb is None:
        raise TypeError("> requires numbers")
    return TOP if na > nb else BOT


def _builtin_le(a, b):
    na, nb = decode_int(a), decode_int(b)
    if na is None or nb is None:
        raise TypeError("<= requires numbers")
    return TOP if na <= nb else BOT


def _builtin_ge(a, b):
    na, nb = decode_int(a), decode_int(b)
    if na is None or nb is None:
        raise TypeError(">= requires numbers")
    return TOP if na >= nb else BOT


def _builtin_eq(a, b):
    return TOP if a == b else BOT


def _builtin_cons(a, b):
    return lisp_cons(a, b)


def _builtin_car(a):
    # Direct structural extraction for pairs (avoids psi_eval traversal,
    # which allows non-Term values like Function objects in cons cells —
    # needed for CPS meta-circular evaluator's reified continuations).
    f = fst(a)
    if f is not None:
        return f
    return eval_term(App(F_ENC, a))


def _builtin_cdr(a):
    # Direct structural extraction (see _builtin_car comment).
    s = snd(a)
    if s is not None:
        return s
    return eval_term(App(ETA, a))


def _builtin_null(a):
    """NULL — T if a is NIL (⊥), else NIL."""
    return TOP if a == BOT else BOT


def _builtin_zerop(a):
    """ZEROP — T if a is 0.

    Normal: 0 = App(Q, ⊤). Algebraic: 0 = ⊤.
    """
    return TOP if a == encode_int(0) else BOT


def _builtin_atom(a):
    """ATOM — T if a is an atom (not a cons pair), else NIL."""
    return TOP if isinstance(a, int) else BOT


def _builtin_numberp(a):
    return TOP if decode_int(a) is not None else BOT


def _builtin_display(a):
    sys.stdout.write(display(a))
    sys.stdout.flush()
    return _VOID


def _builtin_print(a):
    print(display(a))
    return _VOID


def _builtin_terpri():
    print()
    return _VOID


def _builtin_list(*args):
    result: Term = BOT  # NIL
    for a in reversed(args):
        result = lisp_cons(a, result)
    return result


def _builtin_equal(a, b):
    return TOP if a == b else BOT


def _builtin_mod(a, b):
    na, nb = decode_int(a), decode_int(b)
    if na is None or nb is None or nb == 0:
        raise TypeError("mod requires positive numbers")
    return encode_int(na % nb)


def _builtin_div(a, b):
    na, nb = decode_int(a), decode_int(b)
    if na is None or nb is None or nb == 0:
        raise TypeError("/ requires positive numbers")
    return encode_int(na // nb)


def _builtin_1plus(a):
    na = decode_int(a)
    if na is None:
        raise TypeError("1+ requires a number")
    return encode_int(na + 1)


def _builtin_1minus(a):
    na = decode_int(a)
    if na is None:
        raise TypeError("1- requires a number")
    return encode_int(max(0, na - 1))


def _builtin_write_char(a):
    """Write a single character by ASCII code. Machine-level IO."""
    na = decode_int(a)
    if na is None:
        raise TypeError("write-char requires an integer (ASCII code)")
    sys.stdout.write(chr(na))
    sys.stdout.flush()
    return _VOID


def _builtin_dot(a, b):
    """Raw Cayley table lookup: dot(a, b) = TABLE[a][b]."""
    na, nb = decode_int(a), decode_int(b)
    if na is None or nb is None:
        raise TypeError("dot requires integers (atom indices 0-15)")
    if not (0 <= na <= 15 and 0 <= nb <= 15):
        raise TypeError(f"dot: indices must be 0-15, got {na} and {nb}")
    return encode_int(TABLE[na][nb])


def _builtin_atom_name(a):
    """Return the symbolic name of atom a (by index) as a char-code list."""
    na = decode_int(a)
    if na is None or not (0 <= na <= 15):
        raise TypeError(f"atom-name requires index 0-15, got {display(a)}")
    name = NAMES.get(na, str(na))
    result: Term = BOT
    for c in reversed(name):
        result = lisp_cons(encode_int(ord(c)), result)
    return result


def _builtin_write_string(a):
    """Write a list of ASCII codes as characters. Machine-level IO."""
    while is_pair_term(a):
        ch = fst(a)
        n = decode_int(ch)
        if n is not None:
            sys.stdout.write(chr(n))
        a = snd(a)
    sys.stdout.flush()
    return _VOID


def builtin_env() -> dict:
    """Create the initial environment with built-in operations."""
    return {
        "+": _builtin_add,
        "-": _builtin_sub,
        "*": _builtin_mul,
        "<": _builtin_lt,
        ">": _builtin_gt,
        "<=": _builtin_le,
        ">=": _builtin_ge,
        "=": _builtin_eq,
        "eq": _builtin_eq,
        "equal": _builtin_equal,
        "cons": _builtin_cons,
        "car": _builtin_car,
        "cdr": _builtin_cdr,
        "null": _builtin_null,
        "zerop": _builtin_zerop,
        "atom": _builtin_atom,
        "numberp": _builtin_numberp,
        "display": _builtin_display,
        "print": _builtin_print,
        "terpri": _builtin_terpri,
        "list": _builtin_list,
        "mod": _builtin_mod,
        "/": _builtin_div,
        "1+": _builtin_1plus,
        "1-": _builtin_1minus,
        "write-char": _builtin_write_char,
        "write-string": _builtin_write_string,
        "dot": _builtin_dot,
        "atom-name": _builtin_atom_name,
    }


# ═══════════════════════════════════════════════════════════════════════
# Run + REPL
# ═══════════════════════════════════════════════════════════════════════

def run(source: str, env: dict | None = None) -> list:
    """Parse and evaluate all expressions in source."""
    if env is None:
        env = builtin_env()
    exprs = parse_all(source)
    results = []
    for expr in exprs:
        result = evaluate(expr, env)
        results.append(result)
    return results


def run_file(path: str, env: dict | None = None) -> list:
    """Run a Lisp file."""
    with open(path) as f:
        source = f.read()
    if env is None:
        env = builtin_env()
    return run(source, env)


def repl():
    """Interactive REPL."""
    env = builtin_env()
    if ALGEBRAIC:
        print("Ψ-Lisp [algebraic mode] — type expressions, Ctrl-D to exit")
        print("  0 = ⊤, n = n Q layers around ⊤. NIL = ⊥ (only falsy value).")
    else:
        print("Ψ-Lisp — type expressions, Ctrl-D to exit")
        print("  T = ⊤ (true), NIL = ⊥ (false/empty list)")
        print("  Integers = Q-chains rooted at ⊤. Only NIL is falsy.")
    print()

    while True:
        try:
            line = input("ψ> ")
        except (EOFError, KeyboardInterrupt):
            print()
            break

        line = line.strip()
        if not line:
            continue

        while line.count("(") > line.count(")"):
            try:
                line += " " + input(".. ")
            except (EOFError, KeyboardInterrupt):
                print()
                break

        try:
            results = run(line, env)
            for r in results:
                if r is not _VOID:
                    print(display(r))
        except Exception as e:
            print(f"error: {e}")


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    global SHOW_TERM, TRACE, ALGEBRAIC

    # CPS meta-circular evaluator needs deep recursion
    sys.setrecursionlimit(50000)

    args = sys.argv[1:]
    files = []

    for a in args:
        if a == "--show-term":
            SHOW_TERM = True
        elif a == "--trace":
            TRACE = True
        elif a == "--algebraic":
            ALGEBRAIC = True
        elif a.startswith("-"):
            print(f"unknown flag: {a}", file=sys.stderr)
            sys.exit(1)
        else:
            files.append(a)

    if not files:
        repl()
        return

    env = builtin_env()
    for path in files:
        if len(files) == 1:
            print(f"── {path} ──")
        try:
            results = run_file(path, env)
            for r in results:
                if r is not _VOID:
                    print(display(r))
        except Exception as e:
            print(f"error: {e}")
            sys.exit(1)
        print()


if __name__ == "__main__":
    main()

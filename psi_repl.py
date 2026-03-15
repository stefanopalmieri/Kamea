#!/usr/bin/env python3
"""
Ψ₁₆ᶠ / Ψ∗ REPL

An interpreter for the Ψ₁₆ᶠ atom algebra and Ψ∗ term algebra
with EDN-like syntax and a Lark PEG parser.

Usage:
  python psi_repl.py              # interactive REPL
  python psi_repl.py -e '(:E :top)'  # evaluate expression

Syntax:
  :top :bot :Q :E ...             atom keywords
  42                               natural number literal
  ' expr                           quote (suppress eval)
  ( expr* )                        application / special form
  name                             variable reference

Special forms:
  (def name val)                   bind in ENV
  (do e1 e2 ...)                   sequence, return last
  (print e1 ...)                   print formatted values
  (table)                          print colored 16×16 Cayley table
  (dot a b)                        raw atom table lookup
  (nat n)                          build nat(n)
  (pair a b)                       build pair
  (fst e) (snd e)                  projections
  (succ e)                         App(Q, val) (lazy)
  (pred e)                         eval App(E, val)
  (to-nat e)                       decode natural to int
  (f x) or (f x y ...)             left-fold application via psi_eval
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import Any, Union

from lark import Lark, Transformer, Tree

from psi_star import (
    App,
    psi_eval,
    dot,
    TABLE,
    NAMES,
    nat,
    to_nat,
    pair,
    fst,
    snd,
    term_str,
    TOP,
    BOT,
    Q,
    E,
    F_ENC,
    G_ENC,
    TAU,
    RHO,
    ETA,
    Y_COMB,
    Term,
)

# ============================================================
# Keyword → atom mapping
# ============================================================

KEYWORD_MAP = {
    "top": TOP, "bot": BOT, "f": F_ENC, "tau": TAU,
    "g": G_ENC, "seq": 5, "Q": Q, "E": E,
    "rho": RHO, "eta": ETA, "Y": Y_COMB, "PAIR": 11,
    "s0": 12, "inc": 13, "s1": 14, "dec": 15,
}

# ============================================================
# PEG Grammar
# ============================================================

GRAMMAR = r"""
    start: expr+

    ?expr: keyword
         | number
         | string
         | quoted
         | list
         | atom

    keyword: /:[a-zA-Z_]\w*/
    number: /\d+/
    string: ESCAPED_STRING
    atom: /[a-zA-Z_][\w\-]*/
    quoted: "'" expr
    list: "(" expr* ")"

    %import common.ESCAPED_STRING
    COMMENT: /;[^\n]*/
    %ignore COMMENT
    %ignore /\s+/
"""

parser = Lark(GRAMMAR, parser="earley", ambiguity="resolve")

# ============================================================
# AST nodes
# ============================================================

@dataclass(frozen=True)
class Keyword:
    name: str
    def __repr__(self): return f":{self.name}"

@dataclass(frozen=True)
class Symbol:
    name: str
    def __repr__(self): return self.name

@dataclass(frozen=True)
class Quoted:
    expr: Any
    def __repr__(self): return f"'{format_val(self.expr)}"

@dataclass(frozen=True)
class Number:
    value: int
    def __repr__(self): return str(self.value)

@dataclass(frozen=True)
class StringLit:
    value: str
    def __repr__(self): return f'"{self.value}"'

# ============================================================
# Lark tree → AST
# ============================================================

class ASTBuilder(Transformer):
    def keyword(self, items):
        name = str(items[0]).lstrip(":")
        return Keyword(name)

    def number(self, items):
        return Number(int(str(items[0])))

    def string(self, items):
        s = str(items[0])
        # Strip surrounding quotes
        if s.startswith('"') and s.endswith('"'):
            s = s[1:-1]
        # Unescape basic sequences
        s = s.replace("\\n", "\n").replace("\\t", "\t").replace('\\"', '"').replace("\\\\", "\\")
        return StringLit(s)

    def atom(self, items):
        return Symbol(str(items[0]))

    def quoted(self, items):
        return Quoted(items[0])

    def list(self, items):
        return list(items)

    def start(self, items):
        return items

ast_builder = ASTBuilder()

def parse(text: str) -> list:
    tree = parser.parse(text)
    return ast_builder.transform(tree)

# ============================================================
# Environment
# ============================================================

ENV: dict[str, Any] = {}

# ============================================================
# Eval
# ============================================================

def psi_repl_eval(expr, env: dict | None = None) -> Any:
    """Evaluate a parsed AST expression."""
    if env is None:
        env = ENV

    # Keyword → atom
    if isinstance(expr, Keyword):
        if expr.name in KEYWORD_MAP:
            return KEYWORD_MAP[expr.name]
        raise ValueError(f"Unknown keyword :{expr.name}")

    # Number literal → nat
    if isinstance(expr, Number):
        return nat(expr.value)

    # String literal → passthrough
    if isinstance(expr, StringLit):
        return expr.value

    # Quoted → don't eval
    if isinstance(expr, Quoted):
        return _quote_to_term(expr.expr)

    # Symbol → env lookup
    if isinstance(expr, Symbol):
        if expr.name in env:
            return env[expr.name]
        raise ValueError(f"Unbound variable: {expr.name}")

    # List → special form or application
    if isinstance(expr, list):
        if not expr:
            return TOP  # () → ⊤

        head = expr[0]

        # Special forms (head is a Symbol)
        if isinstance(head, Symbol):
            name = head.name

            if name == "def" and len(expr) == 3:
                var = expr[1]
                if not isinstance(var, Symbol):
                    raise ValueError(f"def requires a symbol name, got {var}")
                val = psi_repl_eval(expr[2], env)
                env[var.name] = val
                return val

            if name == "do":
                result = TOP
                for e in expr[1:]:
                    result = psi_repl_eval(e, env)
                return result

            if name == "print":
                parts = []
                for e in expr[1:]:
                    val = psi_repl_eval(e, env)
                    parts.append(format_val(val))
                print(" ".join(parts))
                return TOP

            if name == "table":
                _print_table()
                return TOP

            if name == "dot" and len(expr) == 3:
                a = psi_repl_eval(expr[1], env)
                b = psi_repl_eval(expr[2], env)
                if not isinstance(a, int) or not isinstance(b, int):
                    raise ValueError(f"dot requires atoms, got {format_val(a)}, {format_val(b)}")
                return dot(a, b)

            if name == "nat" and len(expr) == 2:
                n = psi_repl_eval(expr[1], env)
                if isinstance(n, Number):
                    return nat(n.value)
                if isinstance(n, int):
                    # Could be an atom used as a number
                    return nat(n)
                nn = to_nat(n)
                if nn is not None:
                    return nat(nn)
                raise ValueError(f"nat requires a number, got {format_val(n)}")

            if name == "pair" and len(expr) == 3:
                a = psi_repl_eval(expr[1], env)
                b = psi_repl_eval(expr[2], env)
                return pair(a, b)

            if name == "fst" and len(expr) == 2:
                val = psi_repl_eval(expr[1], env)
                return psi_eval(App(F_ENC, val))

            if name == "snd" and len(expr) == 2:
                val = psi_repl_eval(expr[1], env)
                return psi_eval(App(ETA, val))

            if name == "succ" and len(expr) == 2:
                val = psi_repl_eval(expr[1], env)
                return App(Q, val)

            if name == "pred" and len(expr) == 2:
                val = psi_repl_eval(expr[1], env)
                return psi_eval(App(E, val))

            if name == "to-nat" and len(expr) == 2:
                val = psi_repl_eval(expr[1], env)
                n = to_nat(val)
                if n is None:
                    raise ValueError(f"Cannot decode as nat: {format_val(val)}")
                return nat(n)

        # General application: left-fold
        fn_val = psi_repl_eval(expr[0], env)
        for arg_expr in expr[1:]:
            arg_val = psi_repl_eval(arg_expr, env)
            fn_val = psi_eval(App(fn_val, arg_val))
        return fn_val

    # Fallback: return as-is (already a Term value)
    return expr


def _quote_to_term(expr) -> Term:
    """Convert a parsed AST to a Ψ∗ term without evaluating."""
    if isinstance(expr, Keyword):
        if expr.name in KEYWORD_MAP:
            return KEYWORD_MAP[expr.name]
        raise ValueError(f"Unknown keyword :{expr.name}")
    if isinstance(expr, Number):
        return nat(expr.value)
    if isinstance(expr, Symbol):
        if expr.name in ENV:
            return ENV[expr.name]
        raise ValueError(f"Unbound variable: {expr.name}")
    if isinstance(expr, Quoted):
        return _quote_to_term(expr.expr)
    if isinstance(expr, list):
        if not expr:
            return TOP
        result = _quote_to_term(expr[0])
        for e in expr[1:]:
            result = App(result, _quote_to_term(e))
        return result
    return expr

# ============================================================
# Formatting
# ============================================================

def format_val(v) -> str:
    """Pretty-print a Ψ∗ term, detecting nats and pairs."""
    if isinstance(v, str):
        return v
    if isinstance(v, int):
        return NAMES.get(v, str(v))
    if isinstance(v, App):
        # Try nat
        n = to_nat(v)
        if n is not None:
            return f"nat({n})"
        # Try pair
        a = fst(v)
        b = snd(v)
        if a is not None and b is not None:
            return f"pair({format_val(a)}, {format_val(b)})"
        return term_str(v, max_depth=20)
    return str(v)

# ============================================================
# Colored table
# ============================================================

def _print_table():
    """Print 16×16 Cayley table with ANSI colors."""
    # Simple palette: use hue rotation
    COLORS = [
        "\033[48;2;232;192;144m", "\033[48;2;24;24;42m",
        "\033[48;2;30;39;144m",   "\033[48;2;56;72;40m",
        "\033[48;2;12;20;42m",    "\033[48;2;11;10;9m",
        "\033[48;2;232;168;32m",  "\033[48;2;116;58;26m",
        "\033[48;2;92;36;176m",   "\033[48;2;56;192;216m",
        "\033[48;2;61;75;215m",   "\033[48;2;112;56;208m",
        "\033[48;2;80;24;136m",   "\033[48;2;115;50;98m",
        "\033[48;2;28;28;54m",    "\033[48;2;48;56;32m",
    ]
    RST = "\033[0m"

    # Header
    hdr = "   "
    for c in range(16):
        name = NAMES.get(c, str(c))
        hdr += f" {name:>2}"
    print(hdr)

    for r in range(16):
        name = NAMES.get(r, str(r))
        line = f"{name:>2} "
        for c in range(16):
            v = TABLE[r][c]
            vname = NAMES.get(v, str(v))
            # Pick fg based on bg luminance
            rgb = _palette_rgb(v)
            lum = 0.299 * rgb[0] + 0.587 * rgb[1] + 0.114 * rgb[2]
            fg = "\033[30m" if lum >= 140 else "\033[97m"
            line += f"{COLORS[v]}{fg} {vname:>2}{RST}"
        print(line)


def _palette_rgb(v: int) -> tuple[int, int, int]:
    """Return RGB for value v from the default palette."""
    HEX = {
        0: "#e8c090", 1: "#18182a", 2: "#1e2790", 3: "#384828",
        4: "#0c142a", 5: "#0b0a09", 6: "#e8a820", 7: "#743a1a",
        8: "#5c24b0", 9: "#38c0d8", 10: "#3d4bd7", 11: "#7038d0",
        12: "#501888", 13: "#733262", 14: "#1c1c36", 15: "#303820",
    }
    h = HEX.get(v, "#808080")
    return int(h[1:3], 16), int(h[3:5], 16), int(h[5:7], 16)

# ============================================================
# Public API (used by kick_eval)
# ============================================================

def eval_string(text: str) -> Any:
    """Parse and evaluate a Ψ∗ expression string. Returns the result."""
    exprs = parse(text)
    result = TOP
    for expr in exprs:
        result = psi_repl_eval(expr)
    return result

# ============================================================
# Interactive REPL
# ============================================================

def repl():
    """Interactive REPL loop."""
    if ALGEBRAIC:
        print("Ψ₁₆ᶠ / Ψ∗ REPL [algebraic mode]  (type Ctrl-D to exit)")
    else:
        print("Ψ₁₆ᶠ / Ψ∗ REPL  (type Ctrl-D to exit)")
    print(f"  Atoms: {', '.join(':' + k for k in KEYWORD_MAP)}")
    print(f"  Forms: def, do, print, table, dot, nat, pair, fst, snd, succ, pred, to-nat")
    print()

    while True:
        try:
            line = input("psi> ")
        except (EOFError, KeyboardInterrupt):
            print()
            break
        line = line.strip()
        if not line or line.startswith(";"):
            continue
        try:
            exprs = parse(line)
            result = TOP
            for expr in exprs:
                result = psi_repl_eval(expr)
            if result is not None:
                if ALGEBRAIC:
                    ad = _algebraic_nat_display(result)
                    print(ad if ad else format_val(result))
                else:
                    print(format_val(result))
        except Exception as exc:
            print(f"error: {exc}")

# ============================================================
# Main
# ============================================================

ALGEBRAIC = False


def _algebraic_nat_display(t) -> str | None:
    """If t is a nat (Q-chain rooted at ⊤), format as Q·(Q·(⊤)) [= 2]."""
    n = to_nat(t)
    if n is None:
        return None
    if n == 0:
        return "⊤ [= 0]"
    s = "⊤"
    for i in range(n):
        s = f"Q·{s}" if i == 0 else f"Q·({s})"
    return f"{s} [= {n}]"


def main():
    global ALGEBRAIC
    import argparse
    ap = argparse.ArgumentParser(description="Ψ₁₆ᶠ / Ψ∗ REPL")
    ap.add_argument("-e", "--eval", type=str, help="Evaluate expression and exit")
    ap.add_argument("--algebraic", action="store_true", help="Show Q-chain representations")
    args = ap.parse_args()

    ALGEBRAIC = args.algebraic

    if args.eval:
        try:
            result = eval_string(args.eval)
            if ALGEBRAIC:
                ad = _algebraic_nat_display(result)
                print(ad if ad else format_val(result))
            else:
                print(format_val(result))
        except Exception as exc:
            print(f"error: {exc}", file=sys.stderr)
            sys.exit(1)
    else:
        repl()


if __name__ == "__main__":
    main()

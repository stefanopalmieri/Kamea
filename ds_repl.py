#!/usr/bin/env python3
"""
Distinction Structures REPL

An interpreter for the DS algebra with EDN-like syntax,
PEG parser via Lark, and self-discovery on boot.

Usage:
  uv run ds_repl.py              # interactive REPL
  uv run ds_repl.py -e '(:e_D :k)'  # evaluate expression
  uv run ds_repl.py script.ds    # run a file

Syntax:
  :top :bot :e_D ...             atoms (keywords)
  "hello"                        string sugar (DS-native ANSI char list)
  0xA / 0xFF                     hex byte literal (0x00..0xFF)
  (:e_D :k)                      application
  '(:e_D :k)                     quote
  (eval '(:e_D :k))              eval quoted expression
  (app :e_D :k)                  build application node as data
  (unapp (app :e_D :k))          decompose app node
  (bit :top)                     contextual bit (#app[:binary :top|:bot])
  (bit 0x1)                      hex bit shorthand (0x0 or 0x1)
  (unbit (bit :top))             decode contextual bit to :top/:bot
  (byte b7 ... b0)               DS-native byte from 8 DS bits (MSB->LSB)
  (byte 0x4 0x1)                 DS-native byte from 2 hex nibbles
  (byte 0x41)                    DS-native byte from one hex byte
  (char byte)                    ANSI char from a DS byte
  (char 0x41)                    ANSI char from one hex byte
  (char :ansi (byte (bit :bot) (bit :top) (bit :bot) (bit :bot)
                    (bit :bot) (bit :bot) (bit :bot) (bit :top))) explicit char context + byte
  (char-byte (char byte))        extract byte from char
  (char-ctx (char byte))         extract context keyword from char
  (string c1 c2 ...)             build string from chars (or 1-char strings)
  (bit? x) (byte? x) (char? x)   DS-level predicates
  (if cond t e)                  conditional on :top
  (ok v) (err :code data)        result wrappers
  (ok? r) (err? r)               test wrappers
  (unwrap r)                     unwrap ok payload (or pass err)
  (err-code r) (err-data r)      inspect error payload
  (expand expr)                  macro-expand convenience forms
  (print expr1 expr2 ...)        print evaluated values, returns last (or :p)
  (def x (:e_D :k))              bind name
  (do expr1 expr2 ...)           sequence, returns last
  (discover!)                    run self-discovery procedure
  (table)                        print the Cayley table
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Any
import ast
import sys
import itertools
import re

from lark import Lark, Transformer, v_args
from delta2_74181 import alu_74181

# ============================================================
# PEG Grammar (Lark Earley/LALR with PEG-like rules)
# ============================================================

GRAMMAR = r"""
    start: expr+

    ?expr: atom
         | keyword
         | hexbyte
         | string
         | quoted
         | list
         | special

    keyword: /:[a-zA-Z_][a-zA-Z0-9_!?\-]*/
    atom: /[a-zA-Z_][a-zA-Z0-9_!?\-]*/
    hexbyte: /0x[0-9a-fA-F]{1,2}/
    string: ESCAPED_STRING
    quoted: "'" expr
    list: "(" expr* ")"
    special: "#app" "[" expr expr "]"
           | "#bundle" "[" expr expr "]"

    %import common.ESCAPED_STRING
    COMMENT: /;[^\n]*/
    %ignore COMMENT
    %ignore /\s+/
"""

parser = Lark(GRAMMAR, parser="earley", ambiguity="resolve")

# ============================================================
# AST
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
class Literal:
    value: Any
    def __repr__(self): return f"#lit[{format_val(self.value)}]"

@dataclass(frozen=True)
class HexByte:
    value: int
    def __repr__(self): return f"0x{self.value:X}"

@dataclass(frozen=True)
class AppNode:
    f: Any
    x: Any
    def __repr__(self): return f"#app[{format_val(self.f)} {format_val(self.x)}]"

@dataclass(frozen=True)
class Bundle:
    f: Any
    x: Any
    def __repr__(self): return f"#bundle[{format_val(self.f)} {format_val(self.x)}]"

@dataclass(frozen=True)
class Partial:
    f: Any
    def __repr__(self): return f"#partial[{format_val(self.f)}]"

@dataclass(frozen=True)
class ALUPartial1:
    """ALU dispatch with selector applied, waiting for operand A."""
    mode: str       # "logic", "arith", "arithc"
    selector: int   # 0-15
    def __repr__(self): return f"#alu1[{self.mode} N{self.selector:X}]"

@dataclass(frozen=True)
class ALUPartial2:
    """ALU dispatch with selector and operand A applied, waiting for B."""
    mode: str
    selector: int
    a: int          # 0-15
    def __repr__(self): return f"#alu2[{self.mode} N{self.selector:X} N{self.a:X}]"

@dataclass(frozen=True)
class ALUCoutProbe:
    """ALU_COUT applied to an ALUPartial2 — awaiting operand B to extract real Cn+4."""
    mode: str
    selector: int
    a: int
    def __repr__(self): return f"#cout[{self.mode} N{self.selector:X} N{self.a:X}]"

class List:
    def __init__(self, items):
        self.items = items
    def __repr__(self):
        return "(" + " ".join(format_val(i) for i in self.items) + ")"


@v_args(inline=True)
class ASTBuilder(Transformer):
    def keyword(self, tok):
        return Keyword(str(tok)[1:])  # strip leading :

    def atom(self, tok):
        return Symbol(str(tok))

    def hexbyte(self, tok):
        return HexByte(int(str(tok)[2:], 16))

    def string(self, tok):
        return ast.literal_eval(str(tok))

    def quoted(self, expr):
        return Quoted(expr)

    def list(self, *items):
        return List(list(items))

    def special(self, *items):
        items = list(items)
        if len(items) == 2:
            # Could be #app or #bundle — determine from parse context
            return AppNode(items[0], items[1])
        return items

    def start(self, *exprs):
        return list(exprs)


ast_builder = ASTBuilder()

def parse(text: str):
    tree = parser.parse(text)
    result = ast_builder.transform(tree)
    return result

# ============================================================
# Δ₁ Core: The 17-element Cayley table
# ============================================================

ATOMS_D1 = [
    "top", "bot", "i", "k", "a", "b", "e_I",
    "e_D", "e_M", "e_Sigma", "e_Delta",
    "d_I", "d_K", "m_I", "m_K", "s_C", "p",
]
NIBBLE_NAMES = [f"N{i:X}" for i in range(16)]
ALU_DISPATCH_NAMES = ["ALU_LOGIC", "ALU_ARITH", "ALU_ARITHC"]
ALU_PRED_NAMES = ["ALU_ZERO", "ALU_COUT"]
ALU_MISC_NAMES = ["N_SUCC"]

ATOMS = ATOMS_D1 + NIBBLE_NAMES + ALU_DISPATCH_NAMES + ALU_PRED_NAMES + ALU_MISC_NAMES
ATOM_SET = set(ATOMS)
NIBBLE_SET = set(NIBBLE_NAMES)
ALU_DISPATCH_SET = set(ALU_DISPATCH_NAMES)
ALU_PRED_SET = set(ALU_PRED_NAMES)


def is_nibble_name(name: str) -> bool:
    return name in NIBBLE_SET

def nibble_val(name: str) -> int:
    return int(name[1:], 16)

def nibble_name(n: int) -> str:
    return f"N{n % 16:X}"

# DS-native data encoding constants
ANSI_MIN = 0
ANSI_MAX = 255
BIT_CTX = "binary"
BYTE_NIL = "byte_nil"
STRING_NIL = "str_nil"
CHAR_CTX_ANSI = "ansi"
LEGACY_CHAR_TAG = "char"
ANSI_RE = re.compile(r"^ansi_([0-9]{1,3})$")


def ansi_keyword_name(code: int) -> str:
    if not (ANSI_MIN <= code <= ANSI_MAX):
        raise ValueError(f"ANSI code must be in 0..255, got {code}")
    return f"ansi_{code:03d}"


def coerce_bit_value(value: Any) -> int | None:
    """Interpret a value as bit 0/1 from DS booleans (or internal ints)."""
    if isinstance(value, int) and value in (0, 1):
        return int(value)
    if isinstance(value, HexByte) and value.value in (0, 1):
        return value.value
    if isinstance(value, Keyword):
        if value.name == "top":
            return 1
        if value.name == "bot":
            return 0
    return None


def coerce_nibble_value(value: Any) -> int | None:
    """Interpret a value as nibble 0..15."""
    if isinstance(value, HexByte):
        return value.value
    if isinstance(value, int) and 0 <= value <= 15:
        return int(value)
    return None


def encode_bit(bit: Any) -> AppNode:
    """Encode a bit as #app[:binary :top|:bot]."""
    bit_val = coerce_bit_value(bit)
    if bit_val is None:
        raise ValueError(f"Bit must be :top or :bot, got {bit}")
    return AppNode(Keyword(BIT_CTX), Keyword("top" if bit_val == 1 else "bot"))


def decode_bit(term: Any) -> int | None:
    """Decode contextual bit #app[:binary :top|:bot] to 0/1."""
    if not isinstance(term, AppNode):
        return None
    if not isinstance(term.f, Keyword) or term.f.name != BIT_CTX:
        return None
    if not isinstance(term.x, Keyword):
        return None
    if term.x.name == "top":
        return 1
    if term.x.name == "bot":
        return 0
    return None


def encode_byte_from_bits(bits: list[int]) -> Any:
    """Encode exactly 8 bits (MSB→LSB) as a DS list ending in :byte_nil."""
    if len(bits) != 8:
        raise ValueError(f"Byte expects exactly 8 bits, got {len(bits)}")
    out: Any = Keyword(BYTE_NIL)
    for b in reversed(bits):
        out = AppNode(encode_bit(b), out)
    return out


def encode_byte(code: int) -> Any:
    """Encode an integer 0..255 as a DS byte."""
    if not (ANSI_MIN <= code <= ANSI_MAX):
        raise ValueError(f"Byte must be in 0..255, got {code}")
    bits = [(code >> shift) & 1 for shift in range(7, -1, -1)]
    return encode_byte_from_bits(bits)


def decode_byte(term: Any, max_nodes: int = 16) -> int | None:
    """Decode DS byte to integer when shape is 8 contextual bits + :byte_nil."""
    bits: list[int] = []
    cur = term
    for _ in range(max_nodes):
        if isinstance(cur, Keyword) and cur.name == BYTE_NIL:
            break
        if not isinstance(cur, AppNode):
            return None
        bit = decode_bit(cur.f)
        if bit is None:
            return None
        bits.append(bit)
        cur = cur.x
    else:
        return None

    if len(bits) != 8:
        return None
    if not (isinstance(cur, Keyword) and cur.name == BYTE_NIL):
        return None

    code = 0
    for b in bits:
        code = (code << 1) | b
    return code


def split_char(term: Any) -> tuple[str, Any] | None:
    """Split a DS char into (context, byte), with legacy fallback support."""
    if isinstance(term, AppNode) and isinstance(term.f, Keyword):
        if decode_byte(term.x) is not None:
            return (term.f.name, term.x)

    # Backward compatibility for legacy #app[:char :ansi_NNN] values.
    if (
        isinstance(term, AppNode)
        and isinstance(term.f, Keyword)
        and term.f.name == LEGACY_CHAR_TAG
        and isinstance(term.x, Keyword)
    ):
        m = ANSI_RE.fullmatch(term.x.name)
        if m:
            code = int(m.group(1))
            if ANSI_MIN <= code <= ANSI_MAX:
                return (CHAR_CTX_ANSI, encode_byte(code))
    return None


def encode_char_code(code: int) -> AppNode:
    """Encode ANSI code as #app[:ansi <byte>]."""
    return AppNode(Keyword(CHAR_CTX_ANSI), encode_byte(code))


def decode_char_code(term: Any) -> int | None:
    """Decode ANSI char value #app[:ansi <byte>] to 0..255."""
    parts = split_char(term)
    if parts is None:
        return None
    ctx, byte_term = parts
    if ctx != CHAR_CTX_ANSI:
        return None
    return decode_byte(byte_term)


def encode_string_from_chars(chars: list[Any]) -> Any:
    """Encode a sequence of DS-native char values as a linked list."""
    out: Any = Keyword(STRING_NIL)
    for ch in reversed(chars):
        out = AppNode(ch, out)
    return out


def encode_string(text: str) -> Any:
    """Encode Python string as DS-native ANSI char list."""
    chars = []
    for ch in text:
        code = ord(ch)
        if not (ANSI_MIN <= code <= ANSI_MAX):
            raise ValueError(
                f'Non-ANSI character {ch!r} (U+{code:04X}) is not encodable; use 0..255 only'
            )
        chars.append(encode_char_code(code))
    return encode_string_from_chars(chars)


def decode_string(term: Any, max_nodes: int = 10000) -> str | None:
    """Decode DS-native ANSI char list back to Python string if it matches."""
    chars: list[str] = []
    cur = term
    for _ in range(max_nodes):
        if isinstance(cur, Keyword) and cur.name == STRING_NIL:
            return "".join(chars)
        if not isinstance(cur, AppNode):
            return None
        code = decode_char_code(cur.f)
        if code is None:
            return None
        chars.append(chr(code))
        cur = cur.x
    return None


def escape_string_literal(text: str) -> str:
    """Render ANSI string with explicit escapes for non-printables."""
    out: list[str] = []
    for ch in text:
        code = ord(ch)
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\r":
            out.append("\\r")
        elif ch == "\t":
            out.append("\\t")
        elif 32 <= code <= 126:
            out.append(ch)
        else:
            out.append(f"\\x{code:02x}")
    return "".join(out)


def format_byte_bits(code: int) -> str:
    return "".join(str((code >> shift) & 1) for shift in range(7, -1, -1))


def dot_d1(x: str, y: str) -> str:
    """Δ₁ operation on atom name strings."""
    if x == "top": return "top"
    if x == "bot": return "bot"
    if x == "e_I": return "top" if y in ("i", "k") else "bot"
    if x == "d_K": return "top" if y in ("a", "b") else "bot"
    if x == "m_K": return "top" if y == "a" else "bot"
    if x == "m_I": return "bot" if y == "p" else "top"
    if x == "e_D" and y == "i": return "d_I"
    if x == "e_D" and y == "k": return "d_K"
    if x == "e_M" and y == "i": return "m_I"
    if x == "e_M" and y == "k": return "m_K"
    if x == "e_Sigma" and y == "s_C": return "e_Delta"
    if x == "e_Delta" and y == "e_D": return "d_I"
    if x == "p" and y == "top": return "top"
    if y == "top" and x in ("i", "k", "a", "b", "d_I", "s_C"):
        return x
    return "p"


def dot_atom(x: str, y: str) -> str:
    """Full 43-atom Cayley table (Δ₁ + 74181 extension)."""
    # D1 atoms use the original table (works for D1 × anything since
    # D1 testers return bot for non-D1 atoms except m_I which returns top)
    if x in ATOMS_D1:
        return dot_d1(x, y)

    # Nibble self-identification on top
    if is_nibble_name(x) and y == "top":
        return x

    # Nibble × Nibble: Z/16Z addition
    if is_nibble_name(x) and is_nibble_name(y):
        return nibble_name((nibble_val(x) + nibble_val(y)) % 16)

    # ALU dispatch self-identification on top
    if x in ALU_DISPATCH_SET and y == "top":
        return x

    # ALU dispatch × Nibble: distinguishing mappings
    if x == "ALU_LOGIC" and is_nibble_name(y):
        return y  # identity
    if x == "ALU_ARITH" and is_nibble_name(y):
        return nibble_name((nibble_val(y) + 1) % 16)  # successor
    if x == "ALU_ARITHC" and is_nibble_name(y):
        return nibble_name((nibble_val(y) + 2) % 16)  # double successor

    # ALU predicate self-identification on top
    if x in ALU_PRED_SET and y == "top":
        return x

    # ALU_ZERO: tester on nibbles
    if x == "ALU_ZERO" and is_nibble_name(y):
        return "top" if y == "N0" else "bot"

    # ALU_COUT: tester on nibbles (high bit)
    if x == "ALU_COUT" and is_nibble_name(y):
        return "top" if nibble_val(y) >= 8 else "bot"

    # N_SUCC: successor on nibbles (16-cycle)
    if x == "N_SUCC" and y == "top":
        return x
    if x == "N_SUCC" and y == "bot":
        return "N0"  # reset on bot
    if x == "N_SUCC" and is_nibble_name(y):
        return nibble_name((nibble_val(y) + 1) % 16)

    # Default: everything else → p
    return "p"

# ============================================================
# Δ₃ Evaluator
# ============================================================

MAX_FUEL = 100


def ds_apply(left: Any, right: Any, fuel: int = MAX_FUEL) -> Any:
    """Apply left to right in the DS algebra."""
    if fuel <= 0:
        return Keyword("p")

    # QUOTE
    if isinstance(left, Keyword) and left.name == "QUOTE":
        return Quoted(right)

    # EVAL
    if isinstance(left, Keyword) and left.name == "EVAL":
        if isinstance(right, Quoted):
            return ds_eval(right.expr, fuel - 1)
        return Keyword("p")

    # APP (curried)
    if isinstance(left, Keyword) and left.name == "APP":
        return Partial(right)

    # Partial completion
    if isinstance(left, Partial):
        return AppNode(left.f, right)

    # UNAPP
    if isinstance(left, Keyword) and left.name == "UNAPP":
        if isinstance(right, AppNode):
            return Bundle(right.f, right.x)
        return Keyword("p")

    # Bundle queries
    if isinstance(left, Bundle):
        if isinstance(right, Keyword) and right.name == "top":
            return left.f
        if isinstance(right, Keyword) and right.name == "bot":
            return left.x
        return Keyword("p")

    # ALU dispatch × nibble → ALUPartial1
    if isinstance(left, Keyword) and left.name in ALU_DISPATCH_SET:
        if isinstance(right, Keyword) and is_nibble_name(right.name):
            mode = {"ALU_LOGIC": "logic", "ALU_ARITH": "arith", "ALU_ARITHC": "arithc"}[left.name]
            return ALUPartial1(mode, nibble_val(right.name))

    # ALUPartial1 + nibble → ALUPartial2
    if isinstance(left, ALUPartial1):
        if isinstance(right, Keyword) and is_nibble_name(right.name):
            return ALUPartial2(left.mode, left.selector, nibble_val(right.name))
        return Keyword("p")

    # ALUPartial2 + nibble → computed result (just the nibble)
    if isinstance(left, ALUPartial2):
        if isinstance(right, Keyword) and is_nibble_name(right.name):
            result, carry, zero = alu_74181(left.mode, left.selector, left.a, nibble_val(right.name))
            return Keyword(nibble_name(result))
        return Keyword("p")

    # ALU_COUT modal: on ALUPartial2, becomes carry probe awaiting B
    if isinstance(left, Keyword) and left.name == "ALU_COUT":
        if isinstance(right, ALUPartial2):
            return ALUCoutProbe(right.mode, right.selector, right.a)

    # ALUCoutProbe + nibble → real Cn+4 carry-out
    if isinstance(left, ALUCoutProbe):
        if isinstance(right, Keyword) and is_nibble_name(right.name):
            _, carry, _ = alu_74181(left.mode, left.selector, left.a, nibble_val(right.name))
            return Keyword("top" if carry else "bot")
        return Keyword("p")

    # Inertness: structured values under atoms
    if isinstance(left, Keyword) and left.name in ATOM_SET:
        if isinstance(right, (Quoted, Literal, AppNode, Bundle, Partial,
                              ALUPartial1, ALUPartial2, ALUCoutProbe)):
            return Keyword("p")

    # Atom × Atom fallback (full 43-atom Cayley table)
    if isinstance(left, Keyword) and isinstance(right, Keyword):
        if left.name in ATOM_SET and right.name in ATOM_SET:
            return Keyword(dot_atom(left.name, right.name))

    return Keyword("p")


def ds_unapp_query(val: Any, selector: str) -> Any:
    """Project from app-like data using UNAPP + boolean selector."""
    bun = ds_apply(Keyword("UNAPP"), val)
    return ds_apply(bun, Keyword(selector))


def bool_kw(flag: bool) -> Keyword:
    return Keyword("top" if flag else "bot")


def normalize_err_code(code: Any) -> Keyword:
    if isinstance(code, Keyword):
        return code
    if isinstance(code, Symbol):
        return Keyword(code.name)
    if isinstance(code, HexByte):
        return Keyword(f"hex_{code.value:02X}")
    if isinstance(code, str):
        return Keyword(code)
    return Keyword("error")


def error_detail_term(message: str) -> Any:
    """Encode an error detail string in an ANSI-safe DS string form."""
    safe = message.encode("ascii", "backslashreplace").decode("ascii")
    return encode_string(safe)


def ok_result(value: Any) -> AppNode:
    return AppNode(Keyword("ok"), value)


def err_result(code: Any, detail: Any = None) -> AppNode:
    if detail is None:
        detail = Keyword("p")
    return AppNode(Keyword("err"), AppNode(normalize_err_code(code), detail))


def is_ok_result(v: Any) -> bool:
    return isinstance(v, AppNode) and isinstance(v.f, Keyword) and v.f.name == "ok"


def ok_payload(v: Any) -> Any:
    return v.x if is_ok_result(v) else None


def err_parts(v: Any) -> tuple[str, Any] | None:
    if not (isinstance(v, AppNode) and isinstance(v.f, Keyword) and v.f.name == "err"):
        return None
    if isinstance(v.x, AppNode) and isinstance(v.x.f, Keyword):
        return (v.x.f.name, v.x.x)
    return ("error_payload", v.x)


def is_err_result(v: Any) -> bool:
    return err_parts(v) is not None


def is_bit_value(v: Any) -> bool:
    return decode_bit(v) is not None


def is_byte_value(v: Any) -> bool:
    return decode_byte(v) is not None


def is_char_value(v: Any) -> bool:
    return split_char(v) is not None


def expand_if(cond: Any, yes: Any, no: Any) -> List:
    return List([Symbol("if"), cond, yes, no])


def expand_err(code: str, detail: Any) -> List:
    return List([Symbol("err"), Keyword(code), detail])


def build_app_chain_expr(items: list[Any], nil_term: Any) -> Any:
    out: Any = nil_term
    for item in reversed(items):
        out = List([Symbol("app"), item, out])
    return out


def expand_unapp_projection(val: Any, selector: str) -> List:
    """Build core DS expression ((unapp val) :selector)."""
    return List([List([Symbol("unapp"), val]), Keyword(selector)])


def guard_expr(checks: list[tuple[Any, Any]], success: Any) -> Any:
    """Build nested if-checks around a success expression."""
    result = success
    for cond, err_expr in reversed(checks):
        result = expand_if(cond, result, err_expr)
    return result


def expand_convenience(expr: Any) -> Any:
    """Macro-expand REPL convenience forms into core DS data/forms."""
    if isinstance(expr, str):
        try:
            return encode_string(expr)
        except ValueError as e:
            return err_result("non_ansi_string", error_detail_term(str(e)))
    if isinstance(expr, (Keyword, Symbol, HexByte, Quoted, Literal, AppNode, Bundle, Partial)):
        return expr

    if isinstance(expr, List):
        items = expr.items
        if not items:
            return Keyword("p")

        if isinstance(items[0], Symbol):
            name = items[0].name

            if name == "bit":
                if len(items) != 2:
                    return err_result("bit_arity", List(items))
                v = expand_convenience(items[1])
                if is_err_result(v):
                    return v
                bit_val = coerce_bit_value(v)
                if bit_val is not None:
                    return encode_bit(bit_val)
                if is_bit_value(v):
                    return v
                return expand_if(
                    List([Symbol("bit?"), v]),
                    v,
                    expand_err("expected_bit", v),
                )

            if name == "unbit":
                if len(items) != 2:
                    return err_result("unbit_arity", List(items))
                v = expand_convenience(items[1])
                if is_err_result(v):
                    return v
                return expand_if(
                    List([Symbol("bit?"), v]),
                    expand_unapp_projection(v, "bot"),
                    expand_err("expected_bit", v),
                )

            if name == "byte":
                if len(items) == 2:
                    v = expand_convenience(items[1])
                    if is_err_result(v):
                        return v
                    if isinstance(v, HexByte):
                        return encode_byte(v.value)
                    code = decode_byte(v)
                    if code is not None:
                        return encode_byte(code)
                    return expand_if(
                        List([Symbol("byte?"), v]),
                        v,
                        expand_err("expected_byte", v),
                    )
                if len(items) == 3:
                    hi_expr = expand_convenience(items[1])
                    lo_expr = expand_convenience(items[2])
                    if is_err_result(hi_expr):
                        return hi_expr
                    if is_err_result(lo_expr):
                        return lo_expr
                    hi = coerce_nibble_value(hi_expr)
                    lo = coerce_nibble_value(lo_expr)
                    if hi is None or lo is None:
                        return expand_err("expected_hex_nibbles", List([hi_expr, lo_expr]))
                    return encode_byte((hi << 4) | lo)
                if len(items) == 9:
                    checks: list[tuple[Any, Any]] = []
                    bit_terms: list[Any] = []
                    for arg in items[1:]:
                        v = expand_convenience(arg)
                        if is_err_result(v):
                            return v
                        if isinstance(v, HexByte) and v.value in (0, 1):
                            bit_terms.append(encode_bit(v.value))
                            continue
                        if is_bit_value(v):
                            bit_terms.append(v)
                            continue
                        bit_terms.append(v)
                        checks.append((List([Symbol("bit?"), v]), expand_err("expected_bit", v)))
                    success = build_app_chain_expr(bit_terms, Keyword(BYTE_NIL))
                    return guard_expr(checks, success)
                return err_result("byte_arity", List(items))

            if name == "char":
                if len(items) == 2:
                    v = expand_convenience(items[1])
                    if is_err_result(v):
                        return v
                    if isinstance(v, HexByte):
                        return encode_char_code(v.value)
                    if is_byte_value(v):
                        return AppNode(Keyword(CHAR_CTX_ANSI), v)
                    return expand_if(
                        List([Symbol("byte?"), v]),
                        List([Symbol("app"), Keyword(CHAR_CTX_ANSI), v]),
                        expand_err("expected_byte", v),
                    )
                if len(items) == 3:
                    ctx = expand_convenience(items[1])
                    by = expand_convenience(items[2])
                    if is_err_result(ctx):
                        return ctx
                    if is_err_result(by):
                        return by
                    if not isinstance(ctx, Keyword):
                        return expand_err("expected_char_context", ctx)
                    if is_byte_value(by):
                        return AppNode(Keyword(ctx.name), by)
                    return expand_if(
                        List([Symbol("byte?"), by]),
                        List([Symbol("app"), ctx, by]),
                        expand_err("expected_byte", by),
                    )
                return err_result("char_arity", List(items))

            if name == "char-byte":
                if len(items) != 2:
                    return err_result("char_byte_arity", List(items))
                v = expand_convenience(items[1])
                if is_err_result(v):
                    return v
                return expand_if(
                    List([Symbol("char?"), v]),
                    expand_unapp_projection(v, "bot"),
                    expand_err("expected_char", v),
                )

            if name == "char-ctx":
                if len(items) != 2:
                    return err_result("char_ctx_arity", List(items))
                v = expand_convenience(items[1])
                if is_err_result(v):
                    return v
                return expand_if(
                    List([Symbol("char?"), v]),
                    expand_unapp_projection(v, "top"),
                    expand_err("expected_char", v),
                )

            if name == "string":
                chars: list[Any] = []
                checks: list[tuple[Any, Any]] = []
                for arg in items[1:]:
                    v = expand_convenience(arg)
                    if is_err_result(v):
                        return v
                    if isinstance(v, HexByte):
                        chars.append(encode_char_code(v.value))
                        continue
                    code = decode_char_code(v)
                    if code is not None:
                        chars.append(encode_char_code(code))
                        continue
                    decoded = decode_string(v)
                    if decoded is not None and len(decoded) == 1:
                        chars.append(encode_char_code(ord(decoded)))
                        continue
                    chars.append(v)
                    checks.append((List([Symbol("char?"), v]), expand_err("expected_char", v)))
                success = build_app_chain_expr(chars, Keyword(STRING_NIL))
                return guard_expr(checks, success)

        return List([expand_convenience(i) for i in items])

    return expr


def ds_eval(expr: Any, fuel: int = MAX_FUEL) -> Any:
    """Evaluate a DS expression."""
    if fuel <= 0:
        return Keyword("p")

    if isinstance(expr, Keyword):
        return expr
    if isinstance(expr, Quoted):
        return expr
    if isinstance(expr, Literal):
        return expr.value
    if isinstance(expr, Bundle):
        return expr
    if isinstance(expr, Partial):
        return expr
    if isinstance(expr, AppNode):
        left = ds_eval(expr.f, fuel - 1)
        right = ds_eval(expr.x, fuel - 1)
        return ds_apply(left, right, fuel - 1)

    return Keyword("p")


# ============================================================
# REPL Evaluator (handles special forms)
# ============================================================

ENV = {}  # name -> value bindings


def repl_eval(expr: Any) -> Any:
    """Evaluate in REPL context (handles def, do, discover!, etc.)."""
    # Keywords evaluate to themselves
    if isinstance(expr, Keyword):
        return expr

    # String literals are sugar for DS-native char lists
    if isinstance(expr, str):
        try:
            return encode_string(expr)
        except ValueError as e:
            return err_result("non_ansi_string", error_detail_term(str(e)))

    # Hex byte literals are self-evaluating data
    if isinstance(expr, HexByte):
        return expr

    # Symbols look up in environment
    if isinstance(expr, Symbol):
        if expr.name in ENV:
            return ENV[expr.name]
        # Check if it's a DS atom
        if expr.name in ATOM_SET:
            return Keyword(expr.name)
        # Check special atoms
        if expr.name in ("QUOTE", "EVAL", "APP", "UNAPP"):
            return Keyword(expr.name)
        raise NameError(f"Unbound symbol: {expr.name}")

    # Quoted expressions
    if isinstance(expr, Quoted):
        return Quoted(quote_transform(expr.expr))

    # Structured values
    if isinstance(expr, (AppNode, Bundle, Partial)):
        return expr

    # Lists: special forms and application
    if isinstance(expr, List):
        items = expr.items
        if not items:
            return Keyword("p")

        # Special forms
        if isinstance(items[0], Symbol):
            name = items[0].name

            # (def name expr)
            if name == "def" and len(items) == 3:
                sym = items[1]
                if not isinstance(sym, Symbol):
                    raise SyntaxError(f"def expects a symbol, got {sym}")
                val = repl_eval(items[2])
                ENV[sym.name] = val
                return val

            # (do expr1 expr2 ...)
            if name == "do":
                result = Keyword("p")
                for e in items[1:]:
                    result = repl_eval(e)
                return result

            # (discover!)
            if name == "discover!":
                return run_discovery()

            # (table)
            if name == "table":
                print_table()
                return Keyword("p")

            # (if cond then else)
            if name == "if":
                if len(items) != 4:
                    return err_result("if_arity", List(items))
                cond = repl_eval(items[1])
                if is_err_result(cond):
                    return cond
                branch = items[2] if isinstance(cond, Keyword) and cond.name == "top" else items[3]
                return repl_eval(branch)

            # Result wrappers
            if name == "ok":
                if len(items) != 2:
                    return err_result("ok_arity", List(items))
                return ok_result(repl_eval(items[1]))

            if name == "err":
                if len(items) not in (2, 3):
                    return err_result("err_arity", List(items))
                code_val = repl_eval(items[1])
                if is_err_result(code_val):
                    return code_val
                detail_val = repl_eval(items[2]) if len(items) == 3 else Keyword("p")
                if is_err_result(detail_val):
                    return detail_val
                return err_result(code_val, detail_val)

            if name == "ok?":
                if len(items) != 2:
                    return err_result("okq_arity", List(items))
                return bool_kw(is_ok_result(repl_eval(items[1])))

            if name == "err?":
                if len(items) != 2:
                    return err_result("errq_arity", List(items))
                return bool_kw(is_err_result(repl_eval(items[1])))

            if name == "unwrap":
                if len(items) != 2:
                    return err_result("unwrap_arity", List(items))
                val = repl_eval(items[1])
                if is_ok_result(val):
                    return ok_payload(val)
                if is_err_result(val):
                    return val
                return Keyword("p")

            if name == "err-code":
                if len(items) != 2:
                    return err_result("err_code_arity", List(items))
                parts = err_parts(repl_eval(items[1]))
                if parts is None:
                    return Keyword("p")
                return Keyword(parts[0])

            if name == "err-data":
                if len(items) != 2:
                    return err_result("err_data_arity", List(items))
                parts = err_parts(repl_eval(items[1]))
                if parts is None:
                    return Keyword("p")
                return parts[1]

            # Predicates
            if name == "bit?":
                if len(items) != 2:
                    return err_result("bitq_arity", List(items))
                return bool_kw(is_bit_value(repl_eval(items[1])))

            if name == "byte?":
                if len(items) != 2:
                    return err_result("byteq_arity", List(items))
                return bool_kw(is_byte_value(repl_eval(items[1])))

            if name == "char?":
                if len(items) != 2:
                    return err_result("charq_arity", List(items))
                return bool_kw(is_char_value(repl_eval(items[1])))

            # (expand expr)
            if name == "expand":
                if len(items) != 2:
                    return err_result("expand_arity", List(items))
                try:
                    return expand_convenience(items[1])
                except Exception as e:
                    return err_result("expand_error", error_detail_term(str(e)))

            # (eval expr)
            if name == "eval":
                if len(items) != 2:
                    return err_result("eval_arity", List(items))
                val = repl_eval(items[1])
                if is_err_result(val):
                    return val
                if isinstance(val, Quoted):
                    return ds_eval(val.expr)
                return Keyword("p")

            # (quote expr) — alternative to 'expr
            if name == "quote":
                if len(items) != 2:
                    return err_result("quote_arity", List(items))
                return Quoted(quote_transform(items[1]))

            # (app f x)
            if name == "app":
                if len(items) != 3:
                    return err_result("app_arity", List(items))
                f = repl_eval(items[1])
                if is_err_result(f):
                    return f
                x = repl_eval(items[2])
                if is_err_result(x):
                    return x
                return AppNode(f, x)

            # (unapp expr)
            if name == "unapp":
                if len(items) != 2:
                    return err_result("unapp_arity", List(items))
                val = repl_eval(items[1])
                if is_err_result(val):
                    return val
                return ds_apply(Keyword("UNAPP"), val)

            # (print expr1 expr2 ...)
            if name == "print":
                if len(items) < 2:
                    return err_result("print_arity", List(items))
                vals = [repl_eval(item) for item in items[1:]]
                for v in vals:
                    if is_err_result(v):
                        return v
                print(" ".join(format_val(v) for v in vals))
                return vals[-1] if vals else Keyword("p")

            # Convenience forms are macro-expanded and then evaluated.
            if name in ("bit", "unbit", "byte", "char", "char-byte", "char-ctx", "string"):
                try:
                    expanded = expand_convenience(expr)
                except Exception as e:
                    return err_result("expand_error", error_detail_term(str(e)))
                if is_err_result(expanded):
                    return expanded
                return repl_eval(expanded)

        # General application: evaluate all, then apply left-to-right
        vals = [repl_eval(item) for item in items]
        if len(vals) == 1:
            return vals[0]
        result = vals[0]
        for v in vals[1:]:
            result = ds_apply(result, v)
        return result

    return expr


def quote_transform(expr: Any) -> Any:
    """Transform an expression inside a quote to preserve structure."""
    if isinstance(expr, str):
        try:
            return Literal(encode_string(expr))
        except ValueError as e:
            return Literal(err_result("non_ansi_string", error_detail_term(str(e))))
    if isinstance(expr, HexByte):
        return Literal(expr)
    if isinstance(expr, Symbol):
        if expr.name in ATOM_SET or expr.name in ("QUOTE", "EVAL", "APP", "UNAPP"):
            return Keyword(expr.name)
        if expr.name in ENV:
            return ENV[expr.name]
        return Keyword(expr.name)
    if isinstance(expr, Keyword):
        return expr
    if isinstance(expr, List):
        if len(expr.items) == 2:
            f = quote_transform(expr.items[0])
            x = quote_transform(expr.items[1])
            return AppNode(f, x)
        if len(expr.items) > 2:
            # Left-fold application
            result = quote_transform(expr.items[0])
            for item in expr.items[1:]:
                result = AppNode(result, quote_transform(item))
            return result
        if len(expr.items) == 1:
            return quote_transform(expr.items[0])
        return Keyword("p")
    if isinstance(expr, Quoted):
        return Quoted(quote_transform(expr.expr))
    return expr


# ============================================================
# Self-Discovery
# ============================================================

def run_discovery() -> Any:
    """Run the 8-step recovery procedure on the Cayley table."""
    domain = list(ATOM_SET)

    def dot(x, y):
        return dot_d1(x, y)

    def left_image(x):
        return {dot(x, y) for y in domain}

    print("  Running self-discovery...")

    # Step 1: Booleans
    absorbers = [x for x in domain if all(dot(x, y) == x for y in domain)]
    print(f"  Step 1 — Booleans: {absorbers}")

    # Step 2: Orient booleans, find testers
    for top, bot in [(absorbers[0], absorbers[1]), (absorbers[1], absorbers[0])]:
        testers = [x for x in domain if x not in (top, bot)
                   and left_image(x).issubset({top, bot}) and len(left_image(x)) == 2]
        if len(testers) == 4:
            Dec = lambda t, top=top: {y for y in domain if dot(t, y) == top}
            sizes = sorted(len(Dec(t)) for t in testers)
            if sizes[0] == 1 and sizes[1] == 2 and sizes[2] == 2:
                break
    else:
        print("  Discovery failed at step 2")
        return Keyword("p")

    print(f"  Step 2 — top={top}, bot={bot}")
    print(f"           Testers: {testers}")

    # Step 2.5: Find p
    p_cands = [x for x in domain if x not in (top, bot) and x not in testers
               and top in left_image(x)]
    p_tok = p_cands[0] if len(p_cands) == 1 else None
    print(f"  Step 2.5 — p={p_tok}")

    # Step 3: Tester cardinalities
    sizes = {t: len(Dec(t)) for t in testers}
    m_K = [t for t in testers if sizes[t] == 1][0]
    m_I = max(testers, key=lambda t: sizes[t])
    two = [t for t in testers if sizes[t] == 2]
    print(f"  Step 3 — m_I={m_I} (|Dec|={sizes[m_I]}), m_K={m_K} (|Dec|=1)")

    # Step 4: e_I vs d_K
    def has_productive(decoded):
        for f in domain:
            if f in (top, bot) or f in testers:
                continue
            for x in decoded:
                out = dot(f, x)
                if out not in (top, bot, p_tok):
                    return True
        return False

    t1, t2 = two
    e_I, d_K = (t1, t2) if has_productive(Dec(t1)) else (t2, t1)
    ctx = list(Dec(e_I))
    print(f"  Step 4 — e_I={e_I}, d_K={d_K}")
    print(f"           Context tokens: {ctx}")

    # Step 5: Encoders
    def is_enc(f):
        if f in (top, bot) or f in testers:
            return False
        return all(dot(f, x) not in (top, bot, p_tok) for x in ctx)

    enc = [f for f in domain if is_enc(f)]
    e_M = enc[0] if all(dot(enc[0], x) in testers for x in ctx) else enc[1]
    e_D = enc[1] if e_M == enc[0] else enc[0]
    print(f"  Step 5 — e_D={e_D}, e_M={e_M}")

    # Step 6: i vs k
    outA, outB = dot(e_M, ctx[0]), dot(e_M, ctx[1])
    if len(Dec(outA)) > len(Dec(outB)):
        i_tok, k_tok = ctx[0], ctx[1]
    else:
        i_tok, k_tok = ctx[1], ctx[0]
    print(f"  Step 6 — i={i_tok}, k={k_tok}")

    # Step 7: Remaining
    ab = list(Dec(d_K))
    a_tok = next(x for x in ab if dot(m_K, x) == top)
    b_tok = next(x for x in ab if x != a_tok)
    d_I = dot(e_D, i_tok)
    print(f"  Step 7 — a={a_tok}, b={b_tok}, d_I={d_I}")

    # Step 8: Triple
    known = {top, bot, e_I, d_K, m_K, m_I, e_M, e_D,
             i_tok, k_tok, a_tok, b_tok, d_I, p_tok}
    remaining = [x for x in domain if x not in known]
    e_S = sC = e_Delta = None
    for f, g in itertools.product(remaining, repeat=2):
        h = dot(f, g)
        if h in (top, bot, p_tok):
            continue
        if dot(h, e_D) == d_I:
            e_S, sC, e_Delta = f, g, h
            break
    print(f"  Step 8 — e_Sigma={e_S}, s_C={sC}, e_Delta={e_Delta}")

    result = {
        "top": top, "bot": bot, "p": p_tok,
        "e_I": e_I, "e_D": e_D, "e_M": e_M,
        "e_Sigma": e_S, "e_Delta": e_Delta,
        "i": i_tok, "k": k_tok, "a": a_tok, "b": b_tok,
        "d_I": d_I, "d_K": d_K, "m_I": m_I, "m_K": m_K, "s_C": sC,
    }
    print(f"\n  All 17 elements recovered.")
    return Keyword("top")


# ============================================================
# Table printer
# ============================================================

def print_table():
    """Print the 17×17 Cayley table."""
    w = max(len(a) for a in ATOMS) + 1
    header = " " * w + "".join(a.rjust(w) for a in ATOMS)
    print(header)
    print(" " * w + "-" * (w * len(ATOMS)))
    for x in ATOMS:
        row = x.rjust(w) + "".join(dot_d1(x, y).rjust(w) for y in ATOMS)
        print(row)


# ============================================================
# Formatter
# ============================================================

def format_val(v: Any) -> str:
    if isinstance(v, Literal):
        return format_val(v.value)
    if isinstance(v, HexByte):
        return f"0x{v.value:X}"
    if is_ok_result(v):
        return f"#ok[{format_val(ok_payload(v))}]"
    parts = err_parts(v)
    if parts is not None:
        code, detail = parts
        return f"#err[:{code} {format_val(detail)}]"
    decoded_string = decode_string(v)
    if decoded_string is not None:
        return f"\"{escape_string_literal(decoded_string)}\""
    split = split_char(v)
    if split is not None:
        ctx, byte_term = split
        byte_code = decode_byte(byte_term)
        if byte_code is not None:
            return f"#char[:{ctx} #byte[{format_byte_bits(byte_code)}]]"
    decoded_byte = decode_byte(v)
    if decoded_byte is not None:
        return f"#byte[{format_byte_bits(decoded_byte)}]"
    decoded_bit = decode_bit(v)
    if decoded_bit is not None:
        return f"#bit[{decoded_bit}]"
    if isinstance(v, Keyword):
        return f":{v.name}"
    if isinstance(v, Quoted):
        return f"'{format_val(v.expr)}"
    if isinstance(v, AppNode):
        return f"#app[{format_val(v.f)} {format_val(v.x)}]"
    if isinstance(v, Bundle):
        return f"#bundle[{format_val(v.f)} {format_val(v.x)}]"
    if isinstance(v, Partial):
        return f"#partial[{format_val(v.f)}]"
    if isinstance(v, ALUPartial1):
        return f"#alu1[{v.mode} :N{v.selector:X}]"
    if isinstance(v, ALUPartial2):
        return f"#alu2[{v.mode} :N{v.selector:X} :N{v.a:X}]"
    if isinstance(v, ALUCoutProbe):
        return f"#cout[{v.mode} :N{v.selector:X} :N{v.a:X}]"
    if isinstance(v, List):
        return "(" + " ".join(format_val(i) for i in v.items) + ")"
    if isinstance(v, Symbol):
        return v.name
    return str(v)


# ============================================================
# REPL
# ============================================================

def repl():
    """Interactive REPL."""
    print("Distinction Structures REPL")
    print("  43 atoms: 17 Δ₁ + 4 Δ₂ + 16 nibbles + 3 ALU dispatch + 2 ALU pred + N_SUCC")
    print('  DS-native text: bit -> byte -> char -> string ("hello")')
    print("  Type (discover!) to run self-discovery")
    print("  Type (table) to see the Cayley table")
    print("  Ctrl-D to exit\n")

    while True:
        try:
            line = input("ds> ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nBye.")
            break

        if not line or line.startswith(";"):
            continue

        try:
            exprs = parse(line)
            for expr in exprs:
                result = repl_eval(expr)
                print(f"=> {format_val(result)}")
        except Exception as e:
            print(f"Error: {e}")


def eval_string(text: str):
    """Evaluate a string of expressions."""
    exprs = parse(text)
    result = None
    for expr in exprs:
        result = repl_eval(expr)
    return result


def eval_file(path: str):
    """Evaluate a file."""
    with open(path) as f:
        text = f.read()
    exprs = parse(text)
    for expr in exprs:
        result = repl_eval(expr)
        print(f"=> {format_val(result)}")


# ============================================================
# Main
# ============================================================

def main():
    if len(sys.argv) > 1:
        try:
            if sys.argv[1] == "-e":
                result = eval_string(" ".join(sys.argv[2:]))
                print(format_val(result))
            else:
                eval_file(sys.argv[1])
        except Exception as e:
            print(f"Error: {e}")
            sys.exit(1)
    else:
        repl()


if __name__ == "__main__":
    main()

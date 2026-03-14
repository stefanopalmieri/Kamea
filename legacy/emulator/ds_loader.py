"""
ds_loader — Bridge between ds_repl.parse() AST and EmulatorHost.load_term() format.

Translates REPL AST nodes (Keyword, Symbol, List, Quoted, AppNode)
into the tuple format expected by the emulator: str atoms, (f, x) apps,
("QUOTED", inner) quoted terms.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from ds_repl import parse, Keyword, Symbol, List, Quoted, HexByte, AppNode
from emulator.cayley import NAME_TO_IDX
from emulator.fingerprint import FP_TOP


# ---------------------------------------------------------------------------
# REPL ASCII name → Cayley Unicode name mapping
# ---------------------------------------------------------------------------

REPL_TO_CAYLEY: dict[str, str] = {
    "top": "⊤",
    "bot": "⊥",
    "e_Sigma": "e_Σ",
    "e_Delta": "e_Δ",
}
# All other names (i, k, N0-NF, ALU_LOGIC, IO_PUT, W_ADD, etc.) are identical.

# REPL-only special forms that have no emulator equivalent
REPL_ONLY_FORMS = {
    "bit", "unbit", "bit?", "byte", "byte?", "char", "char?",
    "char-byte", "char-ctx", "string", "expand",
    "ok", "err", "ok?", "err?", "unwrap", "err-code", "err-data",
    "eval", "quote", "discover!", "table",
}


# ---------------------------------------------------------------------------
# RawWord wrapper — pre-evaluated machine word for def'd values
# ---------------------------------------------------------------------------

@dataclass
class RawWord:
    """A pre-evaluated 64-bit machine word (heap address embedded).

    Distinguishes 'this is a machine word to allocate on heap' from
    'this is an atom name for make_atom_word'.
    """
    word: int


# ---------------------------------------------------------------------------
# AST → emulator term translation
# ---------------------------------------------------------------------------

def _resolve_name(name: str) -> str:
    """Map a REPL atom name to a Cayley atom name."""
    if name in REPL_ONLY_FORMS:
        raise ValueError(
            f"'{name}' is a REPL-only form and cannot be used in the emulator. "
            f"This .ds file requires the REPL: uv run ds_repl.py <file>"
        )
    mapped = REPL_TO_CAYLEY.get(name, name)
    if mapped in NAME_TO_IDX:
        return mapped
    raise ValueError(f"Unknown atom name: {name!r}")


def ast_to_term(node, env: dict[str, RawWord]):
    """
    Recursively convert a ds_repl AST node into the emulator term format.

    Returns:
      - str: atom name (for Keyword/Symbol that maps to an atom)
      - tuple: (f_term, x_term) application or ("QUOTED", inner_term)
      - RawWord: pre-evaluated machine word (from env lookup)
    """
    # :keyword → atom name string
    if isinstance(node, Keyword):
        return _resolve_name(node.name)

    # bare symbol → env lookup or atom name
    if isinstance(node, Symbol):
        name = node.name
        if name in env:
            return env[name]
        return _resolve_name(name)

    # (a b c) → left-fold into ((a, b), c) application tuples
    if isinstance(node, List):
        items = node.items
        if not items:
            return _resolve_name("p")  # empty list → p

        # Handle special forms that appear as list items
        if isinstance(items[0], Symbol):
            form = items[0].name
            if form == "app" and len(items) == 3:
                # (app f x) → ((APP f) x) — creates a quoted app pair
                f_term = ast_to_term(items[1], env)
                x_term = ast_to_term(items[2], env)
                return (("APP", f_term), x_term)
            if form == "unapp" and len(items) == 2:
                # (unapp expr) → (UNAPP expr)
                inner = ast_to_term(items[1], env)
                return ("UNAPP", inner)
            if form == "quote" and len(items) == 2:
                inner = ast_to_term(items[1], env)
                return ("QUOTED", inner)
            if form == "if" and len(items) == 4:
                # (if cond then else) — resolve at translation time
                # The condition must already be in env as a RawWord
                cond_term = ast_to_term(items[1], env)
                if isinstance(cond_term, RawWord):
                    from emulator.machine import unpack_word, TAG_ATOM
                    tag, left, _, _ = unpack_word(cond_term.word)
                    is_true = (tag == TAG_ATOM and (left & 0x7F) == FP_TOP)
                    branch = items[2] if is_true else items[3]
                    return ast_to_term(branch, env)
                raise ValueError(
                    "if condition must be a def'd value (RawWord) "
                    "when used inside expressions"
                )

        # General case: left-fold application
        result = ast_to_term(items[0], env)
        for item in items[1:]:
            result = (result, ast_to_term(item, env))
        return result

    # 'expr → ("QUOTED", inner)
    if isinstance(node, Quoted):
        inner = ast_to_term(node.expr, env)
        return ("QUOTED", inner)

    # #app[f x] → (f, x)
    if isinstance(node, AppNode):
        f_term = ast_to_term(node.f, env)
        x_term = ast_to_term(node.x, env)
        return (f_term, x_term)

    # HexByte → not supported in emulator context
    if isinstance(node, HexByte):
        raise ValueError(f"HexByte literals not supported in emulator: {node!r}")

    # String literal → not supported as a term
    if isinstance(node, str):
        raise ValueError(f"String literals cannot be loaded into emulator: {node!r}")

    raise ValueError(f"Unknown AST node type: {type(node).__name__}: {node!r}")


# ---------------------------------------------------------------------------
# Statement classification
# ---------------------------------------------------------------------------

def classify_statement(node) -> tuple:
    """
    Classify a top-level AST node into a statement kind.

    Returns:
      ("def", name_str, expr_node)
      ("print", items_list)   — items may include raw strings for display
      ("if", cond_node, then_node, else_node)
      ("expr", node)
    """
    if isinstance(node, List):
        items = node.items
        if items and isinstance(items[0], Symbol):
            form = items[0].name

            if form == "def" and len(items) == 3:
                sym = items[1]
                if isinstance(sym, Symbol):
                    return ("def", sym.name, items[2])

            if form == "print" and len(items) >= 2:
                # Tag each arg: string literals get special handling
                print_args = []
                for arg in items[1:]:
                    if isinstance(arg, str):
                        print_args.append(("string", arg))
                    else:
                        print_args.append(("expr", arg))
                return ("print", print_args)

            if form == "if" and len(items) == 4:
                return ("if", items[1], items[2], items[3])

            if form == "do":
                # Unwrap do — return list of inner statements
                return ("do", items[1:])

    return ("expr", node)


# ---------------------------------------------------------------------------
# File / expression loading
# ---------------------------------------------------------------------------

def _flatten_stmts(nodes) -> list:
    """Flatten top-level (do ...) wrappers into a flat statement list."""
    result = []
    for node in nodes:
        classified = classify_statement(node)
        if classified[0] == "do":
            result.extend(_flatten_stmts(classified[1]))
        else:
            result.append(node)
    return result


def load_ds_file(path: str | Path) -> list:
    """Parse a .ds file and return a flat list of top-level AST nodes."""
    text = Path(path).read_text()
    nodes = parse(text)
    if not isinstance(nodes, list):
        nodes = [nodes]
    return _flatten_stmts(nodes)


def parse_expression(text: str) -> list:
    """Parse a single expression string and return AST nodes."""
    nodes = parse(text)
    if not isinstance(nodes, list):
        nodes = [nodes]
    return _flatten_stmts(nodes)

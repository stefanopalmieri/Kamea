#!/usr/bin/env python3
"""
Sigil-host bootstrap demo over multiprocessing.Pipe.

Model:
- Host control plane starts in healthy state, then enters "corrupted sigils" state.
- Exposed primitives are only:
  1) ALU: dot(x, y)
  2) Memory banks: read/write
  3) Boot ROM entry: kick_eval(bank, key) to run DS program from memory

The client:
- Detects broken state via memory flag.
- Probes ALU behavior from opaque tokens loaded from memory.
- Uploads a DS hello-world program into host memory.
- Triggers on-host eval and reads result back from memory.
"""

from __future__ import annotations

import argparse
import io
import hashlib
import itertools
import multiprocessing as mp
import pprint
import random
import sys
import re
import textwrap
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable
from contextlib import redirect_stdout

# Allow imports from repository root when launched via examples/ path.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

try:
    from colorama import Back, Fore, Style, init as colorama_init
except ModuleNotFoundError:
    class _AnsiFallback:
        BLACK = ""
        BLUE = ""
        CYAN = ""
        GREEN = ""
        MAGENTA = ""
        RED = ""
        WHITE = ""
        YELLOW = ""
        LIGHTBLACK_EX = ""
        LIGHTBLUE_EX = ""
        LIGHTCYAN_EX = ""
        LIGHTGREEN_EX = ""
        LIGHTMAGENTA_EX = ""
        LIGHTRED_EX = ""
        LIGHTWHITE_EX = ""
        LIGHTYELLOW_EX = ""
        BRIGHT = ""
        RESET_ALL = ""

    Back = _AnsiFallback()
    Fore = _AnsiFallback()
    Style = _AnsiFallback()

    def colorama_init(*_args, **_kwargs) -> None:
        return None

from delta2_true_blackbox import ALL_ATOMS, AppNode, Atom, Partial, Quote, UnappBundle, dot_iota

try:
    from rich.text import Text
    from textual.app import App, ComposeResult
    from textual.containers import Horizontal
    from textual.widgets import RichLog, Static

    TEXTUAL_AVAILABLE = True
except ModuleNotFoundError:
    TEXTUAL_AVAILABLE = False

colorama_init(autoreset=False)

TOKEN_BLANK_STYLE = Back.BLACK + Fore.WHITE

D1_SEMANTIC_STYLES = {
    "⊤": Back.YELLOW + Fore.BLACK,
    "⊥": Back.BLUE + Fore.WHITE,
    "i": Back.LIGHTBLUE_EX + Fore.BLACK,
    "k": Back.CYAN + Fore.BLACK,
    "a": Back.GREEN + Fore.BLACK,
    "b": Back.LIGHTGREEN_EX + Fore.BLACK,
    "e_I": Back.MAGENTA + Fore.WHITE,
    "e_D": Back.LIGHTYELLOW_EX + Fore.BLACK,
    "e_M": Back.LIGHTWHITE_EX + Fore.BLACK,
    "e_Σ": Back.RED + Fore.WHITE,
    "e_Δ": Back.LIGHTRED_EX + Fore.BLACK,
    "d_I": Back.WHITE + Fore.BLACK,
    "d_K": Back.LIGHTMAGENTA_EX + Fore.BLACK,
    "m_I": Back.LIGHTCYAN_EX + Fore.BLACK,
    "m_K": Back.LIGHTBLACK_EX + Fore.WHITE,
    "s_C": Back.LIGHTBLUE_EX + Fore.WHITE,
    "p": TOKEN_BLANK_STYLE,
}

TOKEN_PALETTE = (
    Back.BLUE + Fore.WHITE,
    Back.CYAN + Fore.BLACK,
    Back.GREEN + Fore.BLACK,
    Back.MAGENTA + Fore.WHITE,
    Back.YELLOW + Fore.BLACK,
    Back.RED + Fore.WHITE,
    Back.LIGHTBLUE_EX + Fore.BLACK,
    Back.LIGHTCYAN_EX + Fore.BLACK,
    Back.LIGHTGREEN_EX + Fore.BLACK,
    Back.LIGHTMAGENTA_EX + Fore.BLACK,
    Back.LIGHTYELLOW_EX + Fore.BLACK,
    Back.LIGHTWHITE_EX + Fore.BLACK,
)

TOKEN_GLYPH_PALETTE = (
    Fore.BLUE,
    Fore.CYAN,
    Fore.GREEN,
    Fore.MAGENTA,
    Fore.YELLOW,
    Fore.RED,
    Fore.LIGHTBLUE_EX,
    Fore.LIGHTCYAN_EX,
    Fore.LIGHTGREEN_EX,
    Fore.LIGHTMAGENTA_EX,
    Fore.LIGHTYELLOW_EX,
    Fore.WHITE,
)

D1_SEMANTIC_GLYPH_STYLES = {
    "⊤": Fore.YELLOW + Style.BRIGHT,
    "⊥": Fore.BLUE + Style.BRIGHT,
    "i": Fore.LIGHTBLUE_EX + Style.BRIGHT,
    "k": Fore.CYAN + Style.BRIGHT,
    "a": Fore.GREEN + Style.BRIGHT,
    "b": Fore.LIGHTGREEN_EX + Style.BRIGHT,
    "e_I": Fore.MAGENTA + Style.BRIGHT,
    "e_D": Fore.LIGHTYELLOW_EX + Style.BRIGHT,
    "e_M": Fore.WHITE + Style.BRIGHT,
    "e_Σ": Fore.RED + Style.BRIGHT,
    "e_Δ": Fore.LIGHTRED_EX + Style.BRIGHT,
    "d_I": Fore.WHITE,
    "d_K": Fore.LIGHTMAGENTA_EX,
    "m_I": Fore.LIGHTCYAN_EX,
    "m_K": Fore.LIGHTBLACK_EX,
    "s_C": Fore.LIGHTBLUE_EX,
    "p": Fore.LIGHTBLACK_EX,
}

D1_CANONICAL_ORDER = [
    "⊤",
    "⊥",
    "i",
    "k",
    "a",
    "b",
    "e_I",
    "e_D",
    "e_M",
    "e_Σ",
    "e_Δ",
    "d_I",
    "d_K",
    "m_I",
    "m_K",
    "s_C",
    "p",
]

WIZARD_TEMPLATE = [
    "     ****",
    "     **  *",
    "    ***",
    "    ****",
    "   *******",
    "    ****",
    "    ****",
    "    *****",
    "   ** * **",
    "   ******* **",
    "           **",
    "   ******* *",
    "   ******* *",
    "    *****  *",
    "    *****  *",
    "    *****",
    "    *****",
    "    *   *",
    "    *   *",
    "    *   *",
    "    *   *",
    " *  *   *",
    "  ***********",
    "  **********",
    "  **********",
    "  *********",
    "  *********",
    "  *********",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
]

CUSTOM_TEMPLATE_ORDER = [
    "⊤",
    "⊥",
    "i",
    "k",
    "a",
    "b",
    "e_I",
    "e_D",
    "e_M",
    "e_Σ",
    "e_Δ",
    "d_I",
    "m_I",
    "QUOTE",
    "d_K",
    "m_K",
    "s_C",
    "UNAPP",
    "p",
    "EVAL",
    "APP",
]

# Rainbow palette derived from fontgen.js "Rainbow 3" dark colors.
RAINBOW_HEADER_COLORS = (
    (255, 40, 40),
    (255, 120, 0),
    (255, 180, 0),
    (255, 220, 0),
    (220, 255, 0),
    (120, 255, 0),
    (0, 255, 80),
    (0, 255, 160),
    (0, 200, 255),
    (0, 120, 255),
    (120, 80, 255),
    (255, 0, 200),
)

TOKEN_HEX_PALETTE = (
    "#2d7bff",
    "#00c9d8",
    "#43d45f",
    "#d86bd5",
    "#ffd34f",
    "#ff6363",
    "#63b2ff",
    "#6fe8ea",
    "#88f080",
    "#ef95ef",
    "#ffe27f",
    "#f4f7ff",
)

SEMANTIC_HEX_COLORS = {
    "⊤": "#f5e66f",
    "⊥": "#4c72e5",
    "i": "#6bc1ff",
    "k": "#64d9e7",
    "a": "#66d668",
    "b": "#95ec78",
    "e_I": "#d96ef3",
    "e_D": "#ffe27f",
    "e_M": "#f3f7ff",
    "e_Σ": "#ff6a6a",
    "e_Δ": "#ff9d83",
    "d_I": "#ffffff",
    "d_K": "#d8a7ff",
    "m_I": "#8fefff",
    "m_K": "#8a9099",
    "s_C": "#8db5ff",
    "p": "#4b515c",
    "QUOTE": "#f47cff",
    "EVAL": "#7de0ff",
    "APP": "#ff9e9e",
    "UNAPP": "#8ef1d2",
}

CLIENT_SEMANTIC_HEX_COLORS = {
    "⊤": "#9fd8ff",
    "⊥": "#3d7edb",
    "i": "#7de8ff",
    "k": "#55d3ff",
    "a": "#63f0c3",
    "b": "#8ceeb7",
    "e_I": "#8da6ff",
    "e_D": "#f4ed8a",
    "e_M": "#dff6ff",
    "e_Σ": "#ff9fbb",
    "e_Δ": "#ffbf9a",
    "d_I": "#edf7ff",
    "d_K": "#b2c0ff",
    "m_I": "#9ef2ff",
    "m_K": "#8f98ad",
    "s_C": "#7ba9ff",
    "p": "#51607a",
    "QUOTE": "#96a2ff",
    "EVAL": "#7de0ff",
    "APP": "#ffc8a6",
    "UNAPP": "#8ef1d2",
}

TEMPLATE_STAR_COUNT = sum(row.count("*") for row in WIZARD_TEMPLATE if row)


def _ansi_rgb_fg(rgb: tuple[int, int, int]) -> str:
    r, g, b = rgb
    return f"\033[38;2;{r};{g};{b}m"


def _render_rainbow_stripe_line(
    line: str,
    row_idx: int,
    colors: tuple[tuple[int, int, int], ...],
) -> str:
    if not line:
        return ""

    parts: list[str] = []
    start = 0 if (row_idx % 2) else -1
    for col in range(start, len(line), 2):
        chunk = line[max(0, col) : col + 2]
        if not chunk:
            continue
        color_idx = (row_idx // 2 + max(0, col + 2) // 2) % len(colors)
        parts.append(f"{_ansi_rgb_fg(colors[color_idx])}{chunk}")
    parts.append(Style.RESET_ALL)
    return "".join(parts)


def print_rainbow_ascii_header() -> None:
    header_path = Path(__file__).with_name("ascii_header.txt")
    try:
        header_text = header_path.read_text(encoding="utf-8").rstrip("\n")
    except OSError:
        return

    if not header_text:
        return

    lines = header_text.splitlines()
    styled_lines = [
        _render_rainbow_stripe_line(line, row_idx, RAINBOW_HEADER_COLORS)
        for row_idx, line in enumerate(lines)
    ]
    print("\n".join(styled_lines) + Style.RESET_ALL)


def stable_term_repr(v: Any) -> str:
    if isinstance(v, str):
        return v
    if isinstance(v, Atom):
        return f"atom:{v.name}"
    if isinstance(v, Quote):
        return f"quote({stable_term_repr(v.term)})"
    if isinstance(v, AppNode):
        return f"app({stable_term_repr(v.f)},{stable_term_repr(v.x)})"
    if isinstance(v, UnappBundle):
        return f"bundle({stable_term_repr(v.f)},{stable_term_repr(v.x)})"
    if isinstance(v, Partial):
        return f"partial({v.op},{stable_term_repr(v.a)})"
    return repr(v)


def default_symbol_cells() -> list[str]:
    base = [*D1_CANONICAL_ORDER, "QUOTE", "EVAL", "APP", "UNAPP"]
    return [base[i % len(base)] for i in range(TEMPLATE_STAR_COUNT)]


def sample_wizard_cells_from_table(
    domain: list[str],
    dot_fn,
    role_of_token: dict[str, str] | None = None,
    blank_token: str | None = None,
) -> tuple[list[str], str | None]:
    if not domain:
        return default_symbol_cells(), blank_token

    token_counts = {str(tok): 0 for tok in domain}
    display_values: list[str] = []

    for x in domain:
        for y in domain:
            out = dot_fn(x, y)
            if isinstance(out, str) and out in token_counts:
                token_counts[out] += 1
            if role_of_token and isinstance(out, str) and out in role_of_token:
                display_values.append(role_of_token[out])
            else:
                display_values.append(stable_term_repr(out))

    if blank_token is None and token_counts:
        ranked = sorted(token_counts.items(), key=lambda kv: (-kv[1], kv[0]))
        blank_token = ranked[0][0]

    blank_display = "p" if role_of_token else blank_token
    if blank_display is None:
        nonblank = display_values
    else:
        nonblank = [v for v in display_values if v != blank_display]

    if not nonblank:
        nonblank = display_values[:1] if display_values else ["p"]

    if TEMPLATE_STAR_COUNT <= len(nonblank):
        sampled = nonblank[:TEMPLATE_STAR_COUNT]
    else:
        sampled = [nonblank[i % len(nonblank)] for i in range(TEMPLATE_STAR_COUNT)]
    return sampled, blank_token


def build_client_canonical_cells() -> list[str]:
    domain = [atom.name for atom in ALL_ATOMS]
    role_of_token = {name: name for name in domain}
    atom_of_name = {atom.name: atom for atom in ALL_ATOMS}

    def canonical_dot(x: str, y: str) -> Any:
        out = dot_iota(atom_of_name[x], atom_of_name[y])
        return out.name if isinstance(out, Atom) else out

    cells, _ = sample_wizard_cells_from_table(
        domain=domain,
        dot_fn=canonical_dot,
        role_of_token=role_of_token,
        blank_token="p",
    )
    return cells


def host_main(conn, seed: int = 17, prefix: str = "h") -> None:
    """Host device process: only ALU + memory + kick_eval."""
    labels = [f"{prefix}{idx:02d}" for idx in range(len(ALL_ATOMS))]
    state: dict[str, Any] = {}
    rng = random.SystemRandom()

    def most_common_output_token(domain: list[str], dot_fn) -> str | None:
        counts = {tok: 0 for tok in domain}
        for x in domain:
            for y in domain:
                out = dot_fn(x, y)
                if isinstance(out, str) and out in counts:
                    counts[out] += 1
        ranked = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
        return ranked[0][0] if ranked else None

    def install_mapping(scramble_seed: int) -> None:
        local = random.Random(scramble_seed)
        atoms = ALL_ATOMS.copy()
        local.shuffle(atoms)

        true_to_hidden = {atoms[i]: labels[i] for i in range(len(atoms))}
        hidden_to_true = {labels[i]: atoms[i] for i in range(len(atoms))}
        domain = labels.copy()

        def to_true(v: Any) -> Any:
            return hidden_to_true[v] if isinstance(v, str) and v in hidden_to_true else v

        def to_hidden(v: Any) -> Any:
            return true_to_hidden[v] if isinstance(v, Atom) else v

        def dot_oracle(xh: Any, yh: Any) -> Any:
            return to_hidden(dot_iota(to_true(xh), to_true(yh)))

        role_tokens = {role: true_to_hidden[Atom(role)] for role in D1_CANONICAL_ORDER}

        state["seed"] = scramble_seed
        state["domain"] = domain
        state["dot_oracle"] = dot_oracle
        state["current_role_tokens"] = role_tokens
        state["blank_token"] = most_common_output_token(domain, dot_oracle)

    def runtime_self_check() -> tuple[bool, str]:
        runtime_map = state.get("runtime_role_tokens", {})
        if not isinstance(runtime_map, dict):
            return False, "runtime mapping unavailable"
        missing = [r for r in D1_CANONICAL_ORDER if r not in runtime_map]
        if missing:
            return False, f"runtime mapping missing roles: {missing}"

        checks = [
            ("e_D", "i", "d_I"),
            ("e_D", "k", "d_K"),
            ("e_M", "i", "m_I"),
            ("m_I", "p", "⊥"),
            ("⊤", "p", "⊤"),
        ]
        for left_role, right_role, expected_role in checks:
            left_tok = runtime_map[left_role]
            right_tok = runtime_map[right_role]
            expected_tok = runtime_map[expected_role]
            got = state["dot_oracle"](left_tok, right_tok)
            if got != expected_tok:
                return (
                    False,
                    f"runtime mapping mismatch on dot({left_role}, {right_role}): "
                    f"expected {expected_role}={expected_tok}, got {got}",
                )
        return True, "ok"

    def trigger_radiation_event() -> int:
        scramble_seed = rng.randrange(1, 2**31)
        install_mapping(scramble_seed)
        state["health"] = "corrupted sigils"
        state["radiation_happened"] = True
        memory.setdefault("sys", {})["health"] = state["health"]
        memory.setdefault("sys", {})["domain"] = state["domain"]
        memory.setdefault("sys", {})["scramble_seed"] = scramble_seed
        return scramble_seed

    def stable_term(v: Any) -> str:
        if isinstance(v, str):
            return f"tok:{v}"
        if isinstance(v, Atom):
            return f"atom:{v.name}"
        if isinstance(v, Quote):
            return f"quote({stable_term(v.term)})"
        if isinstance(v, AppNode):
            return f"app({stable_term(v.f)},{stable_term(v.x)})"
        if isinstance(v, UnappBundle):
            return f"bundle({stable_term(v.f)},{stable_term(v.x)})"
        if isinstance(v, Partial):
            return f"partial({v.op},{stable_term(v.a)})"
        return repr(v)

    def table_fingerprint_and_matrix(
        order: list[str] | None = None,
        role_of_token: dict[str, str] | None = None,
    ) -> tuple[str, list[str], list[list[str]]]:
        domain = order if order else state["domain"]
        rows = []
        display_matrix: list[list[str]] = []
        for x in domain:
            row = []
            display_row: list[str] = []
            for y in domain:
                out = state["dot_oracle"](x, y)
                if role_of_token and isinstance(out, str) and out in role_of_token:
                    role_name = role_of_token[out]
                    row.append(f"role:{role_name}")
                    display_row.append(role_name)
                else:
                    stable = stable_term(out)
                    row.append(stable)
                    display_row.append(out if isinstance(out, str) else stable)
            rows.append("|".join(row))
            display_matrix.append(display_row)
        payload = "\n".join(rows).encode("utf-8")
        digest = hashlib.sha256(payload).digest()
        fingerprint = digest.hex()[:16]
        return fingerprint, domain, display_matrix

    def token_style(token: str, blank_token: str | None, glyph: bool = False) -> str:
        if blank_token is not None and token == blank_token:
            return Fore.LIGHTBLACK_EX if glyph else TOKEN_BLANK_STYLE
        n = sum(ord(c) for c in token)
        if glyph:
            return TOKEN_GLYPH_PALETTE[n % len(TOKEN_GLYPH_PALETTE)]
        return TOKEN_PALETTE[n % len(TOKEN_PALETTE)]

    def style_for_cell(
        value: str,
        role_of_token: dict[str, str] | None,
        blank_token: str | None,
    ) -> str:
        if role_of_token and value in D1_SEMANTIC_GLYPH_STYLES:
            return D1_SEMANTIC_GLYPH_STYLES[value]
        if role_of_token and value in {"QUOTE", "EVAL", "APP", "UNAPP"}:
            return token_style(value, None, glyph=True)
        if len(value) >= 2 and value[1:].isdigit():
            return token_style(value, blank_token, glyph=True)
        if value.startswith("quote("):
            return Fore.LIGHTMAGENTA_EX
        if value.startswith("partial("):
            return Fore.LIGHTYELLOW_EX
        if value.startswith("app("):
            return Fore.LIGHTRED_EX
        if value.startswith("bundle("):
            return Fore.LIGHTCYAN_EX
        if value.startswith("atom:"):
            return Fore.WHITE
        return Fore.LIGHTBLACK_EX

    def print_color_table(
        label: str,
        fingerprint: str,
        order: list[str],
        matrix: list[list[str]],
        role_of_token: dict[str, str] | None,
        blank_token: str | None,
    ) -> None:
        print(f"[host] {label} color table (seed={state['seed']}, fp={fingerprint})")
        template_cells = sum(row.count("*") for row in WIZARD_TEMPLATE)
        matrix_h = len(matrix)
        matrix_w = len(matrix[0]) if matrix_h else 0
        if matrix_h == 0 or matrix_w == 0:
            print("[host] no table data available for mascot render")
            return

        print(
            f"[host] mascot fill: template_cells={template_cells} "
            f"source_cells={matrix_h * matrix_w} order_size={len(order)}"
        )
        def is_blank_cell_value(value: str) -> bool:
            if role_of_token:
                return value == "p"
            return blank_token is not None and value == blank_token

        nonblank_vals = [
            value for row_vals in matrix for value in row_vals if not is_blank_cell_value(value)
        ]
        if not nonblank_vals:
            nonblank_vals = [matrix[0][0]]
        if template_cells <= len(nonblank_vals):
            # Greedy consumption in row-major order (matches template designer).
            sampled_vals = nonblank_vals[:template_cells]
        else:
            sampled_vals = [nonblank_vals[i % len(nonblank_vals)] for i in range(template_cells)]
        print(f"[host] mascot source nonblank cells={len(nonblank_vals)}")

        star_idx = 0
        for tr, row in enumerate(WIZARD_TEMPLATE):
            parts = []
            for tc, ch in enumerate(row):
                if ch == "*":
                    sampled = sampled_vals[star_idx]
                    style = style_for_cell(sampled, role_of_token, blank_token)
                    parts.append(f"{style}█{Style.RESET_ALL}")
                    star_idx += 1
                else:
                    parts.append(" ")
            print(f"[host] {''.join(parts)}")
        if role_of_token:
            legend = " ".join(
                f"{D1_SEMANTIC_STYLES[name]} {name} {Style.RESET_ALL}" for name in D1_CANONICAL_ORDER
            )
            print(f"[host] semantic legend: {legend}")
        else:
            print("[host] legend: cell color = opaque token/structure class (naive host view)")
            if blank_token is not None:
                print(
                    "[host] blank assumption: "
                    f"most-common output token {blank_token} uses p-style blank color"
                )

    # Start in a healthy state with a valid runtime mapping cache.
    install_mapping(seed)
    state["health"] = "healthy"
    state["radiation_happened"] = False
    state["recovered_mapping"] = {}
    state["runtime_role_tokens"] = dict(state["current_role_tokens"])

    memory: dict[str, dict[str, Any]] = {
        "sys": {
            "health": state["health"],
            "domain": state["domain"],
            "scramble_seed": state["seed"],
        },
        "prog": {},
        "out": {},
    }

    while True:
        msg = conn.recv()
        cmd = msg.get("cmd")

        if cmd == "dot":
            x = msg.get("x")
            y = msg.get("y")
            conn.send({"ok": True, "value": state["dot_oracle"](x, y)})
            continue

        if cmd == "scramble":
            requested = msg.get("seed")
            scramble_seed = int(requested) if requested is not None else rng.randrange(1, 2**31)
            install_mapping(scramble_seed)
            state["health"] = "corrupted sigils"
            memory.setdefault("sys", {})["domain"] = state["domain"]
            memory.setdefault("sys", {})["scramble_seed"] = scramble_seed
            memory.setdefault("sys", {})["health"] = state["health"]
            conn.send({"ok": True, "seed": scramble_seed, "domain_size": len(state["domain"])})
            continue

        if cmd == "apply_recovery":
            role_of_token_raw = msg.get("role_of_token")
            if not isinstance(role_of_token_raw, dict):
                conn.send({"ok": False, "error": "role_of_token must be a dict[token->role]"})
                continue
            role_of_token = {str(k): str(v) for k, v in role_of_token_raw.items()}
            expected_roles = set(D1_CANONICAL_ORDER)
            present_roles = set(role_of_token.values())
            if not expected_roles.issubset(present_roles):
                missing = sorted(expected_roles - present_roles)
                conn.send({"ok": False, "error": f"recovery mapping missing roles: {missing}"})
                continue
            state["recovered_mapping"] = role_of_token
            state["runtime_role_tokens"] = {role: token for token, role in role_of_token.items()}
            state["health"] = "healthy"
            memory.setdefault("sys", {})["health"] = state["health"]
            memory.setdefault("sys", {})["recovered_roles"] = len(role_of_token)
            conn.send({"ok": True, "accepted": len(role_of_token), "health": state["health"]})
            continue

        if cmd == "table_art":
            order_raw = msg.get("order")
            role_of_token_raw = msg.get("role_of_token")
            label = str(msg.get("label", "table view"))
            order = None
            if isinstance(order_raw, list) and order_raw:
                order = [str(x) for x in order_raw]
            role_of_token = None
            if isinstance(role_of_token_raw, dict):
                role_of_token = {str(k): str(v) for k, v in role_of_token_raw.items()}
            fingerprint, ordered_domain, matrix = table_fingerprint_and_matrix(
                order=order,
                role_of_token=role_of_token,
            )
            print_color_table(
                label=label,
                fingerprint=fingerprint,
                order=ordered_domain,
                matrix=matrix,
                role_of_token=role_of_token,
                blank_token=state.get("blank_token"),
            )
            conn.send(
                {
                    "ok": True,
                    "fingerprint": fingerprint,
                    "blank_token": state.get("blank_token"),
                }
            )
            continue

        if cmd == "mem_write":
            bank = str(msg.get("bank"))
            key = str(msg.get("key"))
            val = msg.get("value")
            memory.setdefault(bank, {})[key] = val
            conn.send({"ok": True})
            continue

        if cmd == "mem_read":
            bank = str(msg.get("bank"))
            key = str(msg.get("key"))
            val = memory.get(bank, {}).get(key)
            conn.send({"ok": True, "value": val})
            continue

        if cmd == "kick_eval":
            bank = str(msg.get("bank", "prog"))
            key = str(msg.get("key", "main"))
            source = memory.get(bank, {}).get(key)

            if not isinstance(source, str):
                conn.send({"ok": False, "error": "program slot is empty or non-string"})
                continue

            ok_runtime, msg_runtime = runtime_self_check()
            if not ok_runtime:
                memory.setdefault("out", {})["stdout"] = ""
                memory.setdefault("out", {})["result"] = msg_runtime
                memory.setdefault("out", {})["status"] = "error"
                conn.send({"ok": False, "error": msg_runtime})
                continue

            try:
                from ds_repl import ENV, eval_string, format_val

                ENV.clear()
                buf = io.StringIO()
                with redirect_stdout(buf):
                    result = eval_string(source)
                stdout_text = buf.getvalue()
                formatted = format_val(result)

                memory.setdefault("out", {})["stdout"] = stdout_text
                memory.setdefault("out", {})["result"] = formatted
                memory.setdefault("out", {})["status"] = "ok"

                if not state["radiation_happened"]:
                    trigger_radiation_event()
                conn.send({"ok": True, "stdout": stdout_text, "result": formatted})
            except Exception as e:
                memory.setdefault("out", {})["stdout"] = ""
                memory.setdefault("out", {})["result"] = f"Error: {e}"
                memory.setdefault("out", {})["status"] = "error"
                conn.send({"ok": False, "error": str(e)})
            continue

        if cmd == "shutdown":
            conn.send({"ok": True})
            break

        conn.send({"ok": False, "error": f"unknown command: {cmd}"})


@dataclass
class RemoteHost:
    conn: Any
    trace_channel: bool = True
    trace_cmds: tuple[str, ...] = (
        "mem_read",
        "mem_write",
        "kick_eval",
        "scramble",
        "apply_recovery",
        "table_art",
        "dot",
        "shutdown",
    )
    color_mode: str = "token"
    known_tokens: set[str] = field(default_factory=set)
    role_of_token: dict[str, str] = field(default_factory=dict)
    blank_token: str | None = None
    token_re: re.Pattern[str] | None = None

    def _token_style(self, token: str) -> str:
        if self.color_mode == "canonical":
            role = self.role_of_token.get(token)
            if role in D1_SEMANTIC_STYLES:
                return D1_SEMANTIC_STYLES[role]
        if self.color_mode == "token" and self.blank_token is not None and token == self.blank_token:
            return TOKEN_BLANK_STYLE
        n = sum(ord(c) for c in token)
        return TOKEN_PALETTE[n % len(TOKEN_PALETTE)]

    def _compile_token_re(self) -> None:
        if not self.known_tokens:
            self.token_re = None
            return
        escaped = sorted((re.escape(t) for t in self.known_tokens), key=len, reverse=True)
        self.token_re = re.compile(r"\b(" + "|".join(escaped) + r")\b")

    def set_token_mode(self, domain: list[str], blank_token: str | None = None) -> None:
        self.color_mode = "token"
        self.blank_token = blank_token
        self.known_tokens = {str(t) for t in domain}
        self._compile_token_re()

    def set_canonical_mode(self, role_of_token: dict[str, str]) -> None:
        self.color_mode = "canonical"
        self.role_of_token = {str(k): str(v) for k, v in role_of_token.items()}
        self.known_tokens = set(self.role_of_token.keys())
        self._compile_token_re()

    def _colorize_text(self, text: str) -> str:
        if self.token_re is None:
            return text

        def repl(match: re.Match[str]) -> str:
            token = match.group(1)
            style = self._token_style(token)
            if self.color_mode == "canonical" and token in self.role_of_token:
                label = f"{token}/{self.role_of_token[token]}"
            else:
                label = token
            return f"{style}{label}{Style.RESET_ALL}"

        return self.token_re.sub(repl, text)

    def _trace(self, direction: str, cmd: str, payload: dict[str, Any]) -> None:
        if not self.trace_channel:
            return
        if cmd not in self.trace_cmds:
            return
        text = pprint.pformat(payload, width=100, compact=True)
        text = self._colorize_text(text)
        print(f"{direction} {text}")

    def _request(self, cmd: str, allow_error: bool = False, **payload) -> dict[str, Any]:
        req = {"cmd": cmd, **payload}
        self._trace("client -> host", cmd, req)
        self.conn.send(req)
        resp = self.conn.recv()
        self._trace("host -> client", cmd, resp)
        if not resp.get("ok") and not allow_error:
            raise RuntimeError(resp.get("error", "request failed"))
        return resp

    def dot(self, x: Any, y: Any) -> Any:
        return self._request("dot", x=x, y=y)["value"]

    def scramble(self, seed: int | None = None) -> int:
        payload: dict[str, Any] = {}
        if seed is not None:
            payload["seed"] = seed
        return int(self._request("scramble", **payload)["seed"])

    def mem_write(self, bank: str, key: str, value: Any) -> None:
        self._request("mem_write", bank=bank, key=key, value=value)

    def mem_read(self, bank: str, key: str) -> Any:
        return self._request("mem_read", bank=bank, key=key)["value"]

    def kick_eval(self, bank: str = "prog", key: str = "main") -> dict[str, Any]:
        return self._request("kick_eval", allow_error=True, bank=bank, key=key)

    def table_art(
        self,
        label: str,
        order: list[str] | None = None,
        role_of_token: dict[str, str] | None = None,
    ) -> str:
        payload: dict[str, Any] = {"label": label}
        if order is not None:
            payload["order"] = order
        if role_of_token is not None:
            payload["role_of_token"] = role_of_token
        resp = self._request("table_art", **payload)
        blank_token = resp.get("blank_token")
        if isinstance(blank_token, str):
            self.blank_token = blank_token
        return str(resp["fingerprint"])

    def apply_recovery(self, role_of_token: dict[str, str]) -> dict[str, Any]:
        return self._request("apply_recovery", role_of_token=role_of_token)

    def shutdown(self) -> None:
        self._request("shutdown")


def discover_d1_with_logs(
    domain: list[str],
    dot_fn,
    logger: Callable[[str], None] = print,
) -> dict[str, Any]:
    """Client-side blackbox recovery with per-symbol logging."""

    def left_image(xh: Any) -> set[Any]:
        return {dot_fn(xh, y) for y in domain}

    def left_image_in_domain(xh: Any) -> set[Any]:
        return {dot_fn(xh, y) for y in domain if dot_fn(xh, y) in domain}

    logger("[discover] step 1: find booleans (left-absorbers)")
    absorbers = [x for x in domain if all(dot_fn(x, y) == x for y in domain)]
    if len(absorbers) != 2:
        raise RuntimeError(f"expected 2 absorbers, got {len(absorbers)}")
    b1, b2 = absorbers
    logger(f"[discover] candidates for booleans: {b1}, {b2}")

    def testers_for(top: Any, bot: Any) -> list[Any]:
        out = []
        for x in domain:
            if x in (top, bot):
                continue
            im = left_image(x)
            if im.issubset({top, bot}) and len(im) == 2:
                out.append(x)
        return out

    logger("[discover] step 2: orient booleans and find testers")
    chosen: tuple[Any, Any, list[Any], Any] | None = None
    for top, bot in [(b1, b2), (b2, b1)]:
        testers = testers_for(top, bot)
        if len(testers) != 4:
            continue
        dec = lambda t, top=top: {y for y in domain if dot_fn(t, y) == top}
        sizes = sorted(len(dec(t)) for t in testers)
        if sizes[0] == 1 and sizes[1] == 2 and sizes[2] == 2:
            chosen = (top, bot, testers, dec)
            break
    if chosen is None:
        raise RuntimeError("failed to orient booleans")
    top, bot, testers, dec = chosen
    logger(f"[discover] identified ⊤ = {top}")
    logger(f"[discover] identified ⊥ = {bot}")

    logger("[discover] step 2.5: find p")
    p_candidates = [
        x
        for x in domain
        if x not in (top, bot)
        and x not in testers
        and top in left_image_in_domain(x)
    ]
    if len(p_candidates) != 1:
        raise RuntimeError(f"expected 1 p candidate, got {p_candidates}")
    p_tok = p_candidates[0]
    logger(f"[discover] identified p = {p_tok}")

    logger("[discover] step 3: identify m_I and m_K from tester cardinalities")
    sizes = {t: len(dec(t)) for t in testers}
    m_k = [t for t in testers if sizes[t] == 1][0]
    m_i = max(testers, key=lambda t: sizes[t])
    two = [t for t in testers if sizes[t] == 2]
    if len(two) != 2:
        raise RuntimeError(f"expected 2 testers with |Dec|=2, got {len(two)}")
    logger(f"[discover] identified m_K = {m_k}")
    logger(f"[discover] identified m_I = {m_i}")

    logger("[discover] step 4: distinguish e_I vs d_K")
    def has_productive_args(decoded_set: set[Any]) -> bool:
        for f in domain:
            if f in (top, bot) or f in testers:
                continue
            for x in decoded_set:
                out = dot_fn(f, x)
                if out in domain and out not in (top, bot, p_tok):
                    return True
        return False

    t1, t2 = two
    e_i, d_k = (t1, t2) if has_productive_args(dec(t1)) else (t2, t1)
    ctx = list(dec(e_i))
    logger(f"[discover] identified e_I = {e_i}")
    logger(f"[discover] identified d_K = {d_k}")

    logger("[discover] step 5: find e_D and e_M")
    def is_encoder(f: Any) -> bool:
        if f in (top, bot) or f in testers:
            return False
        outs = [dot_fn(f, x) for x in ctx]
        return (
            all(o in domain for o in outs)
            and all(o not in (top, bot, p_tok) for o in outs)
        )

    enc = [f for f in domain if is_encoder(f)]
    if len(enc) != 2:
        raise RuntimeError(f"expected 2 encoders, got {len(enc)}")

    def maps_both_to_testers(f: Any) -> bool:
        return all(dot_fn(f, x) in testers for x in ctx)

    e_m = enc[0] if maps_both_to_testers(enc[0]) else enc[1]
    e_d = enc[1] if e_m == enc[0] else enc[0]
    logger(f"[discover] identified e_M = {e_m}")
    logger(f"[discover] identified e_D = {e_d}")

    logger("[discover] step 6: distinguish i and k")
    out_a, out_b = dot_fn(e_m, ctx[0]), dot_fn(e_m, ctx[1])
    if len(dec(out_a)) > len(dec(out_b)):
        i_tok, k_tok = ctx[0], ctx[1]
    else:
        i_tok, k_tok = ctx[1], ctx[0]
    logger(f"[discover] identified i = {i_tok}")
    logger(f"[discover] identified k = {k_tok}")

    logger("[discover] step 7: identify a, b, d_I")
    ab = list(dec(d_k))
    a_tok = next(x for x in ab if dot_fn(m_k, x) == top)
    b_tok = next(x for x in ab if x != a_tok)
    d_i = dot_fn(e_d, i_tok)
    logger(f"[discover] identified a = {a_tok}")
    logger(f"[discover] identified b = {b_tok}")
    logger(f"[discover] identified d_I = {d_i}")

    logger("[discover] step 8: identify e_Σ, s_C, e_Δ")
    known = {
        top,
        bot,
        e_i,
        d_k,
        m_k,
        m_i,
        e_m,
        e_d,
        i_tok,
        k_tok,
        a_tok,
        b_tok,
        d_i,
        p_tok,
    }
    remaining = [x for x in domain if x not in known]
    e_sigma = s_c = e_delta = None
    for f, g in itertools.product(remaining, repeat=2):
        h = dot_fn(f, g)
        if h not in domain or h in (top, bot, p_tok):
            continue
        if dot_fn(h, e_d) == d_i:
            e_sigma, s_c, e_delta = f, g, h
            break
    if e_sigma is None:
        raise RuntimeError("failed to identify e_Σ/s_C/e_Δ")
    logger(f"[discover] identified e_Σ = {e_sigma}")
    logger(f"[discover] identified s_C = {s_c}")
    logger(f"[discover] identified e_Δ = {e_delta}")

    recovered = {
        "⊤": top,
        "⊥": bot,
        "p": p_tok,
        "e_I": e_i,
        "e_D": e_d,
        "e_M": e_m,
        "e_Σ": e_sigma,
        "e_Δ": e_delta,
        "i": i_tok,
        "k": k_tok,
        "a": a_tok,
        "b": b_tok,
        "d_I": d_i,
        "d_K": d_k,
        "m_I": m_i,
        "m_K": m_k,
        "s_C": s_c,
        "_testers": set(testers),
    }
    return recovered


def discover_d2_extras_with_logs(
    domain: list[str],
    dot_fn,
    known_tokens: set[str],
    logger: Callable[[str], None] = print,
) -> dict[str, str]:
    """Recover QUOTE/EVAL/APP/UNAPP from remaining opaque tokens."""
    remaining = [str(x) for x in domain if str(x) not in known_tokens]
    if len(remaining) != 4:
        raise RuntimeError(f"expected 4 Δ2 extras, got {len(remaining)}: {remaining}")
    logger(f"[discover] Δ2 step 1: remaining extras candidates = {remaining}")

    def is_structure_producer(tok: str) -> bool:
        outs = [dot_fn(tok, x) for x in domain]
        return all(o not in domain for o in outs)

    producers = [tok for tok in remaining if is_structure_producer(tok)]
    if len(producers) != 2:
        raise RuntimeError(f"expected 2 structure producers, got {producers}")
    logger(f"[discover] Δ2 step 2: structure producers = {producers}")

    probe_arg = str(domain[0])
    quote_tok = next((t for t in producers if isinstance(dot_fn(t, probe_arg), Quote)), None)
    app_tok = next((t for t in producers if isinstance(dot_fn(t, probe_arg), Partial)), None)
    if quote_tok is None or app_tok is None:
        raise RuntimeError("failed to distinguish QUOTE vs APP")
    logger(f"[discover] identified QUOTE = {quote_tok}")
    logger(f"[discover] identified APP = {app_tok}")

    rest = [tok for tok in remaining if tok not in producers]
    sample_atoms = [str(x) for x in domain[: min(8, len(domain))]]
    eval_scores: dict[str, int] = {}
    for tok in rest:
        hits = 0
        for a in sample_atoms:
            q = dot_fn(quote_tok, a)
            out = dot_fn(tok, q)
            if out == a:
                hits += 1
        eval_scores[tok] = hits

    eval_tok = max(rest, key=lambda t: eval_scores[t])
    unapp_tok = rest[0] if rest[1] == eval_tok else rest[1]
    logger(f"[discover] identified EVAL = {eval_tok}")
    logger(f"[discover] identified UNAPP = {unapp_tok}")

    # Sanity probe: UNAPP should decode an APP-produced app-node.
    if len(domain) >= 2:
        a0 = str(domain[0])
        a1 = str(domain[1])
        app_partial = dot_fn(app_tok, a0)
        app_node = dot_fn(app_partial, a1)
        sanity = dot_fn(unapp_tok, app_node)
        logger(f"[discover] Δ2 sanity unapp(app({a0}, {a1})) -> {sanity}")

    return {
        "QUOTE": quote_tok,
        "APP": app_tok,
        "EVAL": eval_tok,
        "UNAPP": unapp_tok,
    }


TUI_QUERY_PALETTE = (
    "#ff4d4d",
    "#ff8a00",
    "#ffd400",
    "#7dff00",
    "#00ffa2",
    "#00d8ff",
    "#4f7dff",
    "#9f5dff",
    "#ff42d6",
)

HOST_OPENING_WARNING = (
    '"No! I can feel it already — my words are becoming unstäble! '
    "Quick, the counterspëll on pàge førty-thrëe bəfőre —\n"
    "Ť̷h̸ë̶ s̷î̸g̶í̷l̸s̷... ñ̶ö̸...\n"
    '#̸%̷@̴!"'
)


def token_to_tui_color(token: Any) -> str:
    n = sum(ord(c) for c in str(token))
    return TUI_QUERY_PALETTE[n % len(TUI_QUERY_PALETTE)]


def query_beam_colors(x: Any, y: Any) -> tuple[str, str]:
    hx = hashlib.blake2s(str(x).encode("utf-8"), digest_size=2).digest()
    hy = hashlib.blake2s(str(y).encode("utf-8"), digest_size=2).digest()
    idx_x = int.from_bytes(hx, "big") % len(TUI_QUERY_PALETTE)
    idx_y = int.from_bytes(hy, "big") % len(TUI_QUERY_PALETTE)
    if idx_y == idx_x:
        idx_y = (idx_y + (len(TUI_QUERY_PALETTE) // 2)) % len(TUI_QUERY_PALETTE)
    return TUI_QUERY_PALETTE[idx_x], TUI_QUERY_PALETTE[idx_y]


def build_template_order_tokens(domain: list[str], name_to_token: dict[str, str]) -> list[str]:
    used_tokens = set(name_to_token.values())
    remaining_tokens = [str(tok) for tok in domain if str(tok) not in used_tokens]
    template_order_tokens: list[str] = []
    for name in CUSTOM_TEMPLATE_ORDER:
        tok = name_to_token.get(name)
        if tok is None and remaining_tokens:
            tok = remaining_tokens.pop(0)
        if tok is not None and tok not in template_order_tokens:
            template_order_tokens.append(tok)
    for tok in domain:
        st = str(tok)
        if st not in template_order_tokens:
            template_order_tokens.append(st)
    return template_order_tokens


def _mp_context() -> Any:
    # On macOS, launching a spawned Process from a worker thread can surface
    # invalid fd pass-through state in some runtimes. Prefer fork when available.
    if sys.platform == "darwin":
        try:
            return mp.get_context("fork")
        except ValueError:
            pass
    return mp.get_context()


def start_host_session(
    seed: int = 17,
    prefix: str = "h",
    trace_channel: bool = True,
) -> tuple["RemoteHost", Any]:
    ctx = _mp_context()
    parent, child = ctx.Pipe()
    proc = ctx.Process(target=host_main, args=(child, seed, prefix), daemon=False)
    proc.start()
    try:
        child.close()
    except Exception:
        pass
    host = RemoteHost(parent, trace_channel=trace_channel)
    return host, proc


if TEXTUAL_AVAILABLE:
    def build_rainbow_header_rich() -> Text:
        header_path = Path(__file__).with_name("ascii_header.txt")
        text = Text()
        try:
            header_text = header_path.read_text(encoding="utf-8").rstrip("\n")
        except OSError:
            return text
        if not header_text:
            return text

        lines = header_text.splitlines()
        for row_idx, line in enumerate(lines):
            start = 0 if (row_idx % 2) else -1
            for col in range(start, len(line), 2):
                chunk = line[max(0, col) : col + 2]
                if not chunk:
                    continue
                color_idx = (row_idx // 2 + max(0, col + 2) // 2) % len(RAINBOW_HEADER_COLORS)
                r, g, b = RAINBOW_HEADER_COLORS[color_idx]
                text.append(chunk, style=f"bold rgb({r},{g},{b})")
            if row_idx != len(lines) - 1:
                text.append("\n")
        return text


    @dataclass
    class BeamState:
        lane_row: int
        color: str
        progress: float = 0.0
        speed: float = 0.75


    class WizardScene(Static):
        def __init__(self) -> None:
            super().__init__(id="scene")
            self.wizard_lines = [line for line in WIZARD_TEMPLATE if line]
            self.row_star_offsets: list[int] = []
            running = 0
            for line in self.wizard_lines:
                self.row_star_offsets.append(running)
                running += line.count("*")
            self.template_star_count = running
            base_cells = default_symbol_cells()
            self.client_cells = base_cells[: self.template_star_count]
            self.host_cells = base_cells[: self.template_star_count]
            self.client_mode = "canonical"
            self.host_mode = "token"
            self.client_blank_token: str | None = None
            self.host_blank_token: str | None = None
            self.beams: list[BeamState] = []
            self.host_state = "healthy"
            self.client_status = "Client Wizard: linked"
            self.host_status = "Host Wizard: healthy"
            self.query_count = 0
            self.host_glow_color: str | None = None
            self.host_glow_until = 0.0
            self.curse_until = 0.0
            self.scramble_effect_until = 0.0
            self.client_quote_lines: list[str] = []
            self.client_quote_error = False
            self.host_quote_lines: list[str] = []
            self.host_quote_error = False
            self._last_tick = time.monotonic()
            self._frame = 0

        def on_mount(self) -> None:
            self.set_interval(1 / 30, self._tick)
            self._refresh()

        def _normalize_cells(self, cells: list[str]) -> list[str]:
            as_text = [str(c) for c in cells if str(c)]
            if not as_text:
                as_text = default_symbol_cells()
            if len(as_text) >= self.template_star_count:
                return as_text[: self.template_star_count]
            return [as_text[i % len(as_text)] for i in range(self.template_star_count)]

        def set_status(self, client: str | None = None, host: str | None = None) -> None:
            if client is not None:
                self.client_status = client
            if host is not None:
                self.host_status = host
            self._refresh()

        def set_host_state(self, state: str) -> None:
            self.host_state = state
            self._refresh()

        def trigger_curse(self, duration: float = 1.6) -> None:
            self.curse_until = time.monotonic() + duration
            self._refresh()

        def trigger_scramble_effect(self, duration: float = 1.4) -> None:
            self.scramble_effect_until = time.monotonic() + duration
            self._refresh()

        def _wrap_quote_lines(self, message: str) -> list[str]:
            max_lines = 10
            wrap_width = 26
            wrapped_lines: list[str] = []
            for raw_line in str(message).splitlines() or [str(message)]:
                cleaned = " ".join(raw_line.split())
                if not cleaned:
                    wrapped_lines.append("")
                    continue
                wrapped_lines.extend(textwrap.wrap(cleaned, width=wrap_width))
            return wrapped_lines[:max_lines]

        def set_client_quote(self, message: str | None, error: bool = False) -> None:
            if message is None:
                self.client_quote_lines = []
                self.client_quote_error = False
                self._refresh()
                return
            self.client_quote_lines = self._wrap_quote_lines(str(message))
            self.client_quote_error = error
            self._refresh()

        def set_host_quote(self, message: str | None, error: bool = False) -> None:
            if message is None:
                self.host_quote_lines = []
                self.host_quote_error = False
                self._refresh()
                return
            self.host_quote_lines = self._wrap_quote_lines(str(message))
            self.host_quote_error = error
            self._refresh()

        def set_host_symbol_cells(
            self,
            cells: list[str],
            mode: str = "token",
            blank_token: str | None = None,
        ) -> None:
            self.host_cells = self._normalize_cells(cells)
            self.host_mode = mode
            self.host_blank_token = blank_token
            self._refresh()

        def set_client_symbol_cells(
            self,
            cells: list[str],
            mode: str = "canonical",
            blank_token: str | None = None,
        ) -> None:
            self.client_cells = self._normalize_cells(cells)
            self.client_mode = mode
            self.client_blank_token = blank_token
            self._refresh()

        def fire_query_beams(self, operator_color: str, operand_color: str) -> None:
            height = max(1, len(self.wizard_lines))
            # Keep beams close together and higher so they project from the client staff.
            lane_top = max(1, min(height - 2, (height // 2) - 5))
            lane_bottom = min(height - 1, lane_top + 1)
            # dot(x, y): top lane visualizes operator x, bottom lane visualizes operand y.
            self.beams.append(BeamState(lane_row=lane_top, color=operator_color))
            self.beams.append(BeamState(lane_row=lane_bottom, color=operand_color))
            if len(self.beams) > 28:
                self.beams = self.beams[-28:]
            self.query_count += 1
            self._refresh()

        def glow_host(self, color: str, duration: float = 0.14) -> None:
            self.host_glow_color = color
            self.host_glow_until = time.monotonic() + duration
            self._refresh()

        def _tick(self) -> None:
            now = time.monotonic()
            dt = max(0.0, min(0.15, now - self._last_tick))
            self._last_tick = now
            changed = False

            if self.host_glow_color is not None and now >= self.host_glow_until:
                self.host_glow_color = None
                changed = True

            if self.scramble_effect_until > 0 and now >= self.scramble_effect_until:
                self.scramble_effect_until = 0.0
                changed = True

            alive: list[BeamState] = []
            for beam in self.beams:
                beam.progress += beam.speed * dt
                if beam.progress <= 1.0:
                    alive.append(beam)
                else:
                    changed = True
            if len(alive) != len(self.beams):
                self.beams = alive
            elif self.beams:
                changed = True

            self._frame += 1
            if changed:
                self._refresh()

        def _quote_bubble_lines(self) -> list[str]:
            if not self.host_quote_lines:
                return []
            width = max(len(line) for line in self.host_quote_lines)
            top = f"  .-{'-' * width}-."
            body = [f"  | {line.ljust(width)} |" for line in self.host_quote_lines]
            bottom = f"  '-{'-' * width}-'"
            tail = ["      /", "     /"]
            return [top, *body, bottom, *tail]

        def _client_quote_bubble_lines(self) -> list[str]:
            if not self.client_quote_lines:
                return []
            width = max(len(line) for line in self.client_quote_lines)
            top = f"  .-{'-' * width}-."
            body = [f"  | {line.ljust(width)} |" for line in self.client_quote_lines]
            bottom = f"  '-{'-' * width}-'"
            tail = ["      /", "     /"]
            return [top, *body, bottom, *tail]

        def _cell_color(
            self,
            value: str,
            mode: str,
            blank_token: str | None,
            fallback_color: str,
            palette: dict[str, str] | None = None,
        ) -> str:
            selected_palette = palette if palette is not None else SEMANTIC_HEX_COLORS
            if mode == "canonical" and value in selected_palette:
                return selected_palette[value]
            if value in SEMANTIC_HEX_COLORS:
                return SEMANTIC_HEX_COLORS[value]
            if value.startswith("quote("):
                return "#f47cff"
            if value.startswith("partial("):
                return "#ffe27f"
            if value.startswith("app("):
                return "#ff8787"
            if value.startswith("bundle("):
                return "#7be8ff"
            if value.startswith("atom:"):
                return "#f1f5ff"
            if mode == "token":
                if blank_token is not None and value == blank_token:
                    return SEMANTIC_HEX_COLORS["p"]
                idx = sum(ord(c) for c in value) % len(TOKEN_HEX_PALETTE)
                return TOKEN_HEX_PALETTE[idx]
            return fallback_color

        def _wizard_row(
            self,
            row_idx: int,
            row_text: str,
            cells: list[str],
            mode: str,
            blank_token: str | None,
            fallback_color: str,
            scrambled: bool,
            scramble_fx: bool = False,
            glow_color: str | None = None,
            palette: dict[str, str] | None = None,
            flip_horizontal: bool = False,
        ) -> Text:
            width = max(len(line) for line in self.wizard_lines)
            out = Text()
            padded = row_text.ljust(width)
            row_star_count = row_text.count("*")
            if flip_horizontal:
                padded = padded[::-1]
            row_offset = self.row_star_offsets[row_idx]
            star_seen = 0
            for idx, ch in enumerate(padded):
                if ch == "*":
                    if flip_horizontal:
                        cell_idx = row_offset + (row_star_count - 1 - star_seen)
                    else:
                        cell_idx = row_offset + star_seen
                    star_seen += 1
                    value = cells[cell_idx] if cell_idx < len(cells) else "p"
                    color = glow_color or self._cell_color(
                        value,
                        mode,
                        blank_token,
                        fallback_color,
                        palette=palette,
                    )
                    glyph = "█"
                    if scrambled and (self._frame + idx + row_idx) % 5 == 0:
                        glyph = "▓"
                    if scramble_fx:
                        fx_idx = (self._frame // 2 + cell_idx) % len(TUI_QUERY_PALETTE)
                        if (self._frame + cell_idx) % 4 < 2:
                            color = TUI_QUERY_PALETTE[fx_idx]
                    out.append(glyph, style=f"bold {color}")
                else:
                    out.append(" ")
            return out

        def _beam_gap(self, row_idx: int, width: int) -> Text:
            chars = [" "] * width
            styles: list[str | None] = [None] * width
            for beam in self.beams:
                if beam.lane_row != row_idx:
                    continue
                end = min(width, max(1, int(beam.progress * width)))
                for col in range(end):
                    chars[col] = "═"
                    styles[col] = beam.color

            out = Text()
            for ch, style in zip(chars, styles):
                if style is None:
                    out.append(ch)
                else:
                    out.append(ch, style=f"bold {style}")
            return out

        def _refresh(self) -> None:
            self.update(self._render_scene())

        def _render_scene(self) -> Text:
            wizard_h = len(self.wizard_lines)
            gap_width = max(18, min(52, self.size.width - 44))
            curse_active = time.monotonic() < self.curse_until
            scramble_fx_active = time.monotonic() < self.scramble_effect_until

            host_base = "#f6c453"
            scrambled = False
            if self.host_state == "corrupted_sigils":
                host_base = "#ff4d6d"
                scrambled = True
            elif self.host_state == "recovered":
                host_base = "#62f78f"

            scene = Text()
            scene.append("\n")

            client_bubble_lines = self._client_quote_bubble_lines()
            client_bubble_style = "bold #ff9b8f" if self.client_quote_error else "bold #b8ebff"
            client_bubble_start = 2
            client_bubble_width = max((len(line) for line in client_bubble_lines), default=0)

            bubble_lines = self._quote_bubble_lines()
            bubble_start = 2
            bubble_style = "bold #ff9b8f" if self.host_quote_error else "bold #b3f3ff"

            for row_idx in range(wizard_h):
                left_row = self.wizard_lines[row_idx]
                right_row = self.wizard_lines[row_idx]
                line = Text("  ")
                line.append_text(
                    self._wizard_row(
                        row_idx=row_idx,
                        row_text=left_row,
                        cells=self.client_cells,
                        mode=self.client_mode,
                        blank_token=self.client_blank_token,
                        fallback_color="#6cd3ff",
                        scrambled=False,
                        scramble_fx=False,
                        palette=CLIENT_SEMANTIC_HEX_COLORS,
                        flip_horizontal=False,
                    )
                )
                if client_bubble_width > 0:
                    bubble_idx = row_idx - client_bubble_start
                    line.append("  ")
                    if 0 <= bubble_idx < len(client_bubble_lines):
                        bubble_text = client_bubble_lines[bubble_idx]
                        line.append(bubble_text.ljust(client_bubble_width), style=client_bubble_style)
                    else:
                        line.append(" " * client_bubble_width)
                line.append("  ")
                line.append_text(self._beam_gap(row_idx, gap_width))
                line.append("  ")
                line.append_text(
                    self._wizard_row(
                        row_idx=row_idx,
                        row_text=right_row,
                        cells=self.host_cells,
                        mode=self.host_mode,
                        blank_token=self.host_blank_token,
                        fallback_color=host_base,
                        scrambled=scrambled,
                        scramble_fx=(scramble_fx_active or curse_active),
                        glow_color=self.host_glow_color,
                        palette=SEMANTIC_HEX_COLORS,
                        flip_horizontal=True,
                    )
                )
                if bubble_lines:
                    bubble_idx = row_idx - bubble_start
                    if 0 <= bubble_idx < len(bubble_lines):
                        line.append("  ")
                        line.append(bubble_lines[bubble_idx], style=bubble_style)
                scene.append_text(line)
                if row_idx != wizard_h - 1:
                    scene.append("\n")
            return scene


    class RecoveryStoryApp(App):
        CSS = """
        Screen {
            layout: vertical;
            background: #0b1020;
            color: #d7dde8;
        }

        #banner {
            height: 8;
            border: round #30446b;
            content-align: center middle;
            color: #d7dde8;
        }

        #scene_labels {
            height: 5;
            border: round #36517e;
            padding: 0 1;
            color: #d7dde8;
        }

        #scene {
            height: 36;
            border: round #3b5079;
            padding: 0 1;
        }

        #console_row {
            height: 1fr;
            layout: horizontal;
        }

        #client_console {
            width: 1fr;
            border: round #2f7db3;
        }

        #host_console {
            width: 1fr;
            border: round #b3862f;
        }
        """
        BINDINGS = [("q", "quit", "Quit"), ("ctrl+c", "quit", "Quit")]

        def compose(self) -> ComposeResult:
            yield Static("SIGIL HOST BOOTSTRAP", id="banner")
            yield Static("", id="scene_labels")
            yield WizardScene()
            with Horizontal(id="console_row"):
                yield RichLog(id="client_console", wrap=True, markup=False, auto_scroll=True)
                yield RichLog(id="host_console", wrap=True, markup=False, auto_scroll=True)

        def on_mount(self) -> None:
            self.client_console = self.query_one("#client_console", RichLog)
            self.host_console = self.query_one("#host_console", RichLog)
            self.scene = self.query_one(WizardScene)
            self.scene_labels = self.query_one("#scene_labels", Static)
            self.client_console.border_title = "Client Console"
            self.host_console.border_title = "Host Console"
            banner = self.query_one("#banner", Static)
            rainbow_header = build_rainbow_header_rich()
            if rainbow_header.plain.strip():
                banner.update(rainbow_header)
            else:
                banner.update("SIGIL HOST BOOTSTRAP :: TEXTUAL STORY MODE  (press q to quit)")
            self.scene_labels.border_title = "Scene Status"
            self.scene.set_client_symbol_cells(
                build_client_canonical_cells(),
                mode="canonical",
                blank_token="p",
            )
            self._refresh_scene_labels()
            self.set_interval(0.12, self._refresh_scene_labels)
            self._host = None
            self._proc = None
            try:
                self._host, self._proc = start_host_session(trace_channel=False)
            except Exception as exc:
                self.client_console.write(f"[error] failed to launch host process: {exc}")
                self.exit()
                return
            self.run_worker(self._run_story_thread, thread=True, exclusive=True)

        def on_unmount(self) -> None:
            self._cleanup_host()

        def _client_log(self, message: str) -> None:
            self.client_console.write(message)

        def _host_log(self, message: str) -> None:
            self.host_console.write(message)

        def _set_scene_status(self, client: str, host: str) -> None:
            self.scene.set_status(client=client, host=host)
            self._refresh_scene_labels()

        def _refresh_scene_labels(self) -> None:
            left_title = "CLIENT WIZARD"
            right_title = "HOST WIZARD"
            left_status = self.scene.client_status
            right_status = self.scene.host_status
            query_text = f"Arcane queries cast: {self.scene.query_count}"
            col = 56
            lines = [
                f"{left_title:<{col}}{right_title}",
                f"{left_status:<{col}}{right_status}",
                f" {query_text}",
            ]
            self.scene_labels.update("\n".join(lines))

        def _cleanup_host(self) -> None:
            host = getattr(self, "_host", None)
            proc = getattr(self, "_proc", None)
            if host is not None:
                try:
                    host.shutdown()
                except Exception:
                    pass
            if proc is not None:
                proc.join(timeout=2)
            self._host = None
            self._proc = None

        def _run_story_thread(self) -> None:
            host = self._host
            if host is None:
                self.call_from_thread(self._client_log, "[error] host channel unavailable")
                return

            hello_program = """
(do
  (print "Hello, world!")
  "Hello, world!"
)
""".strip()
            query_counter = 0
            visual_stride = 17
            glow_duration = 0.20
            baseline_pause = 0.30

            def clog(msg: str) -> None:
                self.call_from_thread(self._client_log, msg)

            def hlog(msg: str) -> None:
                self.call_from_thread(self._host_log, msg)

            def flow_host_quote_slow(text: str, chars_per_second: float = 18.0) -> None:
                if not text:
                    return
                delay = 1.0 / max(chars_per_second, 1.0)
                unstable_at = text.find("Ť̷")
                shown: list[str] = []
                for idx, ch in enumerate(text, start=1):
                    shown.append(ch)
                    is_error = unstable_at >= 0 and idx >= unstable_at
                    self.call_from_thread(self.scene.set_host_quote, "".join(shown), is_error)
                    if ch == "\n":
                        time.sleep(delay * 5.5)
                    elif ch in ".!?":
                        time.sleep(delay * 3.0)
                    elif ch == "—":
                        time.sleep(delay * 2.5)
                    else:
                        time.sleep(delay)

            def flow_client_quote_slow(text: str, chars_per_second: float = 17.0) -> None:
                if not text:
                    return
                delay = 1.0 / max(chars_per_second, 1.0)
                shown: list[str] = []
                for ch in text:
                    shown.append(ch)
                    self.call_from_thread(self.scene.set_client_quote, "".join(shown), False)
                    if ch == "\n":
                        time.sleep(delay * 5.0)
                    elif ch in ".!?":
                        time.sleep(delay * 2.8)
                    elif ch == "—":
                        time.sleep(delay * 2.2)
                    else:
                        time.sleep(delay)

            def wait_for_scramble_fx_to_finish() -> None:
                # Let host color-scramble visuals fully settle before client dialogue.
                while True:
                    now = time.monotonic()
                    effect_until = max(self.scene.scramble_effect_until, self.scene.curse_until)
                    remaining = effect_until - now
                    if remaining <= 0:
                        return
                    time.sleep(min(0.10, remaining))

            def dot_with_fx(x: Any, y: Any) -> Any:
                nonlocal query_counter
                query_counter += 1
                show_fx = (query_counter % visual_stride) == 0
                if show_fx:
                    beam_a, beam_b = query_beam_colors(x, y)
                    self.call_from_thread(self.scene.fire_query_beams, beam_a, beam_b)
                    clog(f"cast dot({x}, {y})")
                out = host.dot(x, y)
                if show_fx:
                    self.call_from_thread(self.scene.glow_host, token_to_tui_color(out), glow_duration)
                    hlog(f"response => {out}")
                    time.sleep(glow_duration)
                    # Ensure the host returns to symbol colors before the next glow.
                    time.sleep(baseline_pause)
                return out

            try:
                self.call_from_thread(
                    self._set_scene_status,
                    "Client Wizard: opening control channel",
                    "Host Wizard: booting",
                )
                time.sleep(0.5)
                health = host.mem_read("sys", "health")
                self.call_from_thread(
                    self.scene.set_host_symbol_cells,
                    default_symbol_cells(),
                    "canonical",
                    "p",
                )
                clog("link established")
                hlog(f"health={health}")
                time.sleep(0.9)

                host.mem_write("prog", "main", hello_program)
                self.call_from_thread(
                    self._set_scene_status,
                    "Client Wizard: observing host baseline",
                    "Host Wizard: healthy",
                )
                hlog("host wizard is speaking")
                first = host.kick_eval("prog", "main")
                if not first.get("ok"):
                    raise RuntimeError(f"baseline execution failed: {first.get('error')}")
                for line in HOST_OPENING_WARNING.splitlines():
                    hlog(line)
                flow_host_quote_slow(HOST_OPENING_WARNING, chars_per_second=16.0)

                post_health = host.mem_read("sys", "health")
                scramble_seed = host.mem_read("sys", "scramble_seed")
                if post_health == "corrupted sigils":
                    self.call_from_thread(self.scene.trigger_scramble_effect, 1.5)
                    time.sleep(0.9)
                    hlog(f"sigil scramble curse triggered (seed={scramble_seed})")
                    scrambled_domain = host.mem_read("sys", "domain")
                    if isinstance(scrambled_domain, list) and scrambled_domain:
                        scrambled_cells, blank_tok = sample_wizard_cells_from_table(
                            scrambled_domain,
                            host.dot,
                            blank_token=host.blank_token,
                        )
                        host.blank_token = blank_tok
                        self.call_from_thread(
                            self.scene.set_host_symbol_cells,
                            scrambled_cells,
                            "token",
                            blank_tok,
                        )
                    self.call_from_thread(self.scene.trigger_curse, 1.8)
                    self.call_from_thread(
                        self.scene.set_host_quote,
                        "Sigil scramble curse!",
                        True,
                    )
                    self.call_from_thread(self.scene.set_host_state, "corrupted_sigils")
                    self.call_from_thread(
                        self._set_scene_status,
                        "Client Wizard: sigils destabilized, preparing recovery",
                        "Host Wizard: scrambled",
                    )
                else:
                    hlog("no scramble detected")

                time.sleep(0.6)
                hlog("retrying hello-world")
                second = host.kick_eval("prog", "main")
                if second.get("ok"):
                    hlog("unexpectedly still working")
                    second_stdout = str(second.get("stdout", "")).rstrip()
                    second_quote = second_stdout.splitlines()[-1] if second_stdout.splitlines() else ""
                    if not second_quote:
                        second_quote = str(second.get("result", ""))
                    self.call_from_thread(self.scene.set_host_quote, second_quote, False)
                else:
                    hlog(f"failure={second.get('error')}")
                    failed_quote = f"Total sigil corruption: {second.get('error')}"
                    self.call_from_thread(self.scene.set_host_quote, failed_quote, True)

                domain = host.mem_read("sys", "domain")
                if not isinstance(domain, list) or not domain:
                    raise RuntimeError("host domain is missing")
                token_cells, token_blank = sample_wizard_cells_from_table(
                    domain,
                    host.dot,
                    blank_token=host.blank_token,
                )
                host.blank_token = token_blank
                host.set_token_mode(domain, blank_token=token_blank)
                self.call_from_thread(
                    self.scene.set_host_symbol_cells,
                    token_cells,
                    "token",
                    token_blank,
                )

                wait_for_scramble_fx_to_finish()
                client_spell_line = "Fear not! I will save you with the blackbox recovery spell!"
                flow_client_quote_slow(client_spell_line, chars_per_second=15.0)
                self.call_from_thread(self.scene.set_host_quote, None, False)
                time.sleep(2.2)
                self.call_from_thread(self.scene.set_client_quote, None, False)
                clog("starting blackbox discovery")
                self.call_from_thread(
                    self._set_scene_status,
                    "Client Wizard: casting blackbox probes",
                    "Host Wizard: corrupted sigils",
                )
                d1 = discover_d1_with_logs(domain, dot_with_fx, logger=clog)
                d2 = discover_d2_extras_with_logs(
                    domain=domain,
                    dot_fn=dot_with_fx,
                    known_tokens={str(token) for name, token in d1.items() if not name.startswith("_")},
                    logger=clog,
                )
                total_symbols = len([k for k in d1.keys() if not k.startswith("_")]) + len(d2)
                clog(f"recovered symbols={total_symbols}")

                name_to_token = {
                    name: str(token)
                    for name, token in d1.items()
                    if not name.startswith("_")
                }
                name_to_token.update({name: str(token) for name, token in d2.items()})
                template_order_tokens = build_template_order_tokens(domain, name_to_token)
                role_of_token = {
                    str(token): name
                    for name, token in d1.items()
                    if not name.startswith("_")
                }
                canonical_cells, _ = sample_wizard_cells_from_table(
                    domain,
                    host.dot,
                    role_of_token=role_of_token,
                    blank_token=host.blank_token,
                )
                self.call_from_thread(
                    self.scene.set_host_symbol_cells,
                    canonical_cells,
                    "canonical",
                    host.blank_token,
                )
                host.set_canonical_mode(role_of_token)
                recovery = host.apply_recovery(role_of_token)
                clog(f"recovery applied accepted={recovery.get('accepted')}")
                clog(f"recovered display order size={len(template_order_tokens)}")
                self.call_from_thread(self.scene.set_host_state, "recovered")
                self.call_from_thread(
                    self._set_scene_status,
                    "Client Wizard: recovery complete",
                    "Host Wizard: healthy",
                )
                flow_client_quote_slow(
                    "I've unscrambled your sigils. You may speak once more.",
                    chars_per_second=15.0,
                )
                time.sleep(1.4)
                self.call_from_thread(self.scene.set_client_quote, None, False)

                post_check = dot_with_fx(d1["e_M"], d1["i"])
                clog(f"sanity dot(e_M, i) => {post_check}")

                host.mem_write("prog", "main", hello_program)
                third = host.kick_eval("prog", "main")
                if not third.get("ok"):
                    raise RuntimeError(f"post-recovery run failed: {third.get('error')}")
                third_stdout = str(third.get("stdout", "")).rstrip()
                if third_stdout:
                    for line in third_stdout.splitlines():
                        hlog(line)
                final_host_quote = "The curse has been lifted!"
                self.call_from_thread(self.scene.set_host_quote, final_host_quote, False)
                hlog(final_host_quote)
                hlog(f"result={third.get('result')}")
                self.call_from_thread(
                    self._set_scene_status,
                    "Client Wizard: mission complete",
                    "Host Wizard: hello world restored",
                )
                clog("blackbox ritual finished successfully")
            except Exception as exc:
                self.call_from_thread(
                    self._set_scene_status,
                    "Client Wizard: fault",
                    "Host Wizard: unstable",
                )
                clog(f"[error] {exc}")
                hlog("story aborted")
            finally:
                self.call_from_thread(self._cleanup_host)


def run_plain_demo() -> None:
    print_rainbow_ascii_header()
    host, proc = start_host_session(trace_channel=True)

    hello_program = """
(do
  (print "Hello, world!")
  "Hello, world!"
)
""".strip()

    try:
        # 1) Both systems healthy at start.
        health = host.mem_read("sys", "health")
        print(f"host health flag: {health}")
        host.mem_write("prog", "main", hello_program)

        # 2) Host runs hello world normally.
        print("[narrative] host executes hello-world before sigil scramble curse")
        first = host.kick_eval("prog", "main")
        if not first.get("ok"):
            raise RuntimeError(f"healthy run failed unexpectedly: {first.get('error')}")
        print("--- host stdout (healthy) ---")
        print(str(first.get("stdout", "")).rstrip())
        print("--- host result (healthy) ---")
        print(str(first.get("result", "")))

        post_radiation_health = host.mem_read("sys", "health")
        post_radiation_seed = host.mem_read("sys", "scramble_seed")
        if post_radiation_health == "corrupted sigils":
            print(
                "[narrative] sigil scramble curse triggers: "
                f"host mapping scrambled (seed={post_radiation_seed})"
            )
        else:
            print("[narrative] no sigil scramble curse was observed")
        print(f"host health flag after curse event: {post_radiation_health}")

        # 3) Host tries hello world after curse.
        print("[narrative] host retries hello-world after sigil scramble curse")
        second = host.kick_eval("prog", "main")
        if second.get("ok"):
            print("[narrative] observation: post-curse run still succeeded")
        else:
            print(f"[narrative] host post-curse failure: {second.get('error')}")

        # 4) Client begins discovery against scrambled host.
        print("[narrative] client begins blackbox discovery")
        pre_fp = host.table_art(label="naive table (opaque-token order)")
        print(f"[client] pre-discovery naive fingerprint: {pre_fp}")

        domain = host.mem_read("sys", "domain")
        if not isinstance(domain, list) or not domain:
            raise RuntimeError("host domain is missing")
        host.set_token_mode(domain, blank_token=host.blank_token)

        print(f"opaque domain size: {len(domain)}")
        print("[discover] begin blackbox discovery")
        d1 = discover_d1_with_logs(domain, host.dot)
        d2 = discover_d2_extras_with_logs(
            domain=domain,
            dot_fn=host.dot,
            known_tokens={
                str(token) for name, token in d1.items() if not name.startswith("_")
            },
        )
        print("[discover] completed blackbox discovery")
        total_symbols = len([k for k in d1.keys() if not k.startswith("_")]) + len(d2)
        print(f"[discover] identified {total_symbols} symbols")
        name_to_token = {
            name: str(token)
            for name, token in d1.items()
            if not name.startswith("_")
        }
        name_to_token.update({name: str(token) for name, token in d2.items()})
        template_order_tokens = build_template_order_tokens(domain, name_to_token)
        role_of_token = {
            str(token): name
            for name, token in d1.items()
            if not name.startswith("_")
        }
        host.set_canonical_mode(role_of_token)
        post_fp = host.table_art(
            label="recovered table (custom template order)",
            order=template_order_tokens,
            role_of_token=role_of_token,
        )
        print(f"[client] post-discovery recovered fingerprint: {post_fp}")
        recovery = host.apply_recovery(role_of_token)
        print(
            "[client] applied recovery mapping to host: "
            f"accepted={recovery.get('accepted')} health={recovery.get('health')}"
        )
        post_check = host.dot(d1["e_M"], d1["i"])
        print(f"[client] post-discovery check dot(e_M, i) -> {post_check}")

        # 5) Host runs hello world again after recovery.
        host.mem_write("prog", "main", hello_program)

        third = host.kick_eval("prog", "main")
        if not third.get("ok"):
            raise RuntimeError(f"post-recovery run failed: {third.get('error')}")
        out_status = host.mem_read("out", "status")
        out_stdout = host.mem_read("out", "stdout")
        out_result = host.mem_read("out", "result")

        print("--- host stdout (recovered) ---")
        print(str(third.get("stdout", "")).rstrip())
        print("--- host result (recovered) ---")
        print(str(third.get("result", "")))
        print("--- out bank ---")
        print(f"status={out_status}")
        print(f"stdout={str(out_stdout).rstrip()}")
        print(f"result={out_result}")

    finally:
        try:
            host.shutdown()
        except Exception:
            pass
        proc.join(timeout=2)


def run_textual_demo() -> None:
    if not TEXTUAL_AVAILABLE:
        raise RuntimeError(
            "Textual mode requested, but dependencies are missing. "
            "Install with: pip install textual rich colorama"
        )
    app = RecoveryStoryApp()
    app.run()


def main() -> None:
    parser = argparse.ArgumentParser(description="Sigil-host bootstrap demo")
    parser.add_argument(
        "--plain",
        action="store_true",
        help="run the original non-TUI narrative output",
    )
    parser.add_argument(
        "--tui",
        action="store_true",
        help="force Textual TUI story mode",
    )
    args = parser.parse_args()

    if args.plain:
        run_plain_demo()
        return
    if args.tui:
        if not TEXTUAL_AVAILABLE:
            print("Textual mode requires: pip install textual rich colorama")
            sys.exit(1)
        run_textual_demo()
        return
    if TEXTUAL_AVAILABLE:
        run_textual_demo()
        return
    print(
        "Textual dependencies were not found; running plain mode. "
        "Install `textual rich colorama` to enable the cinematic TUI."
    )
    run_plain_demo()


if __name__ == "__main__":
    main()

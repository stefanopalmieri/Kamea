#!/usr/bin/env python3
"""
Kaput-host bootstrap demo over multiprocessing.Pipe.

Model:
- Host control plane is "kaput" (no discovery logic available on host).
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

import io
import hashlib
import itertools
import pprint
import random
import sys
import re
from dataclasses import dataclass, field
from multiprocessing import Pipe, Process
from pathlib import Path
from typing import Any
from contextlib import redirect_stdout

# Allow imports from repository root when launched via examples/ path.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from colorama import Back, Fore, Style, init as colorama_init
from delta2_true_blackbox import ALL_ATOMS, AppNode, Atom, Partial, Quote, UnappBundle, dot_iota

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
    "    ****",
    "   ******",
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
        state["health"] = "kaput"
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
            state["health"] = "kaput"
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


def discover_d1_with_logs(domain: list[str], dot_fn) -> dict[str, Any]:
    """Client-side blackbox recovery with per-symbol logging."""

    def left_image(xh: Any) -> set[Any]:
        return {dot_fn(xh, y) for y in domain}

    def left_image_in_domain(xh: Any) -> set[Any]:
        return {dot_fn(xh, y) for y in domain if dot_fn(xh, y) in domain}

    print("[discover] step 1: find booleans (left-absorbers)")
    absorbers = [x for x in domain if all(dot_fn(x, y) == x for y in domain)]
    if len(absorbers) != 2:
        raise RuntimeError(f"expected 2 absorbers, got {len(absorbers)}")
    b1, b2 = absorbers
    print(f"[discover] candidates for booleans: {b1}, {b2}")

    def testers_for(top: Any, bot: Any) -> list[Any]:
        out = []
        for x in domain:
            if x in (top, bot):
                continue
            im = left_image(x)
            if im.issubset({top, bot}) and len(im) == 2:
                out.append(x)
        return out

    print("[discover] step 2: orient booleans and find testers")
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
    print(f"[discover] identified ⊤ = {top}")
    print(f"[discover] identified ⊥ = {bot}")

    print("[discover] step 2.5: find p")
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
    print(f"[discover] identified p = {p_tok}")

    print("[discover] step 3: identify m_I and m_K from tester cardinalities")
    sizes = {t: len(dec(t)) for t in testers}
    m_k = [t for t in testers if sizes[t] == 1][0]
    m_i = max(testers, key=lambda t: sizes[t])
    two = [t for t in testers if sizes[t] == 2]
    if len(two) != 2:
        raise RuntimeError(f"expected 2 testers with |Dec|=2, got {len(two)}")
    print(f"[discover] identified m_K = {m_k}")
    print(f"[discover] identified m_I = {m_i}")

    print("[discover] step 4: distinguish e_I vs d_K")
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
    print(f"[discover] identified e_I = {e_i}")
    print(f"[discover] identified d_K = {d_k}")

    print("[discover] step 5: find e_D and e_M")
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
    print(f"[discover] identified e_M = {e_m}")
    print(f"[discover] identified e_D = {e_d}")

    print("[discover] step 6: distinguish i and k")
    out_a, out_b = dot_fn(e_m, ctx[0]), dot_fn(e_m, ctx[1])
    if len(dec(out_a)) > len(dec(out_b)):
        i_tok, k_tok = ctx[0], ctx[1]
    else:
        i_tok, k_tok = ctx[1], ctx[0]
    print(f"[discover] identified i = {i_tok}")
    print(f"[discover] identified k = {k_tok}")

    print("[discover] step 7: identify a, b, d_I")
    ab = list(dec(d_k))
    a_tok = next(x for x in ab if dot_fn(m_k, x) == top)
    b_tok = next(x for x in ab if x != a_tok)
    d_i = dot_fn(e_d, i_tok)
    print(f"[discover] identified a = {a_tok}")
    print(f"[discover] identified b = {b_tok}")
    print(f"[discover] identified d_I = {d_i}")

    print("[discover] step 8: identify e_Σ, s_C, e_Δ")
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
    print(f"[discover] identified e_Σ = {e_sigma}")
    print(f"[discover] identified s_C = {s_c}")
    print(f"[discover] identified e_Δ = {e_delta}")

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
) -> dict[str, str]:
    """Recover QUOTE/EVAL/APP/UNAPP from remaining opaque tokens."""
    remaining = [str(x) for x in domain if str(x) not in known_tokens]
    if len(remaining) != 4:
        raise RuntimeError(f"expected 4 Δ2 extras, got {len(remaining)}: {remaining}")
    print(f"[discover] Δ2 step 1: remaining extras candidates = {remaining}")

    def is_structure_producer(tok: str) -> bool:
        outs = [dot_fn(tok, x) for x in domain]
        return all(o not in domain for o in outs)

    producers = [tok for tok in remaining if is_structure_producer(tok)]
    if len(producers) != 2:
        raise RuntimeError(f"expected 2 structure producers, got {producers}")
    print(f"[discover] Δ2 step 2: structure producers = {producers}")

    probe_arg = str(domain[0])
    quote_tok = next((t for t in producers if isinstance(dot_fn(t, probe_arg), Quote)), None)
    app_tok = next((t for t in producers if isinstance(dot_fn(t, probe_arg), Partial)), None)
    if quote_tok is None or app_tok is None:
        raise RuntimeError("failed to distinguish QUOTE vs APP")
    print(f"[discover] identified QUOTE = {quote_tok}")
    print(f"[discover] identified APP = {app_tok}")

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
    print(f"[discover] identified EVAL = {eval_tok}")
    print(f"[discover] identified UNAPP = {unapp_tok}")

    # Sanity probe: UNAPP should decode an APP-produced app-node.
    if len(domain) >= 2:
        a0 = str(domain[0])
        a1 = str(domain[1])
        app_partial = dot_fn(app_tok, a0)
        app_node = dot_fn(app_partial, a1)
        sanity = dot_fn(unapp_tok, app_node)
        print(f"[discover] Δ2 sanity unapp(app({a0}, {a1})) -> {sanity}")

    return {
        "QUOTE": quote_tok,
        "APP": app_tok,
        "EVAL": eval_tok,
        "UNAPP": unapp_tok,
    }


def main() -> None:
    print_rainbow_ascii_header()
    parent, child = Pipe()
    proc = Process(target=host_main, args=(child, 17, "h"), daemon=True)
    proc.start()

    host = RemoteHost(parent)

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
        print("[narrative] host executes hello-world before radiation")
        first = host.kick_eval("prog", "main")
        if not first.get("ok"):
            raise RuntimeError(f"healthy run failed unexpectedly: {first.get('error')}")
        print("--- host stdout (healthy) ---")
        print(str(first.get("stdout", "")).rstrip())
        print("--- host result (healthy) ---")
        print(str(first.get("result", "")))

        post_radiation_health = host.mem_read("sys", "health")
        post_radiation_seed = host.mem_read("sys", "scramble_seed")
        if post_radiation_health == "kaput":
            print(
                "[narrative] radiation event occurs: "
                f"host mapping scrambled (seed={post_radiation_seed})"
            )
        else:
            print("[narrative] no radiation event was observed")
        print(f"host health flag after radiation event: {post_radiation_health}")

        # 3) Host tries hello world after radiation.
        print("[narrative] host retries hello-world after radiation")
        second = host.kick_eval("prog", "main")
        if second.get("ok"):
            print("[narrative] observation: post-radiation run still succeeded")
        else:
            print(f"[narrative] host post-radiation failure: {second.get('error')}")

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
        # Build recovered display order from user-provided template order names.
        # For names not discovered by recovery, consume
        # remaining tokens in domain order.
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


if __name__ == "__main__":
    main()

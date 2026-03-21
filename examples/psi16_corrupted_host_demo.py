#!/usr/bin/env python3
"""
Ψ₁₆ᶠ Corrupted-host bootstrap demo over multiprocessing.Pipe.

Model:
- Host control plane starts healthy, then enters "corrupted sigils" state.
- Exposed primitives: ALU dot(x,y), memory banks read/write, kick_eval.
- The client detects corruption, runs a pure Ψ-Lisp recovery spell that
  probes the opaque ALU via IO atoms (put/get), and restores health.

Mascot rendering uses the wiz2 bijective 16×16 sprite: every cell in the
Ψ₁₆ᶠ Cayley table maps to exactly one pixel, colored by output value.

Modes:
  Default  — Textual TUI with animated sprite, speech bubbles, effects
  --plain  — original print-based narrative (no Textual dependency)

Usage:
  python examples/psi16_corrupted_host_demo.py
  python examples/psi16_corrupted_host_demo.py --plain
"""

from __future__ import annotations

import io
import json
import multiprocessing as mp
import random
import sys
import time
from collections import Counter
from contextlib import redirect_stdout
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from psi_blackbox import (
    ELEM_NAMES,
    PSI_16_FULL,
    make_blackbox,
    recover_adaptive,
    verify_axioms,
)
from psi_lisp import (
    builtin_env as lisp_builtin_env,
    run as lisp_run,
    encode_int,
    decode_int,
    list_elements,
    is_pair_term,
    LISP_NIL,
    display as lisp_display,
)

# ── Try importing Textual ────────────────────────────────────────────────────

try:
    from rich.cells import cell_len
    from rich.text import Text
    from textual.app import App, ComposeResult
    from textual.containers import Horizontal
    from textual.widget import Widget
    from textual.widgets import RichLog, Static

    # Textual 8+ uses Content instead of Rich Text for rendering
    try:
        from textual.content import Content
        _HAS_CONTENT = True
    except ImportError:
        _HAS_CONTENT = False

    TEXTUAL_AVAILABLE = True
except ModuleNotFoundError:
    TEXTUAL_AVAILABLE = False

# ── ANSI helpers ─────────────────────────────────────────────────────────────

def _fg(r: int, g: int, b: int) -> str:
    return f"\033[38;2;{r};{g};{b}m"

def _bg(r: int, g: int, b: int) -> str:
    return f"\033[48;2;{r};{g};{b}m"

RST = "\033[0m"
BOLD = "\033[1m"
DIM = "\033[2m"

# ── Palette (from wiz2.json designer session) ───────────────────────────────

DEFAULT_PALETTE: dict[int, str] = {
    0:  "#e8c090",   # ⊤  peach
    1:  "#18182a",   # ⊥  dark indigo
    2:  "#1e2790",   # f  deep blue
    3:  "#384828",   # τ  dark moss
    4:  "#0c142a",   # g  deep indigo
    5:  "#0b0a09",   # SEQ near-black
    6:  "#e8a820",   # Q  gold
    7:  "#743a1a",   # E  burnt sienna
    8:  "#5c24b0",   # ρ  purple
    9:  "#38c0d8",   # η  cyan
    10: "#3d4bd7",   # Y  blue
    11: "#7038d0",   # PAIR bright purple
    12: "#501888",   # s0 deep purple
    13: "#733262",   # INC mauve
    14: "#1c1c36",   # s1 dark navy
    15: "#303820",   # DEC dark olive
}

SUPPLY = Counter(v for row in PSI_16_FULL for v in row)

# ── Lisp spell IO channel ──────────────────────────────────────────────────

_SPELL_PATH = Path(__file__).with_name("psi_recovery_spell.lisp")


_STATUS_SNIPPETS = {
    0: "(find-idempotents domain)      ; x where x\u00b7x = x",
    1: "(classify-loop non-abs abs-a abs-b \u2026)",
    2: "(if (= (length semi-a) 1) abs-a abs-b)  ; orient \u22a4/\u22a5",
    3: "(find-E full-pres z top bot)   ; Kripke test",
    4: "(find-Q q-cands E)             ; E\u00b7(Q\u00b7E) = Q",
    5: "(probe E E) (probe E Q) (probe Q Q) (probe Q \u22a4)",
    6: "(probe f s1) (probe PAIR DEC) \u2026 ; depth-2 tree",
}


class OracleIOChannel:
    """Routes put/get IO atoms from the Lisp spell to the oracle and report callback."""

    def __init__(self, oracle_fn, report_fn=None, status_fn=None):
        self.oracle_fn = oracle_fn
        self.report_fn = report_fn
        self.status_fn = status_fn
        self._buffer: list[int] = []
        self._result_queue: list[int] = []

    def put(self, val):
        self._buffer.append(decode_int(val))
        self._dispatch()
        return LISP_NIL

    def get(self):
        return encode_int(self._result_queue.pop(0))

    def _dispatch(self):
        if not self._buffer:
            return
        op = self._buffer[0]
        if op == 0 and len(self._buffer) == 3:  # PROBE
            _, a, b = self._buffer
            self._buffer.clear()
            self._result_queue.append(self.oracle_fn(a, b))
        elif op == 1 and len(self._buffer) == 3:  # REPORT
            _, idx, label = self._buffer
            self._buffer.clear()
            if self.report_fn:
                self.report_fn(idx, label)
        elif op == 2 and len(self._buffer) == 2:  # STATUS
            _, phase = self._buffer
            self._buffer.clear()
            if self.status_fn:
                snippet = _STATUS_SNIPPETS.get(phase, f"phase {phase}")
                self.status_fn(phase, snippet)


def _make_lisp_list(values):
    """Build a Ψ∗ proper list from Python ints (via encode_int)."""
    from psi_lisp import lisp_cons
    result = LISP_NIL
    for v in reversed(values):
        result = lisp_cons(encode_int(v), result)
    return result


def _run_spell(domain, oracle_fn, report_fn=None, status_fn=None):
    """Run the Lisp recovery spell and return rec dict {name: label}."""
    channel = OracleIOChannel(oracle_fn, report_fn, status_fn)
    env = lisp_builtin_env()
    env["put"] = channel.put
    env["get"] = channel.get
    env["domain"] = _make_lisp_list(domain)

    spell_src = _SPELL_PATH.read_text()
    results = lisp_run(spell_src, env)

    return _assoc_list_to_rec(results[-1])


def _assoc_list_to_rec(term):
    """Convert Lisp assoc list ((0 . top) (1 . bot) ...) to {name: label}."""
    idx_to_name = {v: k for k, v in {
        "⊤": 0, "⊥": 1, "f": 2, "τ": 3, "g": 4, "SEQ": 5,
        "Q": 6, "E": 7, "ρ": 8, "η": 9, "Y": 10, "PAIR": 11,
        "s0": 12, "INC": 13, "s1": 14, "DEC": 15,
    }.items()}
    rec = {}
    from psi_lisp import fst, snd
    for pair_term in list_elements(term):
        idx = decode_int(fst(pair_term))
        label = decode_int(snd(pair_term))
        name = idx_to_name[idx]
        rec[name] = label
    return rec


HOST_OPENING_WARNING = (
    '"No! I can feel it already \u2014 my sigils are shifting! '
    "Quick, the recovery spell bef\u00f8re \u2014\n"
    "\u0164\u0337h\u0338\u00eb\u0336 s\u0337\u00ee\u0338g\u0336\u00ed\u0337l\u0338s\u0337... "
    "\u00f1\u0336\u00f6\u0338...\n"
    '#\u0338%\u0337@\u0334!"'
)


def hex_to_rgb(h: str) -> tuple[int, int, int]:
    return int(h[1:3], 16), int(h[3:5], 16), int(h[5:7], 16)


def lum(h: str) -> float:
    r, g, b = hex_to_rgb(h)
    return 0.299 * r + 0.587 * g + 0.114 * b


def text_color(h: str) -> str:
    return _fg(16, 16, 16) if lum(h) >= 140 else _fg(240, 240, 240)


# ── Wiz2 sprite template ────────────────────────────────────────────────────

WIZ2_SILHOUETTE = [
    "........#####...",  # 0  hat tip
    ".....######.#.#.",  # 1  hat + staff
    "....#######.....",  # 2  hat
    "....#########...",  # 3  hat brim
    "..#############.",  # 4  brim wide
    ".############.#.",  # 5  face top + staff
    "....##########..",  # 6  face + eyes
    "....########.#.#",  # 7  face + staff
    "..#.########.#.#",  # 8  face + staff
    "....########.#..",  # 9  chin
    ".#.##########...",  # 10 robe + arm
    "..#############.",  # 11 robe
    "..##########.#..",  # 12 robe + staff
    "....########.#.#",  # 13 robe lower
    ".#..########.#..",  # 14 robe lower
    "....###..###....",  # 15 boots
]

BG_VALUES = {1, 3, 4, 14}


def load_wiz2_mapping() -> dict[tuple[int, int], tuple[int, int]] | None:
    """Try to load the hand-designed mapping from wiz2.json."""
    path = Path(__file__).with_name("wiz2.json")
    if not path.exists():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        mapping = {}
        for tgt_str, src_list in data["mapping"].items():
            tr, tc = (int(x) for x in tgt_str.split(","))
            mapping[(tr, tc)] = (src_list[0], src_list[1])
        return mapping
    except Exception:
        return None


def build_sprite_grid(
    mapping: dict[tuple[int, int], tuple[int, int]] | None = None,
) -> list[list[int]]:
    """Build 16x16 sprite from mapping (target -> source Cayley cell)."""
    if mapping and len(mapping) == 256:
        grid = [[0] * 16 for _ in range(16)]
        for (tr, tc), (sr, sc) in mapping.items():
            grid[tr][tc] = PSI_16_FULL[sr][sc]
        return grid

    # Auto-fill from silhouette
    char_cells = []
    bg_cells = []
    for r in range(16):
        for c in range(16):
            if r < len(WIZ2_SILHOUETTE) and c < len(WIZ2_SILHOUETTE[r]):
                if WIZ2_SILHOUETTE[r][c] == '#':
                    char_cells.append((r, c))
                else:
                    bg_cells.append((r, c))
            else:
                bg_cells.append((r, c))

    char_pool = []
    bg_pool = []
    for r in range(16):
        for c in range(16):
            v = PSI_16_FULL[r][c]
            if v in BG_VALUES:
                bg_pool.append(v)
            else:
                char_pool.append(v)

    grid = [[0] * 16 for _ in range(16)]
    for i, (r, c) in enumerate(char_cells):
        grid[r][c] = char_pool[i % len(char_pool)] if char_pool else 0
    for i, (r, c) in enumerate(bg_cells):
        grid[r][c] = bg_pool[i % len(bg_pool)] if bg_pool else 1
    return grid


def build_gap_fill(
    mapping: dict[tuple[int, int], tuple[int, int]] | None,
    gap_width: int,
    gap_height: int = 16,
    seed: int = 42,
) -> list[list[int]]:
    """Build a gap-fill grid from background Cayley cells (non-silhouette targets).

    Collects the Cayley output values for target pixels that fall outside the
    wizard silhouette, shuffles them, and tiles into the gap area.
    """
    # Collect background-only values from non-silhouette target pixels
    bg_pool: list[int] = []
    if mapping:
        for (tr, tc), (sr, sc) in mapping.items():
            is_char = (tr < len(WIZ2_SILHOUETTE) and
                       tc < len(WIZ2_SILHOUETTE[tr]) and
                       WIZ2_SILHOUETTE[tr][tc] == '#')
            if not is_char:
                v = PSI_16_FULL[sr][sc]
                if v in BG_VALUES:
                    bg_pool.append(v)
    if not bg_pool:
        bg_pool = sorted(BG_VALUES) * 20  # fallback

    rng = random.Random(seed)
    rng.shuffle(bg_pool)

    grid = [[0] * gap_width for _ in range(gap_height)]
    if not bg_pool:
        return grid
    for r in range(gap_height):
        for c in range(gap_width):
            grid[r][c] = bg_pool[(r * gap_width + c) % len(bg_pool)]
    return grid


def render_sprite_ansi(
    sprite: list[list[int]],
    palette: dict[int, str],
    indent: str = "  ",
    label: str | None = None,
    dim: bool = False,
) -> str:
    """Render 16x16 sprite as ANSI half-block art (2 pixel rows per text row)."""
    lines = []
    if label:
        lines.append(f"{indent}{DIM}{label}{RST}")
    for row_pair in range(8):
        r_top = row_pair * 2
        r_bot = r_top + 1
        parts = [indent]
        for c in range(16):
            v_top = sprite[r_top][c] if r_top < 16 else 0
            v_bot = sprite[r_bot][c] if r_bot < 16 else 0
            ct = hex_to_rgb(palette.get(v_top, "#000000"))
            cb = hex_to_rgb(palette.get(v_bot, "#000000"))
            if dim:
                ct = tuple(max(0, x // 3) for x in ct)
                cb = tuple(max(0, x // 3) for x in cb)
            parts.append(f"{_fg(*ct)}{_bg(*cb)}\u2580{RST}")
        lines.append("".join(parts))
    return "\n".join(lines)


def render_corrupted_sprite_ansi(
    sprite: list[list[int]],
    mapping: dict[str, list[int]],
    palette: dict[int, str],
    dot_fn,
    indent: str = "  ",
) -> str:
    """Render sprite by re-querying each pixel through the (corrupted) host."""
    grid = [[0] * 16 for _ in range(16)]
    for key, src in mapping.items():
        tr, tc = (int(x) for x in key.split(","))
        sr, sc = src
        grid[tr][tc] = dot_fn(sr, sc)
    return render_sprite_ansi(grid, palette, indent, label="(corrupted)")


# ── Host process ─────────────────────────────────────────────────────────────

def host_main(conn, seed: int = 17) -> None:
    """Host device process: ALU + memory + kick_eval."""
    rng = random.SystemRandom()
    state: dict[str, Any] = {}

    def install_mapping(scramble_seed: int) -> None:
        local = random.Random(scramble_seed)
        perm = list(range(16))
        local.shuffle(perm)
        inv = [0] * 16
        for i, p in enumerate(perm):
            inv[p] = i
        domain = list(range(16))

        def dot_oracle(x: int, y: int) -> int:
            return perm[PSI_16_FULL[inv[x]][inv[y]]]

        ground_truth = {ELEM_NAMES[i]: perm[i] for i in range(16)}

        state["seed"] = scramble_seed
        state["perm"] = perm
        state["inv"] = inv
        state["domain"] = domain
        state["dot_oracle"] = dot_oracle
        state["ground_truth"] = ground_truth

    def runtime_self_check() -> tuple[bool, str]:
        runtime_map = state.get("runtime_role_tokens", {})
        if not isinstance(runtime_map, dict) or len(runtime_map) < 16:
            return False, "runtime mapping unavailable or incomplete"
        dot = state["dot_oracle"]
        checks = [
            ("E", "\u22a4", "\u22a4"),
            ("E", "\u22a5", "\u22a5"),
            ("\u03b7", "\u03c1", "\u03c4"),
        ]
        for left, right, expected in checks:
            lt = runtime_map.get(left)
            rt = runtime_map.get(right)
            et = runtime_map.get(expected)
            if lt is None or rt is None or et is None:
                return False, f"missing role token for {left}/{right}/{expected}"
            if dot(lt, rt) != et:
                return False, f"dot({left},{right}) != {expected}"
        return True, "ok"

    install_mapping(seed)
    state["health"] = "healthy"
    state["radiation_happened"] = False
    state["runtime_role_tokens"] = {
        name: state["ground_truth"][name] for name in ELEM_NAMES.values()
    }

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
            x, y = msg["x"], msg["y"]
            conn.send({"ok": True, "value": state["dot_oracle"](x, y)})

        elif cmd == "scramble":
            requested = msg.get("seed")
            ss = int(requested) if requested is not None else rng.randrange(1, 2**31)
            install_mapping(ss)
            state["health"] = "corrupted sigils"
            state["runtime_role_tokens"] = {}
            memory["sys"]["health"] = state["health"]
            memory["sys"]["domain"] = state["domain"]
            memory["sys"]["scramble_seed"] = ss
            conn.send({"ok": True, "seed": ss})

        elif cmd == "apply_recovery":
            role_map = msg.get("role_of_token", {})
            state["runtime_role_tokens"] = {
                role: int(tok) for tok, role in role_map.items()
            }
            state["health"] = "healthy"
            memory["sys"]["health"] = "healthy"
            conn.send({"ok": True, "health": "healthy", "accepted": len(role_map)})

        elif cmd == "mem_write":
            bank, key, val = msg["bank"], msg["key"], msg["value"]
            memory.setdefault(bank, {})[key] = val
            conn.send({"ok": True})

        elif cmd == "mem_read":
            bank, key = msg["bank"], msg["key"]
            conn.send({"ok": True, "value": memory.get(bank, {}).get(key)})

        elif cmd == "kick_eval":
            bank, key = msg["bank"], msg["key"]
            source = memory.get(bank, {}).get(key)
            if source is None:
                conn.send({"ok": False, "error": f"no source at {bank}/{key}"})
                continue
            ok_rt, msg_rt = runtime_self_check()
            if not ok_rt:
                conn.send({"ok": False, "error": f"runtime check failed: {msg_rt}"})
                continue
            try:
                from psi_repl import ENV, eval_string, format_val
                ENV.clear()
                buf = io.StringIO()
                with redirect_stdout(buf):
                    result = eval_string(source)
                stdout_str = buf.getvalue()
                result_str = format_val(result)
                memory.setdefault("out", {})
                memory["out"]["status"] = "ok"
                memory["out"]["stdout"] = stdout_str
                memory["out"]["result"] = result_str
                conn.send({
                    "ok": True,
                    "stdout": stdout_str,
                    "result": result_str,
                })
                if not state["radiation_happened"]:
                    # Side-effect: radiation scrambles host
                    rng_seed = rng.randrange(1, 2**31)
                    install_mapping(rng_seed)
                    state["health"] = "corrupted sigils"
                    state["runtime_role_tokens"] = {}
                    memory["sys"]["health"] = state["health"]
                    memory["sys"]["domain"] = state["domain"]
                    memory["sys"]["scramble_seed"] = rng_seed
                    state["radiation_happened"] = True
            except Exception as exc:
                memory.setdefault("out", {})
                memory["out"]["status"] = "error"
                memory["out"]["stdout"] = ""
                memory["out"]["result"] = str(exc)
                conn.send({"ok": False, "error": str(exc)})

        elif cmd == "shutdown":
            conn.send({"ok": True})
            break

        else:
            conn.send({"ok": False, "error": f"unknown: {cmd}"})


# ── Remote host wrapper ──────────────────────────────────────────────────────

class RemoteHost:
    def __init__(self, conn, trace: bool = True):
        self.conn = conn
        self.trace = trace

    def _req(self, cmd: str, **kw) -> dict[str, Any]:
        msg = {"cmd": cmd, **kw}
        if self.trace:
            abbr = {k: v for k, v in kw.items() if k not in ("value",)}
            extra = f" {abbr}" if abbr else ""
            print(f"  {DIM}\u2192 {cmd}{extra}{RST}")
        self.conn.send(msg)
        resp = self.conn.recv()
        if not resp.get("ok") and cmd not in ("kick_eval",):
            raise RuntimeError(resp.get("error", "request failed"))
        return resp

    def dot(self, x: int, y: int) -> int:
        return self._req("dot", x=x, y=y)["value"]

    def scramble(self, seed: int | None = None) -> int:
        kw = {"seed": seed} if seed is not None else {}
        return self._req("scramble", **kw)["seed"]

    def mem_write(self, bank: str, key: str, value: Any) -> None:
        self._req("mem_write", bank=bank, key=key, value=value)

    def mem_read(self, bank: str, key: str) -> Any:
        return self._req("mem_read", bank=bank, key=key)["value"]

    def kick_eval(self, bank: str, key: str) -> dict:
        return self._req("kick_eval", bank=bank, key=key)

    def apply_recovery(self, role_of_token: dict[str, str]) -> dict:
        return self._req("apply_recovery", role_of_token=role_of_token)

    def shutdown(self) -> None:
        self._req("shutdown")


# ── Session launcher ─────────────────────────────────────────────────────────

def _mp_context():
    if sys.platform == "darwin":
        try:
            return mp.get_context("fork")
        except ValueError:
            pass
    return mp.get_context()


def start_session(seed: int = 17, trace: bool = True) -> tuple[RemoteHost, Any]:
    ctx = _mp_context()
    parent, child = ctx.Pipe()
    proc = ctx.Process(target=host_main, args=(child, seed), daemon=False)
    proc.start()
    try:
        child.close()
    except Exception:
        pass
    return RemoteHost(parent, trace=trace), proc


# ── Narrative helpers (plain mode) ───────────────────────────────────────────

def section(title: str) -> None:
    w = 60
    print(f"\n{'\u2500' * w}")
    print(f"  {BOLD}{title}{RST}")
    print(f"{'\u2500' * w}")


def narrate(text: str) -> None:
    print(f"  {_fg(160, 180, 200)}{text}{RST}")


def result_line(label: str, value: str, ok: bool = True) -> None:
    color = _fg(120, 220, 140) if ok else _fg(220, 80, 80)
    print(f"  {color}{'\u2713' if ok else '\u2717'} {label}: {value}{RST}")


# ═══════════════════════════════════════════════════════════════════════════
# TEXTUAL TUI
# ═══════════════════════════════════════════════════════════════════════════

if TEXTUAL_AVAILABLE:

    def _blend(c1: tuple[int, int, int], c2: tuple[int, int, int], t: float) -> tuple[int, int, int]:
        """Blend c1 toward c2 by factor t (0=c1, 1=c2)."""
        t = max(0.0, min(1.0, t))
        return (
            int(c1[0] + (c2[0] - c1[0]) * t),
            int(c1[1] + (c2[1] - c1[1]) * t),
            int(c1[2] + (c2[2] - c1[2]) * t),
        )

    def _rgb_hex(r: int, g: int, b: int) -> str:
        return f"#{r:02x}{g:02x}{b:02x}"

    # Mirrored silhouette for right wizard (facing left)
    WIZ2_SILHOUETTE_MIRROR = [row[::-1] for row in WIZ2_SILHOUETTE]

    BEAM_GAP = 18  # chars between the two wizards

    class SpriteScene(Widget):
        """Widget that renders two wiz2 sprites facing each other with beam and speech bubbles."""

        def __init__(self, **kwargs):
            super().__init__(**kwargs)
            self._palette = dict(DEFAULT_PALETTE)
            self._grid: list[list[int]] = []
            self._corrupted_grid: list[list[int]] | None = None
            self._left_speech_text: str | None = None
            self._left_speech_error: bool = False
            self._right_speech_text: str | None = None
            self._right_speech_error: bool = False
            self._status_text: str = ""
            self._frame = 0

            # Effects state
            self._glow_color: tuple[int, int, int] | None = None
            self._glow_until: float = 0.0
            self._curse_until: float = 0.0
            self._beam_input_rgb: tuple[int, int, int] = (128, 128, 128)
            self._beam_output_rgb: tuple[int, int, int] = (128, 128, 128)
            self._beam_until: float = 0.0

            # Pixel-level restore tracking
            self._atom_to_pixels: dict[int, list[tuple[int, int]]] = {}
            self._restored_pixels: set[tuple[int, int]] = set()

            # Gap fill texture (set by init_gap_fill)
            self._gap_fill: list[list[int]] = []

        def on_mount(self) -> None:
            self.set_interval(0.12, self._tick)

        def _tick(self) -> None:
            self._frame += 1
            self.refresh()

        def render(self):
            """Override render to return Content for Textual 8+."""
            text = self._build_scene()
            if _HAS_CONTENT:
                return Content.from_rich_text(text)
            return text

        def set_grid(self, grid: list[list[int]]) -> None:
            self._grid = grid
            self._corrupted_grid = None

        def set_corrupted_grid(self, grid: list[list[int]]) -> None:
            self._corrupted_grid = grid

        def set_left_speech(self, text: str | None, error: bool = False) -> None:
            self._left_speech_text = text
            self._left_speech_error = error

        def set_right_speech(self, text: str | None, error: bool = False) -> None:
            self._right_speech_text = text
            self._right_speech_error = error

        def set_status(self, text: str) -> None:
            self._status_text = text

        def fire_glow(self, color: tuple[int, int, int], duration: float = 0.3) -> None:
            self._glow_color = color
            self._glow_until = time.monotonic() + duration

        def fire_curse(self, duration: float = 1.5) -> None:
            self._curse_until = time.monotonic() + duration

        def fire_beam(self, input_rgb: tuple[int, int, int], output_rgb: tuple[int, int, int], duration: float = 0.3) -> None:
            self._beam_input_rgb = input_rgb
            self._beam_output_rgb = output_rgb
            self._beam_until = time.monotonic() + duration

        def init_gap_fill(self, mapping: dict[tuple[int, int], tuple[int, int]] | None) -> None:
            self._gap_fill = build_gap_fill(mapping, BEAM_GAP, 16)

        def init_atom_pixel_map(self, mapping: dict[tuple[int, int], tuple[int, int]]) -> None:
            """Build reverse index: canonical atom value → list of pixel positions."""
            self._atom_to_pixels = {}
            for (tr, tc), (sr, sc) in mapping.items():
                val = PSI_16_FULL[sr][sc]
                self._atom_to_pixels.setdefault(val, []).append((tr, tc))
            self._restored_pixels = set()

        def restore_pixels_for_atoms(self, canonical_indices: set[int]) -> None:
            """Restore pixels whose source Cayley cell outputs one of the given canonical atoms."""
            for k in canonical_indices:
                for pos in self._atom_to_pixels.get(k, []):
                    self._restored_pixels.add(pos)

        def finish_restore(self) -> None:
            self._corrupted_grid = None
            self._restored_pixels = set()

        @staticmethod
        def _mirror_grid(grid: list[list[int]]) -> list[list[int]]:
            return [row[::-1] for row in grid]

        def _build_scene(self) -> Text:
            now = time.monotonic()
            glow_active = now < self._glow_until
            curse_active = now < self._curse_until
            beam_active = now < self._beam_until

            if not self._grid:
                return Text("(no sprite loaded)")

            # Left wizard: always clean
            left_display = self._grid

            # Right wizard: corrupted → restoring → clean, then mirrored
            if self._corrupted_grid is not None:
                if self._restored_pixels:
                    right_pre = [row[:] for row in self._corrupted_grid]
                    for (r, c) in self._restored_pixels:
                        right_pre[r][c] = self._grid[r][c]
                else:
                    right_pre = self._corrupted_grid
            else:
                right_pre = self._grid
            right_display = self._mirror_grid(right_pre)

            scene = Text()

            # Status line at top
            if self._status_text:
                scene.append(f"  {self._status_text}\n")

            dark = (11, 16, 32)

            # Beam on row_pairs 3 and 4 (input beam top, output beam bottom)
            beam_input_row_pair = 3
            beam_output_row_pair = 4

            gap_fill = self._gap_fill

            # Build speech bubbles for inline placement
            BUBBLE_COL_W = 34  # fixed column width so graphics don't shift
            left_bubble = self._build_bubble(self._left_speech_text, BUBBLE_COL_W)
            right_bubble = self._build_bubble(self._right_speech_text, BUBBLE_COL_W)
            left_style = "bold #ff9b8f" if self._left_speech_error else "bold #b3f3ff"
            right_style = "bold #ff9b8f" if self._right_speech_error else "bold #b3f3ff"
            bubble_start = 1  # start bubbles at row_pair 1

            for row_pair in range(8):
                r_top = row_pair * 2
                r_bot = r_top + 1

                # ── Left speech bubble (right-aligned, fixed-width column) ──
                bidx = row_pair - bubble_start
                if 0 <= bidx < len(left_bubble):
                    line = left_bubble[bidx]
                    pad = BUBBLE_COL_W - len(line)
                    if pad > 0:
                        scene.append(" " * pad)
                    scene.append(line, style=left_style)
                    scene.append(" ")
                    # fill remaining if line + pad + 1 < BUBBLE_COL_W + 1
                else:
                    scene.append(" " * (BUBBLE_COL_W + 1))

                # ── Left wizard (16 pixels) ──
                for c in range(16):
                    v_top = left_display[r_top][c]
                    v_bot = left_display[r_bot][c]
                    fg_rgb = hex_to_rgb(self._palette.get(v_top, "#000000"))
                    bg_rgb = hex_to_rgb(self._palette.get(v_bot, "#000000"))

                    is_char_top = (r_top < len(WIZ2_SILHOUETTE) and
                                   c < len(WIZ2_SILHOUETTE[r_top]) and
                                   WIZ2_SILHOUETTE[r_top][c] == '#')
                    is_char_bot = (r_bot < len(WIZ2_SILHOUETTE) and
                                   c < len(WIZ2_SILHOUETTE[r_bot]) and
                                   WIZ2_SILHOUETTE[r_bot][c] == '#')

                    if glow_active and self._glow_color:
                        if is_char_top:
                            fg_rgb = _blend(fg_rgb, self._glow_color, 0.5)
                        if is_char_bot:
                            bg_rgb = _blend(bg_rgb, self._glow_color, 0.5)

                    scene.append("\u2580", style=f"{_rgb_hex(*fg_rgb)} on {_rgb_hex(*bg_rgb)}")

                # ── Gap / beam (BEAM_GAP chars) ──
                if beam_active and row_pair == beam_input_row_pair:
                    scene.append("\u2501" * BEAM_GAP, style=f"{_rgb_hex(*self._beam_input_rgb)} on {_rgb_hex(*dark)}")
                elif beam_active and row_pair == beam_output_row_pair:
                    scene.append("\u2501" * BEAM_GAP, style=f"{_rgb_hex(*self._beam_output_rgb)} on {_rgb_hex(*dark)}")
                else:
                    # Fill gap with texture from unused Cayley cells
                    for gc in range(BEAM_GAP):
                        vt = gap_fill[r_top][gc] if gap_fill and r_top < len(gap_fill) and gc < len(gap_fill[r_top]) else 0
                        vb = gap_fill[r_bot][gc] if gap_fill and r_bot < len(gap_fill) and gc < len(gap_fill[r_bot]) else 0
                        ft = hex_to_rgb(self._palette.get(vt, "#000000"))
                        fb = hex_to_rgb(self._palette.get(vb, "#000000"))
                        scene.append("\u2580", style=f"{_rgb_hex(*ft)} on {_rgb_hex(*fb)}")

                # ── Right wizard (16 pixels, mirrored) ──
                for c in range(16):
                    v_top = right_display[r_top][c]
                    v_bot = right_display[r_bot][c]
                    fg_rgb = hex_to_rgb(self._palette.get(v_top, "#000000"))
                    bg_rgb = hex_to_rgb(self._palette.get(v_bot, "#000000"))

                    is_char_top = (r_top < len(WIZ2_SILHOUETTE_MIRROR) and
                                   c < len(WIZ2_SILHOUETTE_MIRROR[r_top]) and
                                   WIZ2_SILHOUETTE_MIRROR[r_top][c] == '#')
                    is_char_bot = (r_bot < len(WIZ2_SILHOUETTE_MIRROR) and
                                   c < len(WIZ2_SILHOUETTE_MIRROR[r_bot]) and
                                   WIZ2_SILHOUETTE_MIRROR[r_bot][c] == '#')

                    if curse_active:
                        if is_char_top:
                            shift = ((self._frame * 37 + r_top * 13 + c * 7) % 360)
                            fg_rgb = _hue_shift(fg_rgb, shift)
                        if is_char_bot:
                            shift = ((self._frame * 41 + r_bot * 17 + c * 11) % 360)
                            bg_rgb = _hue_shift(bg_rgb, shift)

                    if glow_active and self._glow_color:
                        if is_char_top:
                            fg_rgb = _blend(fg_rgb, self._glow_color, 0.5)
                        if is_char_bot:
                            bg_rgb = _blend(bg_rgb, self._glow_color, 0.5)

                    scene.append("\u2580", style=f"{_rgb_hex(*fg_rgb)} on {_rgb_hex(*bg_rgb)}")

                # ── Right speech bubble (left-aligned, fixed-width column) ──
                if 0 <= bidx < len(right_bubble):
                    scene.append(" ")
                    line = right_bubble[bidx]
                    scene.append(line, style=right_style)
                    pad = BUBBLE_COL_W - len(line)
                    if pad > 0:
                        scene.append(" " * pad)
                else:
                    scene.append(" " * (BUBBLE_COL_W + 1))

                scene.append("\n")

            return scene

        @staticmethod
        def _build_bubble(text: str | None, max_width: int = 16) -> list[str]:
            if not text:
                return []
            wrap_at = max(max_width - 4, 8)
            words = text.split()
            lines: list[str] = []
            current = ""
            for w in words:
                if current and cell_len(current) + 1 + cell_len(w) > wrap_at:
                    lines.append(current)
                    current = w
                else:
                    current = f"{current} {w}" if current else w
            if current:
                lines.append(current)

            width = max((cell_len(l) for l in lines), default=0)
            width = max(width, 4)
            top = f".-{'-' * width}-."
            body = [f"| {l}{' ' * max(0, width - cell_len(l))} |" for l in lines]
            bottom = f"'-{'-' * width}-'"
            return [top, *body, bottom]

    # Rainbow palette from corrupted_host_bootstrap_demo.py
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

    def _build_rainbow_banner() -> Text:
        """Load ascii_header.txt and render with rainbow stripe colors."""
        header_path = Path(__file__).with_name("ascii_header.txt")
        try:
            header_text = header_path.read_text(encoding="utf-8").rstrip("\n")
        except OSError:
            return Text("\u03a8\u2081\u2086\u1da0 Corrupted-Host Bootstrap")
        if not header_text:
            return Text("\u03a8\u2081\u2086\u1da0 Corrupted-Host Bootstrap")

        result = Text()
        colors = RAINBOW_HEADER_COLORS
        for row_idx, line in enumerate(header_text.splitlines()):
            start = 0 if (row_idx % 2) else -1
            for col in range(start, len(line), 2):
                chunk = line[max(0, col):col + 2]
                if not chunk:
                    continue
                color_idx = (row_idx // 2 + max(0, col + 2) // 2) % len(colors)
                r, g, b = colors[color_idx]
                result.append(chunk, style=f"#{r:02x}{g:02x}{b:02x}")
            result.append("\n")
        result.append("  press q to quit", style="dim")
        return result

    def _hue_shift(rgb: tuple[int, int, int], degrees: int) -> tuple[int, int, int]:
        """Quick hue rotation for curse flicker effect."""
        r, g, b = rgb
        # Simple channel rotation + noise
        if degrees < 120:
            return (g, b, r)
        elif degrees < 240:
            return (b, r, g)
        else:
            return ((r + 80) % 256, (g + 60) % 256, (b + 100) % 256)


    class PsiCorruptedHostApp(App):
        CSS = """
        Screen {
            layout: vertical;
            background: #0b1020;
            color: #d7dde8;
        }

        #banner {
            height: 9;
            border: round #30446b;
            content-align: center middle;
            color: #d7dde8;
        }

        #scene {
            height: 18;
            border: round #3b5079;
            padding: 0 1;
            content-align: center top;
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
            banner = Static(id="banner")
            banner.update(_build_rainbow_banner())
            yield banner
            yield SpriteScene(id="scene")
            with Horizontal(id="console_row"):
                yield RichLog(id="client_console", wrap=True, markup=False, auto_scroll=True)
                yield RichLog(id="host_console", wrap=True, markup=False, auto_scroll=True)

        def on_mount(self) -> None:
            self.client_console = self.query_one("#client_console", RichLog)
            self.host_console = self.query_one("#host_console", RichLog)
            self.scene = self.query_one("#scene", SpriteScene)
            self.client_console.border_title = "Client Console"
            self.host_console.border_title = "Host Console"

            # Load sprite
            wiz2_mapping = load_wiz2_mapping()
            self._sprite = build_sprite_grid(wiz2_mapping)
            self._wiz2_raw: dict[str, list[int]] = {}
            self._wiz2_tuple: dict[tuple[int, int], tuple[int, int]] = {}
            if wiz2_mapping:
                for (tr, tc), (sr, sc) in wiz2_mapping.items():
                    self._wiz2_raw[f"{tr},{tc}"] = [sr, sc]
                    self._wiz2_tuple[(tr, tc)] = (sr, sc)
            else:
                for r in range(16):
                    for c in range(16):
                        self._wiz2_raw[f"{r},{c}"] = [r, c]
                        self._wiz2_tuple[(r, c)] = (r, c)

            self.scene.set_grid(self._sprite)
            self.scene.init_gap_fill(wiz2_mapping)

            # Launch host + story
            self._host = None
            self._proc = None
            try:
                self._host, self._proc = start_session(seed=17, trace=False)
            except Exception as exc:
                self.client_console.write(f"[error] failed to launch host: {exc}")
                self.exit()
                return
            self.run_worker(self._run_story_thread, thread=True, exclusive=True)

        def on_unmount(self) -> None:
            self._cleanup_host()

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
                return

            palette = dict(DEFAULT_PALETTE)
            query_counter = 0
            visual_stride = 11

            def clog(msg: str) -> None:
                self.call_from_thread(self.client_console.write, msg)

            def hlog(msg: str) -> None:
                self.call_from_thread(self.host_console.write, msg)

            def set_left_speech(text: str | None, error: bool = False) -> None:
                self.call_from_thread(self.scene.set_left_speech, text, error)

            def set_right_speech(text: str | None, error: bool = False) -> None:
                self.call_from_thread(self.scene.set_right_speech, text, error)

            def set_status(text: str) -> None:
                self.call_from_thread(self.scene.set_status, text)

            def flow_speech_slow(text: str, error: bool = False, cps: float = 18.0, side: str = "left", unstable_at: int | None = None) -> None:
                """Character-by-character speech bubble reveal.

                If unstable_at is set, switch to error styling after that
                character index (simulates corruption onset mid-sentence).
                """
                if not text:
                    return
                setter = self.scene.set_left_speech if side == "left" else self.scene.set_right_speech
                delay = 1.0 / max(cps, 1.0)
                shown: list[str] = []
                for i, ch in enumerate(text):
                    shown.append(ch)
                    use_error = error or (unstable_at is not None and i >= unstable_at)
                    self.call_from_thread(setter, "".join(shown), use_error)
                    if ch == "\n":
                        time.sleep(delay * 5.0)
                    elif ch in ".!?\u2014":
                        time.sleep(delay * 3.0)
                    else:
                        time.sleep(delay)

            def dot_with_fx(x: int, y: int) -> int:
                nonlocal query_counter
                query_counter += 1
                show_fx = (query_counter % visual_stride) == 0
                if show_fx:
                    in_rgb = hex_to_rgb(palette.get(x % 16, "#ffffff"))
                    self.call_from_thread(
                        self.scene.fire_beam,
                        in_rgb, (80, 80, 80), 0.6,
                    )
                    clog(f"cast dot({x}, {y})")
                out = host.dot(x, y)
                if show_fx:
                    out_rgb = hex_to_rgb(palette.get(out % 16, "#ffffff"))
                    self.call_from_thread(self.scene.fire_beam, in_rgb, out_rgb, 0.5)
                    self.call_from_thread(self.scene.fire_glow, out_rgb, 0.3)
                    hlog(f"response => {out}")
                    time.sleep(0.4)
                return out

            hello_program = '(do (print "Hello from Psi*!") :top)'
            final_program = '(do (print "The curse is lifted!") :top)'

            try:
                # ── Phase 1: Healthy ──
                set_status("Phase 1: Healthy host")
                time.sleep(0.5)

                health = host.mem_read("sys", "health")
                clog(f"host health: {health}")
                hlog(f"health={health}")
                time.sleep(0.5)

                # Upload and run hello program
                host.mem_write("prog", "main", hello_program)
                clog("uploaded hello program")
                result = host.kick_eval("prog", "main")
                if result.get("ok"):
                    stdout = result.get("stdout", "").strip()
                    if stdout:
                        hlog(f"stdout: {stdout}")
                    hlog(f"result: {result.get('result')}")
                    flow_speech_slow("Hello from Psi*! All systems nominal.", cps=16.0, side="right")
                else:
                    hlog(f"error: {result.get('error')}")
                time.sleep(1.0)

                # ── Phase 2: Curse (auto-triggered by kick_eval side-effect) ──
                set_status("Phase 2: Sigil scramble curse")
                set_right_speech(None)
                time.sleep(0.3)

                # Progressive corruption speech — detect garbled char onset
                warning = HOST_OPENING_WARNING
                # Find first non-ASCII char as corruption onset point
                unstable_idx = None
                for ci, ch in enumerate(warning):
                    if ord(ch) > 127 and ch not in '\u2014':
                        unstable_idx = ci
                        break
                flow_speech_slow(warning, cps=14.0, side="right", unstable_at=unstable_idx)
                time.sleep(0.5)

                # Discover corruption organically by reading sys/health
                post_health = host.mem_read("sys", "health")
                clog(f"host health check: {post_health}")

                if post_health == "corrupted sigils":
                    scramble_seed = host.mem_read("sys", "scramble_seed")
                    clog(f"corruption detected! (seed={scramble_seed})")
                    hlog(f"CORRUPTED (seed={scramble_seed})")

                # Build corrupted sprite by re-querying through garbled oracle
                corrupted = [[0] * 16 for _ in range(16)]
                for key, src in self._wiz2_raw.items():
                    tr, tc = (int(x) for x in key.split(","))
                    sr, sc = src
                    corrupted[tr][tc] = host.dot(sr, sc)
                self.call_from_thread(self.scene.set_corrupted_grid, corrupted)
                self.call_from_thread(self.scene.fire_curse, 1.5)
                time.sleep(0.5)

                # kick_eval should fail now
                host.mem_write("prog", "main", hello_program)
                result2 = host.kick_eval("prog", "main")
                if result2.get("ok"):
                    hlog("unexpectedly still working")
                else:
                    hlog(f"kick_eval FAILED: {result2.get('error')}")
                    set_right_speech(f"Error: {result2.get('error')}", error=True)
                time.sleep(1.5)

                # ── Phase 3: Recovery ──
                set_status("Phase 3: Black-box recovery")
                set_right_speech(None)
                time.sleep(0.3)

                flow_speech_slow("Fear not! I shall cast the recovery spell \u2014\nwritten in the algebra's own tongue,\nspeaking only through its own voice.", cps=15.0, side="left")
                time.sleep(1.0)
                set_left_speech(None)

                domain = host.mem_read("sys", "domain")
                clog(f"opaque domain: {len(domain)} labels")

                # Init pixel map for atom-based restore
                self.call_from_thread(self.scene.init_atom_pixel_map, self._wiz2_tuple)

                t0 = time.monotonic()
                dot_calls = [0]

                def counted_dot_fx(x, y):
                    dot_calls[0] += 1
                    return dot_with_fx(x, y)

                def on_report(idx, label):
                    name = ELEM_NAMES.get(idx, f"s{idx}")
                    clog(f"[recover] identified: {name}")
                    self.call_from_thread(self.scene.restore_pixels_for_atoms, {idx})
                    time.sleep(0.25)

                def on_status(phase, snippet):
                    set_left_speech(snippet)
                    time.sleep(0.4)

                rec = _run_spell(domain, counted_dot_fx, report_fn=on_report, status_fn=on_status)
                set_left_speech(None)
                dt = time.monotonic() - t0
                clog(f"recovery: {dt:.2f}s, {dot_calls[0]} dot calls")

                # Verify axioms
                clog("verifying axioms...")
                axiom_results = verify_axioms(counted_dot_fx, rec)
                all_ok = True
                for aname, passed in axiom_results:
                    mark = "\u2713" if passed else "\u2717"
                    clog(f"  {mark} {aname}")
                    if not passed:
                        all_ok = False

                clog(f"axioms: {'ALL PASS' if all_ok else 'FAILURES'}")

                # Apply recovery
                role_of_token = {str(tok): name for name, tok in rec.items()}
                resp = host.apply_recovery(role_of_token)
                hlog(f"recovery applied: accepted={resp.get('accepted')}")

                # Finish restore
                self.call_from_thread(self.scene.finish_restore)
                time.sleep(0.5)

                # ── Phase 4: Restored ──
                set_status("Phase 4: Restored")

                # Glow gold
                self.call_from_thread(self.scene.fire_glow, (232, 192, 144), 1.0)

                # Run final program
                host.mem_write("prog", "main", final_program)
                result3 = host.kick_eval("prog", "main")
                if result3.get("ok"):
                    stdout = result3.get("stdout", "").strip()
                    if stdout:
                        hlog(f"stdout: {stdout}")
                    hlog(f"result: {result3.get('result')}")
                    flow_speech_slow("The curse is lifted!", cps=14.0, side="right")
                else:
                    hlog(f"post-recovery FAILED: {result3.get('error')}")
                    set_right_speech(f"Error: {result3.get('error')}", error=True)

                clog("blackbox ritual complete")
                set_status("Complete - press q to quit")

            except Exception as exc:
                clog(f"[error] {exc}")
                hlog("story aborted")
                set_status("Error - press q to quit")
            finally:
                self.call_from_thread(self._cleanup_host)


# ═══════════════════════════════════════════════════════════════════════════
# PLAIN MODE (original print-based demo)
# ═══════════════════════════════════════════════════════════════════════════

def run_plain_demo() -> None:
    palette = dict(DEFAULT_PALETTE)
    wiz2_mapping = load_wiz2_mapping()
    sprite = build_sprite_grid(wiz2_mapping)
    wiz2_raw: dict[str, list[int]] = {}
    if wiz2_mapping:
        for (tr, tc), (sr, sc) in wiz2_mapping.items():
            wiz2_raw[f"{tr},{tc}"] = [sr, sc]
    else:
        for r in range(16):
            for c in range(16):
                wiz2_raw[f"{r},{c}"] = [r, c]

    print()
    print(f"  {BOLD}{_fg(180, 140, 255)}\u03a8\u2081\u2086\u1da0 Corrupted-Host Bootstrap Demo{RST}")
    print(f"  {DIM}16-element algebra \u00b7 bijective sprite \u00b7 multiprocessing pipe{RST}")

    # ── Phase 1: Healthy state ──
    section("Phase 1: Healthy Host")
    host, proc = start_session(seed=17, trace=False)

    try:
        health = host.mem_read("sys", "health")
        result_line("Host health", health, health == "healthy")

        print()
        narrate("Wizard sprite (canonical coloring):")
        print(render_sprite_ansi(sprite, palette, indent="    "))
        print()

        # Legend
        parts = []
        for v in range(16):
            name = ELEM_NAMES[v]
            rgb = hex_to_rgb(palette[v])
            tc = text_color(palette[v])
            parts.append(f"{_bg(*rgb)}{tc} {name} {RST}")
        print(f"    {''.join(parts)}")
        print()

        narrate("Recovering initial mapping from healthy host...")
        domain = host.mem_read("sys", "domain")
        init_rec = recover_adaptive(domain, host.dot)
        e_tok = init_rec["E"]
        top_tok = init_rec["\u22a4"]
        bot_tok = init_rec["\u22a5"]
        e_top = host.dot(e_tok, top_tok)
        e_bot = host.dot(e_tok, bot_tok)
        result_line("E\u00b7\u22a4 = \u22a4", f"dot({e_tok},{top_tok}) = {e_top}", e_top == top_tok)
        result_line("E\u00b7\u22a5 = \u22a5", f"dot({e_tok},{bot_tok}) = {e_bot}", e_bot == bot_tok)

        # kick_eval test
        hello_program = '(do (print "Hello from Psi*!") :top)'
        host.mem_write("prog", "main", hello_program)
        result1 = host.kick_eval("prog", "main")
        if result1.get("ok"):
            narrate(f"kick_eval stdout: {result1.get('stdout', '').strip()}")
            result_line("kick_eval", result1.get("result", ""), True)
        else:
            result_line("kick_eval", result1.get("error", ""), False)

        # ── Phase 2: Corruption (auto-triggered by kick_eval side-effect) ──
        section("Phase 2: Sigil Scramble Curse")

        # Discover corruption organically by reading sys/health
        post_health = host.mem_read("sys", "health")
        if post_health == "corrupted sigils":
            scramble_seed = host.mem_read("sys", "scramble_seed")
            narrate(f"Corruption detected! Host scrambled (seed={scramble_seed})")
        else:
            narrate("No corruption detected (unexpected)")
            scramble_seed = None
        result_line("Host health", post_health, post_health == "healthy")

        print()
        narrate("Wizard sprite under scrambled sigils:")
        print(render_corrupted_sprite_ansi(sprite, wiz2_raw, palette, host.dot, indent="    "))
        print()

        narrate("Same dot query with scrambled labels...")
        e_top_scram = host.dot(init_rec["E"], init_rec["\u22a4"])
        result_line(
            "E\u00b7\u22a4 = \u22a4 (old labels)",
            f"got {e_top_scram} \u2014 {'correct' if e_top_scram == init_rec['\u22a4'] else 'WRONG'}",
            e_top_scram == init_rec["\u22a4"],
        )

        # kick_eval should fail
        result2 = host.kick_eval("prog", "main")
        if result2.get("ok"):
            result_line("kick_eval (post-curse)", "unexpectedly succeeded", False)
        else:
            result_line("kick_eval (post-curse)", f"FAILED: {result2.get('error')}", False)

        # ── Phase 3: Recovery ──
        section("Phase 3: Black-Box Recovery")

        domain = host.mem_read("sys", "domain")
        narrate(f"Opaque domain: {len(domain)} labels")

        dot_calls = [0]
        def counted_dot(x, y):
            dot_calls[0] += 1
            return host.dot(x, y)

        def on_report(idx, label):
            name = ELEM_NAMES.get(idx, f"s{idx}")
            narrate(f"identified: {name}")

        def on_status(phase, snippet):
            print(f"    {DIM}{snippet}{RST}")

        narrate("Running \u03a8-Lisp recovery spell...")
        t0 = time.monotonic()
        rec = _run_spell(domain, counted_dot, report_fn=on_report, status_fn=on_status)
        dt = time.monotonic() - t0

        result_line("Recovery time", f"{dt:.3f}s, {dot_calls[0]} dot calls", True)

        narrate("Recovered element mapping:")
        for name in ["\u22a4", "\u22a5", "f", "\u03c4", "g", "SEQ", "Q", "E",
                      "\u03c1", "\u03b7", "Y", "PAIR", "s0", "INC", "s1", "DEC"]:
            tok = rec[name]
            idx = list(ELEM_NAMES.values()).index(name) if name in ELEM_NAMES.values() else 0
            rgb = hex_to_rgb(palette.get(idx, "#888888"))
            print(f"    {_fg(*rgb)}{name:>4}{RST} \u2192 label {tok}")

        narrate("Verifying axioms on recovered mapping...")
        axiom_results = verify_axioms(counted_dot, rec)
        all_ok = True
        for aname, passed in axiom_results:
            result_line(aname, "pass" if passed else "FAIL", passed)
            if not passed:
                all_ok = False

        # ── Phase 4: Apply recovery ──
        section("Phase 4: Restored Host")

        role_of_token = {str(tok): name for name, tok in rec.items()}
        resp = host.apply_recovery(role_of_token)
        result_line("Recovery applied", f"accepted={resp.get('accepted')} health={resp.get('health')}", resp.get("health") == "healthy")

        print()
        narrate("Wizard sprite after recovery:")
        print(render_sprite_ansi(sprite, palette, indent="    "))
        print()

        # Post-recovery dot check
        e_tok = rec["E"]
        top_tok = rec["\u22a4"]
        bot_tok = rec["\u22a5"]
        narrate("Post-recovery dot check using recovered labels...")
        e_top_rec = host.dot(e_tok, top_tok)
        e_bot_rec = host.dot(e_tok, bot_tok)
        result_line("E\u00b7\u22a4 = \u22a4", f"dot({e_tok},{top_tok}) = {e_top_rec}", e_top_rec == top_tok)
        result_line("E\u00b7\u22a5 = \u22a5", f"dot({e_tok},{bot_tok}) = {e_bot_rec}", e_bot_rec == bot_tok)

        # Post-recovery kick_eval
        final_program = '(do (print "The curse is lifted!") :top)'
        host.mem_write("prog", "main", final_program)
        result3 = host.kick_eval("prog", "main")
        if result3.get("ok"):
            narrate(f"kick_eval stdout: {result3.get('stdout', '').strip()}")
            result_line("kick_eval (restored)", result3.get("result", ""), True)
        else:
            result_line("kick_eval (restored)", f"FAILED: {result3.get('error')}", False)

        # Read back out bank
        out_status = host.mem_read("out", "status")
        out_stdout = host.mem_read("out", "stdout")
        out_result = host.mem_read("out", "result")
        narrate(f"out bank: status={out_status}, result={out_result}")

        # Final summary
        section("Summary")
        narrate(f"Dot oracle calls: {dot_calls[0]}")
        narrate(f"All axioms verified: {'yes' if all_ok else 'NO'}")
        narrate("Host fully restored from opaque scramble.")
        print()

    finally:
        try:
            host.shutdown()
        except Exception:
            pass
        proc.join(timeout=2)


# ═══════════════════════════════════════════════════════════════════════════
# ENTRY POINT
# ═══════════════════════════════════════════════════════════════════════════

def run_textual_demo() -> None:
    if not TEXTUAL_AVAILABLE:
        raise RuntimeError(
            "Textual mode requires: pip install textual rich"
        )
    app = PsiCorruptedHostApp()
    app.run()


def main() -> None:
    import argparse
    ap = argparse.ArgumentParser(description="\u03a8\u2081\u2086\u1da0 Corrupted-host bootstrap demo")
    ap.add_argument("--plain", action="store_true", help="Plain print-based mode (no TUI)")
    ap.add_argument("--tui", action="store_true", help="Force Textual TUI mode")
    args = ap.parse_args()

    if args.plain:
        run_plain_demo()
        return
    if args.tui:
        run_textual_demo()
        return
    if TEXTUAL_AVAILABLE:
        run_textual_demo()
        return
    print("Textual not found; running plain mode. Install `textual rich` to enable TUI.")
    run_plain_demo()


if __name__ == "__main__":
    main()

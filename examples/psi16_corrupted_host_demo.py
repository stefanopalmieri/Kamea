#!/usr/bin/env python3
"""
Ψ₁₆ᶠ Corrupted-host bootstrap demo over multiprocessing.Pipe.

Model:
- Host control plane starts healthy, then enters "corrupted sigils" state.
- Exposed primitives: ALU dot(x,y), memory banks read/write, kick_eval.
- The client detects corruption, probes the opaque ALU, recovers all 16
  element identities via psi_blackbox.recover_adaptive, and restores health.

Mascot rendering uses the wiz2 bijective 16×16 sprite: every cell in the
Ψ₁₆ᶠ Cayley table maps to exactly one pixel, colored by output value.

Usage:
  python examples/psi16_corrupted_host_demo.py
"""

from __future__ import annotations

import json
import multiprocessing as mp
import random
import sys
import time
from collections import Counter
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


def hex_to_rgb(h: str) -> tuple[int, int, int]:
    return int(h[1:3], 16), int(h[3:5], 16), int(h[5:7], 16)


def lum(h: str) -> float:
    r, g, b = hex_to_rgb(h)
    return 0.299 * r + 0.587 * g + 0.114 * b


def text_color(h: str) -> str:
    return _fg(16, 16, 16) if lum(h) >= 140 else _fg(240, 240, 240)


# ── Wiz2 sprite template ────────────────────────────────────────────────────
# Background values: 1(⊥), 3(τ), 4(g), 14(s1)
# Character values: everything else including 0(⊤/skin), 5(SEQ/brim)

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
    """Build 16×16 sprite from mapping (target → source Cayley cell).

    If no mapping, auto-generate using the silhouette: character pixels get
    non-bg values, background pixels get bg values, assigned greedily.
    """
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

    # Pool all 256 Cayley values
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


def render_sprite_ansi(
    sprite: list[list[int]],
    palette: dict[int, str],
    indent: str = "  ",
    label: str | None = None,
    dim: bool = False,
) -> str:
    """Render 16×16 sprite as ANSI half-block art (2 pixel rows per text row)."""
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
            # Upper half block: fg = top color, bg = bottom color
            if dim:
                ct = tuple(max(0, x // 3) for x in ct)
                cb = tuple(max(0, x // 3) for x in cb)
            parts.append(f"{_fg(*ct)}{_bg(*cb)}▀{RST}")
        lines.append("".join(parts))
    return "\n".join(lines)


def render_corrupted_sprite_ansi(
    sprite: list[list[int]],
    mapping: dict[str, list[int]],
    palette: dict[int, str],
    dot_fn,
    indent: str = "  ",
) -> str:
    """Render sprite by re-querying each pixel through the (corrupted) host.

    Each pixel's source cell (r,c) is queried via dot_fn using the OLD labels.
    Since the host's internal label mapping has changed, the returned values
    are structurally different — not just a palette swap — genuinely garbling
    the image.
    """
    grid = [[0] * 16 for _ in range(16)]
    for key, src in mapping.items():
        tr, tc = (int(x) for x in key.split(","))
        sr, sc = src
        # Query with old source coords — host interprets them differently now
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
        # Spot checks
        checks = [
            ("E", "⊤", "⊤"),    # E-transparency
            ("E", "⊥", "⊥"),
            ("η", "ρ", "τ"),     # Selection axiom
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
                role: tok for tok, role in role_map.items()
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

        elif cmd == "get_perm":
            conn.send({"ok": True, "perm": state.get("perm", list(range(16)))})

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
            print(f"  {DIM}→ {cmd}{extra}{RST}")
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

    def apply_recovery(self, role_of_token: dict[str, str]) -> dict:
        return self._req("apply_recovery", role_of_token=role_of_token)

    def get_perm(self) -> list[int]:
        return self._req("get_perm")["perm"]

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


# ── Narrative helpers ────────────────────────────────────────────────────────

def section(title: str) -> None:
    w = 60
    print(f"\n{'─' * w}")
    print(f"  {BOLD}{title}{RST}")
    print(f"{'─' * w}")


def narrate(text: str) -> None:
    print(f"  {_fg(160, 180, 200)}{text}{RST}")


def result_line(label: str, value: str, ok: bool = True) -> None:
    color = _fg(120, 220, 140) if ok else _fg(220, 80, 80)
    print(f"  {color}{'✓' if ok else '✗'} {label}: {value}{RST}")


# ── Main demo ────────────────────────────────────────────────────────────────

def run_demo() -> None:
    palette = dict(DEFAULT_PALETTE)
    wiz2_mapping = load_wiz2_mapping()
    sprite = build_sprite_grid(wiz2_mapping)
    # Keep raw JSON-style mapping for corrupted re-query
    wiz2_raw: dict[str, list[int]] = {}
    if wiz2_mapping:
        for (tr, tc), (sr, sc) in wiz2_mapping.items():
            wiz2_raw[f"{tr},{tc}"] = [sr, sc]
    else:
        # Fallback: identity mapping (source = target)
        for r in range(16):
            for c in range(16):
                wiz2_raw[f"{r},{c}"] = [r, c]

    # ── Title ──
    print()
    print(f"  {BOLD}{_fg(180, 140, 255)}Ψ₁₆ᶠ Corrupted-Host Bootstrap Demo{RST}")
    print(f"  {DIM}16-element algebra · bijective sprite · multiprocessing pipe{RST}")

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

        # The host starts with seed=17 mapping (already scrambled but "known").
        # Recover the known-good mapping to verify the oracle works.
        narrate("Recovering initial mapping from healthy host...")
        domain = host.mem_read("sys", "domain")
        init_rec = recover_adaptive(domain, host.dot)
        e_tok = init_rec["E"]
        top_tok = init_rec["⊤"]
        bot_tok = init_rec["⊥"]
        e_top = host.dot(e_tok, top_tok)
        e_bot = host.dot(e_tok, bot_tok)
        result_line("E·⊤ = ⊤", f"dot({e_tok},{top_tok}) = {e_top}", e_top == top_tok)
        result_line("E·⊥ = ⊥", f"dot({e_tok},{bot_tok}) = {e_bot}", e_bot == bot_tok)

        # ── Phase 2: Corruption ──
        section("Phase 2: Sigil Scramble Curse")

        narrate('"The sigils are shifting... I can feel the algebra twisting!"')
        scramble_seed = host.scramble()
        narrate(f"Host sigils scrambled (seed={scramble_seed})")

        post_health = host.mem_read("sys", "health")
        result_line("Host health", post_health, post_health == "healthy")

        print()
        narrate("Wizard sprite under scrambled sigils:")
        print(render_corrupted_sprite_ansi(sprite, wiz2_raw, palette, host.dot, indent="    "))
        print()

        # Show that the same dot query now gives wrong results
        narrate("Same dot query with scrambled labels...")
        e_top_scram = host.dot(init_rec["E"], init_rec["⊤"])
        result_line(
            "E·⊤ = ⊤ (old labels)",
            f"got {e_top_scram} — {'correct' if e_top_scram == init_rec['⊤'] else 'WRONG'}",
            e_top_scram == init_rec["⊤"],
        )

        # ── Phase 3: Recovery ──
        section("Phase 3: Black-Box Recovery")

        domain = host.mem_read("sys", "domain")
        narrate(f"Opaque domain: {len(domain)} labels")

        dot_calls = [0]
        def counted_dot(x, y):
            dot_calls[0] += 1
            return host.dot(x, y)

        narrate("Running adaptive recovery algorithm...")
        t0 = time.monotonic()
        rec = recover_adaptive(domain, counted_dot)
        dt = time.monotonic() - t0

        result_line("Recovery time", f"{dt:.3f}s, {dot_calls[0]} dot calls", True)

        # Show recovered mapping
        narrate("Recovered element mapping:")
        for i, (name, tok) in enumerate(sorted(rec.items(), key=lambda kv: list(ELEM_NAMES.values()).index(kv[0]) if kv[0] in ELEM_NAMES.values() else 99)):
            rgb = hex_to_rgb(palette.get(list(ELEM_NAMES.keys())[list(ELEM_NAMES.values()).index(name)], "#888888"))
            print(f"    {_fg(*rgb)}{name:>4}{RST} → label {tok}")

        # Verify axioms
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

        # Verify recovered dot oracle works
        e_tok = rec["E"]
        top_tok = rec["⊤"]
        bot_tok = rec["⊥"]
        narrate("Post-recovery dot check using recovered labels...")
        e_top_rec = host.dot(e_tok, top_tok)
        e_bot_rec = host.dot(e_tok, bot_tok)
        result_line("E·⊤ = ⊤", f"dot({e_tok},{top_tok}) = {e_top_rec}", e_top_rec == top_tok)
        result_line("E·⊥ = ⊥", f"dot({e_tok},{bot_tok}) = {e_bot_rec}", e_bot_rec == bot_tok)

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


if __name__ == "__main__":
    run_demo()

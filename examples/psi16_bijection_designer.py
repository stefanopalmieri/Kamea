#!/usr/bin/env python3
"""
Ψ₁₆ᶠ Bijection Sprite Designer — interactive Cayley-to-pixel mapper.

Click a SOURCE cell in the Cayley table, then click a TARGET cell in the
sprite grid to create a one-to-one mapping.  Every cell in the 16×16 Cayley
table maps to exactly one pixel in the 16×16 sprite (bijection).

The color palette is fully user-editable: click any color swatch to pick a
new color for that value.

Usage:
  python examples/psi16_bijection_designer.py
"""

from __future__ import annotations

import json
import random
import tkinter as tk
from collections import Counter
from pathlib import Path
from tkinter import colorchooser, filedialog, messagebox

# ── Ψ₁₆ᶠ Cayley table ──────────────────────────────────────────────────────

PSI_16 = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [5, 1, 13, 7, 11, 5, 6, 8, 2, 5, 11, 9, 4, 14, 3, 15],
    [0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1],
    [0, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11],
    [0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0],
    [15, 0, 5, 9, 3, 15, 14, 14, 2, 12, 8, 14, 12, 4, 12, 8],
    [0, 1, 8, 4, 13, 2, 11, 2, 14, 3, 15, 12, 14, 15, 6, 5],
    [12, 1, 13, 7, 11, 5, 12, 11, 4, 12, 5, 14, 15, 7, 11, 12],
    [1, 6, 14, 14, 14, 14, 9, 8, 3, 15, 5, 7, 13, 11, 12, 4],
    [13, 1, 4, 3, 12, 11, 2, 11, 5, 3, 8, 14, 9, 7, 11, 11],
    [14, 1, 9, 10, 11, 13, 12, 7, 5, 6, 8, 2, 14, 12, 10, 4],
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1],
    [3, 0, 14, 4, 14, 6, 11, 12, 7, 3, 15, 10, 14, 2, 6, 8],
    [14, 0, 5, 4, 3, 2, 12, 5, 11, 14, 3, 14, 12, 2, 6, 3],
    [1, 3, 13, 15, 3, 7, 14, 8, 15, 4, 11, 6, 7, 14, 12, 10],
]

ELEM_NAMES = {
    0: "\u22a4", 1: "\u22a5", 2: "f", 3: "\u03c4", 4: "g", 5: "SEQ",
    6: "Q", 7: "E", 8: "\u03c1", 9: "\u03b7", 10: "Y", 11: "PAIR",
    12: "s0", 13: "INC", 14: "s1", 15: "DEC",
}

SUPPLY = Counter(v for row in PSI_16 for v in row)

# ── Default palette (user can change every color) ────────────────────────────

DEFAULT_PALETTE = {
    0:  "#e8c090",   # ⊤  peach
    1:  "#18182a",   # ⊥  dark indigo
    2:  "#d8d0b8",   # f  cream
    3:  "#384828",   # τ  dark moss
    4:  "#161630",   # g  deep indigo
    5:  "#c0b8a0",   # SEQ silver
    6:  "#e8a820",   # Q  gold
    7:  "#c06028",   # E  burnt orange
    8:  "#5c24b0",   # ρ  purple
    9:  "#38c0d8",   # η  cyan
    10: "#d03050",   # Y  crimson
    11: "#7038d0",   # PAIR bright purple
    12: "#501888",   # s0 deep purple
    13: "#98b0c0",   # INC steel blue
    14: "#1c1c36",   # s1 dark navy
    15: "#303820",   # DEC dark olive
}

CELL = 30          # pixel size of each grid cell
HEADER = 18        # row/col header width


def text_color(hex_color: str) -> str:
    """Return black or white text depending on background luminance."""
    try:
        r = int(hex_color[1:3], 16)
        g = int(hex_color[3:5], 16)
        b = int(hex_color[5:7], 16)
    except (ValueError, IndexError):
        return "#ffffff"
    lum = 0.299 * r + 0.587 * g + 0.114 * b
    return "#101010" if lum >= 140 else "#f0f0f0"


def hex_blend(hex_color: str, factor: float) -> str:
    """Darken a hex color by factor (0=black, 1=original)."""
    try:
        r = int(int(hex_color[1:3], 16) * factor)
        g = int(int(hex_color[3:5], 16) * factor)
        b = int(int(hex_color[5:7], 16) * factor)
    except (ValueError, IndexError):
        return hex_color
    return f"#{min(r,255):02x}{min(g,255):02x}{min(b,255):02x}"


class BijectionDesigner:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("\u03a8\u2081\u2086\u1da0 Bijection Sprite Designer")
        self.root.configure(bg="#1a1a2e")

        # ── State ──
        self.palette = dict(DEFAULT_PALETTE)
        self.mapping: dict[tuple[int, int], tuple[int, int]] = {}   # target → source
        self.reverse: dict[tuple[int, int], tuple[int, int]] = {}   # source → target
        self.selected_source: tuple[int, int] | None = None
        self.swap_target: tuple[int, int] | None = None
        self.undo_stack: list[tuple] = []
        self.redo_stack: list[tuple] = []

        # ── Tk vars ──
        self.status_var = tk.StringVar(value="Click a source cell, then a target cell")
        self.count_var = tk.StringVar(value="Mapped: 0/256")

        self._build_ui()
        self._bind_keys()
        self.refresh_all()

    # ══════════════════════════════════════════════════════════════════════════
    #  UI CONSTRUCTION
    # ══════════════════════════════════════════════════════════════════════════

    def _build_ui(self):
        self.root.columnconfigure(0, weight=0)
        self.root.columnconfigure(1, weight=0)
        self.root.columnconfigure(2, weight=1)
        self.root.rowconfigure(1, weight=1)

        # ── Status bar ──
        status_frame = tk.Frame(self.root, bg="#16213e", height=32)
        status_frame.grid(row=0, column=0, columnspan=3, sticky="ew")
        status_frame.columnconfigure(1, weight=1)
        tk.Label(
            status_frame, textvariable=self.status_var,
            bg="#16213e", fg="#e0e0e0", font=("Menlo", 11), anchor="w", padx=10,
        ).grid(row=0, column=0, sticky="w")
        tk.Label(
            status_frame, textvariable=self.count_var,
            bg="#16213e", fg="#70d0a0", font=("Menlo", 11, "bold"), anchor="e", padx=10,
        ).grid(row=0, column=1, sticky="e")

        # ── Source grid (Cayley table) ──
        src_frame = tk.LabelFrame(
            self.root, text="  SOURCE  (Cayley Table)  ", bg="#1a1a2e",
            fg="#aaa", font=("Menlo", 10), padx=6, pady=6,
        )
        src_frame.grid(row=1, column=0, sticky="n", padx=(10, 4), pady=10)

        src_size = 16 * CELL + HEADER
        self.source_canvas = tk.Canvas(
            src_frame, width=src_size, height=src_size,
            bg="#0f0f1a", highlightthickness=0,
        )
        self.source_canvas.pack()
        self.source_canvas.bind("<Button-1>", self._on_source_click)
        self.source_canvas.bind("<Motion>", self._on_source_motion)

        # ── Target grid (Sprite) ──
        tgt_frame = tk.LabelFrame(
            self.root, text="  TARGET  (Sprite)  ", bg="#1a1a2e",
            fg="#aaa", font=("Menlo", 10), padx=6, pady=6,
        )
        tgt_frame.grid(row=1, column=1, sticky="n", padx=4, pady=10)

        tgt_size = 16 * CELL + HEADER
        self.target_canvas = tk.Canvas(
            tgt_frame, width=tgt_size, height=tgt_size,
            bg="#0f0f1a", highlightthickness=0,
        )
        self.target_canvas.pack()
        self.target_canvas.bind("<Button-1>", self._on_target_click)
        self.target_canvas.bind("<Button-2>", self._on_target_right_click)  # macOS
        self.target_canvas.bind("<Button-3>", self._on_target_right_click)
        self.target_canvas.bind("<Motion>", self._on_target_motion)

        # ── Right panel ──
        right = tk.Frame(self.root, bg="#1a1a2e")
        right.grid(row=1, column=2, sticky="nsew", padx=(4, 10), pady=10)
        right.columnconfigure(0, weight=1)

        self._build_tools(right)
        self._build_palette_editor(right)
        self._build_supply_panel(right)

    def _build_tools(self, parent: tk.Frame):
        tools = tk.LabelFrame(
            parent, text="  Tools  ", bg="#1a1a2e", fg="#aaa",
            font=("Menlo", 10), padx=8, pady=8,
        )
        tools.grid(row=0, column=0, sticky="ew", pady=(0, 8))

        btn_style = dict(bg="#2a2a4e", fg="#e0e0e0", activebackground="#3a3a6e",
                         activeforeground="#fff", font=("Menlo", 10), relief="flat",
                         padx=6, pady=3, cursor="hand2")

        row = 0
        for label, cmd in [
            ("Undo  \u2318Z", self.undo),
            ("Redo  \u2318\u21e7Z", self.redo),
            ("Clear All", self._clear_all),
            ("Auto-fill remaining", self._auto_fill),
            ("Save JSON...", self.save_json),
            ("Load JSON...", self.load_json),
            ("Export PNG...", self.export_png),
        ]:
            tk.Button(tools, text=label, command=cmd, width=22, **btn_style).grid(
                row=row, column=0, sticky="ew", pady=2,
            )
            row += 1

        # Swap mode hint
        tk.Label(
            tools, text="Right-click target\nto swap two pixels",
            bg="#1a1a2e", fg="#666", font=("Menlo", 9), justify="left",
        ).grid(row=row, column=0, sticky="w", pady=(6, 0))

    def _build_palette_editor(self, parent: tk.Frame):
        pal = tk.LabelFrame(
            parent, text="  Palette (click to edit)  ", bg="#1a1a2e",
            fg="#aaa", font=("Menlo", 10), padx=8, pady=8,
        )
        pal.grid(row=1, column=0, sticky="ew", pady=(0, 8))

        self.swatch_labels: dict[int, tk.Label] = {}
        for i in range(16):
            r, c = divmod(i, 4)
            frame = tk.Frame(pal, bg="#1a1a2e")
            frame.grid(row=r, column=c, padx=3, pady=3)
            name = ELEM_NAMES[i]
            color = self.palette[i]
            lbl = tk.Label(
                frame, text=f"{i}:{name}", width=7,
                bg=color, fg=text_color(color),
                font=("Menlo", 9, "bold"), relief="raised", cursor="hand2",
            )
            lbl.pack()
            lbl.bind("<Button-1>", lambda e, idx=i: self._pick_color(idx))
            self.swatch_labels[i] = lbl

    def _build_supply_panel(self, parent: tk.Frame):
        sup = tk.LabelFrame(
            parent, text="  Value Supply  ", bg="#1a1a2e",
            fg="#aaa", font=("Menlo", 10), padx=8, pady=8,
        )
        sup.grid(row=2, column=0, sticky="ew")

        self.supply_labels: dict[int, tk.Label] = {}
        for i in range(16):
            r, c = divmod(i, 2)
            lbl = tk.Label(
                sup, text="", bg="#1a1a2e", fg="#ccc",
                font=("Menlo", 9), anchor="w",
            )
            lbl.grid(row=r, column=c, sticky="ew", padx=4)
            self.supply_labels[i] = lbl
            sup.columnconfigure(c, weight=1)

    def _bind_keys(self):
        self.root.bind("<Command-z>", lambda e: self.undo())
        self.root.bind("<Command-Z>", lambda e: self.redo())
        self.root.bind("<Command-Shift-z>", lambda e: self.redo())
        self.root.bind("<Command-Shift-Z>", lambda e: self.redo())
        self.root.bind("<Control-z>", lambda e: self.undo())
        self.root.bind("<Control-Z>", lambda e: self.redo())
        self.root.bind("<Control-Shift-z>", lambda e: self.redo())
        self.root.bind("<Escape>", lambda e: self._cancel_selection())

    # ══════════════════════════════════════════════════════════════════════════
    #  CORE OPERATIONS
    # ══════════════════════════════════════════════════════════════════════════

    def _do_action(self, action: tuple):
        """Execute an action and push to undo stack."""
        self.undo_stack.append(action)
        self.redo_stack.clear()
        self._apply(action)

    def undo(self):
        if not self.undo_stack:
            return
        action = self.undo_stack.pop()
        self.redo_stack.append(action)
        self._unapply(action)

    def redo(self):
        if not self.redo_stack:
            return
        action = self.redo_stack.pop()
        self.undo_stack.append(action)
        self._apply(action)

    # ══════════════════════════════════════════════════════════════════════════
    #  CLICK HANDLERS
    # ══════════════════════════════════════════════════════════════════════════

    def _canvas_to_rc(self, event, with_header=True) -> tuple[int, int] | None:
        offset = HEADER if with_header else 0
        c = (event.x - offset) // CELL
        r = (event.y - offset) // CELL
        if 0 <= r < 16 and 0 <= c < 16:
            return (r, c)
        return None

    def _on_source_click(self, event):
        rc = self._canvas_to_rc(event)
        if rc is None:
            return
        # If already mapped, ignore (can't select mapped sources)
        if rc in self.reverse:
            self.status_var.set(f"Source {rc} already mapped \u2192 target {self.reverse[rc]}")
            return
        self.selected_source = rc
        self.swap_target = None
        val = PSI_16[rc[0]][rc[1]]
        self.status_var.set(
            f"Selected source ({rc[0]},{rc[1]})  "
            f"{ELEM_NAMES[rc[0]]}\u00b7{ELEM_NAMES[rc[1]]} = {ELEM_NAMES[val]}  "
            f"\u2014 click a target cell"
        )
        self.refresh_all()

    def _on_target_click(self, event):
        rc = self._canvas_to_rc(event)
        if rc is None:
            return

        # If in swap mode
        if self.swap_target is not None:
            if rc in self.mapping and rc != self.swap_target:
                self._do_action(("swap", self.swap_target, rc))
                self.status_var.set(
                    f"Swapped targets {self.swap_target} \u2194 {rc}"
                )
                self.swap_target = None
                self.selected_source = None
            else:
                self.status_var.set("Swap cancelled (target not mapped or same cell)")
                self.swap_target = None
            return

        # If clicking a mapped cell, unmap it
        if rc in self.mapping:
            src = self.mapping[rc]
            self._do_action(("unmap", rc, src))
            self.status_var.set(f"Unmapped target {rc} (source {src} returned to pool)")
            return

        # If we have a selected source, map it
        if self.selected_source is not None:
            src = self.selected_source
            self._do_action(("map", rc, src))
            val = PSI_16[src[0]][src[1]]
            self.status_var.set(
                f"Mapped source ({src[0]},{src[1]}) \u2192 target ({rc[0]},{rc[1]})  "
                f"value={ELEM_NAMES[val]}"
            )
            self.selected_source = None
            return

        self.status_var.set("Select a source cell first")

    def _on_target_right_click(self, event):
        rc = self._canvas_to_rc(event)
        if rc is None or rc not in self.mapping:
            return
        self.swap_target = rc
        self.selected_source = None
        self.status_var.set(
            f"SWAP MODE: click another mapped target to swap with ({rc[0]},{rc[1]})"
        )
        self.refresh_all()

    def _on_source_motion(self, event):
        rc = self._canvas_to_rc(event)
        if rc is None:
            return
        val = PSI_16[rc[0]][rc[1]]
        mapped_str = ""
        if rc in self.reverse:
            tgt = self.reverse[rc]
            mapped_str = f"  \u2192 target ({tgt[0]},{tgt[1]})"
        self.source_canvas.config(
            cursor="hand2" if rc not in self.reverse else "arrow"
        )

    def _on_target_motion(self, event):
        rc = self._canvas_to_rc(event)
        if rc is None:
            self.target_canvas.config(cursor="arrow")
            return
        if rc in self.mapping:
            self.target_canvas.config(cursor="hand2")
        elif self.selected_source is not None:
            self.target_canvas.config(cursor="crosshair")
        else:
            self.target_canvas.config(cursor="arrow")

    def _cancel_selection(self):
        self.selected_source = None
        self.swap_target = None
        self.status_var.set("Selection cancelled")
        self.refresh_all()

    # ══════════════════════════════════════════════════════════════════════════
    #  DRAWING
    # ══════════════════════════════════════════════════════════════════════════

    def refresh_all(self):
        self._draw_source_grid()
        self._draw_target_grid()
        self._update_supply()
        n = len(self.mapping)
        if n == 256:
            self.count_var.set("256/256 BIJECTION COMPLETE \u2713")
        else:
            self.count_var.set(f"Mapped: {n}/256")

    def _draw_source_grid(self):
        c = self.source_canvas
        c.delete("all")

        # Row/col headers
        for i in range(16):
            name = ELEM_NAMES[i]
            # Column header
            cx = HEADER + i * CELL + CELL // 2
            c.create_text(cx, HEADER // 2, text=name, fill="#888",
                          font=("Menlo", 7), anchor="center")
            # Row header
            cy = HEADER + i * CELL + CELL // 2
            c.create_text(HEADER // 2, cy, text=name, fill="#888",
                          font=("Menlo", 7), anchor="center")

        for r in range(16):
            for col in range(16):
                val = PSI_16[r][col]
                color = self.palette[val]
                x0 = HEADER + col * CELL
                y0 = HEADER + r * CELL
                x1 = x0 + CELL
                y1 = y0 + CELL

                src_rc = (r, col)
                is_mapped = src_rc in self.reverse
                is_selected = src_rc == self.selected_source

                # Dim mapped cells
                fill = hex_blend(color, 0.35) if is_mapped else color
                outline = "#ffdd44" if is_selected else ("#333" if is_mapped else "#222")
                width = 3 if is_selected else 1

                c.create_rectangle(x0, y0, x1, y1, fill=fill, outline=outline, width=width)

                # Show value name in cell
                fg = text_color(fill)
                if is_mapped:
                    fg = "#555"
                label = ELEM_NAMES[val]
                if len(label) > 3:
                    label = str(val)
                c.create_text(
                    (x0 + x1) // 2, (y0 + y1) // 2,
                    text=label, fill=fg, font=("Menlo", 8),
                )

    def _draw_target_grid(self):
        c = self.target_canvas
        c.delete("all")

        # Row/col headers (numbered 0-15)
        for i in range(16):
            cx = HEADER + i * CELL + CELL // 2
            c.create_text(cx, HEADER // 2, text=str(i), fill="#888",
                          font=("Menlo", 7), anchor="center")
            cy = HEADER + i * CELL + CELL // 2
            c.create_text(HEADER // 2, cy, text=str(i), fill="#888",
                          font=("Menlo", 7), anchor="center")

        for r in range(16):
            for col in range(16):
                x0 = HEADER + col * CELL
                y0 = HEADER + r * CELL
                x1 = x0 + CELL
                y1 = y0 + CELL

                tgt_rc = (r, col)
                is_swap = tgt_rc == self.swap_target

                if tgt_rc in self.mapping:
                    src = self.mapping[tgt_rc]
                    val = PSI_16[src[0]][src[1]]
                    color = self.palette[val]
                    outline = "#ff6644" if is_swap else "#333"
                    width = 3 if is_swap else 1
                    c.create_rectangle(x0, y0, x1, y1, fill=color, outline=outline, width=width)
                    fg = text_color(color)
                    c.create_text(
                        (x0 + x1) // 2, (y0 + y1) // 2,
                        text=ELEM_NAMES[val], fill=fg, font=("Menlo", 7),
                    )
                else:
                    # Empty cell
                    c.create_rectangle(x0, y0, x1, y1, fill="#1a1a2e", outline="#2a2a3e")

    def _update_supply(self):
        placed: Counter[int] = Counter()
        for tgt, src in self.mapping.items():
            val = PSI_16[src[0]][src[1]]
            placed[val] += 1

        for i in range(16):
            total = SUPPLY[i]
            used = placed.get(i, 0)
            left = total - used
            name = ELEM_NAMES[i]
            color = self.palette[i]
            text = f"{name:>4}: {used:2}/{total:2}  ({left:2} left)"
            lbl = self.supply_labels[i]
            lbl.config(text=text, fg=color if left > 0 else "#444")

    # ══════════════════════════════════════════════════════════════════════════
    #  PALETTE EDITOR
    # ══════════════════════════════════════════════════════════════════════════

    def _pick_color(self, idx: int):
        current = self.palette[idx]
        result = colorchooser.askcolor(
            color=current, title=f"Color for {idx}:{ELEM_NAMES[idx]}",
        )
        if result[1] is not None:
            self.palette[idx] = result[1]
            lbl = self.swatch_labels[idx]
            lbl.config(bg=result[1], fg=text_color(result[1]))
            self.refresh_all()

    # ══════════════════════════════════════════════════════════════════════════
    #  TOOLS
    # ══════════════════════════════════════════════════════════════════════════

    def _clear_all(self):
        if not self.mapping:
            return
        if not messagebox.askyesno("Clear All", f"Remove all {len(self.mapping)} mappings?"):
            return
        # Store all current mappings as a batch undo
        actions = [("map", tgt, src) for tgt, src in self.mapping.items()]
        # Clear
        self.mapping.clear()
        self.reverse.clear()
        self.selected_source = None
        self.swap_target = None
        # Push a compound undo (clear)
        self.undo_stack.append(("clear", actions))
        self.redo_stack.clear()
        self.status_var.set("All mappings cleared")
        self.refresh_all()

    def _auto_fill(self):
        unmapped_sources = [
            (r, c) for r in range(16) for c in range(16)
            if (r, c) not in self.reverse
        ]
        unmapped_targets = [
            (r, c) for r in range(16) for c in range(16)
            if (r, c) not in self.mapping
        ]
        if not unmapped_sources:
            self.status_var.set("All cells already mapped!")
            return
        random.shuffle(unmapped_sources)
        random.shuffle(unmapped_targets)
        actions = []
        for src, tgt in zip(unmapped_sources, unmapped_targets):
            self.mapping[tgt] = src
            self.reverse[src] = tgt
            actions.append(("map", tgt, src))
        self.undo_stack.append(("batch", actions))
        self.redo_stack.clear()
        self.status_var.set(f"Auto-filled {len(actions)} remaining cells")
        self.refresh_all()

    def save_json(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON", "*.json")],
            initialdir=str(Path(__file__).parent),
            title="Save mapping",
        )
        if not path:
            return
        data = {
            "palette": {str(k): v for k, v in self.palette.items()},
            "mapping": {
                f"{tgt[0]},{tgt[1]}": [src[0], src[1]]
                for tgt, src in self.mapping.items()
            },
        }
        Path(path).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        self.status_var.set(f"Saved to {Path(path).name}")

    def load_json(self):
        path = filedialog.askopenfilename(
            filetypes=[("JSON", "*.json")],
            initialdir=str(Path(__file__).parent),
            title="Load mapping",
        )
        if not path:
            return
        try:
            data = json.loads(Path(path).read_text(encoding="utf-8"))
        except Exception as exc:
            messagebox.showerror("Load Error", str(exc))
            return

        # Load palette
        if "palette" in data:
            for k, v in data["palette"].items():
                idx = int(k)
                if 0 <= idx < 16:
                    self.palette[idx] = v
                    lbl = self.swatch_labels[idx]
                    lbl.config(bg=v, fg=text_color(v))

        # Load mapping
        self.mapping.clear()
        self.reverse.clear()
        if "mapping" in data:
            for tgt_str, src_list in data["mapping"].items():
                tgt = tuple(int(x) for x in tgt_str.split(","))
                src = (src_list[0], src_list[1])
                self.mapping[tgt] = src
                self.reverse[src] = tgt

        self.undo_stack.clear()
        self.redo_stack.clear()
        self.selected_source = None
        self.swap_target = None
        self.status_var.set(f"Loaded {len(self.mapping)} mappings from {Path(path).name}")
        self.refresh_all()

    def export_png(self):
        if len(self.mapping) < 256:
            if not messagebox.askyesno(
                "Incomplete", f"Only {len(self.mapping)}/256 mapped. Export anyway?"
            ):
                return

        path = filedialog.asksaveasfilename(
            defaultextension=".png",
            filetypes=[("PNG", "*.png")],
            initialdir=str(Path(__file__).parent),
            title="Export sprite PNG",
        )
        if not path:
            return

        try:
            from PIL import Image
        except ImportError:
            messagebox.showerror("Missing Pillow", "pip install Pillow")
            return

        base = Path(path)

        for scale, suffix in [(1, ""), (8, "_8x"), (32, "_32x")]:
            img = Image.new("RGB", (16 * scale, 16 * scale), (0, 0, 0))
            for r in range(16):
                for c in range(16):
                    tgt = (r, c)
                    if tgt in self.mapping:
                        src = self.mapping[tgt]
                        val = PSI_16[src[0]][src[1]]
                        hex_c = self.palette[val]
                    else:
                        hex_c = "#000000"
                    rgb = tuple(int(hex_c[i:i+2], 16) for i in (1, 3, 5))
                    for dy in range(scale):
                        for dx in range(scale):
                            img.putpixel((c * scale + dx, r * scale + dy), rgb)
            out = base.with_stem(base.stem + suffix)
            img.save(str(out))

        self.status_var.set(f"Exported 1x/8x/32x to {base.parent.name}/")

    # ══════════════════════════════════════════════════════════════════════════
    #  UNDO SUPPORT FOR COMPOUND ACTIONS
    # ══════════════════════════════════════════════════════════════════════════

    def _apply(self, action: tuple):
        kind = action[0]
        if kind == "map":
            _, tgt, src = action
            self.mapping[tgt] = src
            self.reverse[src] = tgt
        elif kind == "unmap":
            _, tgt, src = action
            self.mapping.pop(tgt, None)
            self.reverse.pop(src, None)
        elif kind == "swap":
            _, t1, t2 = action
            s1, s2 = self.mapping[t1], self.mapping[t2]
            self.mapping[t1], self.mapping[t2] = s2, s1
            self.reverse[s1], self.reverse[s2] = t2, t1
        elif kind == "batch":
            for sub in action[1]:
                self._apply(sub)
        elif kind == "clear":
            for sub in action[1]:
                self._unapply(sub)
        self.refresh_all()

    def _unapply(self, action: tuple):
        kind = action[0]
        if kind == "map":
            _, tgt, src = action
            self.mapping.pop(tgt, None)
            self.reverse.pop(src, None)
        elif kind == "unmap":
            _, tgt, src = action
            self.mapping[tgt] = src
            self.reverse[src] = tgt
        elif kind == "swap":
            _, t1, t2 = action
            s1, s2 = self.mapping[t1], self.mapping[t2]
            self.mapping[t1], self.mapping[t2] = s2, s1
            self.reverse[s1], self.reverse[s2] = t2, t1
        elif kind == "batch":
            for sub in reversed(action[1]):
                self._unapply(sub)
        elif kind == "clear":
            for sub in action[1]:
                self._apply(sub)
        self.refresh_all()


def main():
    root = tk.Tk()
    root.geometry("1200x620")
    root.minsize(1000, 580)
    BijectionDesigner(root)
    root.mainloop()


if __name__ == "__main__":
    main()

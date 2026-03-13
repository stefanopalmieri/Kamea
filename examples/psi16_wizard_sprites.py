#!/usr/bin/env python3
"""
Ψ₁₆ᶠ Wizard Sprite Designer — bijective Cayley-to-pixel mapping.

Each 16×16 sprite uses ALL 256 cells of the Ψ₁₆ᶠ Cayley table exactly once.

Design approach:
  1. Define wizard SILHOUETTE ('#' = character, '.' = ground)
  2. Auto-assign zones within silhouette based on row position
  3. Fill ground with D+G tessellation
  4. Expand groups → values, verify bijection, render PNG

Usage:
  python examples/psi16_wizard_sprites.py
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict

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

SUPPLY = Counter(v for row in PSI_16 for v in row)

# ── Color palette ────────────────────────────────────────────────────────────

COLORS = {
    # DARK ground: dark indigo stone (blend together)
    1:  "#18182a",  14: "#1c1c36",  4:  "#161630",
    # PURPLE: bright purple hat/robe
    11: "#7038d0",  12: "#501888",  8:  "#5c24b0",
    # WARM: peach skin
    0:  "#e8c090",
    # LIGHT: silver beard/trim
    5:  "#c0b8a0",  2:  "#d8d0b8",  13: "#98b0c0",
    # EARTH: dark moss/grass in cracks
    3:  "#384828",  15: "#303820",
    # Accents (bright, used in character features)
    6:  "#e8a820",   # Q: gold (buckles)
    7:  "#c06028",   # E: burnt orange (boots/trim)
    9:  "#38c0d8",   # H: cyan (magic sparkle)
    10: "#d03050",   # Y: crimson (eyes)
}

# Visual groups: values that look the same
GROUPS = {
    'D': ([1, 14, 4],    82),   # DARK ground
    'P': ([11, 12, 8],   55),   # PURPLE character
    'W': ([0],           42),   # WARM character
    'L': ([5, 2, 13],    28),   # LIGHT character
    'G': ([3, 15],       23),   # EARTH ground/boots
    'Q': ([6],            8),   # gold accent
    'E': ([7],            9),   # orange accent
    'H': ([9],            5),   # cyan accent
    'Y': ([10],           4),   # crimson accent
}


# ── Auto-zone assignment ────────────────────────────────────────────────────

def auto_zone(silhouette: list[str], zone_map: dict) -> list[str]:
    """
    Assign visual groups to character pixels based on row position and zone_map.

    zone_map format: {row_range: (group, accent_positions)}
    Example: {(0,5): 'P', (5,9): 'W', (9,11): 'L', (11,14): 'P', (14,16): 'G'}

    Accent placements are specified separately.
    """
    grid = [list(row) for row in silhouette]
    # First pass: assign base groups by row range
    for r in range(16):
        for c in range(16):
            if grid[r][c] == '#':
                for (r0, r1), grp in zone_map.items():
                    if r0 <= r < r1:
                        grid[r][c] = grp
                        break
    return ["".join(row) for row in grid]


def place_accents(grid: list[str], placements: list[tuple[int, int, str]]) -> list[str]:
    """Place accent pixels at specific (row, col) positions."""
    g = [list(row) for row in grid]
    for r, c, grp in placements:
        g[r][c] = grp
    return ["".join(row) for row in g]


def build_wizard(silhouette: list[str], name: str = "") -> list[str] | None:
    """
    Auto-assign zones to a wizard silhouette, respecting group budgets.

    Strategy:
      1. Scan rows to identify hat/face/beard/robe/boot zones
      2. Assign base groups (P/W/L/P/G)
      3. Place accents (Q buckles, Y eyes, H sparkle, E trim)
      4. Adjust to match exact budgets
    """
    # Count character pixels per row
    char_pixels: list[list[int]] = []  # (row, [cols])
    total_char = 0
    for r in range(16):
        cols = [c for c in range(16) if silhouette[r][c] == '#']
        char_pixels.append(cols)
        total_char += len(cols)

    total_bg = 256 - total_char

    # Determine zone boundaries by looking at shape width changes
    # Hat: top narrow section that widens
    # Face: wide section below hat
    # Beard: section below face
    # Robe: section below beard
    # Boots: bottom narrow section

    # Find the widest row (likely face area)
    widths = [len(cols) for cols in char_pixels]
    max_width = max(widths)

    # Heuristic zone detection:
    # Hat starts where character starts, ends where width stabilizes at max
    # Face is the wide area
    # Beard is below face
    # Robe is the mid-lower section
    # Boots are the bottom narrow section

    # Simple approach: divide character rows into zones by fraction
    first_row = next(r for r in range(16) if char_pixels[r])
    last_row = next(r for r in range(15, -1, -1) if char_pixels[r])
    char_height = last_row - first_row + 1

    # Zone boundaries (relative positions)
    hat_end = first_row + max(1, int(char_height * 0.30))
    brim_end = hat_end + 1
    face_end = brim_end + max(1, int(char_height * 0.22))
    beard_end = face_end + max(1, int(char_height * 0.13))
    robe_end = last_row - 1
    # boots = last 2 rows

    # Assign base groups
    grid = [list(row) for row in silhouette]

    # Track how many of each group we assign
    assigned: dict[str, int] = Counter()

    def assign(r: int, c: int, grp: str) -> None:
        grid[r][c] = grp
        assigned[grp] += 1

    for r in range(16):
        for c in char_pixels[r]:
            if r < hat_end:
                assign(r, c, 'P')
            elif r < brim_end:
                assign(r, c, 'P')  # brim row
            elif r < face_end:
                assign(r, c, 'W')
            elif r < beard_end:
                assign(r, c, 'L')
            elif r < robe_end:
                assign(r, c, 'P')
            else:
                assign(r, c, 'G')  # boots/ground shadow

    # Now adjust to fit budgets. Main concern: P might be over 55.
    # Strategy: if P is over, convert some P robe pixels to other groups.
    p_over = assigned.get('P', 0) - 55
    if p_over > 0:
        # Convert bottom robe rows from P → E (trim) or G
        for r in range(robe_end - 1, brim_end, -1):
            for c in reversed(char_pixels[r]):
                if grid[r][c] == 'P' and p_over > 0:
                    # Edges → E (orange trim), middle stays P
                    if c == char_pixels[r][0] or c == char_pixels[r][-1]:
                        assign_code = 'E' if assigned.get('E', 0) < 9 else 'G'
                    else:
                        assign_code = 'L' if assigned.get('L', 0) < 28 else 'G'
                    grid[r][c] = assign_code
                    assigned['P'] -= 1
                    assigned[assign_code] += 1
                    p_over -= 1
                if p_over <= 0:
                    break
            if p_over <= 0:
                break

    # W might be over 42
    w_over = assigned.get('W', 0) - 42
    if w_over > 0:
        # Convert some face pixels to L (arms) at edges
        for r in range(face_end - 1, brim_end, -1):
            for c in char_pixels[r]:
                if grid[r][c] == 'W' and w_over > 0:
                    if c == char_pixels[r][0] or c == char_pixels[r][-1]:
                        grid[r][c] = 'L'
                        assigned['W'] -= 1
                        assigned['L'] += 1
                        w_over -= 1
                if w_over <= 0:
                    break
            if w_over <= 0:
                break

    # L might be over 28
    l_over = assigned.get('L', 0) - 28
    if l_over > 0:
        for r in range(beard_end - 1, face_end - 1, -1):
            for c in reversed(char_pixels[r]):
                if grid[r][c] == 'L' and l_over > 0:
                    grid[r][c] = 'E' if assigned.get('E', 0) < 9 else 'G'
                    assigned['L'] -= 1
                    assigned[grid[r][c]] += 1
                    l_over -= 1
                if l_over <= 0:
                    break
            if l_over <= 0:
                break

    # G might be over 23
    g_over = assigned.get('G', 0) - 23
    if g_over > 0:
        for r in range(last_row, -1, -1):
            for c in reversed(char_pixels[r]):
                if grid[r][c] == 'G' and g_over > 0:
                    grid[r][c] = 'E' if assigned.get('E', 0) < 9 else 'D'
                    assigned['G'] -= 1
                    assigned[grid[r][c]] += 1
                    g_over -= 1
                if g_over <= 0:
                    break
            if g_over <= 0:
                break

    # Place accent pixels
    # Eyes (Y): 2 pixels in face zone, symmetric
    eyes_placed = 0
    face_rows = [r for r in range(brim_end, face_end) if len(char_pixels[r]) >= 6]
    if face_rows:
        eye_row = face_rows[min(1, len(face_rows) - 1)]
        cols = char_pixels[eye_row]
        if len(cols) >= 6:
            left_eye = cols[2]
            right_eye = cols[-3]
            for ec in [left_eye, right_eye]:
                if grid[eye_row][ec] == 'W':
                    grid[eye_row][ec] = 'Y'
                    assigned['W'] -= 1
                    assigned['Y'] += 1
                    eyes_placed += 1

    # Hat gem (Y): 1-2 pixels at hat center
    y_need = 4 - assigned.get('Y', 0)
    if y_need > 0:
        hat_rows = [r for r in range(first_row, hat_end) if char_pixels[r]]
        for hr in hat_rows:
            cols = char_pixels[hr]
            mid = cols[len(cols) // 2]
            if grid[hr][mid] == 'P' and y_need > 0:
                grid[hr][mid] = 'Y'
                assigned['P'] -= 1
                assigned['Y'] += 1
                y_need -= 1
                break

    # Buckles (Q): on brim row and robe
    q_need = 8 - assigned.get('Q', 0)
    # Brim buckles
    if brim_end < 16 and char_pixels[brim_end - 1]:
        brim_cols = char_pixels[brim_end - 1]
        if len(brim_cols) >= 4:
            for qi, bc in enumerate([brim_cols[1], brim_cols[-2]]):
                if grid[brim_end - 1][bc] == 'P' and q_need > 0:
                    grid[brim_end - 1][bc] = 'Q'
                    assigned['P'] -= 1
                    assigned['Q'] += 1
                    q_need -= 1

    # Robe buckles
    robe_rows = [r for r in range(beard_end, robe_end) if char_pixels[r]]
    for rr in robe_rows[:2]:
        cols = char_pixels[rr]
        if len(cols) >= 4:
            for bc in [cols[2], cols[-3]]:
                if grid[rr][bc] == 'P' and q_need > 0:
                    grid[rr][bc] = 'Q'
                    assigned['P'] -= 1
                    assigned['Q'] += 1
                    q_need -= 1
        if q_need <= 0:
            break

    # If still need Q, place in remaining character pixels
    if q_need > 0:
        for r in range(last_row, first_row, -1):
            for c in char_pixels[r]:
                if q_need <= 0:
                    break
                if grid[r][c] in ('P', 'G', 'L') and assigned.get(grid[r][c], 0) > 1:
                    old = grid[r][c]
                    grid[r][c] = 'Q'
                    assigned[old] -= 1
                    assigned['Q'] += 1
                    q_need -= 1

    # Magic sparkle (H): nose area + magic effects
    h_need = 5 - assigned.get('H', 0)
    # Nose: 1 pixel in mid-face
    if face_rows and h_need > 0:
        nose_row = face_rows[min(2, len(face_rows) - 1)]
        cols = char_pixels[nose_row]
        mid = cols[len(cols) // 2]
        if grid[nose_row][mid] == 'W':
            grid[nose_row][mid] = 'H'
            assigned['W'] -= 1
            assigned['H'] += 1
            h_need -= 1

    # Remaining H: scatter in character
    if h_need > 0:
        for r in range(last_row, first_row, -1):
            for c in char_pixels[r]:
                if h_need <= 0:
                    break
                if grid[r][c] in ('G', 'E', 'L') and assigned.get(grid[r][c], 0) > 1:
                    old = grid[r][c]
                    grid[r][c] = 'H'
                    assigned[old] -= 1
                    assigned['H'] += 1
                    h_need -= 1

    # Orange trim (E): edges of robe bottom
    e_need = 9 - assigned.get('E', 0)
    if e_need > 0:
        for r in range(robe_end - 1, beard_end - 1, -1):
            cols = char_pixels[r]
            for c in [cols[0], cols[-1]] if len(cols) >= 2 else cols:
                if e_need <= 0:
                    break
                if grid[r][c] in ('P', 'L') and assigned.get(grid[r][c], 0) > 1:
                    old = grid[r][c]
                    grid[r][c] = 'E'
                    assigned[old] -= 1
                    assigned['E'] += 1
                    e_need -= 1

    # Remaining E: scatter in boots area
    if e_need > 0:
        for r in range(last_row, robe_end - 2, -1):
            for c in char_pixels[r]:
                if e_need <= 0:
                    break
                if grid[r][c] in ('G', 'P', 'L') and assigned.get(grid[r][c], 0) > 1:
                    old = grid[r][c]
                    grid[r][c] = 'E'
                    assigned[old] -= 1
                    assigned['E'] += 1
                    e_need -= 1

    # Final budget check — any remaining Y
    y_need = 4 - assigned.get('Y', 0)
    if y_need > 0:
        for r in range(first_row, face_end):
            for c in char_pixels[r]:
                if y_need <= 0:
                    break
                if grid[r][c] in ('P', 'W') and assigned.get(grid[r][c], 0) > 2:
                    old = grid[r][c]
                    grid[r][c] = 'Y'
                    assigned[old] -= 1
                    assigned['Y'] += 1
                    y_need -= 1

    # Verify budgets
    ok = True
    for code, (_, total) in GROUPS.items():
        used = assigned.get(code, 0)
        if used > total:
            if name:
                print(f"  {name}: group '{code}' over by {used - total}")
            ok = False

    if not ok:
        return None

    return ["".join(row) for row in grid]


def fill_ground(group_grid: list[str], name: str) -> list[str] | None:
    """Fill '.' positions with remaining supply using tessellated stone+moss."""
    grid = [list(row) for row in group_grid]

    # Count what character used
    char_demand: dict[str, int] = Counter()
    for r in range(16):
        for c in range(16):
            ch = grid[r][c]
            if ch != '.':
                char_demand[ch] += 1

    remaining: dict[str, int] = {}
    for code, (_, total) in GROUPS.items():
        remaining[code] = total - char_demand.get(code, 0)
        if remaining[code] < 0:
            print(f"  {name}: group '{code}' over by {-remaining[code]}")
            return None

    bg_pos = [(r, c) for r in range(16) for c in range(16) if grid[r][c] == '.']
    total_bg = len(bg_pos)
    total_remain = sum(remaining.values())

    if total_remain != total_bg:
        print(f"  {name}: remaining {total_remain} != bg {total_bg}")
        for code in GROUPS:
            if remaining[code] > 0:
                print(f"    {code}: {remaining[code]}")
        return None

    # Tessellated stone floor: mostly D with G as moss in mortar lines
    final: list[str] = []
    for r, c in bg_pos:
        br = r % 4
        bc = (c + (2 if (r // 2) % 2 else 0)) % 4
        if br == 0 or bc == 0:
            final.append('G')
        else:
            final.append('D')

    # Rebalance to match remaining supply
    fc = Counter(final)

    # First handle groups that aren't D or G (leftover P, W, L, accents)
    for code in GROUPS:
        need = remaining[code]
        have = fc.get(code, 0)
        if need > have:
            # Need more of this group — take from group with most excess
            diff = need - have
            for i in range(len(final)):
                if diff <= 0:
                    break
                src = final[i]
                if fc[src] > remaining[src]:
                    final[i] = code
                    fc[src] -= 1
                    fc[code] = fc.get(code, 0) + 1
                    diff -= 1

    # Handle excess (groups assigned more than remaining)
    for code in list(GROUPS.keys()):
        have = fc.get(code, 0)
        need = remaining[code]
        if have > need:
            diff = have - need
            for i in range(len(final)):
                if diff <= 0:
                    break
                if final[i] == code:
                    # Find a group that needs more
                    for other in GROUPS:
                        if fc.get(other, 0) < remaining[other]:
                            final[i] = other
                            fc[code] -= 1
                            fc[other] = fc.get(other, 0) + 1
                            diff -= 1
                            break

    # Verify
    fc2 = Counter(final)
    for code in GROUPS:
        if fc2.get(code, 0) != remaining[code]:
            print(f"  {name}: ground {code}: {fc2.get(code,0)} != {remaining[code]}")
            return None

    for i, (r, c) in enumerate(bg_pos):
        grid[r][c] = final[i]

    return ["".join(row) for row in grid]


def expand_to_values(group_grid: list[str]) -> list[list[int]]:
    """Expand group codes → specific Cayley values via spatial clustering."""
    positions: dict[str, list[tuple[int, int]]] = defaultdict(list)
    for r, row in enumerate(group_grid):
        for c, ch in enumerate(row):
            positions[ch].append((r, c))

    grid = [[0] * 16 for _ in range(16)]
    for code, pos_list in positions.items():
        values, _ = GROUPS[code]
        pool: list[int] = []
        for v in values:
            pool.extend([v] * SUPPLY[v])
        assert len(pool) >= len(pos_list), \
            f"Group {code}: {len(pool)} < {len(pos_list)}"
        for i, (r, c) in enumerate(pos_list):
            grid[r][c] = pool[i]

    demand = Counter(v for row in grid for v in row)
    for v in range(16):
        assert demand.get(v, 0) == SUPPLY[v], \
            f"Value {v}: got {demand.get(v,0)}, need {SUPPLY[v]}"
    return grid


def solve_bijection(sprite: list[list[int]]) -> None:
    pools: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for r in range(16):
        for c in range(16):
            pools[PSI_16[r][c]].append((r, c))
    avail = {v: list(cells) for v, cells in pools.items()}
    result = set()
    for r in range(16):
        for c in range(16):
            cell = avail[sprite[r][c]].pop(0)
            result.add(cell)
    assert len(result) == 256, f"Bijection failed: {len(result)} unique cells"


def render_png(sprites: dict[str, list[list[int]]]) -> None:
    try:
        from PIL import Image, ImageDraw, ImageFont
    except ImportError:
        print("  (pip install Pillow)")
        return

    for name, sprite in sprites.items():
        for scale, suffix in [(32, ""), (8, "_sm")]:
            img = Image.new("RGB", (16 * scale, 16 * scale))
            draw = ImageDraw.Draw(img)
            for r in range(16):
                for c in range(16):
                    rgb = tuple(int(COLORS[sprite[r][c]][i:i+2], 16)
                                for i in (1, 3, 5))
                    x0, y0 = c * scale, r * scale
                    draw.rectangle([x0, y0, x0+scale-1, y0+scale-1], fill=rgb)
            path = f"examples/{name}{suffix}.png"
            img.save(path)
            if not suffix:
                print(f"  Saved {path}")

    # Combined strip
    scale = 28
    gap = 8
    n = len(sprites)
    w = n * 16 * scale + (n + 1) * gap
    h = 16 * scale + 38
    img = Image.new("RGB", (w, h), (10, 10, 10))
    draw = ImageDraw.Draw(img)
    try:
        font = ImageFont.truetype("/System/Library/Fonts/Menlo.ttc", 10)
    except Exception:
        font = ImageFont.load_default()
    x = gap
    for name, sprite in sprites.items():
        draw.text((x, 4), name, fill=(160, 160, 160), font=font)
        for r in range(16):
            for c in range(16):
                rgb = tuple(int(COLORS[sprite[r][c]][i:i+2], 16)
                            for i in (1, 3, 5))
                x0, y0 = x + c * scale, 22 + r * scale
                draw.rectangle([x0, y0, x0+scale-1, y0+scale-1], fill=rgb)
        x += 16 * scale + gap
    img.save("examples/psi16_wizards_combined.png")
    print(f"  Saved examples/psi16_wizards_combined.png")


# ── Silhouette templates ────────────────────────────────────────────────────
# '#' = character pixel (auto-zoned), '.' = ground

SILHOUETTES = {}

# Big chibi wizard: fills ~60% of frame
SILHOUETTES["wizard_chibi"] = [
    "......##........",  # 0  hat tip
    ".....####.......",  # 1  hat
    "....######......",  # 2  hat
    "...########.....",  # 3  hat wide
    "..##########....",  # 4  brim
    "..############..",  # 5  face top
    ".##############.",  # 6  face + arms
    "..############..",  # 7  face
    "..############..",  # 8  face bottom
    "..############..",  # 9  beard
    "..############..",  # 10 beard
    "..############..",  # 11 robe
    "..############..",  # 12 robe
    "...##########...",  # 13 robe lower
    "...####..####...",  # 14 boots
    "................",  # 15 ground
]

# Taller mage: slimmer, more vertical
SILHOUETTES["mage"] = [
    ".......#........",  # 0  hat tip
    "......###.......",  # 1  hat
    ".....#####......",  # 2  hat
    "....#######.....",  # 3  hat
    "...#########....",  # 4  hat wide
    "...#########....",  # 5  brim
    "..###########...",  # 6  face
    "..###########...",  # 7  face
    "..###########...",  # 8  face/beard
    "...#########....",  # 9  beard
    "...#########....",  # 10 robe
    "...#########....",  # 11 robe
    "..###########...",  # 12 robe wide
    "...#########....",  # 13 robe
    "...####.####....",  # 14 boots
    "................",  # 15 ground
]

# Wide sorcerer: imposing presence
SILHOUETTES["sorcerer"] = [
    "........#.......",  # 0  hat tip
    ".......###......",  # 1  hat
    "......#####.....",  # 2  hat
    ".....#######....",  # 3  hat
    "....#########...",  # 4  brim
    "...###########..",  # 5  face
    "..#############.",  # 6  face wide
    "..#############.",  # 7  face
    "..#############.",  # 8  beard
    "..#############.",  # 9  beard
    "..#############.",  # 10 robe
    ".##############.",  # 11 robe wide
    ".##############.",  # 12 robe
    "..############..",  # 13 robe
    "..####..####....",  # 14 boots
    "................",  # 15 ground
]

# Staff wizard: staff to the side
SILHOUETTES["staff_wiz"] = [
    "..........#.....",  # 0  staff top / sparkle
    ".....##...#.....",  # 1  hat + staff
    "....####..#.....",  # 2  hat + staff
    "...######.#.....",  # 3  hat + staff
    "..########......",  # 4  brim
    "..###########...",  # 5  face
    ".############...",  # 6  face + arm
    "..###########...",  # 7  face
    "..###########...",  # 8  beard
    "..###########...",  # 9  beard
    "..###########...",  # 10 robe
    "..###########...",  # 11 robe
    "...#########....",  # 12 robe
    "...#########....",  # 13 robe
    "...####.####....",  # 14 boots
    "................",  # 15 ground
]

# wiz2: hand-designed in bijection designer, staff on right
# Derived from wiz2.json silhouette (bg = BOT, tau, g, s1)
SILHOUETTES["wiz2"] = [
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--text", action="store_true")
    parser.add_argument("--debug", action="store_true")
    args = parser.parse_args()

    print("Ψ₁₆ᶠ Wizard Sprites — Bijective Cayley Mapping")
    print("=" * 50)

    sprites: dict[str, list[list[int]]] = {}

    for name, sil in SILHOUETTES.items():
        print(f"\n── {name} ──")
        if len(sil) != 16 or any(len(r) != 16 for r in sil):
            print(f"  Bad dimensions!")
            for i, r in enumerate(sil):
                if len(r) != 16:
                    print(f"    row {i}: len={len(r)}")
            continue

        char_count = sum(row.count('#') for row in sil)
        print(f"  Character: {char_count} px, Ground: {256 - char_count} px")

        # Auto-zone the silhouette
        group_grid = build_wizard(sil, name)
        if group_grid is None:
            print(f"  Failed to zone (group budget overflow)")
            continue

        if args.debug:
            demand = Counter(ch for row in group_grid for ch in row if ch != '.')
            for code in ['P', 'W', 'L', 'Q', 'E', 'H', 'Y', 'G']:
                used = demand.get(code, 0)
                total = GROUPS[code][1]
                print(f"    {code}: {used}/{total}")

        # Fill ground tessellation
        filled = fill_ground(group_grid, name)
        if filled is None:
            continue

        # Expand to values and verify bijection
        pixel_grid = expand_to_values(filled)
        solve_bijection(pixel_grid)
        sprites[name] = pixel_grid
        print(f"  ✓ PERFECT bijection")

    if not sprites:
        print("\nNo valid sprites!")
        return

    print(f"\n{len(sprites)} sprites ready.")
    if not args.text:
        render_png(sprites)


if __name__ == "__main__":
    main()

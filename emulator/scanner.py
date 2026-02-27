"""
Cayley ROM recovery scanner — hardware module.

A dedicated scanner chip that reads the Cayley ROM directly to identify
all 66 atoms by their structural signatures. Runs at boot before the
eval/apply machine starts. No heap, no stack, no eval/apply.

Every dot(x, y) is a single ROM read: rom[x * N + y].
"""

from __future__ import annotations

from .chips import EEPROM

# QUALE_MAP_INV compiled as: target_name → opaque_atom_name
_QUALE_MAP_INV = {
    "k": "QUOTE",       "i": "EVAL",        "⊤": "APP",         "⊥": "UNAPP",
    "e_Σ": "IO_PUT",    "e_Δ": "IO_GET",    "d_I": "IO_RDY",    "s_C": "IO_SEQ",
    "N8": "W_PACK8",    "b": "W_LO",        "a": "W_HI",        "p": "W_MERGE",
    "N4": "W_NIB",      "N_SUCC": "W_ADD",  "ALU_COUT": "W_SUB","ALU_ZERO": "W_CMP",
    "N6": "W_XOR",      "NB": "W_AND",      "NE": "W_OR",       "N0": "W_NOT",
    "ALU_ARITH": "W_SHL","ALU_LOGIC": "W_SHR","ALU_ARITHC": "W_ROTL","d_K": "W_ROTR",
    "N9": "MUL16",      "NA": "MAC16",
    "e_I": "QUALE",
}


class CayleyScanner:
    """
    Hardware recovery scanner.

    Reads the Cayley ROM to identify all 66 atoms by structural
    signatures. Pure combinational logic + registers — no heap,
    no stack, no eval/apply state machine.
    """

    def __init__(self, cayley_rom: EEPROM, num_atoms: int = 66):
        self.rom = cayley_rom
        self.N = num_atoms
        self.rom_reads = 0

    def dot(self, x: int, y: int) -> int:
        """Single Cayley ROM lookup."""
        self.rom_reads += 1
        return self.rom.read(x * self.N + y)

    def scan(self) -> dict[str, int]:
        """
        Run full recovery. Returns {atom_name: scrambled_index}.

        Phase 1a: D1 (17 atoms)
        Phase 1b: Nibbles + ALU + QUALE (22 atoms)
        Phase 1c: QUALE column (27 opaque atoms)
        """
        self.rom_reads = 0

        # Track which indices are identified
        identified = [False] * self.N
        atom_map: dict[str, int] = {}

        def claim(name: str, idx: int):
            atom_map[name] = idx
            identified[idx] = True

        def remaining():
            return [i for i in range(self.N) if not identified[i]]

        # ── Phase 1a: D1 (17 atoms) ──────────────────────────────────

        # Step 1: Find 2 absorbers (⊤ and ⊥)
        absorbers = []
        for x in range(self.N):
            is_absorb = True
            for y in range(self.N):
                if self.dot(x, y) != x:
                    is_absorb = False
                    break
            if is_absorb:
                absorbers.append(x)
        assert len(absorbers) == 2, f"Expected 2 absorbers, got {len(absorbers)}"

        # Step 2: Find 4 testers and orient ⊤/⊥
        def find_testers(top, bot):
            out = []
            for x in range(self.N):
                if x == top or x == bot:
                    continue
                has_top = False
                has_bot = False
                only_bool = True
                for y in range(self.N):
                    r = self.dot(x, y)
                    if r == top:
                        has_top = True
                    elif r == bot:
                        has_bot = True
                    else:
                        only_bool = False
                        break
                if only_bool and has_top and has_bot:
                    out.append(x)
            return out

        def decoded_set_size(tester, top):
            count = 0
            for y in range(self.N):
                if self.dot(tester, y) == top:
                    count += 1
            return count

        # Try both orientations
        top = bot = None
        testers = None
        for b1, b2 in [(absorbers[0], absorbers[1]), (absorbers[1], absorbers[0])]:
            ts = find_testers(b1, b2)
            if len(ts) != 4:
                continue
            sizes = sorted(decoded_set_size(t, b1) for t in ts)
            if sizes[0] == 1 and sizes[1] == 2 and sizes[2] == 2:
                top, bot = b1, b2
                testers = ts
                break
        assert top is not None, "Failed to orient booleans"

        claim("⊤", top)
        claim("⊥", bot)

        # Step 3: Identify testers by decoded-set size
        tester_sizes = {t: decoded_set_size(t, top) for t in testers}
        m_K = [t for t in testers if tester_sizes[t] == 1][0]
        m_I = max(testers, key=lambda t: tester_sizes[t])
        two_testers = [t for t in testers if tester_sizes[t] == 2]
        assert len(two_testers) == 2

        # Step 2.5: Find p
        # p: dot(x, ⊤) == ⊤ AND dot(m_I, x) == ⊥, not absorber/tester
        tester_set = set(testers)
        p_idx = None
        for x in range(self.N):
            if x == top or x == bot or x in tester_set:
                continue
            if self.dot(x, top) == top and self.dot(m_I, x) == bot:
                p_idx = x
                break
        assert p_idx is not None, "Failed to find p"
        claim("p", p_idx)

        # Step 4: Distinguish e_I from d_K
        # e_I's decoded set has productive arguments; d_K's doesn't
        def decoded_set(tester):
            return [y for y in range(self.N) if self.dot(tester, y) == top]

        def has_productive_args(dec_set):
            for f in range(self.N):
                if f == top or f == bot or f in tester_set:
                    continue
                for x in dec_set:
                    out = self.dot(f, x)
                    if out != top and out != bot and out != p_idx:
                        return True
            return False

        t1, t2 = two_testers
        if has_productive_args(decoded_set(t1)):
            e_I_idx, d_K_idx = t1, t2
        else:
            e_I_idx, d_K_idx = t2, t1

        claim("e_I", e_I_idx)
        claim("d_K", d_K_idx)
        claim("m_I", m_I)
        claim("m_K", m_K)

        # ctx = decoded set of e_I (the two atoms i, k)
        ctx = decoded_set(e_I_idx)
        assert len(ctx) == 2

        # Step 5: Find encoders e_D and e_M
        encoders = []
        for f in range(self.N):
            if f == top or f == bot or f in tester_set:
                continue
            outs = [self.dot(f, x) for x in ctx]
            if all(o != top and o != bot and o != p_idx for o in outs):
                encoders.append(f)
        assert len(encoders) == 2, f"Expected 2 encoders, got {len(encoders)}"

        # e_M maps both ctx elements to testers; e_D does not
        def maps_both_to_testers(f):
            return all(self.dot(f, x) in tester_set for x in ctx)

        if maps_both_to_testers(encoders[0]):
            e_M_idx, e_D_idx = encoders[0], encoders[1]
        else:
            e_M_idx, e_D_idx = encoders[1], encoders[0]

        claim("e_M", e_M_idx)
        claim("e_D", e_D_idx)

        # Step 6: Distinguish i from k
        outA = self.dot(e_M_idx, ctx[0])
        outB = self.dot(e_M_idx, ctx[1])
        dec_A = decoded_set_size(outA, top)
        dec_B = decoded_set_size(outB, top)
        if dec_A > dec_B:
            i_idx, k_idx = ctx[0], ctx[1]
        else:
            i_idx, k_idx = ctx[1], ctx[0]

        claim("i", i_idx)
        claim("k", k_idx)

        # Step 7: Identify a, b, d_I
        dk_dec = decoded_set(d_K_idx)
        assert len(dk_dec) == 2
        if self.dot(m_K, dk_dec[0]) == top:
            a_idx, b_idx = dk_dec[0], dk_dec[1]
        else:
            a_idx, b_idx = dk_dec[1], dk_dec[0]

        d_I_idx = self.dot(e_D_idx, i_idx)

        claim("a", a_idx)
        claim("b", b_idx)
        claim("d_I", d_I_idx)

        # Step 8: Find e_Σ, s_C, e_Δ
        known_set = set(atom_map.values())
        rem = [x for x in range(self.N) if x not in known_set]

        e_S_idx = sC_idx = e_Delta_idx = None
        for f in rem:
            for g in rem:
                h = self.dot(f, g)
                if h == top or h == bot or h == p_idx:
                    continue
                if h in known_set or h == f or h == g:
                    continue
                # s_C self-identifies on ⊤
                if self.dot(g, top) != g:
                    continue
                if self.dot(h, e_D_idx) == d_I_idx:
                    e_S_idx, sC_idx, e_Delta_idx = f, g, h
                    break
            if e_S_idx is not None:
                break
        assert e_S_idx is not None, "Failed to recover e_Σ/s_C/e_Δ"

        claim("e_Σ", e_S_idx)
        claim("s_C", sC_idx)
        claim("e_Δ", e_Delta_idx)

        # ── Phase 1b: Nibbles + ALU + QUALE (22 atoms) ───────────────

        rem = remaining()

        # Step 1: Identify 2 predicates
        predicates = []
        for x in rem:
            has_top = False
            has_bot = False
            has_self = False
            for y in range(self.N):
                r = self.dot(x, y)
                if r == top:
                    has_top = True
                elif r == bot:
                    has_bot = True
                if r == x:
                    has_self = True
            if has_top and has_bot and has_self:
                predicates.append(x)
        assert len(predicates) == 2, f"Expected 2 predicates, got {len(predicates)}"
        pred_set = set(predicates)

        # Step 2: Find 16 nibbles (self-composable in remaining non-pred set)
        non_pred = [x for x in rem if x not in pred_set]
        non_pred_set = set(non_pred)
        nibbles = []
        non_nibbles = []
        for x in non_pred:
            xx = self.dot(x, x)
            if xx in non_pred_set and xx != p_idx:
                nibbles.append(x)
            else:
                non_nibbles.append(x)
        assert len(nibbles) == 16, f"Expected 16 nibbles, got {len(nibbles)}"

        # Step 3: Find N_SUCC
        # At the Cayley level, N_SUCC and ALU dispatch atoms all map nibbles
        # to nibbles. N_SUCC is distinguished by dot(x, ⊥) = N0 (a nibble),
        # while dispatch atoms give dot(x, ⊥) = p.
        nibble_set = set(nibbles)
        n_succ_idx = None
        non_nibble_rest = []
        for x in non_nibbles:
            images = [self.dot(x, n) for n in nibbles]
            if (all(img in nibble_set for img in images)
                    and len(set(images)) == 16
                    and self.dot(x, bot) in nibble_set):
                n_succ_idx = x
            else:
                non_nibble_rest.append(x)
        assert n_succ_idx is not None, "Failed to identify N_SUCC"

        # Step 4: Distinguish ALU_ZERO (1 nibble→⊤) from ALU_COUT (8→⊤)
        dec_a_count = sum(1 for n in nibbles if self.dot(predicates[0], n) == top)
        dec_b_count = sum(1 for n in nibbles if self.dot(predicates[1], n) == top)
        if dec_a_count == 1:
            alu_zero_idx, alu_cout_idx = predicates[0], predicates[1]
        else:
            alu_zero_idx, alu_cout_idx = predicates[1], predicates[0]

        # Step 5: Find N0 via ALU_ZERO, walk N_SUCC to order nibbles
        n0_idx = None
        for n in nibbles:
            if self.dot(alu_zero_idx, n) == top:
                n0_idx = n
                break
        assert n0_idx is not None, "Failed to find N0"

        nibble_order = [n0_idx]
        cur = n0_idx
        for _ in range(15):
            cur = self.dot(n_succ_idx, cur)
            nibble_order.append(cur)
        assert len(set(nibble_order)) == 16, "Nibble ordering failed"

        for i in range(16):
            claim(f"N{i:X}", nibble_order[i])
        claim("N_SUCC", n_succ_idx)
        claim("ALU_ZERO", alu_zero_idx)
        claim("ALU_COUT", alu_cout_idx)

        # Step 6: Find QUALE — dot(x, x) == e_I among remaining non-nibble/non-pred
        quale_idx = None
        non_nibble_rest2 = []
        for x in non_nibble_rest:
            if self.dot(x, x) == e_I_idx:
                quale_idx = x
            else:
                non_nibble_rest2.append(x)
        assert quale_idx is not None, "Failed to identify QUALE"
        claim("QUALE", quale_idx)

        # Step 7: Find 3 ALU dispatch — self-identify on ⊤
        dispatch = []
        opaque = []
        for x in non_nibble_rest2:
            if self.dot(x, top) == x:
                dispatch.append(x)
            else:
                opaque.append(x)
        assert len(dispatch) == 3, f"Expected 3 dispatch, got {len(dispatch)}"

        # Distinguish ALU_LOGIC/ARITH/ARITHC by their permutation on nibbles:
        # At the Cayley level (no partial applications):
        #   ALU_LOGIC: identity — dot(d, N0) = N0
        #   ALU_ARITH: successor — dot(d, N0) = N1
        #   ALU_ARITHC: double successor — dot(d, N0) = N2
        n1_idx = nibble_order[1]
        n2_idx = nibble_order[2]

        alu_logic_idx = alu_arith_idx = alu_arithc_idx = None
        for d in dispatch:
            result = self.dot(d, n0_idx)
            if result == n0_idx:
                alu_logic_idx = d
            elif result == n1_idx:
                alu_arith_idx = d
            elif result == n2_idx:
                alu_arithc_idx = d
        assert alu_logic_idx is not None, "Failed to identify ALU_LOGIC"
        assert alu_arith_idx is not None, "Failed to identify ALU_ARITH"
        assert alu_arithc_idx is not None, "Failed to identify ALU_ARITHC"

        claim("ALU_LOGIC", alu_logic_idx)
        claim("ALU_ARITH", alu_arith_idx)
        claim("ALU_ARITHC", alu_arithc_idx)

        # ── Phase 1c: QUALE column (27 opaque atoms) ─────────────────

        # Build reverse lookup: identified index → name
        idx_to_name = {v: k for k, v in atom_map.items()}

        for u in opaque:
            target_idx = self.dot(u, quale_idx)
            target_name = idx_to_name.get(target_idx)
            assert target_name is not None, (
                f"QUALE target index {target_idx} not found in identified atoms"
            )
            opaque_name = _QUALE_MAP_INV.get(target_name)
            assert opaque_name is not None, (
                f"Target {target_name} not in QUALE_MAP_INV"
            )
            claim(opaque_name, u)

        assert len(atom_map) == self.N, (
            f"Expected {self.N} atoms, identified {len(atom_map)}"
        )
        return atom_map

#!/usr/bin/env python3
"""
Ψ∗ — the term algebra over Ψ₁₆ᶜ (C-interop-optimized).

Same evaluation semantics as psi_star.py but with the Ψ₁₆ᶜ Cayley table,
which adds INC/DEC/INV extension elements with algebraic identities the
supercompiler can exploit and arithmetic C interpretations:

  INC(x) = ((x - 1) & 3) + 2   on core {2,3,4,5}  (4-cycle)
  DEC(x) = ((x - 3) & 3) + 2   on core {2,3,4,5}  (reverse 4-cycle)
  INV(x) = 7 - x               on core {2,3,4,5}  (involution)

Supercompiler cancellation rules (5 total):
  E·(Q·x) → x, Q·(E·x) → x            (existing QE/EQ)
  INC·(DEC·x) → x, DEC·(INC·x) → x    (new, from cycle)
  INV·(INV·x) → x                      (new, involution)
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Union

# ═══════════════════════════════════════════════════════════════════════
# Ψ₁₆ᶜ Cayley table (SAT-verified, all axioms satisfied)
# ═══════════════════════════════════════════════════════════════════════

TABLE = [
    [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [ 1, 4, 7, 3,12, 5, 9,15,10,15,13,11, 3, 8,14, 2],
    [ 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],
    [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [ 1, 8,11,15,10, 6, 4,13, 7, 4,12,14, 3, 5, 9, 2],
    [ 0, 1,15,12, 6,13, 5,11,14, 8, 4, 2, 7, 7, 6, 3],
    [ 7, 1,10, 3,12, 5,12,14, 2, 4,11,13, 8, 6,14, 9],
    [ 4, 1,11,11,11,11, 4, 5, 3, 6, 2,10, 7, 3,13, 9],
    [ 1, 8, 2,13,10, 7, 7,12, 5, 9,14, 3,15, 4, 6,11],
    [ 1, 6, 3, 3, 7, 3,11, 2,11, 4, 8,13, 5,11,11, 3],
    [ 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [ 1, 2, 3, 4, 5, 2,14, 5,12, 3,13,11,13,15,15, 5],
    [ 1, 0, 5, 4, 3, 2,10, 9,14, 7, 6,12,11,13, 8,15],
    [ 0, 3, 5, 2, 3, 4, 3, 3, 5,13,13, 4,12, 5,15,14],
]

# Axiom-forced elements (same indices as Ψ₁₆ᶠ)
TOP = 0      # ⊤ (absorber, zero)
BOT = 1      # ⊥ (absorber)
F_ENC = 2    # f (encoder, fst projection)
TAU = 3      # τ (tester)
G_ENC = 4    # g (pair constructor)
Q = 6        # Q (quote / successor — lazy constructor)
E = 7        # E (eval / predecessor — destructor)
RHO = 8      # ρ (structural branch)
ETA = 9      # η (snd projection)
Y_COMB = 10  # Y (fixed-point combinator)

# Extension elements (Ψ₁₆ᶜ-specific)
SEQ = 12     # SEQ (tester, boolean predicate)
INC = 13     # INC (encoder, 4-cycle on core)
INV = 14     # INV (encoder, involution: 7-x on core)
DEC = 15     # DEC (encoder, reverse 4-cycle on core)

NAMES = {
    0: "⊤", 1: "⊥", 2: "f", 3: "τ", 4: "g", 5: "5",
    6: "Q", 7: "E", 8: "ρ", 9: "η", 10: "Y", 11: "11",
    12: "SEQ", 13: "INC", 14: "INV", 15: "DEC",
}


def dot(a: int, b: int) -> int:
    """Ψ₁₆ᶜ binary operation."""
    return TABLE[a][b]


# ═══════════════════════════════════════════════════════════════════════
# Ψ∗ term representation (identical to psi_star.py)
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class App:
    fun: Term
    arg: Term

Term = Union[int, App]


def term_str(t: Term, max_depth: int = 30) -> str:
    if max_depth <= 0:
        return "..."
    if isinstance(t, int):
        return NAMES.get(t, str(t))
    return f"({term_str(t.fun, max_depth-1)} · {term_str(t.arg, max_depth-1)})"


# ═══════════════════════════════════════════════════════════════════════
# Naturals, pairs (identical to psi_star.py)
# ═══════════════════════════════════════════════════════════════════════

def nat(n: int) -> Term:
    t: Term = TOP
    for _ in range(n):
        t = App(Q, t)
    return t

def to_nat(t: Term) -> int | None:
    n = 0
    while isinstance(t, App) and t.fun == Q:
        n += 1
        t = t.arg
    return n if t == TOP else None

def is_zero(t: Term) -> bool:
    return t == TOP

def pair(a: Term, b: Term) -> Term:
    return App(App(G_ENC, a), b)

def fst(t: Term) -> Term | None:
    if isinstance(t, App) and isinstance(t.fun, App) and t.fun.fun == G_ENC:
        return t.fun.arg
    return None

def snd(t: Term) -> Term | None:
    if isinstance(t, App) and isinstance(t.fun, App) and t.fun.fun == G_ENC:
        return t.arg
    return None


# ═══════════════════════════════════════════════════════════════════════
# Ψ∗ evaluator (identical to psi_star.py)
# ═══════════════════════════════════════════════════════════════════════

class EvalError(Exception):
    pass

def psi_eval(t: Term, max_steps: int = 100000, _steps: list | None = None) -> Term:
    if _steps is None:
        _steps = [0]
    _steps[0] += 1
    if _steps[0] > max_steps:
        raise EvalError(f"Exceeded {max_steps} steps")

    if isinstance(t, int):
        return t

    fn, arg = t.fun, t.arg

    if fn == Q:
        return t
    if fn == G_ENC:
        return App(G_ENC, psi_eval(arg, max_steps, _steps))
    if fn == E:
        val = psi_eval(arg, max_steps, _steps)
        if isinstance(val, App) and val.fun == Q:
            return psi_eval(val.arg, max_steps, _steps)
        if isinstance(val, int):
            return dot(E, val)
        return App(E, val)
    if fn == F_ENC:
        val = psi_eval(arg, max_steps, _steps)
        first = fst(val)
        if first is not None:
            return psi_eval(first, max_steps, _steps)
        if isinstance(val, int):
            return dot(F_ENC, val)
        return App(F_ENC, val)
    if fn == ETA:
        val = psi_eval(arg, max_steps, _steps)
        second = snd(val)
        if second is not None:
            return psi_eval(second, max_steps, _steps)
        if isinstance(val, int):
            return dot(ETA, val)
        return App(ETA, val)
    if fn == Y_COMB:
        return App(Y_COMB, psi_eval(arg, max_steps, _steps))
    if fn == RHO:
        val = psi_eval(arg, max_steps, _steps)
        if isinstance(val, int):
            return psi_eval(App(F_ENC, arg), max_steps, _steps)
        else:
            return psi_eval(App(G_ENC, arg), max_steps, _steps)

    fn_val = psi_eval(fn, max_steps, _steps)
    arg_val = psi_eval(arg, max_steps, _steps)

    if isinstance(fn_val, int) and not isinstance(fn, int):
        return psi_eval(App(fn_val, arg_val), max_steps, _steps)
    if isinstance(fn_val, App) and fn_val.fun == G_ENC:
        return App(fn_val, arg_val)
    if isinstance(fn_val, int) and isinstance(arg_val, int):
        return dot(fn_val, arg_val)
    return App(fn_val, arg_val)


# ═══════════════════════════════════════════════════════════════════════
# 2-Counter Machine (identical to psi_star.py)
# ═══════════════════════════════════════════════════════════════════════

INST_INC0 = 0; INST_INC1 = 1; INST_DEC0 = 2; INST_DEC1 = 3
INST_JZ0 = 4; INST_JZ1 = 5; INST_HALT = 6; INST_GOTO = 7
INST_NAMES = ["INC0", "INC1", "DEC0", "DEC1", "JZ0", "JZ1", "HALT", "GOTO"]

@dataclass
class Inst:
    op: int
    target: int = 0
    def __repr__(self):
        if self.op in (INST_JZ0, INST_JZ1, INST_GOTO):
            return f"{INST_NAMES[self.op]}({self.target})"
        return INST_NAMES[self.op]

def run_2cm_ref(prog: list[Inst], max_steps: int = 10000) -> list[tuple[int, int, int]]:
    c0, c1, pc = 0, 0, 0
    trace = [(pc, c0, c1)]
    for _ in range(max_steps):
        if pc >= len(prog): break
        i = prog[pc]
        if i.op == INST_HALT: break
        elif i.op == INST_INC0: c0 += 1; pc += 1
        elif i.op == INST_INC1: c1 += 1; pc += 1
        elif i.op == INST_DEC0: c0 -= 1; pc += 1
        elif i.op == INST_DEC1: c1 -= 1; pc += 1
        elif i.op == INST_JZ0: pc = i.target if c0 == 0 else pc + 1
        elif i.op == INST_JZ1: pc = i.target if c1 == 0 else pc + 1
        elif i.op == INST_GOTO: pc = i.target
        trace.append((pc, c0, c1))
    return trace

def run_2cm_psi(prog: list[Inst], max_steps: int = 10000,
                verbose: bool = False) -> list[tuple[int, int, int]]:
    c0: Term = nat(0)
    c1: Term = nat(0)
    pc: Term = nat(0)
    state = pair(pair(c0, c1), pc)
    trace = [(0, 0, 0)]

    for step in range(max_steps):
        inner = psi_eval(App(F_ENC, state))
        c0 = psi_eval(App(F_ENC, inner))
        c1 = psi_eval(App(ETA, inner))
        pc_term = psi_eval(App(ETA, state))

        pc_val = to_nat(pc_term)
        if pc_val is None or pc_val >= len(prog): break
        inst = prog[pc_val]
        if verbose:
            print(f"  Step {step}: PC={pc_val}, c0={to_nat(c0)}, c1={to_nat(c1)}, op={inst}")
        if inst.op == INST_HALT: break

        if inst.op == INST_INC0:
            c0 = App(Q, c0); pc_term = App(Q, pc_term)
        elif inst.op == INST_INC1:
            c1 = App(Q, c1); pc_term = App(Q, pc_term)
        elif inst.op == INST_DEC0:
            c0 = psi_eval(App(E, c0)); pc_term = App(Q, pc_term)
        elif inst.op == INST_DEC1:
            c1 = psi_eval(App(E, c1)); pc_term = App(Q, pc_term)
        elif inst.op == INST_JZ0:
            pc_term = nat(inst.target) if is_zero(c0) else App(Q, pc_term)
        elif inst.op == INST_JZ1:
            pc_term = nat(inst.target) if is_zero(c1) else App(Q, pc_term)
        elif inst.op == INST_GOTO:
            pc_term = nat(inst.target)

        state = pair(pair(c0, c1), pc_term)
        c0_val, c1_val = to_nat(c0), to_nat(c1)
        pc_new = to_nat(pc_term)
        if c0_val is None or c1_val is None or pc_new is None:
            print(f"  ERROR: decode failed at step {step}")
            break
        trace.append((pc_new, c0_val, c1_val))
    return trace


# ═══════════════════════════════════════════════════════════════════════
# Tests
# ═══════════════════════════════════════════════════════════════════════

def test_primitives():
    """Test axiom-forced Ψ∗ primitives."""
    print("=" * 70)
    print("Ψ∗ PRIMITIVE TESTS (Ψ₁₆ᶜ table)")
    print("=" * 70)

    # Naturals
    print("\n--- Naturals ---")
    for n in range(5):
        t = nat(n)
        v = to_nat(t)
        assert v == n, f"nat({n}) decode failed: {v}"
    print("  nat(0..4): OK")

    # Q/E
    print("\n--- Q/E (succ/pred) ---")
    for n in range(4):
        assert to_nat(psi_eval(App(Q, nat(n)))) == n + 1
    for n in range(1, 5):
        assert to_nat(psi_eval(App(E, nat(n)))) == n - 1
    print("  Q·nat(n) = nat(n+1), E·nat(n) = nat(n-1): OK")

    # E-transparency
    e_zero = psi_eval(App(E, TOP))
    print(f"  E·⊤ = {term_str(e_zero)} (E-transparency)")

    # Pairs
    print("\n--- Pairs ---")
    p = pair(nat(2), nat(3))
    assert to_nat(fst(p)) == 2 and to_nat(snd(p)) == 3
    assert to_nat(psi_eval(App(F_ENC, p))) == 2
    assert to_nat(psi_eval(App(ETA, p))) == 3
    print("  pair/fst/snd: OK")

    # Nested pairs
    state = pair(pair(nat(3), nat(5)), nat(2))
    inner = psi_eval(App(F_ENC, state))
    assert to_nat(psi_eval(App(F_ENC, inner))) == 3
    assert to_nat(psi_eval(App(ETA, inner))) == 5
    assert to_nat(psi_eval(App(ETA, state))) == 2
    print("  Nested pairs (state encoding): OK")

    # ρ structural branch
    print("\n--- ρ branch ---")
    r_atom = psi_eval(App(RHO, TOP))
    r_comp = psi_eval(App(RHO, App(Q, TOP)))
    print(f"  ρ·⊤ (atom) → f-path = {term_str(r_atom)}")
    print(f"  ρ·(Q·⊤) (compound) → g-path = {term_str(r_comp)}")

    # INC/DEC/INV on core
    print("\n--- INC/DEC/INV on core ---")
    for x in range(2, 6):
        inc_x = dot(INC, x)
        dec_x = dot(DEC, x)
        inv_x = dot(INV, x)
        print(f"  INC·{x}={inc_x}  DEC·{x}={dec_x}  INV·{x}={inv_x}")
        assert inc_x == ((x - 1) % 4) + 2, f"INC·{x} failed"
        assert dec_x == ((x - 3) % 4) + 2, f"DEC·{x} failed"
        assert inv_x == 7 - x, f"INV·{x} failed"
    print("  Arithmetic interpretations: OK")

    # Cancellation: INC·(DEC·x) = x, DEC·(INC·x) = x on core
    print("\n--- Cancellations ---")
    for x in range(2, 6):
        assert dot(INC, dot(DEC, x)) == x, f"INC·DEC·{x} failed"
        assert dot(DEC, dot(INC, x)) == x, f"DEC·INC·{x} failed"
    print("  INC·(DEC·x) = x on core: OK")
    print("  DEC·(INC·x) = x on core: OK")

    # INV involution on all
    for x in range(16):
        assert dot(INV, dot(INV, x)) == x, f"INV·INV·{x} failed"
    print("  INV·(INV·x) = x on all 16: OK")

    print("\nAll primitive tests passed")


def _compare(prog: list[Inst]) -> bool:
    print("\nProgram:")
    for i, inst in enumerate(prog):
        print(f"  L{i}: {inst}")
    ref = run_2cm_ref(prog)
    psi = run_2cm_psi(prog, verbose=False)
    max_len = max(len(ref), len(psi))
    all_match = True
    for i in range(max_len):
        r = ref[i] if i < len(ref) else None
        p = psi[i] if i < len(psi) else None
        if r != p:
            all_match = False
    print(f"  Traces match: {all_match}")
    if psi:
        final = psi[-1]
        print(f"  Final state: c0={final[1]}, c1={final[2]}")
    return all_match


def test_2cm():
    """Run 2CM tests."""
    results = []

    print("\n" + "=" * 70)
    print("TEST 1: INC0 x3, HALT  →  c0=3, c1=0")
    print("=" * 70)
    results.append(_compare([
        Inst(INST_INC0), Inst(INST_INC0), Inst(INST_INC0), Inst(INST_HALT)]))

    print("\n" + "=" * 70)
    print("TEST 2: INC0 x3, DEC0 x2, HALT  →  c0=1, c1=0")
    print("=" * 70)
    results.append(_compare([
        Inst(INST_INC0), Inst(INST_INC0), Inst(INST_INC0),
        Inst(INST_DEC0), Inst(INST_DEC0), Inst(INST_HALT)]))

    print("\n" + "=" * 70)
    print("TEST 3: Transfer c0=3 → c1")
    print("=" * 70)
    results.append(_compare([
        Inst(INST_INC0), Inst(INST_INC0), Inst(INST_INC0),
        Inst(INST_JZ0, target=7), Inst(INST_DEC0),
        Inst(INST_INC1), Inst(INST_GOTO, target=3), Inst(INST_HALT)]))

    print("\n" + "=" * 70)
    print("TEST 4: Clear c0=5 → 0")
    print("=" * 70)
    results.append(_compare([
        Inst(INST_INC0), Inst(INST_INC0), Inst(INST_INC0),
        Inst(INST_INC0), Inst(INST_INC0),
        Inst(INST_JZ0, target=8), Inst(INST_DEC0),
        Inst(INST_GOTO, target=5), Inst(INST_HALT)]))

    return results


if __name__ == "__main__":
    test_primitives()
    results = test_2cm()

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    names = [
        "1. Simple (INC x3, HALT)",
        "2. Decrement (INC x3, DEC x2)",
        "3. Transfer loop (c0=3 → c1)",
        "4. Clear (c0=5 → 0)",
    ]
    for name, ok in zip(names, results):
        print(f"  {name:40s} {'PASS' if ok else 'FAIL'}")
    all_pass = all(results)
    print(f"\n  All: {'PASS' if all_pass else 'FAIL'}")

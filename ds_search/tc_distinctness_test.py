#!/usr/bin/env python3
"""
Test whether Turing completeness forces the 13 remaining distinctness requirements.

For each of the 13 SAT pairs (role merges that the categorical axioms permit),
check whether the Ψ∗ term algebra can still simulate 2-counter machines when
that pair is merged.

Methodology: reassign element constants so the two merged roles share the same
atom value, then run the psi_star.py 2CM simulation. The evaluator dispatches
on atom identity, so merging creates priority conflicts.

Elements used in 2CM simulation: ⊤(0), Q(6), E(7), f(2), g(4), η(9)
Elements NOT used in 2CM:         ⊥(1), τ(3), ρ(8), Y(10)

Evaluator dispatch priority (first match wins):
  Q > g > E > f > η > Y > ρ

Usage:
  uv run python -m ds_search.tc_distinctness_test
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Union
import sys


# ═══════════════════════════════════════════════════════════════════════
# Ψ∗ term algebra (copied from psi_star.py, parameterized by elements)
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class App:
    fun: "Term"
    arg: "Term"

Term = Union[int, App]


class Config:
    """Element assignment configuration. Merging sets two roles to the same value."""
    def __init__(self):
        self.TOP = 0
        self.BOT = 1
        self.F_ENC = 2
        self.TAU = 3
        self.G_ENC = 4
        self.Q = 6
        self.E = 7
        self.RHO = 8
        self.ETA = 9
        self.Y_COMB = 10

    def merge(self, role_a: str, role_b: str):
        """Set role_b to have the same element value as role_a."""
        val = getattr(self, role_a)
        setattr(self, role_b, val)
        return self


# Cayley table (only used for atom-atom fallback)
TABLE = [
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    [5,1,13,7,11,5,6,8,2,5,11,9,4,14,3,15],
    [0,1,0,0,0,0,1,1,1,0,1,1,0,0,1,1],
    [0,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11],
    [0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,0],
    [15,0,5,9,3,15,14,14,2,12,8,14,12,4,12,8],
    [0,1,8,4,13,2,11,2,14,3,15,12,14,15,6,5],
    [12,1,13,7,11,5,12,11,4,12,5,14,15,7,11,12],
    [1,6,14,14,14,14,9,8,3,15,5,7,13,11,12,4],
    [13,1,4,3,12,11,2,11,5,3,8,14,9,7,11,11],
    [14,1,9,10,11,13,12,7,5,6,8,2,14,12,10,4],
    [0,1,1,0,1,1,0,1,1,1,0,0,0,0,0,1],
    [3,0,14,4,14,6,11,12,7,3,15,10,14,2,6,8],
    [14,0,5,4,3,2,12,5,11,14,3,14,12,2,6,3],
    [1,3,13,15,3,7,14,8,15,4,11,6,7,14,12,10],
]


def dot(a: int, b: int) -> int:
    return TABLE[a][b]


# ═══════════════════════════════════════════════════════════════════════
# Parameterized evaluator
# ═══════════════════════════════════════════════════════════════════════

class EvalError(Exception):
    pass


def psi_eval(t: Term, cfg: Config, max_steps: int = 100000,
             _steps: list | None = None) -> Term:
    """Evaluate a Ψ∗ term with configurable element assignments."""
    if _steps is None:
        _steps = [0]
    _steps[0] += 1
    if _steps[0] > max_steps:
        raise EvalError(f"Exceeded {max_steps} steps")

    if isinstance(t, int):
        return t

    fn, arg = t.fun, t.arg

    # Q: freeze (constructor, lazy)
    if fn == cfg.Q:
        return t

    # g: pair constructor
    if fn == cfg.G_ENC:
        return App(cfg.G_ENC, psi_eval(arg, cfg, max_steps, _steps))

    # E: unwrap Q (destructor / predecessor)
    if fn == cfg.E:
        val = psi_eval(arg, cfg, max_steps, _steps)
        if isinstance(val, App) and val.fun == cfg.Q:
            return psi_eval(val.arg, cfg, max_steps, _steps)
        if isinstance(val, int):
            return dot(cfg.E, val)
        return App(cfg.E, val)

    # f: fst (destructor)
    if fn == cfg.F_ENC:
        val = psi_eval(arg, cfg, max_steps, _steps)
        if isinstance(val, App) and isinstance(val.fun, App) and val.fun.fun == cfg.G_ENC:
            return psi_eval(val.fun.arg, cfg, max_steps, _steps)
        if isinstance(val, int):
            return dot(cfg.F_ENC, val)
        return App(cfg.F_ENC, val)

    # η: snd (destructor)
    if fn == cfg.ETA:
        val = psi_eval(arg, cfg, max_steps, _steps)
        if isinstance(val, App) and isinstance(val.fun, App) and val.fun.fun == cfg.G_ENC:
            return psi_eval(val.arg, cfg, max_steps, _steps)
        if isinstance(val, int):
            return dot(cfg.ETA, val)
        return App(cfg.ETA, val)

    # Y: fixed-point combinator
    if fn == cfg.Y_COMB:
        return App(cfg.Y_COMB, psi_eval(arg, cfg, max_steps, _steps))

    # ρ: structural branch
    if fn == cfg.RHO:
        val = psi_eval(arg, cfg, max_steps, _steps)
        if isinstance(val, int):
            return psi_eval(App(cfg.F_ENC, arg), cfg, max_steps, _steps)
        else:
            return psi_eval(App(cfg.G_ENC, arg), cfg, max_steps, _steps)

    # General application
    fn_val = psi_eval(fn, cfg, max_steps, _steps)
    arg_val = psi_eval(arg, cfg, max_steps, _steps)

    if isinstance(fn_val, int) and not isinstance(fn, int):
        return psi_eval(App(fn_val, arg_val), cfg, max_steps, _steps)

    if isinstance(fn_val, App) and fn_val.fun == cfg.G_ENC:
        return App(fn_val, arg_val)

    if isinstance(fn_val, int) and isinstance(arg_val, int):
        return dot(fn_val, arg_val)

    return App(fn_val, arg_val)


# ═══════════════════════════════════════════════════════════════════════
# Parameterized 2CM simulation
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


def nat(n: int, cfg: Config) -> Term:
    t: Term = cfg.TOP
    for _ in range(n):
        t = App(cfg.Q, t)
    return t


def to_nat(t: Term, cfg: Config) -> int | None:
    n = 0
    while isinstance(t, App) and t.fun == cfg.Q:
        n += 1
        t = t.arg
    return n if t == cfg.TOP else None


def pair(a: Term, b: Term, cfg: Config) -> Term:
    return App(App(cfg.G_ENC, a), b)


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


def run_2cm_psi(prog: list[Inst], cfg: Config,
                max_steps: int = 10000) -> list[tuple[int, int, int]] | str:
    """Run 2CM simulation. Returns trace on success, error string on failure."""
    c0: Term = nat(0, cfg)
    c1: Term = nat(0, cfg)
    pc: Term = nat(0, cfg)
    state = pair(pair(c0, c1, cfg), pc, cfg)
    trace = [(0, 0, 0)]

    try:
        for step in range(max_steps):
            inner = psi_eval(App(cfg.F_ENC, state), cfg)
            c0 = psi_eval(App(cfg.F_ENC, inner), cfg)
            c1 = psi_eval(App(cfg.ETA, inner), cfg)
            pc_term = psi_eval(App(cfg.ETA, state), cfg)

            pc_val = to_nat(pc_term, cfg)
            if pc_val is None or pc_val >= len(prog):
                return f"pc decode failed at step {step}: pc_term not a nat"

            inst = prog[pc_val]
            if inst.op == INST_HALT:
                break

            if inst.op == INST_INC0:
                c0 = App(cfg.Q, c0)
                pc_term = App(cfg.Q, pc_term)
            elif inst.op == INST_INC1:
                c1 = App(cfg.Q, c1)
                pc_term = App(cfg.Q, pc_term)
            elif inst.op == INST_DEC0:
                c0 = psi_eval(App(cfg.E, c0), cfg)
                pc_term = App(cfg.Q, pc_term)
            elif inst.op == INST_DEC1:
                c1 = psi_eval(App(cfg.E, c1), cfg)
                pc_term = App(cfg.Q, pc_term)
            elif inst.op == INST_JZ0:
                if c0 == cfg.TOP:
                    pc_term = nat(inst.target, cfg)
                else:
                    pc_term = App(cfg.Q, pc_term)
            elif inst.op == INST_JZ1:
                if c1 == cfg.TOP:
                    pc_term = nat(inst.target, cfg)
                else:
                    pc_term = App(cfg.Q, pc_term)
            elif inst.op == INST_GOTO:
                pc_term = nat(inst.target, cfg)

            state = pair(pair(c0, c1, cfg), pc_term, cfg)

            c0_val = to_nat(c0, cfg)
            c1_val = to_nat(c1, cfg)
            pc_new = to_nat(pc_term, cfg)
            if c0_val is None or c1_val is None or pc_new is None:
                return (f"decode failed at step {step}: "
                        f"c0={'OK' if c0_val is not None else 'FAIL'}, "
                        f"c1={'OK' if c1_val is not None else 'FAIL'}, "
                        f"pc={'OK' if pc_new is not None else 'FAIL'}")
            trace.append((pc_new, c0_val, c1_val))

    except EvalError as e:
        return f"eval error: {e}"
    except RecursionError:
        return "recursion depth exceeded (infinite eval loop)"

    return trace


# ═══════════════════════════════════════════════════════════════════════
# Test programs
# ═══════════════════════════════════════════════════════════════════════

# Test 1: INC c0 three times → c0=3
PROG_SIMPLE = [Inst(INST_INC0), Inst(INST_INC0), Inst(INST_INC0), Inst(INST_HALT)]

# Test 2: INC c0 three times, DEC twice → c0=1
PROG_DEC = [
    Inst(INST_INC0), Inst(INST_INC0), Inst(INST_INC0),
    Inst(INST_DEC0), Inst(INST_DEC0), Inst(INST_HALT),
]

# Test 3: Transfer c0=3 → c1 (loop with JZ, DEC, INC, GOTO)
PROG_TRANSFER = [
    Inst(INST_INC0), Inst(INST_INC0), Inst(INST_INC0),  # c0=3
    Inst(INST_JZ0, target=7),
    Inst(INST_DEC0), Inst(INST_INC1), Inst(INST_GOTO, target=3),
    Inst(INST_HALT),
]

# Test 4: Clear c0=5 → 0
PROG_CLEAR = [
    Inst(INST_INC0), Inst(INST_INC0), Inst(INST_INC0),
    Inst(INST_INC0), Inst(INST_INC0),
    Inst(INST_JZ0, target=8),
    Inst(INST_DEC0), Inst(INST_GOTO, target=5),
    Inst(INST_HALT),
]

TESTS = [
    ("simple (INC×3)", PROG_SIMPLE),
    ("decrement (INC×3, DEC×2)", PROG_DEC),
    ("transfer (c0=3→c1)", PROG_TRANSFER),
    ("clear (c0=5→0)", PROG_CLEAR),
]


# ═══════════════════════════════════════════════════════════════════════
# The 13 SAT pairs and their merge configurations
# ═══════════════════════════════════════════════════════════════════════

# Role name → Config attribute
ROLE_MAP = {
    "⊤": "TOP", "⊥": "BOT", "Q": "Q", "E": "E",
    "f": "F_ENC", "g": "G_ENC", "τ": "TAU",
    "ρ": "RHO", "η": "ETA", "Y": "Y_COMB",
}

# The 13 SAT pairs (from forced_roles_test.py)
SAT_PAIRS = [
    ("⊤", "⊥"),
    ("Q", "E"),
    ("Q", "f"),
    ("Q", "ρ"),
    ("Q", "Y"),
    ("E", "f"),
    ("E", "ρ"),
    ("E", "Y"),
    ("f", "ρ"),
    ("f", "η"),
    ("f", "Y"),
    ("ρ", "Y"),
    ("η", "Y"),
]

# Elements actually used in 2CM simulation
USED_IN_2CM = {"⊤", "Q", "E", "f", "g", "η"}


def diagnose_failure(role_a: str, role_b: str) -> str:
    """Explain WHY merging these roles breaks TC."""
    a_used = role_a in USED_IN_2CM
    b_used = role_b in USED_IN_2CM

    if not a_used and not b_used:
        return "neither used in 2CM"

    # Dispatch priority (evaluator order):
    priority = {"Q": 0, "g": 1, "E": 2, "f": 3, "η": 4, "Y": 5, "ρ": 6,
                "⊤": -1, "⊥": -1, "τ": -1}

    if not a_used:
        # b is used, a is not. Merging to a's value means b's dispatch
        # position changes. Since a is not used, its dispatch case is never
        # hit normally. If b's value changes to a's, b's case may still fire
        # (if a's value doesn't conflict with a higher-priority case).
        return f"{role_b} used, {role_a} not used"
    if not b_used:
        return f"{role_a} used, {role_b} not used"

    # Both used. The one with higher priority (lower number) wins.
    pa = priority.get(role_a, 99)
    pb = priority.get(role_b, 99)
    winner = role_a if pa < pb else role_b
    loser = role_b if pa < pb else role_a

    role_descriptions = {
        "Q": "succ (freeze/constructor)",
        "E": "pred (unwrap/destructor)",
        "f": "fst (pair projection)",
        "η": "snd (pair projection)",
        "g": "pair constructor",
        "ρ": "branch (structural dispatch)",
        "Y": "fixed-point combinator",
        "⊤": "zero",
        "⊥": "second absorber",
    }

    return (f"{winner} dispatch wins (priority), "
            f"{loser} ({role_descriptions.get(loser, '?')}) is DEAD")


# ═══════════════════════════════════════════════════════════════════════
# Main test
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("=" * 80)
    print("TC DISTINCTNESS TEST: Do the 13 SAT pairs break Turing completeness?")
    print("=" * 80)
    print()
    print("For each of the 13 role pairs that the categorical axioms permit merging,")
    print("test whether the Ψ∗ 2CM simulation still works with the merge applied.")
    print()
    print(f"Elements used in 2CM: {USED_IN_2CM}")
    print(f"Evaluator priority: Q > g > E > f > η > Y > ρ")
    print()

    # First, verify baseline (no merges)
    print("─" * 80)
    print("BASELINE (no merges):")
    baseline_cfg = Config()
    for name, prog in TESTS:
        ref = run_2cm_ref(prog)
        psi = run_2cm_psi(prog, baseline_cfg)
        ok = isinstance(psi, list) and psi == ref
        print(f"  {name:35s} {'PASS' if ok else 'FAIL'}")
        if not ok:
            print(f"    ERROR: Baseline failed! ref={ref[-1] if ref else '?'}, psi={psi}")
            sys.exit(1)
    print("  All baseline tests pass.")
    print()

    # Test each merge
    results = []
    print("─" * 80)
    print(f"{'Pair':>8s}  {'Test1':>7s} {'Test2':>7s} {'Test3':>7s} {'Test4':>7s}  {'TC?':>5s}  Failure Mode")
    print("─" * 80)

    for role_a, role_b in SAT_PAIRS:
        cfg = Config()
        attr_a = ROLE_MAP[role_a]
        attr_b = ROLE_MAP[role_b]
        # Merge: set role_b to have the same value as role_a
        cfg.merge(attr_a, attr_b)

        test_results = []
        failure_detail = None

        for name, prog in TESTS:
            ref = run_2cm_ref(prog)
            psi = run_2cm_psi(prog, cfg)

            if isinstance(psi, str):
                test_results.append(("ERR", psi))
                if failure_detail is None:
                    failure_detail = psi
            elif psi == ref:
                test_results.append(("PASS", None))
            else:
                # Find first divergence
                for i in range(min(len(ref), len(psi))):
                    if ref[i] != psi[i]:
                        test_results.append(("FAIL", f"diverge at step {i}: ref={ref[i]} psi={psi[i]}"))
                        if failure_detail is None:
                            failure_detail = f"diverge at step {i}: ref={ref[i]} psi={psi[i]}"
                        break
                else:
                    test_results.append(("FAIL", f"trace length mismatch: ref={len(ref)} psi={len(psi)}"))
                    if failure_detail is None:
                        failure_detail = f"trace length: ref={len(ref)} psi={len(psi)}"

        all_pass = all(r[0] == "PASS" for r in test_results)
        tc_status = "YES" if all_pass else "NO"

        status_strs = [r[0] for r in test_results]
        diag = diagnose_failure(role_a, role_b) if not all_pass else "—"
        source = "expressiveness only" if all_pass else "TC requirement"

        print(f"{role_a}={role_b:>3s}  {status_strs[0]:>7s} {status_strs[1]:>7s} "
              f"{status_strs[2]:>7s} {status_strs[3]:>7s}  {tc_status:>5s}  {diag}")

        results.append({
            "pair": f"{role_a}={role_b}",
            "tc": all_pass,
            "tests": test_results,
            "diagnosis": diag,
            "source": source,
            "failure": failure_detail,
        })

    # Summary table
    print()
    print("=" * 80)
    print("SUMMARY TABLE")
    print("=" * 80)
    print()
    print(f"| {'Merged Pair':>13s} | {'TC Simulation':>14s} | {'Failure Mode':>45s} | {'Distinctness Source':>20s} |")
    print(f"|{'-'*15}|{'-'*16}|{'-'*47}|{'-'*22}|")

    tc_fail_count = 0
    tc_pass_count = 0
    for r in results:
        tc_str = "SUCCEEDS" if r["tc"] else "FAILS"
        fail_str = r["diagnosis"] if not r["tc"] else "—"
        src_str = r["source"]
        print(f"| {r['pair']:>13s} | {tc_str:>14s} | {fail_str:>45s} | {src_str:>20s} |")
        if r["tc"]:
            tc_pass_count += 1
        else:
            tc_fail_count += 1

    print()
    print(f"TC-required pairs:       {tc_fail_count}/13")
    print(f"Expressiveness-only pairs: {tc_pass_count}/13")

    if tc_fail_count == 13:
        print("\n*** ALL 13 pairs break TC. Distinctness is derivable from TC. ***")
        print("*** The distinctness axiom is a theorem, not an axiom. ***")
    elif tc_fail_count == 0:
        print("\n*** No pairs break TC. Distinctness is purely an expressiveness choice. ***")
    else:
        print(f"\n*** {tc_fail_count} pairs are TC-required, {tc_pass_count} are expressiveness-only. ***")
        print("\nTC-required pairs (merging breaks computation):")
        for r in results:
            if not r["tc"]:
                print(f"  {r['pair']:>8s}: {r['diagnosis']}")
        print("\nExpressiveness-only pairs (merging preserves TC):")
        for r in results:
            if r["tc"]:
                print(f"  {r['pair']:>8s}")


if __name__ == "__main__":
    main()

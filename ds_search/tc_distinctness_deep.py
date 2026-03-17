#!/usr/bin/env python3
"""
Deep analysis of TC-required distinctness pairs.

The initial test found 4 pairs that break TC: Q=E, Q=f, E=f, f=η.
All fail because the evaluator's dispatch priority makes one role "shadow"
the other. But is this an artifact of dispatch ordering, or a genuine
structural impossibility?

For each of the 4 failing pairs, we ask:
  Can ANY evaluation strategy for the merged element support both roles?

The answer depends on whether the two roles are structurally distinguishable
at the point of dispatch. If they are, an evaluator could in principle
route correctly. If they aren't, the merge genuinely kills TC.

Analysis:

Q=E: Q freezes its argument (lazy constructor). E evaluates its argument
     then unwraps Q. If Q=E, the single element must BOTH freeze and unwrap.
     Given App(merged, x):
     - As Q: return App(merged, x) without evaluating x
     - As E: evaluate x, then if x = App(merged, y), return y
     These are contradictory: Q demands laziness, E demands eagerness.
     No dispatch strategy resolves this — the semantics conflict on every input.
     GENUINELY TC-REQUIRED.

Q=f: Q freezes. f extracts fst from pairs.
     Given App(merged, x):
     - As Q: return App(merged, x) [freeze]
     - As f: evaluate x, extract fst if it's a pair
     Again contradictory: Q must not evaluate x, f must evaluate x.
     GENUINELY TC-REQUIRED.

E=f: E unwraps Q. f extracts fst from pairs.
     Given App(merged, pair(a,b)):
     - As E: check if pair(a,b) has form App(Q, y). It doesn't (it's App(App(g,a),b)).
             So E falls through to dot(E, val) or irreducible.
     - As f: extract a from pair(a,b).
     These DON'T conflict on pairs — E wouldn't unwrap a pair anyway.
     Given App(merged, App(Q, y)):
     - As E: unwrap Q, return y.
     - As f: check if App(Q,y) is a pair. It's not (fun=Q, not App(g,_)).
             So f falls through.
     These DON'T conflict on Q-terms either!
     Could a smart dispatcher handle both? YES:
       App(merged, val):
         if val = App(Q, y): return y  [E behavior]
         if val = App(App(g, a), b): return a  [f behavior]
         else: fallback
     This works because Q-terms and g-pairs have different structure.
     E=f might NOT be genuinely TC-required — it might be an artifact
     of the evaluator choosing E-dispatch for everything.

f=η: f extracts fst, η extracts snd from pairs.
     Given App(merged, App(App(g, a), b)):
     - As f: return a
     - As η: return b
     Same input structure, contradictory outputs.
     No dispatch strategy can resolve which projection to take.
     GENUINELY TC-REQUIRED.

Let's verify E=f with a smart dispatcher.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Union
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from ds_search.tc_distinctness_test import (
    App, Term, Config, dot, nat, to_nat, pair,
    Inst, INST_INC0, INST_INC1, INST_DEC0, INST_DEC1,
    INST_JZ0, INST_JZ1, INST_HALT, INST_GOTO,
    TESTS, run_2cm_ref,
)


class EvalError(Exception):
    pass


def psi_eval_smart(t: Term, cfg: Config, max_steps: int = 100000,
                   _steps: list | None = None) -> Term:
    """Evaluator with SMART dispatch for merged E=f.

    When E and f share the same element, dispatch by ARGUMENT STRUCTURE:
    - If arg evaluates to App(Q, y): do E (unwrap Q)
    - If arg evaluates to App(App(g, a), b): do f (extract fst)
    - Otherwise: atom fallback
    """
    if _steps is None:
        _steps = [0]
    _steps[0] += 1
    if _steps[0] > max_steps:
        raise EvalError(f"Exceeded {max_steps} steps")

    if isinstance(t, int):
        return t

    fn, arg = t.fun, t.arg

    # Q: freeze
    if fn == cfg.Q:
        return t

    # g: pair constructor
    if fn == cfg.G_ENC:
        return App(cfg.G_ENC, psi_eval_smart(arg, cfg, max_steps, _steps))

    # Smart E/f dispatch: if E == F_ENC (merged), dispatch by argument structure
    if fn == cfg.E and cfg.E == cfg.F_ENC:
        val = psi_eval_smart(arg, cfg, max_steps, _steps)
        # E behavior: unwrap Q
        if isinstance(val, App) and val.fun == cfg.Q:
            return psi_eval_smart(val.arg, cfg, max_steps, _steps)
        # f behavior: extract fst from pair
        if isinstance(val, App) and isinstance(val.fun, App) and val.fun.fun == cfg.G_ENC:
            return psi_eval_smart(val.fun.arg, cfg, max_steps, _steps)
        # Atom fallback
        if isinstance(val, int):
            return dot(cfg.E, val)
        return App(cfg.E, val)

    # Normal E: unwrap Q
    if fn == cfg.E:
        val = psi_eval_smart(arg, cfg, max_steps, _steps)
        if isinstance(val, App) and val.fun == cfg.Q:
            return psi_eval_smart(val.arg, cfg, max_steps, _steps)
        if isinstance(val, int):
            return dot(cfg.E, val)
        return App(cfg.E, val)

    # Normal f: fst
    if fn == cfg.F_ENC:
        val = psi_eval_smart(arg, cfg, max_steps, _steps)
        if isinstance(val, App) and isinstance(val.fun, App) and val.fun.fun == cfg.G_ENC:
            return psi_eval_smart(val.fun.arg, cfg, max_steps, _steps)
        if isinstance(val, int):
            return dot(cfg.F_ENC, val)
        return App(cfg.F_ENC, val)

    # η: snd
    if fn == cfg.ETA:
        val = psi_eval_smart(arg, cfg, max_steps, _steps)
        if isinstance(val, App) and isinstance(val.fun, App) and val.fun.fun == cfg.G_ENC:
            return psi_eval_smart(val.arg, cfg, max_steps, _steps)
        if isinstance(val, int):
            return dot(cfg.ETA, val)
        return App(cfg.ETA, val)

    # Y: fixpoint
    if fn == cfg.Y_COMB:
        return App(cfg.Y_COMB, psi_eval_smart(arg, cfg, max_steps, _steps))

    # ρ: branch
    if fn == cfg.RHO:
        val = psi_eval_smart(arg, cfg, max_steps, _steps)
        if isinstance(val, int):
            return psi_eval_smart(App(cfg.F_ENC, arg), cfg, max_steps, _steps)
        else:
            return psi_eval_smart(App(cfg.G_ENC, arg), cfg, max_steps, _steps)

    # General application
    fn_val = psi_eval_smart(fn, cfg, max_steps, _steps)
    arg_val = psi_eval_smart(arg, cfg, max_steps, _steps)

    if isinstance(fn_val, int) and not isinstance(fn, int):
        return psi_eval_smart(App(fn_val, arg_val), cfg, max_steps, _steps)
    if isinstance(fn_val, App) and fn_val.fun == cfg.G_ENC:
        return App(fn_val, arg_val)
    if isinstance(fn_val, int) and isinstance(arg_val, int):
        return dot(fn_val, arg_val)
    return App(fn_val, arg_val)


def run_2cm_smart(prog, cfg, max_steps=10000):
    """Run 2CM with smart evaluator."""
    c0: Term = nat(0, cfg)
    c1: Term = nat(0, cfg)
    pc: Term = nat(0, cfg)
    state = pair(pair(c0, c1, cfg), pc, cfg)
    trace = [(0, 0, 0)]

    try:
        for step in range(max_steps):
            inner = psi_eval_smart(App(cfg.F_ENC, state), cfg)
            c0 = psi_eval_smart(App(cfg.F_ENC, inner), cfg)
            c1 = psi_eval_smart(App(cfg.ETA, inner), cfg)
            pc_term = psi_eval_smart(App(cfg.ETA, state), cfg)

            pc_val = to_nat(pc_term, cfg)
            if pc_val is None or pc_val >= len(prog):
                return f"pc decode failed at step {step}"

            inst = prog[pc_val]
            if inst.op == INST_HALT:
                break

            if inst.op == INST_INC0:
                c0 = App(cfg.Q, c0); pc_term = App(cfg.Q, pc_term)
            elif inst.op == INST_INC1:
                c1 = App(cfg.Q, c1); pc_term = App(cfg.Q, pc_term)
            elif inst.op == INST_DEC0:
                c0 = psi_eval_smart(App(cfg.E, c0), cfg); pc_term = App(cfg.Q, pc_term)
            elif inst.op == INST_DEC1:
                c1 = psi_eval_smart(App(cfg.E, c1), cfg); pc_term = App(cfg.Q, pc_term)
            elif inst.op == INST_JZ0:
                pc_term = nat(inst.target, cfg) if c0 == cfg.TOP else App(cfg.Q, pc_term)
            elif inst.op == INST_JZ1:
                pc_term = nat(inst.target, cfg) if c1 == cfg.TOP else App(cfg.Q, pc_term)
            elif inst.op == INST_GOTO:
                pc_term = nat(inst.target, cfg)

            state = pair(pair(c0, c1, cfg), pc_term, cfg)
            c0_val, c1_val, pc_new = to_nat(c0, cfg), to_nat(c1, cfg), to_nat(pc_term, cfg)
            if c0_val is None or c1_val is None or pc_new is None:
                return f"decode failed at step {step}"
            trace.append((pc_new, c0_val, c1_val))
    except EvalError as e:
        return f"eval error: {e}"
    except RecursionError:
        return "recursion depth exceeded"

    return trace


def main():
    print("=" * 80)
    print("DEEP ANALYSIS: Can smart dispatch save E=f?")
    print("=" * 80)
    print()
    print("E and f operate on DIFFERENT term structures:")
    print("  E unwraps App(Q, y) → y        (Q-terms)")
    print("  f extracts App(App(g, a), b) → a  (g-pairs)")
    print("These never collide. A smart dispatcher routes by argument shape.")
    print()

    cfg = Config()
    cfg.merge("E", "F_ENC")  # E = f = element 7

    print(f"Merged: E = f = element {cfg.E}")
    print()

    all_pass = True
    for name, prog in TESTS:
        ref = run_2cm_ref(prog)
        psi = run_2cm_smart(prog, cfg)

        if isinstance(psi, str):
            print(f"  {name:35s} ERR: {psi}")
            all_pass = False
        elif psi == ref:
            print(f"  {name:35s} PASS")
        else:
            print(f"  {name:35s} FAIL")
            all_pass = False

    print()
    if all_pass:
        print("*** E=f SUCCEEDS with smart dispatch. ***")
        print("E=f is NOT genuinely TC-required — it's a dispatch artifact.")
        print("The structural separation (Q-terms vs g-pairs) allows a single")
        print("element to serve both roles.")
    else:
        print("*** E=f FAILS even with smart dispatch. ***")
        print("E=f is genuinely TC-required.")

    print()
    print("=" * 80)
    print("STRUCTURAL ANALYSIS OF ALL 4 FAILING PAIRS")
    print("=" * 80)
    print()
    pairs_analysis = [
        ("Q=E", "Q freezes (lazy), E evaluates then unwraps (eager).",
         "CONTRADICTORY on every input: laziness vs eagerness.",
         "GENUINE — no dispatch strategy resolves lazy vs eager."),
        ("Q=f", "Q freezes (lazy), f evaluates then extracts fst.",
         "CONTRADICTORY on every input: Q must not eval arg, f must eval arg.",
         "GENUINE — lazy vs eager conflict, same as Q=E."),
        ("E=f", "E unwraps Q-terms, f extracts from g-pairs.",
         "NON-CONFLICTING: Q-terms and g-pairs are structurally disjoint.",
         f"{'ARTIFACT — smart dispatch resolves it.' if all_pass else 'GENUINE.'}"),
        ("f=η", "f extracts fst from pair, η extracts snd from pair.",
         "CONTRADICTORY on pairs: same input, different outputs (a vs b).",
         "GENUINE — no dispatch strategy resolves fst vs snd on the same pair."),
    ]

    for pair_name, desc, conflict, verdict in pairs_analysis:
        print(f"  {pair_name}:")
        print(f"    Roles: {desc}")
        print(f"    Conflict: {conflict}")
        print(f"    Verdict: {verdict}")
        print()

    print("=" * 80)
    print("REVISED SUMMARY")
    print("=" * 80)
    print()
    if all_pass:
        genuinely_required = ["Q=E", "Q=f", "f=η"]
        artifact = ["E=f"]
        expressiveness = ["⊤=⊥", "Q=ρ", "Q=Y", "E=ρ", "E=Y", "f=ρ", "f=Y", "ρ=Y", "η=Y"]
        print(f"Genuinely TC-required ({len(genuinely_required)}): {genuinely_required}")
        print(f"  Q≠E: succ/pred need distinct lazy/eager semantics")
        print(f"  Q≠f: succ/fst need distinct lazy/eager semantics")
        print(f"  f≠η: fst/snd need distinct projection targets")
        print()
        print(f"Dispatch artifact ({len(artifact)}): {artifact}")
        print(f"  E and f operate on disjoint term shapes (Q-terms vs g-pairs)")
        print()
        print(f"Expressiveness only ({len(expressiveness)}): {expressiveness}")
        print(f"  These merges preserve TC — distinctness justified by expressiveness alone")
        print()
        print(f"Final count: 3 TC-required, 1 artifact, 9 expressiveness")
        print(f"The distinctness axiom adds 13 requirements, of which 3 are TC-derivable.")
    else:
        print("E=f is genuinely required. Original count stands: 4 TC-required, 9 expressiveness.")


if __name__ == "__main__":
    main()

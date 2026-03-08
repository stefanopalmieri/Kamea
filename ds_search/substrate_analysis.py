#!/usr/bin/env python3
"""
Substrate viability analysis for Level 4 algebras.

Samples multiple Level 4 models at each size N=6..12 and measures
properties relevant to computational self-description:

1. Tester separation: do testers collectively distinguish all elements?
2. Encoder reach: how many distinct testers can encoders produce?
3. Compositional depth: can you chain encoder→tester→encoder?
4. Default/inert element: is there a "garbage" sink?
5. Self-identification: does any element satisfy x·a = x for some a?
6. Recoverability: can the algebra's own operations identify every element?
7. Encoder–tester duality: do encoders and testers form a closed subsystem?

Then checks all the same properties on Δ₁ for comparison.

Usage:
  uv run python ds_search/substrate_analysis.py
"""

from __future__ import annotations

import time
from collections import Counter
from itertools import combinations

from z3 import Or, sat

from ds_search.axiom_explorer import (
    DELTA1_TABLE,
    SearchResult,
    classify_elements,
    encode_level,
    extract_table,
    print_table,
)


# ═══════════════════════════════════════════════════════════════════════
# Substrate metrics
# ═══════════════════════════════════════════════════════════════════════

def tester_separation(table: list[list[int]]) -> dict:
    """
    Do the testers collectively separate all element pairs?

    For each pair (x, y), check if ∃ tester t such that t·x ≠ t·y.
    Returns the number of separated pairs, total pairs, and any
    unseparated pairs.
    """
    N = len(table)
    cats = classify_elements(table)
    testers = cats["testers"]

    total_pairs = 0
    separated = 0
    unseparated = []

    for x in range(N):
        for y in range(x + 1, N):
            total_pairs += 1
            sep = any(table[t][x] != table[t][y] for t in testers)
            if sep:
                separated += 1
            else:
                unseparated.append((x, y))

    return {
        "total_pairs": total_pairs,
        "separated": separated,
        "fraction": separated / total_pairs if total_pairs else 0,
        "unseparated": unseparated,
        "full_separation": len(unseparated) == 0,
    }


def encoder_reach(table: list[list[int]]) -> dict:
    """
    For each encoder, what testers does it produce?
    What's the union of all tester outputs across all encoders?
    """
    N = len(table)
    cats = classify_elements(table)
    tester_set = set(cats["testers"])

    encoder_profiles = {}
    all_produced_testers = set()

    for e in cats["encoders"]:
        produced = set()
        for y in range(N):
            v = table[e][y]
            if v not in (0, 1) and v in tester_set:
                produced.add(v)
        encoder_profiles[e] = produced
        all_produced_testers |= produced

    return {
        "encoder_profiles": encoder_profiles,
        "all_produced_testers": all_produced_testers,
        "testers_reachable_from_encoders": len(all_produced_testers),
        "total_testers": len(tester_set),
        "all_testers_reachable": all_produced_testers == tester_set,
    }


def compositional_depth(table: list[list[int]]) -> dict:
    """
    Measure how deep composition chains go.

    - Depth 1: encoder · input → tester (Level 3/4 guarantees this)
    - Depth 2: encoder · input → tester; tester · input → bool
    - Depth 3: can we get encoder · a → tester → (feed into another encoder) → new tester?

    Also: is there an element that, when applied to an encoder, yields
    another encoder? (encoder · x = encoder') That would be a
    "second-order" operation.
    """
    N = len(table)
    cats = classify_elements(table)
    tester_set = set(cats["testers"])
    encoder_set = set(cats["encoders"])

    # Depth-2 chains: encoder · y → t (tester), then t · z → bool
    depth2_chains = 0
    for e in cats["encoders"]:
        for y in range(N):
            t = table[e][y]
            if t in tester_set:
                for z in range(N):
                    if table[t][z] in (0, 1):
                        depth2_chains += 1

    # Encoder-to-encoder: ∃ x, y such that x is encoder, table[x][y] is encoder
    enc_to_enc = []
    for e in cats["encoders"]:
        for y in range(N):
            v = table[e][y]
            if v in encoder_set and v != e:
                enc_to_enc.append((e, y, v))

    # Can any element act as a "higher-order" operator?
    # x · encoder → encoder' (where encoder' ≠ encoder, encoder' is encoder)
    higher_order = []
    for x in range(N):
        for e in cats["encoders"]:
            v = table[x][e]
            if v in encoder_set and v != e:
                higher_order.append((x, e, v))

    return {
        "depth2_chains": depth2_chains,
        "encoder_to_encoder": enc_to_enc,
        "has_enc_to_enc": len(enc_to_enc) > 0,
        "higher_order_ops": higher_order,
        "has_higher_order": len(higher_order) > 0,
    }


def default_element(table: list[list[int]]) -> dict:
    """
    Is there a "default" or "garbage" element that appears in most
    unconstrained positions? (Like p=16 in Δ₁)

    Heuristic: find the most common non-{0,1} value across all
    non-absorber, non-tester rows.
    """
    N = len(table)
    cats = classify_elements(table)
    skip_rows = set(cats["absorbers"]) | set(cats["testers"])

    val_counts = Counter()
    total_entries = 0
    for x in range(N):
        if x in skip_rows:
            continue
        for y in range(N):
            v = table[x][y]
            if v not in (0, 1):
                val_counts[v] += 1
            total_entries += 1

    if not val_counts:
        return {"has_default": False, "total_non_bool_entries": 0}

    most_common_val, most_common_count = val_counts.most_common(1)[0]

    # Check if this element's own row is mostly constant
    default_row = table[most_common_val]
    default_row_unique = len(set(default_row))

    return {
        "has_default": most_common_count > total_entries * 0.3,
        "candidate": most_common_val,
        "candidate_frequency": most_common_count,
        "total_non_bool_entries": sum(val_counts.values()),
        "candidate_fraction": most_common_count / sum(val_counts.values()) if val_counts else 0,
        "candidate_row_unique_values": default_row_unique,
        "value_distribution": dict(val_counts.most_common()),
    }


def self_identification(table: list[list[int]]) -> dict:
    """
    Which elements satisfy x·a = x for some specific a?
    (In Δ₁, several elements satisfy x·top = x.)
    """
    N = len(table)
    self_id = {}  # element → list of 'a' values where x·a = x
    for x in range(N):
        anchors = [a for a in range(N) if table[x][a] == x]
        if anchors:
            self_id[x] = anchors

    # Is there a universal anchor? (some 'a' where x·a = x for many x)
    anchor_counts = Counter()
    for anchors in self_id.values():
        for a in anchors:
            anchor_counts[a] += 1

    return {
        "elements_with_self_id": len(self_id),
        "self_id_map": self_id,
        "anchor_counts": dict(anchor_counts.most_common()),
        "best_anchor": anchor_counts.most_common(1)[0] if anchor_counts else None,
    }


def recoverability(table: list[list[int]]) -> dict:
    """
    Can the algebra's own operations distinguish every element?

    Method: start from the absorbers {0, 1}. Iteratively discover new
    elements by applying known elements to each other. Count how many
    rounds until all N elements are known (or we stall).

    This is the key self-description property: can the algebra "find itself"?
    """
    N = len(table)
    known = {0, 1}
    rounds = 0
    history = [frozenset(known)]

    while len(known) < N:
        new = set()
        for x in known:
            for y in known:
                v = table[x][y]
                if v not in known:
                    new.add(v)
        if not new:
            break
        known |= new
        rounds += 1
        history.append(frozenset(known))

    return {
        "recovered": len(known),
        "total": N,
        "full_recovery": len(known) == N,
        "rounds": rounds,
        "history_sizes": [len(s) for s in history],
        "unreachable": sorted(set(range(N)) - known),
    }


def tester_encoder_closure(table: list[list[int]]) -> dict:
    """
    Do the absorbers + testers + encoders form a closed subsystem?
    i.e., for all x, y in {absorbers ∪ testers ∪ encoders}, is x·y also
    in that set?
    """
    N = len(table)
    cats = classify_elements(table)
    core = set(cats["absorbers"]) | set(cats["testers"]) | set(cats["encoders"])

    escapes = []
    for x in core:
        for y in core:
            v = table[x][y]
            if v not in core:
                escapes.append((x, y, v))

    return {
        "core_size": len(core),
        "is_closed": len(escapes) == 0,
        "escapes": escapes[:10],
        "escape_count": len(escapes),
    }


def full_analysis(table: list[list[int]], label: str = "") -> dict:
    """Run all substrate metrics on a table."""
    cats = classify_elements(table)
    return {
        "label": label,
        "N": len(table),
        "classification": {k: len(v) for k, v in cats.items()},
        "tester_separation": tester_separation(table),
        "encoder_reach": encoder_reach(table),
        "compositional_depth": compositional_depth(table),
        "default_element": default_element(table),
        "self_identification": self_identification(table),
        "recoverability": recoverability(table),
        "tester_encoder_closure": tester_encoder_closure(table),
    }


def print_analysis(a: dict):
    """Pretty-print a substrate analysis."""
    print(f"\n  --- {a['label']} (N={a['N']}) ---")
    c = a["classification"]
    print(f"  Classification: abs={c['absorbers']} tst={c['testers']} "
          f"enc={c['encoders']} inert={c['inert']}")

    ts = a["tester_separation"]
    print(f"  Tester separation: {ts['separated']}/{ts['total_pairs']} "
          f"({ts['fraction']:.0%}) {'FULL' if ts['full_separation'] else 'PARTIAL'}")
    if not ts["full_separation"] and ts["unseparated"]:
        print(f"    Unseparated: {ts['unseparated'][:5]}")

    er = a["encoder_reach"]
    print(f"  Encoder reach: {er['testers_reachable_from_encoders']}/{er['total_testers']} "
          f"testers reachable {'(ALL)' if er['all_testers_reachable'] else '(partial)'}")
    for enc, testers in er["encoder_profiles"].items():
        print(f"    Encoder {enc} → testers {sorted(testers)}")

    cd = a["compositional_depth"]
    print(f"  Composition: depth-2 chains={cd['depth2_chains']}, "
          f"enc→enc={cd['has_enc_to_enc']}, higher-order={cd['has_higher_order']}")
    if cd["encoder_to_encoder"]:
        for e, y, e2 in cd["encoder_to_encoder"][:3]:
            print(f"    {e}·{y} = {e2} (encoder→encoder)")
    if cd["higher_order_ops"]:
        for x, e, e2 in cd["higher_order_ops"][:3]:
            print(f"    {x}·{e} = {e2} (higher-order)")

    de = a["default_element"]
    if de.get("has_default"):
        print(f"  Default element: {de['candidate']} "
              f"(fraction={de['candidate_fraction']:.0%}, "
              f"row_unique={de['candidate_row_unique_values']})")
    else:
        print(f"  Default element: none dominant")
    if de.get("value_distribution"):
        print(f"    Value distribution: {de['value_distribution']}")

    si = a["self_identification"]
    print(f"  Self-identification: {si['elements_with_self_id']}/{a['N']} elements")
    if si["best_anchor"]:
        anchor_val, anchor_count = si["best_anchor"]
        print(f"    Best anchor: element {anchor_val} "
              f"(fixes {anchor_count}/{a['N']} elements)")

    rc = a["recoverability"]
    print(f"  Recoverability: {rc['recovered']}/{rc['total']} in {rc['rounds']} rounds "
          f"{'FULL' if rc['full_recovery'] else 'STALLED'}")
    print(f"    Growth: {rc['history_sizes']}")
    if rc["unreachable"]:
        print(f"    Unreachable: {rc['unreachable']}")

    tc = a["tester_encoder_closure"]
    print(f"  Tester-encoder closure: {'CLOSED' if tc['is_closed'] else 'OPEN'} "
          f"(core={tc['core_size']})")
    if not tc["is_closed"]:
        for x, y, v in tc["escapes"][:3]:
            print(f"    {x}·{y} = {v} (escape)")


# ═══════════════════════════════════════════════════════════════════════
# Sample multiple models at each N
# ═══════════════════════════════════════════════════════════════════════

def sample_models(level: int, N: int, count: int = 5, timeout: int = 120) -> list[list[list[int]]]:
    """Sample up to `count` distinct models at given level and N."""
    s, dot = encode_level(level, N, timeout_seconds=timeout)
    tables = []
    while len(tables) < count:
        if s.check() != sat:
            break
        table = extract_table(s.model(), dot, N)
        tables.append(table)
        s.add(Or([dot[i][j] != table[i][j] for i in range(N) for j in range(N)]))
    return tables


# ═══════════════════════════════════════════════════════════════════════
# Main campaign
# ═══════════════════════════════════════════════════════════════════════

def aggregate_stats(analyses: list[dict]) -> dict:
    """Compute aggregate stats from a list of analyses."""
    n = len(analyses)
    if n == 0:
        return {}
    return {
        "n_models": n,
        "full_sep": sum(1 for a in analyses if a["tester_separation"]["full_separation"]),
        "full_rec": sum(1 for a in analyses if a["recoverability"]["full_recovery"]),
        "has_enc2enc": sum(1 for a in analyses
                          if a["compositional_depth"]["has_enc_to_enc"]),
        "has_higher": sum(1 for a in analyses
                         if a["compositional_depth"]["has_higher_order"]),
        "has_default": sum(1 for a in analyses
                          if a["default_element"].get("has_default")),
        "all_testers_reach": sum(1 for a in analyses
                                 if a["encoder_reach"]["all_testers_reachable"]),
        "closed": sum(1 for a in analyses
                      if a["tester_encoder_closure"]["is_closed"]),
        "avg_self_id": sum(a["self_identification"]["elements_with_self_id"]
                           for a in analyses) / n,
        "avg_rounds": sum(a["recoverability"]["rounds"] for a in analyses) / n,
        "avg_testers": sum(a["classification"]["testers"] for a in analyses) / n,
        "avg_encoders": sum(a["classification"]["encoders"] for a in analyses) / n,
    }


def print_comparison_table(summaries: dict[str, dict], d1_analysis: dict):
    """Print the comparison table."""
    print(f"\n\n{'='*70}")
    print("COMPARISON TABLE")
    print(f"{'='*70}")
    print(f"{'Label':<12} {'#mod':>4}  {'FullSep':>7}  {'FullRec':>7}  "
          f"{'Enc→Enc':>7}  {'Higher':>6}  {'Default':>7}  {'AllTstR':>7}  "
          f"{'Closed':>6}  {'AvgSelf':>7}  {'AvgRnd':>6}  "
          f"{'AvgTst':>6}  {'AvgEnc':>6}")
    print("-" * 115)

    for label in sorted(summaries.keys()):
        s = summaries[label]
        n = s["n_models"]
        print(f"{label:<12} {n:>4}  "
              f"{s['full_sep']:>3}/{n:<3}  {s['full_rec']:>3}/{n:<3}  "
              f"{s['has_enc2enc']:>3}/{n:<3}  {s['has_higher']:>2}/{n:<3}  "
              f"{s['has_default']:>3}/{n:<3}  {s['all_testers_reach']:>3}/{n:<3}  "
              f"{s['closed']:>2}/{n:<3}  "
              f"{s['avg_self_id']:>7.1f}  {s['avg_rounds']:>6.1f}  "
              f"{s['avg_testers']:>6.1f}  {s['avg_encoders']:>6.1f}")

    # Δ₁ row
    d1 = d1_analysis
    d1_flags = {
        "sep": "Y" if d1["tester_separation"]["full_separation"] else "N",
        "rec": "Y" if d1["recoverability"]["full_recovery"] else "N",
        "e2e": "Y" if d1["compositional_depth"]["has_enc_to_enc"] else "N",
        "ho": "Y" if d1["compositional_depth"]["has_higher_order"] else "N",
        "def": "Y" if d1["default_element"].get("has_default") else "N",
        "atr": "Y" if d1["encoder_reach"]["all_testers_reachable"] else "N",
        "cl": "Y" if d1["tester_encoder_closure"]["is_closed"] else "N",
    }
    print(f"\n {'Δ₁':<12}    1  {'  '+d1_flags['sep']:>7}  {'  '+d1_flags['rec']:>7}  "
          f"{'  '+d1_flags['e2e']:>7}  {' '+d1_flags['ho']:>6}  "
          f"{'  '+d1_flags['def']:>7}  {'  '+d1_flags['atr']:>7}  "
          f"{' '+d1_flags['cl']:>6}  "
          f"{d1['self_identification']['elements_with_self_id']:>7.1f}  "
          f"{d1['recoverability']['rounds']:>6.1f}  "
          f"{d1['classification']['testers']:>6.1f}  "
          f"{d1['classification']['encoders']:>6.1f}")


def run_level(level: int, level_name: str, n_range: range,
              summaries: dict, sample_count: int = 5, timeout: int = 120):
    """Sample models at a given level across a range of N."""
    for N in n_range:
        print(f"\n{'='*70}")
        print(f"{level_name}, N={N}")
        print(f"{'='*70}")

        t0 = time.time()
        models = sample_models(level, N, count=sample_count, timeout=timeout)
        sample_time = time.time() - t0
        print(f"  Sampled {len(models)} models in {sample_time:.1f}s")

        if not models:
            print("  No models found!")
            continue

        analyses = []
        for i, table in enumerate(models):
            a = full_analysis(table, f"{level_name[:2]}-N{N}-#{i}")
            analyses.append(a)
            print_analysis(a)
            if N <= 8:
                print("\n  Cayley table:")
                print_table(table)

        summaries[f"{level_name[:2]}N{N:02d}"] = aggregate_stats(analyses)


def main():
    print("=" * 70)
    print("SUBSTRATE VIABILITY ANALYSIS — Level 4 vs Level 5 vs Level 6 vs Δ₁")
    print("=" * 70)

    # ── Analyze Δ₁ first as reference ──
    print("\n" + "=" * 70)
    print("REFERENCE: Δ₁ (N=17)")
    print("=" * 70)
    d1_analysis = full_analysis(DELTA1_TABLE, "Δ₁")
    print_analysis(d1_analysis)
    print("\n  Cayley table:")
    print_table(DELTA1_TABLE)

    summaries = {}

    # ── Level 4 (shallow branch) ──
    run_level(4, "L4", range(6, 13), summaries)

    # ── Level 5 (generative synthesis) ──
    run_level(5, "L5", range(5, 13), summaries)

    # ── Level 6 (generative synthesis + open closure) ──
    run_level(6, "L6", range(5, 13), summaries, timeout=300)

    # ── Print comparison ──
    print_comparison_table(summaries, d1_analysis)


if __name__ == "__main__":
    main()

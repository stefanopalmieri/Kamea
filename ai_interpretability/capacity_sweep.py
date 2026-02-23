#!/usr/bin/env python3
"""
Δ₁ Capacity Sweep: How Network Size Affects Semantic Structure Recovery

Sweeps hidden layer size and measures how capacity affects accuracy,
recovery success, representational clustering, and similarity correlation.

Usage:
  uv run capacity_sweep.py
"""

import random
import itertools
import numpy as np
import torch
import torch.nn as nn
import torch.optim as optim
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from sklearn.manifold import TSNE

from dot_learner import (
    ELEMENTS, N, IDX, dot_table, generate_data, to_onehot_pair,
    DotNet, make_nn_blackbox, ROLE_GROUPS, ROLE_COLORS, PLOT_ORDER,
    get_element_role,
)

# ============================================================
# Training (silent version for sweep)
# ============================================================

def train_silent(model, X_train, Y_train, max_epochs=5000, lr=0.001):
    """Train without printing. Returns final accuracy."""
    optimizer = optim.Adam(model.parameters(), lr=lr)
    criterion = nn.CrossEntropyLoss()
    for epoch in range(1, max_epochs + 1):
        logits = model(X_train)
        loss = criterion(logits, Y_train)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
        if epoch % 500 == 0 or epoch == max_epochs:
            preds = logits.argmax(dim=1)
            acc = (preds == Y_train).float().mean().item()
            if acc == 1.0:
                return 1.0
    with torch.no_grad():
        return (model(X_train).argmax(dim=1) == Y_train).float().mean().item()


# ============================================================
# Recovery with step-level failure tracking
# ============================================================

STEP_NAMES = [
    "1: Booleans",
    "2: Testers",
    "2.5: Find p",
    "3: Tester cardinalities",
    "4: e_I vs d_K",
    "5: Encoders",
    "6: i vs k",
    "7: a, b, d_I",
    "8: Triple",
]


def recover_with_tracking(domain, dot):
    """
    Recovery procedure that returns (result_dict_or_None, num_correct, failed_step).
    failed_step is None if all steps succeed, otherwise the step index (0-8).
    """
    def left_image(x):
        return {dot(x, y) for y in domain}

    # Step 0 (index 0): Booleans
    absorbers = [x for x in domain if all(dot(x, y) == x for y in domain)]
    if len(absorbers) != 2:
        return None, 0, 0
    B1, B2 = absorbers

    # Step 1 (index 1): Testers + orient booleans
    def testers_for(top, bot):
        out = []
        for x in domain:
            if x in (top, bot):
                continue
            im = left_image(x)
            if im.issubset({top, bot}) and len(im) == 2:
                out.append(x)
        return out

    chosen = None
    for top, bot in [(B1, B2), (B2, B1)]:
        testers = testers_for(top, bot)
        if len(testers) != 4:
            continue
        Dec = lambda t, top=top: {y for y in domain if dot(t, y) == top}
        sizes = sorted(len(Dec(t)) for t in testers)
        if sizes[0] == 1 and sizes[1] == 2 and sizes[2] == 2:
            chosen = (top, bot, testers, Dec)
            break
    if chosen is None:
        return None, 2, 1
    top, bot, testers, Dec = chosen

    # Step 2 (index 2): Find p
    p_candidates = [
        x for x in domain
        if x not in (top, bot) and x not in testers
        and top in left_image(x)
    ]
    if len(p_candidates) != 1:
        return None, 6, 2
    p_tok = p_candidates[0]

    # Step 3 (index 3): Tester cardinalities
    sizes = {t: len(Dec(t)) for t in testers}
    mk_list = [t for t in testers if sizes[t] == 1]
    if len(mk_list) != 1:
        return None, 7, 3
    m_K = mk_list[0]
    m_I = max(testers, key=lambda t: sizes[t])
    two = [t for t in testers if sizes[t] == 2]
    if len(two) != 2:
        return None, 7, 3

    # Step 4 (index 4): Distinguish e_I from d_K
    def has_productive_args(decoded_set):
        for f in domain:
            if f in (top, bot) or f in testers:
                continue
            for x in decoded_set:
                out = dot(f, x)
                if out not in (top, bot, p_tok):
                    return True
        return False

    t1, t2 = two
    rich1 = has_productive_args(Dec(t1))
    rich2 = has_productive_args(Dec(t2))
    if rich1 == rich2:
        return None, 7, 4
    e_I, d_K = (t1, t2) if rich1 else (t2, t1)
    ctx = list(Dec(e_I))

    # Step 5 (index 5): Find e_D and e_M
    def is_encoder(f):
        if f in (top, bot) or f in testers:
            return False
        outs = [dot(f, x) for x in ctx]
        return all(o not in (top, bot, p_tok) for o in outs)

    enc = [f for f in domain if is_encoder(f)]
    if len(enc) != 2:
        return None, 9, 5

    def maps_both_to_testers(f):
        return all(dot(f, x) in testers for x in ctx)

    e_M = enc[0] if maps_both_to_testers(enc[0]) else enc[1]
    e_D = enc[1] if e_M == enc[0] else enc[0]

    # Step 6 (index 6): Distinguish i from k
    outA, outB = dot(e_M, ctx[0]), dot(e_M, ctx[1])
    decA, decB = len(Dec(outA)), len(Dec(outB))
    if decA == decB:
        return None, 11, 6
    if decA > decB:
        i_tok, k_tok = ctx[0], ctx[1]
    else:
        i_tok, k_tok = ctx[1], ctx[0]

    # Step 7 (index 7): a, b, d_I
    ab = list(Dec(d_K))
    a_list = [x for x in ab if dot(m_K, x) == top]
    if len(a_list) != 1:
        return None, 12, 7
    a_tok = a_list[0]
    b_tok = next(x for x in ab if x != a_tok)
    d_I = dot(e_D, i_tok)

    # Step 8 (index 8): e_Sigma, s_C, e_Delta
    known = {top, bot, e_I, d_K, m_K, m_I, e_M, e_D,
             i_tok, k_tok, a_tok, b_tok, d_I, p_tok}
    remaining = [x for x in domain if x not in known]

    e_S = sC = e_Delta = None
    for f, g in itertools.product(remaining, repeat=2):
        h = dot(f, g)
        if h in (top, bot, p_tok):
            continue
        if dot(h, e_D) == d_I:
            e_S, sC, e_Delta = f, g, h
            break
    if e_S is None:
        return None, 14, 8

    result = {
        "top": top, "bot": bot, "p": p_tok,
        "e_I": e_I, "e_D": e_D, "e_M": e_M,
        "e_Sigma": e_S, "e_Delta": e_Delta,
        "i": i_tok, "k": k_tok, "a": a_tok, "b": b_tok,
        "d_I": d_I, "d_K": d_K, "m_I": m_I, "m_K": m_K, "s_C": sC,
    }
    return result, 17, None


def count_correct(recovered, true_mapping):
    """Count how many elements were correctly identified."""
    if recovered is None:
        return 0
    inv_true = {v: k for k, v in true_mapping.items()}
    correct = 0
    for name in ELEMENTS:
        true_idx = IDX[name]
        expected_opaque = inv_true[true_idx]
        if recovered.get(name) == expected_opaque:
            correct += 1
    return correct


# ============================================================
# Representation metrics
# ============================================================

def extract_activations(model):
    """Hidden activations for each element as left-arg with right=top."""
    top_idx = IDX["top"]
    activations = {}
    model.eval()
    with torch.no_grad():
        for x in range(N):
            inp = to_onehot_pair([x], [top_idx])
            h = model.net[0](inp)
            h = model.net[1](h)
            activations[ELEMENTS[x]] = h.squeeze().numpy()
    return activations


def clustering_ratio(activations):
    within, between = [], []
    for a in ELEMENTS:
        ra = get_element_role(a)
        for b in ELEMENTS:
            if a == b:
                continue
            d = np.linalg.norm(activations[a] - activations[b])
            if ra == get_element_role(b):
                within.append(d)
            else:
                between.append(d)
    if not within or not between:
        return float("nan")
    return np.mean(within) / np.mean(between)


def similarity_correlation(activations, behav_sim_elements):
    """Pearson r between behavioral and representational similarity (upper tri)."""
    vecs = np.array([activations[ELEMENTS[i]] for i in range(N)])
    norms = np.linalg.norm(vecs, axis=1, keepdims=True)
    norms = np.maximum(norms, 1e-8)
    normed = vecs / norms
    repr_sim = normed @ normed.T
    mask = np.triu_indices(N, k=1)
    return np.corrcoef(behav_sim_elements[mask], repr_sim[mask])[0, 1]


# ============================================================
# Sweep
# ============================================================

HIDDEN_SIZES = [4, 5, 6, 8, 10, 12, 16, 24, 32, 48, 64, 96, 128]
NUM_TRIALS = 10


def run_sweep():
    print("=" * 60)
    print("  Δ₁ CAPACITY SWEEP")
    print("=" * 60)

    # Precompute
    X_left, X_right, Y = generate_data()
    X_train = to_onehot_pair(X_left, X_right)
    Y_train = torch.tensor(Y, dtype=torch.long)

    # Behavioral similarity (element-order, for correlation computation)
    behav_sim_elements = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            behav_sim_elements[i, j] = sum(
                1 for z in range(N) if dot_table(i, z) == dot_table(j, z)) / N

    results = {}  # hidden_size -> list of trial dicts

    for H in HIDDEN_SIZES:
        results[H] = []
        for trial in range(NUM_TRIALS):
            seed = H * 100 + trial
            torch.manual_seed(seed)
            random.seed(seed)

            model = DotNet(hidden=H)
            acc = train_silent(model, X_train, Y_train, max_epochs=5000)

            # Recovery
            domain, dot_oracle, true_mapping = make_nn_blackbox(model, seed=seed)
            try:
                recovered, partial_count, failed_step = recover_with_tracking(
                    domain, dot_oracle)
                num_correct = count_correct(recovered, true_mapping) if recovered else partial_count
            except Exception:
                recovered, num_correct, failed_step = None, 0, 0

            # Representation metrics (only if good accuracy)
            cr = float("nan")
            sc = float("nan")
            if acc >= 0.95:
                acts = extract_activations(model)
                cr = clustering_ratio(acts)
                sc = similarity_correlation(acts, behav_sim_elements)

            trial_result = {
                "acc": acc,
                "recovery": num_correct,
                "failed_step": failed_step,
                "clustering": cr,
                "sim_corr": sc,
                "model": model,
                "seed": seed,
            }
            results[H].append(trial_result)

            print(f"  H={H:3d}, trial {trial+1:2d}/{NUM_TRIALS}: "
                  f"acc={acc:.3f}, recovery={num_correct:2d}/17"
                  f"{'' if failed_step is None else f', fail@step {failed_step}'}")

    return results, behav_sim_elements


# ============================================================
# Plotting
# ============================================================

def plot_sweep(results):
    """Four-panel sweep results."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle("Δ₁ Capacity Sweep: Network Size vs Semantic Structure Recovery",
                 fontsize=14, fontweight="bold")

    hs = HIDDEN_SIZES

    def stats(key, min_acc=None):
        means, stds = [], []
        for H in hs:
            vals = []
            for t in results[H]:
                if min_acc is not None and t["acc"] < min_acc:
                    continue
                v = t[key]
                if not np.isnan(v):
                    vals.append(v)
            if len(vals) >= 3:
                means.append(np.mean(vals))
                stds.append(np.std(vals))
            else:
                means.append(np.nan)
                stds.append(np.nan)
        return np.array(means), np.array(stds)

    def plot_band(ax, means, stds, color="tab:blue"):
        valid = ~np.isnan(means)
        x = np.array(hs)[valid]
        m = means[valid]
        s = stds[valid]
        ax.plot(x, m, "o-", color=color, markersize=4)
        ax.fill_between(x, m - s, m + s, alpha=0.2, color=color)

    # Top-left: Accuracy
    ax = axes[0, 0]
    m, s = stats("acc")
    plot_band(ax, m, s)
    ax.axhline(1.0, color="gray", ls="--", lw=0.8)
    ax.set_xscale("log")
    ax.set_xlabel("Hidden size")
    ax.set_ylabel("Accuracy")
    ax.set_title("Accuracy vs Hidden Size")
    ax.set_xticks(hs)
    ax.set_xticklabels(hs, fontsize=7)
    ax.set_ylim(0.5, 1.05)

    # Top-right: Recovery
    ax = axes[0, 1]
    m, s = stats("recovery")
    plot_band(ax, m, s, color="tab:green")
    ax.axhline(17, color="gray", ls="--", lw=0.8)
    ax.set_xscale("log")
    ax.set_xlabel("Hidden size")
    ax.set_ylabel("Elements recovered (of 17)")
    ax.set_title("Recovery Success vs Hidden Size")
    ax.set_xticks(hs)
    ax.set_xticklabels(hs, fontsize=7)
    ax.set_ylim(-0.5, 18)

    # Bottom-left: Clustering ratio
    ax = axes[1, 0]
    m, s = stats("clustering", min_acc=0.95)
    plot_band(ax, m, s, color="tab:orange")
    ax.axhline(1.0, color="gray", ls="--", lw=0.8)
    ax.set_xscale("log")
    ax.set_xlabel("Hidden size")
    ax.set_ylabel("Within / Between role distance")
    ax.set_title("Clustering Ratio vs Hidden Size")
    ax.set_xticks(hs)
    ax.set_xticklabels(hs, fontsize=7)

    # Bottom-right: Similarity correlation
    ax = axes[1, 1]
    m, s = stats("sim_corr", min_acc=0.95)
    plot_band(ax, m, s, color="tab:red")
    ax.set_xscale("log")
    ax.set_xlabel("Hidden size")
    ax.set_ylabel("Pearson r")
    ax.set_title("Behavioral–Representational Similarity Correlation")
    ax.set_xticks(hs)
    ax.set_xticklabels(hs, fontsize=7)

    plt.tight_layout()
    plt.savefig("sweep_results.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved sweep_results.png")


def plot_failure_order(results):
    """Heatmap of recovery step failures by hidden size."""
    n_steps = len(STEP_NAMES)
    mat = np.zeros((len(HIDDEN_SIZES), n_steps))
    for i, H in enumerate(HIDDEN_SIZES):
        for t in results[H]:
            fs = t["failed_step"]
            if fs is not None:
                mat[i, fs] += 1

    fig, ax = plt.subplots(figsize=(12, 5))
    im = ax.imshow(mat.T, cmap="YlOrRd", aspect="auto", vmin=0, vmax=NUM_TRIALS)
    ax.set_xticks(range(len(HIDDEN_SIZES)))
    ax.set_xticklabels(HIDDEN_SIZES)
    ax.set_yticks(range(n_steps))
    ax.set_yticklabels(STEP_NAMES, fontsize=8)
    ax.set_xlabel("Hidden size")
    ax.set_ylabel("Recovery step")
    ax.set_title("Recovery Step Failures by Hidden Size\n(count of trials failing at each step, out of 10)",
                 fontsize=11)
    fig.colorbar(im, ax=ax, label="Failures (of 10 trials)")

    # Annotate cells
    for i in range(len(HIDDEN_SIZES)):
        for j in range(n_steps):
            v = int(mat[i, j])
            if v > 0:
                ax.text(i, j, str(v), ha="center", va="center",
                        fontsize=8, fontweight="bold",
                        color="white" if v > 5 else "black")

    plt.tight_layout()
    plt.savefig("failure_order.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved failure_order.png")


def plot_compression_representations(results):
    """t-SNE at four hidden sizes, best trial each."""
    target_sizes = HIDDEN_SIZES
    ncols = min(7, len(target_sizes))
    nrows = (len(target_sizes) + ncols - 1) // ncols
    fig, axes = plt.subplots(nrows, ncols, figsize=(ncols * 3.2, nrows * 3.5))
    fig.suptitle("Representational Geometry Under Compression", fontsize=13,
                 fontweight="bold")

    axes_flat = np.array(axes).flatten()
    for idx in range(len(target_sizes), len(axes_flat)):
        axes_flat[idx].set_visible(False)
    for ax, H in zip(axes_flat, target_sizes):
        # Pick best trial
        trials = results[H]
        best = max(trials, key=lambda t: t["acc"])
        model = best["model"]
        model.eval()
        acts = extract_activations(model)

        names = PLOT_ORDER
        vecs = np.array([acts[n] for n in names])

        if vecs.shape[1] < 2:
            # Can't do t-SNE with < 2 dimensions
            coords = np.zeros((len(names), 2))
            if vecs.shape[1] == 1:
                coords[:, 0] = vecs[:, 0]
        else:
            perp = min(5, len(names) - 1)
            coords = TSNE(n_components=2, perplexity=perp, random_state=42,
                          max_iter=1000).fit_transform(vecs)

        for idx, name in enumerate(names):
            role = get_element_role(name)
            color = ROLE_COLORS.get(role, "gray")
            ax.scatter(coords[idx, 0], coords[idx, 1], c=color, s=60,
                       edgecolors="black", linewidths=0.4, zorder=3)
            ax.annotate(name, (coords[idx, 0], coords[idx, 1]),
                        fontsize=5, ha="center", va="bottom",
                        xytext=(0, 4), textcoords="offset points")
        ax.set_title(f"H={H}  (acc={best['acc']:.3f})", fontsize=10)
        ax.set_xticks([])
        ax.set_yticks([])

    handles = [Line2D([0], [0], marker="o", color="w", markerfacecolor=c,
                       markersize=7, label=r) for r, c in ROLE_COLORS.items()]
    fig.legend(handles=handles, loc="lower center", ncol=4, fontsize=8,
               frameon=False)
    plt.tight_layout(rect=[0, 0.06, 1, 0.93])
    plt.savefig("compression_representations.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved compression_representations.png")


def write_table(results):
    """Write summary table."""
    lines = []
    header = f"{'Hidden':>6} | {'Accuracy':>14} | {'Recovery (of 17)':>17} | {'Clustering':>16} | {'Sim Corr':>14}"
    sep = "-" * len(header)
    lines.append(header)
    lines.append(sep)

    for H in HIDDEN_SIZES:
        accs = [t["acc"] for t in results[H]]
        recs = [t["recovery"] for t in results[H]]
        cls = [t["clustering"] for t in results[H] if t["acc"] >= 0.95 and not np.isnan(t["clustering"])]
        scs = [t["sim_corr"] for t in results[H] if t["acc"] >= 0.95 and not np.isnan(t["sim_corr"])]

        acc_str = f"{np.mean(accs):.3f} ± {np.std(accs):.3f}"
        rec_str = f"{np.mean(recs):.1f} ± {np.std(recs):.1f}"
        cl_str = f"{np.mean(cls):.3f} ± {np.std(cls):.3f}" if cls else "n/a"
        sc_str = f"{np.mean(scs):.3f} ± {np.std(scs):.3f}" if scs else "n/a"

        lines.append(f"{H:>6} | {acc_str:>14} | {rec_str:>17} | {cl_str:>16} | {sc_str:>14}")

    table = "\n".join(lines)
    with open("sweep_table.txt", "w") as f:
        f.write(table + "\n")
    print("  Saved sweep_table.txt")
    print()
    print(table)


# ============================================================
# Main
# ============================================================

def main():
    results, behav_sim = run_sweep()

    print("\n--- Generating plots ---")
    plot_sweep(results)
    plot_failure_order(results)
    plot_compression_representations(results)
    write_table(results)

    print("\n" + "=" * 60)
    print("  SWEEP COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Discoverability Regularization: Full Sweep

All 4 regimes (baseline, ext_only, role_only, full_ds) at all hidden sizes.
Measures accuracy, recovery, clustering ratio, and similarity correlation.

Usage:
  uv run discoverability_loss.py
"""

import random
import itertools
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from sklearn.manifold import TSNE
import json
import time

from dot_learner import (
    ELEMENTS, N, IDX, dot_table, to_onehot_pair,
    ROLE_GROUPS, ROLE_COLORS, PLOT_ORDER, get_element_role,
)
from capacity_sweep import recover_with_tracking, count_correct


# ============================================================
# Model
# ============================================================

class DSNet(nn.Module):
    def __init__(self, hidden=128):
        super().__init__()
        self.fc1 = nn.Linear(N * 2, hidden)
        self.fc2 = nn.Linear(hidden, hidden)
        self.fc3 = nn.Linear(hidden, N)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        x = torch.relu(self.fc2(x))
        return self.fc3(x)

    def hidden1(self, x):
        return torch.relu(self.fc1(x))


# ============================================================
# Data
# ============================================================

def make_training_data():
    X_left, X_right, Y = [], [], []
    for x in range(N):
        for y in range(N):
            X_left.append(x)
            X_right.append(y)
            Y.append(dot_table(x, y))
    X_train = to_onehot_pair(X_left, X_right)
    Y_train = torch.tensor(Y, dtype=torch.long)
    return X_train, Y_train


def one_hot_pair(x, y):
    v = torch.zeros(1, N * 2)
    v[0, x] = 1.0
    v[0, N + y] = 1.0
    return v


# ============================================================
# Loss functions
# ============================================================

def compute_L_ext(model, X_train, margin=2.0):
    """Behavioral separability: penalize if best-probe distance < margin."""
    all_logits = model(X_train).view(N, N, N)
    loss = torch.tensor(0.0)
    count = 0
    for xi in range(N):
        for yi in range(xi + 1, N):
            diffs = all_logits[xi] - all_logits[yi]
            dists = torch.norm(diffs, dim=1)
            loss = loss + torch.relu(margin - dists.max())
            count += 1
    return loss / count


def compute_L_role(model, X_train):
    """Negative correlation between behavioral and representational similarity."""
    with torch.no_grad():
        all_preds = model(X_train).argmax(dim=1).view(N, N)
        B = torch.zeros(N, N)
        for i in range(N):
            for j in range(N):
                B[i, j] = (all_preds[i] == all_preds[j]).float().mean()

    activations = []
    for xi in range(N):
        inp = one_hot_pair(xi, 0)
        h = model.hidden1(inp)
        activations.append(h.squeeze())
    act_matrix = torch.stack(activations)
    norms = act_matrix.norm(dim=1, keepdim=True).clamp(min=1e-8)
    R = (act_matrix / norms) @ (act_matrix / norms).T

    mask = torch.triu(torch.ones(N, N, dtype=torch.bool), diagonal=1)
    b_vals = B[mask]
    r_vals = R[mask]
    b_c = b_vals - b_vals.mean()
    r_c = r_vals - r_vals.mean()
    corr = (b_c * r_c).sum() / (b_c.norm() * r_c.norm().clamp(min=1e-8))
    return -corr


# ============================================================
# Training
# ============================================================

REGIMES = {
    "baseline":  {"lambda_ext": 0.0, "lambda_role": 0.0},
    "ext_only":  {"lambda_ext": 1.0, "lambda_role": 0.0},
    "role_only": {"lambda_ext": 0.0, "lambda_role": 0.5},
    "full_ds":   {"lambda_ext": 1.0, "lambda_role": 0.5},
}

HIDDEN_SIZES = [4, 5, 6, 8, 10, 12, 16, 24, 32, 48, 64, 96, 128]
NUM_TRIALS = 10


def train_model(hidden, lambda_ext, lambda_role, seed, epochs=3000):
    torch.manual_seed(seed)
    model = DSNet(hidden)
    optimizer = torch.optim.Adam(model.parameters(), lr=0.001)
    X_train, Y_train = make_training_data()

    warmup = 500
    # Compute L_ext every 5 epochs (not every epoch) for speed
    ext_interval = 5
    # Compute L_role every 10 epochs
    role_interval = 10

    for epoch in range(1, epochs + 1):
        logits = model(X_train)
        L_task = F.cross_entropy(logits, Y_train)

        past_warmup = epoch > warmup
        loss = L_task

        if past_warmup and lambda_ext > 0 and epoch % ext_interval == 0:
            L_ext = compute_L_ext(model, X_train)
            loss = loss + lambda_ext * L_ext

        if past_warmup and lambda_role > 0 and epoch % role_interval == 0:
            L_role = compute_L_role(model, X_train)
            loss = loss + lambda_role * L_role

        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

    with torch.no_grad():
        acc = (model(X_train).argmax(dim=1) == Y_train).float().mean().item()
    model.eval()
    return model, acc


# ============================================================
# Evaluation
# ============================================================

def make_nn_blackbox(model, seed=42):
    rng = random.Random(seed)
    perm = list(range(N))
    rng.shuffle(perm)
    inv_perm = [0] * N
    for i, p in enumerate(perm):
        inv_perm[p] = i
    domain = list(range(N))
    true_mapping = {opaque: perm[opaque] for opaque in range(N)}

    @torch.no_grad()
    def dot_oracle(xh, yh):
        true_x = perm[xh]
        true_y = perm[yh]
        inp = to_onehot_pair([true_x], [true_y])
        pred = model(inp).argmax(dim=1).item()
        return inv_perm[pred]

    return domain, dot_oracle, true_mapping


def evaluate_model(model, seed):
    domain, dot_oracle, true_mapping = make_nn_blackbox(model, seed=seed + 5000)
    recovered, n_correct, failed_step = recover_with_tracking(domain, dot_oracle)
    n_correct_verified = count_correct(recovered, true_mapping) if recovered else n_correct

    cr = float("nan")
    sc = float("nan")

    with torch.no_grad():
        acts = {}
        for x in range(N):
            inp = one_hot_pair(x, 0)
            h = model.hidden1(inp).squeeze().numpy()
            acts[ELEMENTS[x]] = h

        within, between = [], []
        for a in ELEMENTS:
            ra = get_element_role(a)
            for b in ELEMENTS:
                if a == b:
                    continue
                d = np.linalg.norm(acts[a] - acts[b])
                if ra == get_element_role(b):
                    within.append(d)
                else:
                    between.append(d)
        if within and between and np.mean(between) > 0:
            cr = np.mean(within) / np.mean(between)

        vecs = np.array([acts[ELEMENTS[i]] for i in range(N)])
        norms = np.linalg.norm(vecs, axis=1, keepdims=True)
        norms = np.maximum(norms, 1e-8)
        normed = vecs / norms
        repr_sim = normed @ normed.T

        behav_sim = np.zeros((N, N))
        for i in range(N):
            for j in range(N):
                behav_sim[i, j] = sum(
                    1 for z in range(N) if dot_table(i, z) == dot_table(j, z)) / N

        mask = np.triu_indices(N, k=1)
        try:
            sc = float(np.corrcoef(behav_sim[mask], repr_sim[mask])[0, 1])
        except Exception:
            sc = float("nan")

    return {
        "recovery": n_correct_verified,
        "failed_step": failed_step,
        "clustering": cr,
        "sim_corr": sc,
    }


# ============================================================
# Full sweep
# ============================================================

def run_full_sweep():
    print("=" * 60)
    print("  DISCOVERABILITY REGULARIZATION: FULL SWEEP")
    print(f"  {len(REGIMES)} regimes x {len(HIDDEN_SIZES)} sizes x {NUM_TRIALS} trials")
    print(f"  = {len(REGIMES) * len(HIDDEN_SIZES) * NUM_TRIALS} total models")
    print("=" * 60)

    results = {}  # regime -> hidden_size -> list of trial dicts
    best_models = {}  # (regime, hidden_size) -> model with best acc

    total = len(REGIMES) * len(HIDDEN_SIZES) * NUM_TRIALS
    done = 0
    t0 = time.time()

    for regime_name, params in REGIMES.items():
        results[regime_name] = {}
        for H in HIDDEN_SIZES:
            results[regime_name][H] = []
            best_acc = 0
            for trial in range(NUM_TRIALS):
                seed = trial
                model, acc = train_model(
                    H, params["lambda_ext"], params["lambda_role"],
                    seed=seed, epochs=3000)
                metrics = evaluate_model(model, seed=seed)
                metrics["acc"] = acc
                results[regime_name][H].append(metrics)

                if acc > best_acc:
                    best_acc = acc
                    best_models[(regime_name, H)] = model

                done += 1
                elapsed = time.time() - t0
                eta = (elapsed / done) * (total - done) if done > 0 else 0
                print(f"  [{done:4d}/{total}] {regime_name:10s} H={H:3d} t={trial+1:2d}: "
                      f"acc={acc:.3f} rec={metrics['recovery']:2d}/17 "
                      f"clust={metrics['clustering']:.3f} corr={metrics['sim_corr']:.3f} "
                      f"[ETA {eta/60:.0f}m]")

    # Save raw results as JSON (for replotting without rerunning)
    serializable = {}
    for regime in results:
        serializable[regime] = {}
        for H in results[regime]:
            serializable[regime][str(H)] = []
            for t in results[regime][H]:
                serializable[regime][str(H)].append({
                    k: (None if isinstance(v, (float, np.floating)) and np.isnan(v)
                        else float(v) if isinstance(v, (np.floating, np.integer)) else v)
                    for k, v in t.items()
                })
    with open("sweep_data.json", "w") as f:
        json.dump(serializable, f, indent=2)
    print("  Saved sweep_data.json")

    return results, best_models


# ============================================================
# Plotting
# ============================================================

REGIME_COLORS = {
    "baseline":  "#7E8CA0",
    "ext_only":  "#4C9AFF",
    "role_only": "#FF8A65",
    "full_ds":   "#66BB6A",
}


def plot_four_panel_sweep(results):
    """4-panel: accuracy, recovery, clustering, sim_corr — all regimes, all sizes."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle("Discoverability Regularization: Full Sweep\n"
                 "4 regimes × 13 hidden sizes × 10 trials",
                 fontsize=13, fontweight="bold")

    metrics = [
        ("acc", "Accuracy", (0.0, 1.05)),
        ("recovery", "Elements Recovered (of 17)", (-0.5, 18)),
        ("clustering", "Clustering Ratio (lower = better)", None),
        ("sim_corr", "Similarity Correlation", None),
    ]

    for ax, (key, title, ylim) in zip(axes.flatten(), metrics):
        for regime in REGIMES:
            means, stds, hs = [], [], []
            for H in HIDDEN_SIZES:
                vals = [t[key] for t in results[regime][H]
                        if not (isinstance(t[key], float) and np.isnan(t[key]))]
                if vals:
                    means.append(np.mean(vals))
                    stds.append(np.std(vals))
                    hs.append(H)
            hs, means, stds = np.array(hs), np.array(means), np.array(stds)
            color = REGIME_COLORS[regime]
            ax.plot(hs, means, "o-", color=color, label=regime, markersize=3, lw=1.5)
            ax.fill_between(hs, means - stds, means + stds, alpha=0.12, color=color)

        ax.set_xscale("log")
        ax.set_xlabel("Hidden size")
        ax.set_title(title, fontsize=10)
        ax.set_xticks(HIDDEN_SIZES)
        ax.set_xticklabels(HIDDEN_SIZES, fontsize=6)
        ax.legend(fontsize=7)
        if ylim:
            ax.set_ylim(ylim)
        if key == "clustering":
            ax.axhline(1.0, color="gray", ls="--", lw=0.5)
        if key == "recovery":
            ax.axhline(17, color="gray", ls="--", lw=0.5)

    plt.tight_layout()
    plt.savefig("regularization_sweep.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved regularization_sweep.png")


def plot_tsne_grid(results, best_models):
    """Grid of t-SNE: rows = regimes, cols = selected hidden sizes."""
    target_sizes = [6, 8, 16, 32, 128]
    regimes = list(REGIMES.keys())

    fig, axes = plt.subplots(len(regimes), len(target_sizes),
                              figsize=(len(target_sizes) * 3.2, len(regimes) * 3.2))
    fig.suptitle("Representational Geometry: Regime × Capacity",
                 fontsize=13, fontweight="bold")

    for ri, regime in enumerate(regimes):
        for ci, H in enumerate(target_sizes):
            ax = axes[ri, ci]
            key = (regime, H)
            if key not in best_models:
                ax.set_visible(False)
                continue

            model = best_models[key]
            model.eval()
            names = PLOT_ORDER
            vecs = []
            with torch.no_grad():
                for name in names:
                    inp = one_hot_pair(IDX[name], 0)
                    h = model.hidden1(inp).squeeze().numpy()
                    vecs.append(h)
            vecs = np.array(vecs)

            if vecs.shape[1] < 2:
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
                ax.scatter(coords[idx, 0], coords[idx, 1], c=color, s=40,
                           edgecolors="black", linewidths=0.3, zorder=3)
                ax.annotate(name, (coords[idx, 0], coords[idx, 1]),
                            fontsize=4, ha="center", va="bottom",
                            xytext=(0, 3), textcoords="offset points")

            best_acc = max(t["acc"] for t in results[regime][H])
            if ri == 0:
                ax.set_title(f"H={H}", fontsize=9)
            if ci == 0:
                ax.set_ylabel(regime, fontsize=9, fontweight="bold")
            ax.set_xticks([])
            ax.set_yticks([])

    handles = [Line2D([0], [0], marker="o", color="w", markerfacecolor=c,
                       markersize=6, label=r) for r, c in ROLE_COLORS.items()]
    fig.legend(handles=handles, loc="lower center", ncol=4, fontsize=7, frameon=False)
    plt.tight_layout(rect=[0, 0.04, 1, 0.95])
    plt.savefig("regularization_tsne_grid.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved regularization_tsne_grid.png")


def plot_ablation_at_size(results, H=16):
    """Bar chart comparing all 4 regimes at a fixed hidden size."""
    regimes = list(REGIMES.keys())
    fig, ax = plt.subplots(figsize=(10, 5))
    fig.suptitle(f"Ablation at H={H}", fontsize=13, fontweight="bold")

    keys = ["clustering", "sim_corr", "recovery"]
    labels = ["Clustering Ratio", "Sim. Correlation", "Recovery / 17"]
    x = np.arange(len(regimes))
    width = 0.25

    for i, (key, label) in enumerate(zip(keys, labels)):
        means, stds_v = [], []
        for r in regimes:
            vals = [t[key] for t in results[r][H]
                    if not (isinstance(t[key], float) and np.isnan(t[key]))]
            if key == "recovery":
                vals = [v / N for v in vals]
            means.append(np.mean(vals) if vals else 0)
            stds_v.append(np.std(vals) if vals else 0)
        ax.bar(x + i * width, means, width, yerr=stds_v,
               label=label, capsize=3, alpha=0.8)

    ax.set_xticks(x + width)
    ax.set_xticklabels(regimes, fontsize=10)
    ax.legend(fontsize=9)
    ax.set_ylabel("Score")
    plt.tight_layout()
    plt.savefig("ablation.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved ablation.png")


def write_table(results):
    lines = []
    header = (f"{'Regime':<12} | {'H':>4} | {'Accuracy':>14} | "
              f"{'Recovery':>14} | {'Clustering':>14} | {'Sim Corr':>14}")
    lines.append(header)
    lines.append("-" * len(header))

    for regime in REGIMES:
        for H in HIDDEN_SIZES:
            trials = results[regime][H]
            accs = [t["acc"] for t in trials]
            recs = [t["recovery"] for t in trials]
            cls = [t["clustering"] for t in trials
                   if not (isinstance(t["clustering"], float) and np.isnan(t["clustering"]))]
            scs = [t["sim_corr"] for t in trials
                   if not (isinstance(t["sim_corr"], float) and np.isnan(t["sim_corr"]))]

            acc_s = f"{np.mean(accs):.3f}±{np.std(accs):.3f}"
            rec_s = f"{np.mean(recs):5.1f}±{np.std(recs):4.1f}"
            cl_s = f"{np.mean(cls):.3f}±{np.std(cls):.3f}" if cls else "n/a"
            sc_s = f"{np.mean(scs):.3f}±{np.std(scs):.3f}" if scs else "n/a"

            lines.append(f"{regime:<12} | {H:>4} | {acc_s:>14} | "
                         f"{rec_s:>14} | {cl_s:>14} | {sc_s:>14}")
        lines.append("")

    table = "\n".join(lines)
    with open("regularization_results.txt", "w") as f:
        f.write(table + "\n")
    print("  Saved regularization_results.txt")
    print()
    print(table)


# ============================================================
# Main
# ============================================================

def main():
    results, best_models = run_full_sweep()

    print("\n--- Generating plots ---")
    plot_four_panel_sweep(results)
    plot_tsne_grid(results, best_models)
    plot_ablation_at_size(results, H=16)
    write_table(results)

    elapsed = time.time()
    print("\n" + "=" * 60)
    print("  FULL SWEEP COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()

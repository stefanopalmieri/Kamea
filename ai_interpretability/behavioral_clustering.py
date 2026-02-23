#!/usr/bin/env python3
"""
Behavioral Clustering: The Simplest Method That Works

Cluster elements by behavioral fingerprints (rows of the operation table)
rather than hidden activations. Same algorithm (K-Means), different input.

Also: probe count sweep — how many random behavioral queries per element
are needed to beat the best representation-based method?

Usage:
  uv run behavioral_clustering.py
"""

import random
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from sklearn.metrics import adjusted_rand_score
from sklearn.cluster import KMeans
import time

from dot_learner import (
    ELEMENTS, N, IDX, dot_table, to_onehot_pair,
    ROLE_GROUPS, PLOT_ORDER, get_element_role,
)
from discoverability_loss import DSNet, one_hot_pair, compute_L_role
from interpretability_benchmark import (
    DELTA1_LABELS, make_control_algebra, verify_control, CONTROL_LABELS,
)


# ============================================================
# Training
# ============================================================

HIDDEN = 128
NUM_TRIALS = 10


def generate_data_from_fn(dot_fn):
    X_left, X_right, Y = [], [], []
    for x in range(N):
        for y in range(N):
            X_left.append(x)
            X_right.append(y)
            Y.append(dot_fn(x, y))
    return to_onehot_pair(X_left, X_right), torch.tensor(Y, dtype=torch.long)


def train_baseline(dot_fn, seed, epochs=3000):
    torch.manual_seed(seed)
    model = DSNet(HIDDEN)
    optimizer = torch.optim.Adam(model.parameters(), lr=0.001)
    X_train, Y_train = generate_data_from_fn(dot_fn)
    for epoch in range(1, epochs + 1):
        loss = F.cross_entropy(model(X_train), Y_train)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
    with torch.no_grad():
        acc = (model(X_train).argmax(dim=1) == Y_train).float().mean().item()
    model.eval()
    return model, acc


def train_role(dot_fn, seed, epochs=3000, lambda_role=0.5, warmup=500):
    torch.manual_seed(seed)
    model = DSNet(HIDDEN)
    optimizer = torch.optim.Adam(model.parameters(), lr=0.001)
    X_train, Y_train = generate_data_from_fn(dot_fn)
    for epoch in range(1, epochs + 1):
        L_task = F.cross_entropy(model(X_train), Y_train)
        loss = L_task
        if epoch > warmup and epoch % 10 == 0:
            loss = loss + lambda_role * compute_L_role(model, X_train)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
    with torch.no_grad():
        acc = (model(X_train).argmax(dim=1) == Y_train).float().mean().item()
    model.eval()
    return model, acc


# ============================================================
# Methods
# ============================================================

def nn_dot(model, x, y):
    """Single forward pass, returns predicted class index."""
    with torch.no_grad():
        inp = one_hot_pair(x, y)
        return model(inp).argmax(dim=1).item()


def behavioral_kmeans(model, n_probes=None, probe_seed=None):
    """
    K-Means on behavioral fingerprints.
    n_probes=None uses all 17 probes. Otherwise uses n_probes random probes.
    """
    if n_probes is None or n_probes >= N:
        probes = list(range(N))
    else:
        rng = random.Random(probe_seed)
        probes = rng.sample(range(N), n_probes)

    fingerprints = []
    for x in range(N):
        fp = [nn_dot(model, x, z) for z in probes]
        fingerprints.append(fp)

    fingerprints = np.array(fingerprints, dtype=float)
    km = KMeans(n_clusters=8, n_init=20, random_state=42)
    return km.fit_predict(fingerprints)


def representational_kmeans(model):
    """K-Means on hidden activations (averaged over all right-args)."""
    reps = []
    with torch.no_grad():
        for x in range(N):
            acts = []
            for y in range(N):
                inp = to_onehot_pair([x], [y])
                h = model.hidden1(inp).squeeze().numpy()
                acts.append(h)
            reps.append(np.mean(acts, axis=0))
    km = KMeans(n_clusters=8, n_init=20, random_state=42)
    return km.fit_predict(np.array(reps))


# ============================================================
# Main experiment
# ============================================================

def main():
    print("=" * 60)
    print("  BEHAVIORAL CLUSTERING BENCHMARK")
    print("=" * 60)

    # Control algebra
    dot_control, control_table = make_control_algebra(seed=42)
    ok, _ = verify_control(dot_control, control_table)
    if not ok:
        for s in range(43, 100):
            dot_control, control_table = make_control_algebra(seed=s)
            ok, _ = verify_control(dot_control, control_table)
            if ok:
                break
    assert ok

    # ============================================================
    # Part 1: Behavioral vs Representational K-Means
    # ============================================================
    print("\n--- Part 1: Behavioral vs Representational K-Means ---")

    methods = ["Behav KM (17 probes)", "Repr KM (activations)"]
    results = {}
    for regime in ["baseline", "role_only"]:
        results[regime] = {}
        for algebra in ["delta1", "control"]:
            results[regime][algebra] = {m: [] for m in methods}

    t0 = time.time()
    total = 2 * 2 * NUM_TRIALS
    done = 0

    for regime, train_fn in [("baseline", train_baseline), ("role_only", train_role)]:
        for algebra_name, dot_fn, true_labels in [
            ("delta1", dot_table, DELTA1_LABELS),
            ("control", dot_control, CONTROL_LABELS),
        ]:
            for trial in range(NUM_TRIALS):
                model, acc = train_fn(dot_fn, seed=trial)

                bk = behavioral_kmeans(model, n_probes=None)
                bk_ari = adjusted_rand_score(true_labels, bk)
                results[regime][algebra_name]["Behav KM (17 probes)"].append(bk_ari)

                rk = representational_kmeans(model)
                rk_ari = adjusted_rand_score(true_labels, rk)
                results[regime][algebra_name]["Repr KM (activations)"].append(rk_ari)

                done += 1
                eta = ((time.time() - t0) / done) * (total - done)
                print(f"  [{done:2d}/{total}] {regime:10s} {algebra_name:8s} t={trial+1:2d}: "
                      f"Behav={bk_ari:.3f} Repr={rk_ari:.3f} [ETA {eta/60:.1f}m]")

    # ============================================================
    # Part 2: Probe count sweep (Δ₁ baseline only, 10 trials)
    # ============================================================
    print("\n--- Part 2: Probe count sweep ---")

    probe_counts = [1, 2, 3, 4, 5, 6, 8, 10, 13, 17]
    n_probe_seeds = 20  # average over random probe selections
    sweep_results = {k: [] for k in probe_counts}

    # Train 10 baseline models
    baseline_models = []
    for trial in range(NUM_TRIALS):
        model, acc = train_baseline(dot_table, seed=trial)
        baseline_models.append(model)

    for n_probes in probe_counts:
        trial_aris = []
        for trial, model in enumerate(baseline_models):
            seed_aris = []
            for ps in range(n_probe_seeds):
                bk = behavioral_kmeans(model, n_probes=n_probes, probe_seed=ps * 100 + trial)
                seed_aris.append(adjusted_rand_score(DELTA1_LABELS, bk))
            trial_aris.append(np.mean(seed_aris))
        sweep_results[n_probes] = trial_aris
        print(f"  n_probes={n_probes:2d}: ARI={np.mean(trial_aris):.3f} ± {np.std(trial_aris):.3f}")

    # Best representational baseline for comparison
    repr_baseline_mean = np.mean(results["baseline"]["delta1"]["Repr KM (activations)"])

    # ============================================================
    # Plot 1: Behavioral vs Representational comparison
    # ============================================================
    fig, axes = plt.subplots(1, 2, figsize=(14, 5.5))
    fig.suptitle("Behavioral vs Representational K-Means",
                 fontsize=13, fontweight="bold")

    for ax, algebra, title in [(axes[0], "delta1", "Δ₁"), (axes[1], "control", "Control")]:
        x = np.arange(len(methods))
        width = 0.35

        for i, (regime, color) in enumerate([("baseline", "#7E8CA0"), ("role_only", "#66BB6A")]):
            means = [np.mean(results[regime][algebra][m]) for m in methods]
            stds = [np.std(results[regime][algebra][m]) for m in methods]
            bars = ax.bar(x + i * width - width/2, means, width, yerr=stds,
                          label=regime, color=color, capsize=4)
            for bar, m in zip(bars, means):
                ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.02,
                        f"{m:.2f}", ha="center", va="bottom", fontsize=8)

        ax.set_ylabel("Adjusted Rand Index", fontsize=10)
        ax.set_title(title, fontsize=12)
        ax.set_xticks(x)
        ax.set_xticklabels(methods, fontsize=9)
        ax.legend(fontsize=9)
        ax.axhline(0, color="gray", lw=0.5, ls="--")
        ax.set_ylim(-0.2, 1.15)

    plt.tight_layout()
    plt.savefig("behavioral_clustering.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved behavioral_clustering.png")

    # ============================================================
    # Plot 2: Probe count sweep
    # ============================================================
    fig, ax = plt.subplots(figsize=(10, 5.5))
    fig.suptitle("Behavioral Clustering: How Many Probes Do You Need?",
                 fontsize=13, fontweight="bold")

    means = [np.mean(sweep_results[k]) for k in probe_counts]
    stds = [np.std(sweep_results[k]) for k in probe_counts]
    ax.errorbar(probe_counts, means, yerr=stds, fmt="o-", color="#4C9AFF",
                capsize=4, markersize=6, lw=2, label="Behavioral K-Means")
    ax.fill_between(probe_counts,
                    [m - s for m, s in zip(means, stds)],
                    [m + s for m, s in zip(means, stds)],
                    alpha=0.15, color="#4C9AFF")

    # Reference line: best representational method
    ax.axhline(repr_baseline_mean, color="#FF6B6B", ls="--", lw=1.5,
               label=f"Repr K-Means (128 dims) = {repr_baseline_mean:.2f}")

    ax.set_xlabel("Number of behavioral probes per element", fontsize=11)
    ax.set_ylabel("Adjusted Rand Index", fontsize=11)
    ax.set_xticks(probe_counts)
    ax.legend(fontsize=10)
    ax.set_ylim(-0.1, 1.05)

    # Annotate the crossover
    for i, k in enumerate(probe_counts):
        if means[i] > repr_baseline_mean:
            ax.annotate(f"{k} probes beats\n128-dim activations",
                        xy=(k, means[i]), xytext=(k + 2, means[i] - 0.15),
                        fontsize=9, ha="left",
                        arrowprops=dict(arrowstyle="->", color="gray"))
            break

    plt.tight_layout()
    plt.savefig("probe_count_sweep.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved probe_count_sweep.png")

    # ============================================================
    # Table
    # ============================================================
    lines = []
    lines.append("=== Part 1: Behavioral vs Representational K-Means ===")
    lines.append("")
    header = f"{'Regime':<12} | {'Algebra':<8} | {'Behav KM':>12} | {'Repr KM':>12}"
    lines.append(header)
    lines.append("-" * len(header))
    for regime in ["baseline", "role_only"]:
        for algebra in ["delta1", "control"]:
            bk = results[regime][algebra]["Behav KM (17 probes)"]
            rk = results[regime][algebra]["Repr KM (activations)"]
            lines.append(f"{regime:<12} | {algebra:<8} | "
                         f"{np.mean(bk):6.3f}±{np.std(bk):.3f} | "
                         f"{np.mean(rk):6.3f}±{np.std(rk):.3f}")
    lines.append("")
    lines.append("=== Part 2: Probe Count Sweep (Δ₁ baseline) ===")
    lines.append("")
    lines.append(f"{'Probes':>6} | {'ARI':>14} | {'Queries':>8}")
    lines.append("-" * 35)
    for k in probe_counts:
        v = sweep_results[k]
        lines.append(f"{k:>6} | {np.mean(v):6.3f}±{np.std(v):.3f} | {k * N:>8}")
    lines.append("")
    lines.append(f"Repr K-Means baseline: ARI = {repr_baseline_mean:.3f} (uses 128-dim activations)")

    table = "\n".join(lines)
    with open("behavioral_clustering_table.txt", "w") as f:
        f.write(table + "\n")
    print("  Saved behavioral_clustering_table.txt")
    print()
    print(table)

    print("\n" + "=" * 60)
    print("  BENCHMARK COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Benchmark Rerun: Standard Interpretability Methods on L_role-Regularized Networks

Compares interpretability method performance on baseline-trained vs
L_role-regularized networks, on both Δ₁ and control algebra.

Usage:
  uv run regularized_benchmark.py
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
from sklearn.metrics import adjusted_rand_score
from sklearn.cluster import KMeans, SpectralClustering
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler
from collections import Counter
import time

from dot_learner import (
    ELEMENTS, N, IDX, dot_table, to_onehot_pair,
    ROLE_GROUPS, PLOT_ORDER, get_element_role,
)
from discoverability_loss import DSNet, one_hot_pair, compute_L_role
from interpretability_benchmark import (
    DELTA1_ROLES, CONTROL_ROLES, DELTA1_LABELS, CONTROL_LABELS,
    make_control_algebra, verify_control,
    ds_recovery, kmeans_method, linear_probe, activation_patching,
)


# ============================================================
# Training
# ============================================================

NUM_TRIALS = 10
HIDDEN = 128


def generate_data_from_fn(dot_fn):
    X_left, X_right, Y = [], [], []
    for x in range(N):
        for y in range(N):
            X_left.append(x)
            X_right.append(y)
            Y.append(dot_fn(x, y))
    X_train = to_onehot_pair(X_left, X_right)
    Y_train = torch.tensor(Y, dtype=torch.long)
    return X_train, Y_train


def train_baseline(dot_fn, seed, epochs=3000):
    torch.manual_seed(seed)
    model = DSNet(HIDDEN)
    optimizer = torch.optim.Adam(model.parameters(), lr=0.001)
    X_train, Y_train = generate_data_from_fn(dot_fn)

    for epoch in range(1, epochs + 1):
        logits = model(X_train)
        loss = F.cross_entropy(logits, Y_train)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

    with torch.no_grad():
        acc = (model(X_train).argmax(dim=1) == Y_train).float().mean().item()
    model.eval()
    return model, acc


def train_role_regularized(dot_fn, seed, epochs=3000, lambda_role=0.5, warmup=500):
    torch.manual_seed(seed)
    model = DSNet(HIDDEN)
    optimizer = torch.optim.Adam(model.parameters(), lr=0.001)
    X_train, Y_train = generate_data_from_fn(dot_fn)

    for epoch in range(1, epochs + 1):
        logits = model(X_train)
        L_task = F.cross_entropy(logits, Y_train)
        loss = L_task

        if epoch > warmup and epoch % 10 == 0:
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
# Compatibility: make DSNet work with interpretability_benchmark methods
# ============================================================

# The benchmark methods access model.net[0], model.net[1], etc.
# DSNet uses fc1/fc2/fc3. We need to add a .net property that works
# with the Sequential-style indexing used in activation_patching.

def patch_model_for_benchmark(model):
    """Add a .net attribute that mimics Sequential indexing."""
    model.net = nn.Sequential(
        model.fc1, nn.ReLU(), model.fc2, nn.ReLU(), model.fc3
    )
    return model


# ============================================================
# Run benchmark
# ============================================================

def run_all_methods(model, true_labels, seed):
    """Run all 4 interpretability methods on a trained model."""
    model = patch_model_for_benchmark(model)

    # DS Recovery
    pred_labels, n_correct, n_steps = ds_recovery(model, seed=seed + 1000)
    ds_ari = adjusted_rand_score(true_labels, pred_labels) if n_correct > 0 else 0.0

    # K-Means
    km_pred = kmeans_method(model)
    km_ari = adjusted_rand_score(true_labels, km_pred)

    # Linear Probe
    lp_pred = linear_probe(model, true_labels)
    lp_ari = adjusted_rand_score(true_labels, lp_pred)

    # Activation Patching
    ap_pred, causal_sim = activation_patching(model)
    ap_ari = adjusted_rand_score(true_labels, ap_pred)

    return {
        "DS Recovery": ds_ari,
        "K-Means": km_ari,
        "Linear Probe": lp_ari,
        "Activation Patching": ap_ari,
        "km_pred": km_pred,
    }


def main():
    print("=" * 60)
    print("  REGULARIZED BENCHMARK")
    print("  Standard methods on baseline vs L_role networks")
    print("=" * 60)

    # Setup control algebra
    dot_control, control_table = make_control_algebra(seed=42)
    ok, msg = verify_control(dot_control, control_table)
    if not ok:
        for s in range(43, 100):
            dot_control, control_table = make_control_algebra(seed=s)
            ok, msg = verify_control(dot_control, control_table)
            if ok:
                break
    assert ok

    # Results: training_regime -> algebra -> method -> list of ARI values
    results = {
        "baseline": {"delta1": {m: [] for m in ["DS Recovery", "K-Means", "Linear Probe", "Activation Patching"]},
                     "control": {m: [] for m in ["DS Recovery", "K-Means", "Linear Probe", "Activation Patching"]}},
        "role_only": {"delta1": {m: [] for m in ["DS Recovery", "K-Means", "Linear Probe", "Activation Patching"]},
                      "control": {m: [] for m in ["DS Recovery", "K-Means", "Linear Probe", "Activation Patching"]}},
    }

    best_km_baseline = None
    best_km_role = None

    t0 = time.time()
    total = 2 * 2 * NUM_TRIALS  # 2 regimes x 2 algebras x 10 trials
    done = 0

    for regime, train_fn in [("baseline", train_baseline), ("role_only", train_role_regularized)]:
        for algebra_name, dot_fn, true_labels in [
            ("delta1", dot_table, DELTA1_LABELS),
            ("control", dot_control, CONTROL_LABELS),
        ]:
            for trial in range(NUM_TRIALS):
                seed = trial
                model, acc = train_fn(dot_fn, seed=seed)

                metrics = run_all_methods(model, true_labels, seed=seed)

                for m in ["DS Recovery", "K-Means", "Linear Probe", "Activation Patching"]:
                    results[regime][algebra_name][m].append(metrics[m])

                # Save best K-Means predictions for confusion matrices
                if algebra_name == "delta1" and trial == 0:
                    if regime == "baseline":
                        best_km_baseline = metrics["km_pred"]
                    else:
                        best_km_role = metrics["km_pred"]

                done += 1
                elapsed = time.time() - t0
                eta = (elapsed / done) * (total - done) if done > 0 else 0
                print(f"  [{done:2d}/{total}] {regime:10s} {algebra_name:8s} t={trial+1:2d}: "
                      f"acc={acc:.3f} DS={metrics['DS Recovery']:.3f} "
                      f"KM={metrics['K-Means']:.3f} LP={metrics['Linear Probe']:.3f} "
                      f"AP={metrics['Activation Patching']:.3f} [ETA {eta/60:.1f}m]")

    # ============================================================
    # Plot 1: Side-by-side bar chart
    # ============================================================
    methods = ["DS Recovery", "K-Means", "Linear Probe", "Activation Patching"]
    fig, axes = plt.subplots(1, 2, figsize=(16, 6))
    fig.suptitle("Interpretability Methods: Baseline vs L_role-Regularized Training",
                 fontsize=13, fontweight="bold")

    for ax, algebra, true_labels_name in [
        (axes[0], "delta1", "Δ₁"),
        (axes[1], "control", "Control"),
    ]:
        x = np.arange(len(methods))
        width = 0.35

        baseline_means = [np.mean(results["baseline"][algebra][m]) for m in methods]
        baseline_stds = [np.std(results["baseline"][algebra][m]) for m in methods]
        role_means = [np.mean(results["role_only"][algebra][m]) for m in methods]
        role_stds = [np.std(results["role_only"][algebra][m]) for m in methods]

        bars1 = ax.bar(x - width/2, baseline_means, width, yerr=baseline_stds,
                       label="Baseline", color="#7E8CA0", capsize=4)
        bars2 = ax.bar(x + width/2, role_means, width, yerr=role_stds,
                       label="L_role", color="#66BB6A", capsize=4)

        ax.set_ylabel("Adjusted Rand Index", fontsize=10)
        ax.set_title(f"{true_labels_name}", fontsize=12)
        ax.set_xticks(x)
        ax.set_xticklabels(methods, fontsize=8, rotation=15, ha="right")
        ax.legend(fontsize=9)
        ax.axhline(0, color="gray", lw=0.5, ls="--")
        ax.set_ylim(-0.2, 1.15)

        for bars, means in [(bars1, baseline_means), (bars2, role_means)]:
            for bar, m in zip(bars, means):
                ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.03,
                        f"{m:.2f}", ha="center", va="bottom", fontsize=7)

    plt.tight_layout()
    plt.savefig("regularized_benchmark.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved regularized_benchmark.png")

    # ============================================================
    # Plot 2: K-Means confusion matrices side by side
    # ============================================================
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    fig.suptitle("K-Means Confusion: Baseline vs L_role (Δ₁, H=128)",
                 fontsize=13, fontweight="bold")
    role_names = list(DELTA1_ROLES.keys())
    n_roles = len(role_names)
    n_clusters = 8

    for ax, km_pred, title in [
        (ax1, best_km_baseline, "Baseline Training"),
        (ax2, best_km_role, "L_role Training"),
    ]:
        if km_pred is None:
            ax.set_visible(False)
            continue
        conf = np.zeros((n_roles, n_clusters))
        for elem in range(N):
            true_role = DELTA1_LABELS[elem]
            cluster = km_pred[elem]
            conf[true_role, cluster] += 1
        im = ax.imshow(conf, cmap="Blues", aspect="auto")
        ax.set_xticks(range(n_clusters))
        ax.set_xticklabels([f"C{i}" for i in range(n_clusters)], fontsize=8)
        ax.set_yticks(range(n_roles))
        ax.set_yticklabels(role_names, fontsize=8)
        ax.set_xlabel("K-Means Cluster")
        ax.set_ylabel("True Role")
        ax.set_title(title, fontsize=10)
        for i in range(n_roles):
            for j in range(n_clusters):
                v = int(conf[i, j])
                if v > 0:
                    ax.text(j, i, str(v), ha="center", va="center", fontsize=10,
                            color="white" if v > 1 else "black")
        fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)

    plt.tight_layout()
    plt.savefig("regularized_benchmark_detail.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved regularized_benchmark_detail.png")

    # ============================================================
    # Table
    # ============================================================
    lines = []
    header = (f"{'Regime':<12} | {'Algebra':<8} | {'DS Recovery':>14} | "
              f"{'K-Means':>14} | {'Linear Probe':>14} | {'Act. Patching':>14}")
    lines.append(header)
    lines.append("-" * len(header))

    for regime in ["baseline", "role_only"]:
        for algebra in ["delta1", "control"]:
            parts = [f"{regime:<12}", f"{algebra:<8}"]
            for m in methods:
                vals = results[regime][algebra][m]
                parts.append(f"{np.mean(vals):.3f}±{np.std(vals):.3f}")
            lines.append(" | ".join(parts))
        lines.append("")

    table = "\n".join(lines)
    with open("regularized_benchmark_table.txt", "w") as f:
        f.write(table + "\n")
    print("  Saved regularized_benchmark_table.txt")
    print()
    print(table)

    # Summary
    print("\n--- Key comparisons (Δ₁) ---")
    for m in methods:
        b = np.mean(results["baseline"]["delta1"][m])
        r = np.mean(results["role_only"]["delta1"][m])
        delta = r - b
        print(f"  {m:<22}: baseline={b:.3f}  role={r:.3f}  Δ={delta:+.3f}")

    print("\n" + "=" * 60)
    print("  BENCHMARK COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Similarity-Aware Benchmark: Methods That Read Relational Geometry

Three methods designed to operate on similarity structure rather than
raw activation positions, tested on baseline vs L_role networks.

Usage:
  uv run similarity_benchmark.py
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
from sklearn.linear_model import Ridge, LogisticRegression
from sklearn.preprocessing import StandardScaler
import time

from dot_learner import (
    ELEMENTS, N, IDX, dot_table, to_onehot_pair,
    ROLE_GROUPS, PLOT_ORDER, get_element_role,
)
from discoverability_loss import DSNet, one_hot_pair, compute_L_role
from interpretability_benchmark import (
    DELTA1_ROLES, CONTROL_ROLES, DELTA1_LABELS, CONTROL_LABELS,
    make_control_algebra, verify_control, ds_recovery,
)


# ============================================================
# Training (reused from regularized_benchmark)
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
# Representation extraction
# ============================================================

def get_activations(model):
    """17 x H activation matrix (left-arg with right=top)."""
    acts = []
    with torch.no_grad():
        for x in range(N):
            h = model.hidden1(one_hot_pair(x, 0)).squeeze().numpy()
            acts.append(h)
    return np.array(acts)


def get_cosine_sim(acts):
    """17 x 17 cosine similarity matrix."""
    norms = np.linalg.norm(acts, axis=1, keepdims=True)
    norms = np.maximum(norms, 1e-8)
    normed = acts / norms
    return normed @ normed.T


def get_behavioral_table(dot_fn):
    """17 x 17 output table: table[x][y] = dot(x, y)."""
    return [[dot_fn(x, y) for y in range(N)] for x in range(N)]


# ============================================================
# Method 1: Spectral Clustering on representational similarity
# ============================================================

def spectral_on_repr_sim(model):
    acts = get_activations(model)
    R = get_cosine_sim(acts)
    # Ensure non-negative for spectral clustering
    R_nn = np.maximum(R, 0)
    np.fill_diagonal(R_nn, 1.0)
    try:
        sc = SpectralClustering(n_clusters=8, affinity="precomputed",
                                random_state=42, n_init=20)
        return sc.fit_predict(R_nn)
    except Exception:
        return np.zeros(N, dtype=int)


# ============================================================
# Method 2: Behavioral feature probes
# ============================================================

def compute_behavioral_features(dot_fn):
    """Compute behavioral features for each element."""
    features = {}
    table = get_behavioral_table(dot_fn)

    for x in range(N):
        row = table[x]
        # Left-image cardinality
        left_card = len(set(row))
        # Absorber: same output for all y?
        absorber = 1.0 if left_card == 1 else 0.0
        # Boolean-valued: outputs only in {top_idx, bot_idx}?
        # We don't know which are top/bot a priori, but we can check
        # if all outputs are from the same 2 elements
        bool_valued = 1.0 if left_card <= 2 and not absorber else 0.0
        # Default fraction: fraction of outputs that equal the most common output
        from collections import Counter
        counts = Counter(row)
        most_common_count = counts.most_common(1)[0][1]
        default_frac = most_common_count / N

        features[x] = {
            "left_card": left_card / N,  # normalize to 0-1
            "absorber": absorber,
            "bool_valued": bool_valued,
            "default_frac": default_frac,
        }
    return features


def behavioral_feature_probes(model, dot_fn):
    """
    Train linear probes to predict behavioral features from hidden activations.
    Returns dict of feature_name -> R² score.
    """
    acts = get_activations(model)  # (17, H)
    features = compute_behavioral_features(dot_fn)

    feature_names = ["left_card", "absorber", "bool_valued", "default_frac"]
    results = {}

    for fname in feature_names:
        y = np.array([features[x][fname] for x in range(N)])

        # Leave-one-out cross-validation
        predictions = np.zeros(N)
        for hold_out in range(N):
            train_mask = np.ones(N, dtype=bool)
            train_mask[hold_out] = False

            scaler = StandardScaler()
            X_tr = scaler.fit_transform(acts[train_mask])
            X_te = scaler.transform(acts[hold_out:hold_out+1])

            reg = Ridge(alpha=100.0)
            reg.fit(X_tr, y[train_mask])
            predictions[hold_out] = reg.predict(X_te)[0]

        # R² score
        ss_res = np.sum((y - predictions) ** 2)
        ss_tot = np.sum((y - y.mean()) ** 2)
        r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0.0
        results[fname] = max(r2, -1.0)  # clip for display

    return results


# ============================================================
# Method 3: Similarity profile K-Means
# ============================================================

def similarity_profile_kmeans(model):
    """K-Means on rows of the cosine similarity matrix."""
    acts = get_activations(model)
    R = get_cosine_sim(acts)
    km = KMeans(n_clusters=8, n_init=20, random_state=42)
    return km.fit_predict(R)


# ============================================================
# Run benchmark
# ============================================================

def main():
    print("=" * 60)
    print("  SIMILARITY-AWARE BENCHMARK")
    print("  Methods that read relational geometry")
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

    methods = ["DS Recovery", "Spectral", "Sim-Profile KM", "Behav Probes (mean R²)"]
    results = {}
    for regime in ["baseline", "role_only"]:
        results[regime] = {}
        for algebra in ["delta1", "control"]:
            results[regime][algebra] = {m: [] for m in methods}

    # Also collect behavioral probe details
    probe_details = {regime: {algebra: [] for algebra in ["delta1", "control"]}
                     for regime in ["baseline", "role_only"]}

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

                # Patch model for DS recovery compatibility
                model.net = nn.Sequential(
                    model.fc1, nn.ReLU(), model.fc2, nn.ReLU(), model.fc3)

                # DS Recovery
                pred, n_correct, _ = ds_recovery(model, seed=trial + 1000)
                ds_ari = adjusted_rand_score(true_labels, pred) if n_correct > 0 else 0.0
                results[regime][algebra_name]["DS Recovery"].append(ds_ari)

                # Spectral clustering on repr similarity
                sp_pred = spectral_on_repr_sim(model)
                sp_ari = adjusted_rand_score(true_labels, sp_pred)
                results[regime][algebra_name]["Spectral"].append(sp_ari)

                # Similarity profile K-Means
                spkm_pred = similarity_profile_kmeans(model)
                spkm_ari = adjusted_rand_score(true_labels, spkm_pred)
                results[regime][algebra_name]["Sim-Profile KM"].append(spkm_ari)

                # Behavioral feature probes
                bf_results = behavioral_feature_probes(model, dot_fn)
                mean_r2 = np.mean(list(bf_results.values()))
                results[regime][algebra_name]["Behav Probes (mean R²)"].append(mean_r2)
                probe_details[regime][algebra_name].append(bf_results)

                done += 1
                elapsed = time.time() - t0
                eta = (elapsed / done) * (total - done) if done > 0 else 0
                print(f"  [{done:2d}/{total}] {regime:10s} {algebra_name:8s} t={trial+1:2d}: "
                      f"DS={ds_ari:.3f} Spec={sp_ari:.3f} "
                      f"SimKM={spkm_ari:.3f} Probes={mean_r2:.3f} "
                      f"[ETA {eta/60:.1f}m]")

    # ============================================================
    # Plot 1: Main comparison bar chart
    # ============================================================
    fig, axes = plt.subplots(1, 2, figsize=(16, 6))
    fig.suptitle("Similarity-Aware Methods: Baseline vs L_role",
                 fontsize=13, fontweight="bold")

    for ax, algebra, title in [(axes[0], "delta1", "Δ₁"), (axes[1], "control", "Control")]:
        x = np.arange(len(methods))
        width = 0.35

        b_means = [np.mean(results["baseline"][algebra][m]) for m in methods]
        b_stds = [np.std(results["baseline"][algebra][m]) for m in methods]
        r_means = [np.mean(results["role_only"][algebra][m]) for m in methods]
        r_stds = [np.std(results["role_only"][algebra][m]) for m in methods]

        bars1 = ax.bar(x - width/2, b_means, width, yerr=b_stds,
                       label="Baseline", color="#7E8CA0", capsize=4)
        bars2 = ax.bar(x + width/2, r_means, width, yerr=r_stds,
                       label="L_role", color="#66BB6A", capsize=4)

        ax.set_ylabel("ARI / R²", fontsize=10)
        ax.set_title(title, fontsize=12)
        ax.set_xticks(x)
        ax.set_xticklabels(methods, fontsize=7, rotation=15, ha="right")
        ax.legend(fontsize=9)
        ax.axhline(0, color="gray", lw=0.5, ls="--")
        ax.set_ylim(-0.5, 1.15)

        for bars, means in [(bars1, b_means), (bars2, r_means)]:
            for bar, m in zip(bars, means):
                ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.03,
                        f"{m:.2f}", ha="center", va="bottom", fontsize=7)

    plt.tight_layout()
    plt.savefig("similarity_benchmark.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved similarity_benchmark.png")

    # ============================================================
    # Plot 2: Behavioral probe detail
    # ============================================================
    feature_names = ["left_card", "absorber", "bool_valued", "default_frac"]
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    fig.suptitle("Behavioral Feature Probes: R² by Feature",
                 fontsize=13, fontweight="bold")

    for ax, algebra, title in [(axes[0], "delta1", "Δ₁"), (axes[1], "control", "Control")]:
        x = np.arange(len(feature_names))
        width = 0.35

        b_means, b_stds, r_means, r_stds = [], [], [], []
        for fname in feature_names:
            bv = [d[fname] for d in probe_details["baseline"][algebra]]
            rv = [d[fname] for d in probe_details["role_only"][algebra]]
            b_means.append(np.mean(bv))
            b_stds.append(np.std(bv))
            r_means.append(np.mean(rv))
            r_stds.append(np.std(rv))

        ax.bar(x - width/2, b_means, width, yerr=b_stds,
               label="Baseline", color="#7E8CA0", capsize=4)
        ax.bar(x + width/2, r_means, width, yerr=r_stds,
               label="L_role", color="#66BB6A", capsize=4)

        ax.set_ylabel("R²", fontsize=10)
        ax.set_title(title, fontsize=11)
        ax.set_xticks(x)
        ax.set_xticklabels(feature_names, fontsize=9)
        ax.legend(fontsize=9)
        ax.axhline(0, color="gray", lw=0.5, ls="--")
        ax.set_ylim(-0.5, 1.1)

    plt.tight_layout()
    plt.savefig("similarity_benchmark_probes.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved similarity_benchmark_probes.png")

    # ============================================================
    # Table
    # ============================================================
    lines = []
    header = (f"{'Regime':<12} | {'Algebra':<8} | {'DS Recovery':>12} | "
              f"{'Spectral':>12} | {'SimKM':>12} | {'Probes R²':>12}")
    lines.append(header)
    lines.append("-" * len(header))

    for regime in ["baseline", "role_only"]:
        for algebra in ["delta1", "control"]:
            parts = [f"{regime:<12}", f"{algebra:<8}"]
            for m in methods:
                vals = results[regime][algebra][m]
                parts.append(f"{np.mean(vals):6.3f}±{np.std(vals):.3f}")
            lines.append(" | ".join(parts))
        lines.append("")

    table = "\n".join(lines)
    with open("similarity_benchmark_table.txt", "w") as f:
        f.write(table + "\n")
    print("  Saved similarity_benchmark_table.txt")
    print()
    print(table)

    # Summary
    print("\n--- Key comparisons (Δ₁) ---")
    for m in methods:
        b = np.mean(results["baseline"]["delta1"][m])
        r = np.mean(results["role_only"]["delta1"][m])
        print(f"  {m:<24}: baseline={b:.3f}  role={r:.3f}  Δ={r-b:+.3f}")

    print("\n--- Behavioral probe details (Δ₁) ---")
    for fname in feature_names:
        bv = np.mean([d[fname] for d in probe_details["baseline"]["delta1"]])
        rv = np.mean([d[fname] for d in probe_details["role_only"]["delta1"]])
        print(f"  {fname:<15}: baseline R²={bv:.3f}  role R²={rv:.3f}  Δ={rv-bv:+.3f}")

    print("\n" + "=" * 60)
    print("  BENCHMARK COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Similarity heatmaps for all four training regimes.

Recreates the behavioral vs representational similarity comparison
from dot_learner.py, but for baseline, ext_only, role_only, and full_ds.

Usage:
  uv run regularized_similarity.py
"""

import numpy as np
import torch
import torch.nn.functional as F
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from dot_learner import (
    ELEMENTS, N, IDX, dot_table, to_onehot_pair, PLOT_ORDER,
)
from discoverability_loss import DSNet, one_hot_pair, compute_L_role, compute_L_ext

REGIMES = {
    "baseline":  {"lambda_ext": 0.0, "lambda_role": 0.0},
    "ext_only":  {"lambda_ext": 1.0, "lambda_role": 0.0},
    "role_only": {"lambda_ext": 0.0, "lambda_role": 0.5},
    "full_ds":   {"lambda_ext": 1.0, "lambda_role": 0.5},
}

HIDDEN_SIZES = [6, 16, 32, 64]


def make_training_data():
    X_left, X_right, Y = [], [], []
    for x in range(N):
        for y in range(N):
            X_left.append(x)
            X_right.append(y)
            Y.append(dot_table(x, y))
    return to_onehot_pair(X_left, X_right), torch.tensor(Y, dtype=torch.long)


def train_model(hidden, lambda_ext, lambda_role, seed=0, epochs=3000):
    torch.manual_seed(seed)
    model = DSNet(hidden)
    optimizer = torch.optim.Adam(model.parameters(), lr=0.001)
    X_train, Y_train = make_training_data()
    warmup = 500

    for epoch in range(1, epochs + 1):
        logits = model(X_train)
        loss = F.cross_entropy(logits, Y_train)
        past_warmup = epoch > warmup
        if past_warmup and lambda_ext > 0 and epoch % 5 == 0:
            loss = loss + lambda_ext * compute_L_ext(model, X_train)
        if past_warmup and lambda_role > 0 and epoch % 10 == 0:
            loss = loss + lambda_role * compute_L_role(model, X_train)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

    model.eval()
    return model


def get_repr_sim(model):
    """17x17 cosine similarity in PLOT_ORDER."""
    order_idx = [IDX[name] for name in PLOT_ORDER]
    acts = []
    with torch.no_grad():
        for x in order_idx:
            inp = one_hot_pair(x, 0)
            h = model.hidden1(inp).squeeze().numpy()
            acts.append(h)
    vecs = np.array(acts)
    norms = np.linalg.norm(vecs, axis=1, keepdims=True)
    norms = np.maximum(norms, 1e-8)
    normed = vecs / norms
    return normed @ normed.T


def get_behav_sim():
    """17x17 behavioral similarity in PLOT_ORDER."""
    order_idx = [IDX[name] for name in PLOT_ORDER]
    sim = np.zeros((N, N))
    for i, xi in enumerate(order_idx):
        for j, yj in enumerate(order_idx):
            shared = sum(1 for z in range(N) if dot_table(xi, z) == dot_table(yj, z))
            sim[i, j] = shared / N
    return sim


def main():
    behav = get_behav_sim()
    regime_names = list(REGIMES.keys())
    nrows = len(HIDDEN_SIZES)
    ncols = 5  # behavioral + 4 regimes

    print(f"Training {nrows * 4} models...")

    # Train all models
    all_models = {}  # (H, regime) -> model
    for H in HIDDEN_SIZES:
        for name, params in REGIMES.items():
            print(f"  H={H} {name}...")
            all_models[(H, name)] = train_model(H, params["lambda_ext"], params["lambda_role"])

    # Grid: rows = hidden sizes, cols = behavioral + 4 regimes
    fig, axes = plt.subplots(nrows, ncols, figsize=(22, nrows * 4.5))
    fig.suptitle("Representational Similarity by Training Regime and Capacity",
                 fontsize=14, fontweight="bold")

    for ri, H in enumerate(HIDDEN_SIZES):
        # Behavioral reference (col 0)
        ax = axes[ri, 0]
        ax.imshow(behav, cmap="viridis", vmin=0, vmax=1, aspect="equal")
        if ri == 0:
            ax.set_title("Behavioral\n(ground truth)", fontsize=10, fontweight="bold")
        ax.set_ylabel(f"H = {H}", fontsize=12, fontweight="bold")
        ax.set_xticks(range(N))
        ax.set_xticklabels(PLOT_ORDER if ri == nrows - 1 else [], fontsize=4,
                           rotation=60, ha="right")
        ax.set_yticks(range(N))
        ax.set_yticklabels(PLOT_ORDER, fontsize=4)

        # 4 regimes (cols 1-4)
        for ci, name in enumerate(regime_names):
            ax = axes[ri, ci + 1]
            R = get_repr_sim(all_models[(H, name)])
            mask = np.triu_indices(N, k=1)
            corr = np.corrcoef(behav[mask], R[mask])[0, 1]

            ax.imshow(R, cmap="viridis", vmin=0, vmax=1, aspect="equal")
            if ri == 0:
                ax.set_title(f"{name}", fontsize=10, fontweight="bold")
            ax.text(0.98, 0.98, f"r={corr:.3f}", transform=ax.transAxes,
                    fontsize=8, ha="right", va="top",
                    bbox=dict(boxstyle="round,pad=0.2", facecolor="white", alpha=0.8))
            ax.set_xticks(range(N))
            ax.set_xticklabels(PLOT_ORDER if ri == nrows - 1 else [], fontsize=4,
                               rotation=60, ha="right")
            ax.set_yticks(range(N))
            ax.set_yticklabels([], fontsize=4)

    plt.tight_layout()
    plt.savefig("similarity_by_regime.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved similarity_by_regime.png")


if __name__ == "__main__":
    main()

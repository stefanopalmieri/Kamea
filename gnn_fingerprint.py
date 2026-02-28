#!/usr/bin/env python3
"""
GNN Canonical Fingerprinting of the Kamea Algebra.

Trains a 2-layer Graph Isomorphism Network to learn permutation-invariant
embeddings for the 66-element Kamea magma. The GNN discovers each element's
structural role purely from the Cayley table topology.

Two training approaches:
  A) Supervised: classify each node by its WL canonical ordinal
  B) Contrastive: InfoNCE across random permutations (no labels needed)

Architecture: The GNN operates directly on the Cayley table as a complete
directed graph with labeled edges. Each layer embeds result values and
aggregates row/column neighborhoods separately — directly mirroring WL-1
color refinement.

Usage:
  python gnn_fingerprint.py              # train both approaches, full eval
  python gnn_fingerprint.py --approach a # Approach A only
  python gnn_fingerprint.py --approach b # Approach B only
"""

from __future__ import annotations

import argparse
import json
import sys
import os
import time
from pathlib import Path

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from sklearn.manifold import TSNE
from sklearn.cluster import KMeans
from sklearn.metrics import adjusted_rand_score

# ---------------------------------------------------------------------------
# Project imports
# ---------------------------------------------------------------------------

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from kamea import ALL_NAMES
from emulator.fingerprint import _raw_table, _ordinals

N = len(ALL_NAMES)  # 66

# Atom categories for visualization
CATEGORY_MAP: dict[str, str] = {}
_CATS = {
    "D1_core": ["⊤", "⊥", "i", "k", "a", "b", "e_I", "e_D", "e_M", "e_Σ",
                 "e_Δ", "d_I", "d_K", "m_I", "m_K", "s_C", "p"],
    "D2": ["QUOTE", "EVAL", "APP", "UNAPP"],
    "Nibbles": [f"N{i:X}" for i in range(16)],
    "ALU": ["ALU_LOGIC", "ALU_ARITH", "ALU_ARITHC", "ALU_ZERO", "ALU_COUT"],
    "Misc": ["N_SUCC"],
    "IO": ["IO_PUT", "IO_GET", "IO_RDY", "IO_SEQ"],
    "W32": ["W_PACK8", "W_LO", "W_HI", "W_MERGE", "W_NIB",
            "W_ADD", "W_SUB", "W_CMP", "W_XOR", "W_AND", "W_OR", "W_NOT",
            "W_SHL", "W_SHR", "W_ROTL", "W_ROTR"],
    "MUL": ["MUL16", "MAC16"],
    "QUALE": ["QUALE"],
}
for cat, names in _CATS.items():
    for name in names:
        CATEGORY_MAP[name] = cat

TABLE = torch.tensor(_raw_table, dtype=torch.long)
WL_ORDINALS = torch.tensor(_ordinals, dtype=torch.long)
OUT_DIR = Path(__file__).parent / "gnn_output"


# ---------------------------------------------------------------------------
# Permutation utilities
# ---------------------------------------------------------------------------

def permute_table(T: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
    """Apply random permutation σ. Returns (T', perm) where perm[old]=new.

    Satisfies T'[σ(i)][σ(j)] = σ(T[i][j]).
    Pure tensor ops — no Python loops.
    """
    perm = torch.randperm(T.shape[0])
    # Apply σ to all result values, then reindex rows and columns
    T_new = perm[T]          # σ(T[i][j]) for all i,j
    T_new = T_new[perm]      # reindex rows: T_new[σ(i)] → row σ(i)
    # Wait — we need T'[σ(i)][σ(j)] = σ(T[i][j]).
    # perm[T] gives σ(T[i][j]) at position (i,j).
    # We need to place that at position (σ(i), σ(j)).
    # inv_perm undoes σ: T_result[σ(i)][σ(j)] = perm[T][i][j]
    # So: T_result = perm[T] reindexed by inv_perm on both axes.
    # Equivalently: T_result[perm, :][:, perm] = perm[T]
    # Or: T_result = perm[T[inv_perm][:, inv_perm]]... no.
    # Clearest: build inv_perm, then T_result = (perm[T])[inv_perm]... no.
    # Let's just do it right:
    inv_perm = torch.empty_like(perm)
    inv_perm[perm] = torch.arange(T.shape[0])
    # T'[a][b] = perm[T[inv_perm[a]][inv_perm[b]]]
    T_new = perm[T[inv_perm][:, inv_perm]]
    return T_new, perm


def verify_permutation(T_orig, T_perm, perm):
    """Check T'[σ(i)][σ(j)] = σ(T[i][j]) for all i,j."""
    expected = perm[T_orig]  # σ(T[i][j]) at position (i,j)
    actual = T_perm[perm][:, perm]  # T'[σ(i)][σ(j)] at position (i,j)
    return torch.equal(expected, actual)


# ---------------------------------------------------------------------------
# 2-Layer GNN operating directly on the Cayley table
# ---------------------------------------------------------------------------

class CayleyGNN(nn.Module):
    """2-layer GNN that mirrors WL-1 color refinement on a Cayley table.

    Architecture is permutation-equivariant by construction:

    Layer 0 (structural features):
      Sorted row/col frequency histograms + idempotent flag → MLP → h0.

    Layers 1-2 (message passing with separate row/col signals):
      row_signal[i] = Σ_j msg_mlp(h[j] || h[T[i][j]])   (what i does)
      col_signal[i] = Σ_j msg_mlp(h[j] || h[T[j][i]])   (what is done to i)
      h_new[i]      = upd_mlp(h[i] || row_signal || col_signal)

    Row and column signals are kept separate before combining. The shared
    msg_mlp captures neighbor-result pairings; the upd_mlp combines the
    two directional signals with a residual connection.
    """

    def __init__(self, n: int = 66, hidden_dim: int = 64, embed_dim: int = 32):
        super().__init__()
        self.n = n
        self.hidden_dim = hidden_dim
        self.embed_dim = embed_dim

        feat_dim = 2 * n + 1
        self.feat_enc = nn.Sequential(
            nn.Linear(feat_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
        )

        # Layer 1: shared message MLP + update MLP
        self.msg1 = nn.Sequential(
            nn.Linear(2 * hidden_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
        )
        self.upd1 = nn.Sequential(
            nn.Linear(3 * hidden_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
        )

        # Layer 2: same structure → embed_dim
        self.msg2 = nn.Sequential(
            nn.Linear(2 * hidden_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
        )
        self.upd2 = nn.Sequential(
            nn.Linear(3 * hidden_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, embed_dim),
        )
        self.residual_proj = nn.Linear(hidden_dim, embed_dim, bias=False)

    def _structural_features(self, T: torch.Tensor) -> torch.Tensor:
        """Compute permutation-invariant node features from the Cayley table."""
        n = T.shape[0]
        row_counts = F.one_hot(T, n).float().sum(dim=1)
        row_sorted, _ = row_counts.sort(dim=1, descending=True)
        col_counts = F.one_hot(T.t().contiguous(), n).float().sum(dim=1)
        col_sorted, _ = col_counts.sort(dim=1, descending=True)
        diag = T.diagonal()
        idem = (diag == torch.arange(n, device=T.device)).float().unsqueeze(1)
        return torch.cat([row_sorted, col_sorted, idem], dim=1)

    def _layer(self, h: torch.Tensor, T: torch.Tensor,
               msg_mlp: nn.Module, upd_mlp: nn.Module) -> torch.Tensor:
        """One round of message passing with separate row/col signals."""
        n = T.shape[0]
        d = h.shape[1]

        # h[j] broadcast: (n, n, d) — same for all i (complete graph)
        h_j = h.unsqueeze(0).expand(n, n, d)

        # Row signal: Σ_j msg(h[j] || h[T[i][j]])
        h_row_res = h[T.reshape(-1)].reshape(n, n, d)
        row_msgs = msg_mlp(torch.cat([h_j, h_row_res], dim=2))  # (n, n, d)
        row_agg = row_msgs.sum(dim=1)  # (n, d)

        # Col signal: Σ_j msg(h[j] || h[T[j][i]])
        h_col_res = h[T.t().reshape(-1)].reshape(n, n, d)
        col_msgs = msg_mlp(torch.cat([h_j, h_col_res], dim=2))  # (n, n, d)
        col_agg = col_msgs.sum(dim=1)  # (n, d)

        # Update: combine self + row_signal + col_signal
        return upd_mlp(torch.cat([h, row_agg, col_agg], dim=1))

    def forward(self, T: torch.Tensor) -> torch.Tensor:
        """Forward pass on a Cayley table tensor (n × n, dtype=long)."""
        feats = self._structural_features(T)
        h = F.relu(self.feat_enc(feats))

        # Layer 1 + residual
        h = F.relu(self._layer(h, T, self.msg1, self.upd1)) + h

        # Layer 2 + residual projection
        h = self._layer(h, T, self.msg2, self.upd2) + self.residual_proj(h)

        return h


# ---------------------------------------------------------------------------
# Approach A: Supervised classification
# ---------------------------------------------------------------------------

def train_approach_a(model: CayleyGNN, epochs: int = 1500, lr: float = 1e-3,
                     log_every: int = 100) -> dict:
    """Classify each node by WL canonical ordinal (66 classes)."""
    classifier = nn.Linear(model.embed_dim, N)
    all_params = list(model.parameters()) + list(classifier.parameters())
    optimizer = torch.optim.Adam(all_params, lr=lr)

    losses, accuracies = [], []
    t0 = time.time()

    for epoch in range(epochs):
        model.train()
        classifier.train()

        T_perm, perm = permute_table(TABLE)
        embeddings = model(T_perm)
        logits = classifier(embeddings)

        # Node k in T_perm represents original element inv_perm[k]
        inv_perm = torch.empty_like(perm)
        inv_perm[perm] = torch.arange(N)
        targets = WL_ORDINALS[inv_perm]

        loss = F.cross_entropy(logits, targets)
        acc = (logits.argmax(1) == targets).float().mean().item()

        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

        losses.append(loss.item())
        accuracies.append(acc)

        if (epoch + 1) % log_every == 0:
            print(f"  [A] Epoch {epoch+1}/{epochs}  loss={loss.item():.4f}  "
                  f"acc={acc:.3f}  ({time.time()-t0:.1f}s)")

    return {"losses": losses, "accuracies": accuracies,
            "classifier": classifier, "time": time.time() - t0}


# ---------------------------------------------------------------------------
# Approach B: Contrastive (InfoNCE)
# ---------------------------------------------------------------------------

def train_approach_b(model: CayleyGNN, epochs: int = 2000, lr: float = 1e-3,
                     temperature: float = 0.07, log_every: int = 100,
                     ) -> dict:
    """InfoNCE across random permutation pairs — no labels needed."""
    optimizer = torch.optim.Adam(model.parameters(), lr=lr)

    losses, accuracies = [], []
    t0 = time.time()

    for epoch in range(epochs):
        model.train()

        T1, perm1 = permute_table(TABLE)
        T2, perm2 = permute_table(TABLE)

        e1 = F.normalize(model(T1), dim=1)
        e2 = F.normalize(model(T2), dim=1)

        sim = torch.mm(e1, e2.t()) / temperature

        # Node i in graph1 represents original element inv1[i]
        # That element is node perm2[inv1[i]] in graph2
        inv1 = torch.empty_like(perm1)
        inv1[perm1] = torch.arange(N)
        labels = perm2[inv1]

        loss = F.cross_entropy(sim, labels)
        acc = (sim.argmax(1) == labels).float().mean().item()

        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

        losses.append(loss.item())
        accuracies.append(acc)

        if (epoch + 1) % log_every == 0:
            print(f"  [B] Epoch {epoch+1}/{epochs}  loss={loss.item():.4f}  "
                  f"acc={acc:.3f}  ({time.time()-t0:.1f}s)")

    return {"losses": losses, "accuracies": accuracies, "time": time.time() - t0}


# ---------------------------------------------------------------------------
# Evaluation
# ---------------------------------------------------------------------------

@torch.no_grad()
def evaluate(model: CayleyGNN, label: str, n_trials: int = 100) -> dict:
    model.eval()

    all_embeddings = []
    for _ in range(n_trials):
        T_perm, perm = permute_table(TABLE)
        emb = model(T_perm)
        # Original element i lives at position perm[i] in the permuted table,
        # so emb[perm[i]] is the embedding for original element i.
        all_embeddings.append(emb[perm])

    all_emb = torch.stack(all_embeddings)
    mean_emb = all_emb.mean(dim=0)

    # 1. Uniqueness
    dists = torch.cdist(mean_emb.unsqueeze(0), mean_emb.unsqueeze(0)).squeeze(0)
    dists_no_diag = dists + torch.eye(N) * 1e10
    min_dist = dists_no_diag.min().item()
    mean_dist = dists[~torch.eye(N, dtype=bool)].mean().item()
    rounded = (mean_emb * 1000).round()
    unique_count = len(torch.unique(rounded, dim=0))

    # 2. Invariance
    var_per_element = all_emb.var(dim=0).mean(dim=1)
    mean_var = var_per_element.mean().item()
    max_var = var_per_element.max().item()

    # 3. Clustering
    emb_np = mean_emb.numpy()
    cat_names = sorted(set(CATEGORY_MAP.values()))
    cat_to_id = {c: i for i, c in enumerate(cat_names)}
    true_labels = np.array([cat_to_id[CATEGORY_MAP[n]] for n in ALL_NAMES])
    km = KMeans(n_clusters=len(cat_names), n_init=20, random_state=42)
    pred_labels = km.fit_predict(emb_np)
    ari = adjusted_rand_score(true_labels, pred_labels)

    metrics = {
        "unique_embeddings": int(unique_count),
        "min_pairwise_dist": float(min_dist),
        "mean_pairwise_dist": float(mean_dist),
        "mean_invariance_var": float(mean_var),
        "max_invariance_var": float(max_var),
        "clustering_ari": float(ari),
        "n_trials": n_trials,
    }

    print(f"\n{'='*60}")
    print(f"Evaluation: {label}")
    print(f"{'='*60}")
    print(f"  Unique embeddings:     {unique_count}/66")
    print(f"  Min pairwise distance: {min_dist:.6f}")
    print(f"  Mean pairwise dist:    {mean_dist:.4f}")
    print(f"  Invariance variance:   mean={mean_var:.2e}, max={max_var:.2e}")
    print(f"  Clustering ARI:        {ari:.4f}")

    return {"metrics": metrics, "mean_emb": mean_emb, "all_emb": all_emb}


# ---------------------------------------------------------------------------
# Visualization
# ---------------------------------------------------------------------------

def plot_embeddings(mean_emb: torch.Tensor, label: str, out_path: Path):
    emb_np = mean_emb.numpy()
    tsne = TSNE(n_components=2, perplexity=15, random_state=42, max_iter=2000)
    coords = tsne.fit_transform(emb_np)

    cat_names = sorted(set(CATEGORY_MAP.values()))
    colors = plt.cm.tab10(np.linspace(0, 1, len(cat_names)))
    cat_to_color = {c: colors[i] for i, c in enumerate(cat_names)}

    fig, ax = plt.subplots(figsize=(12, 9))
    for cat in cat_names:
        indices = [i for i, name in enumerate(ALL_NAMES)
                   if CATEGORY_MAP[name] == cat]
        ax.scatter(coords[indices, 0], coords[indices, 1],
                   c=[cat_to_color[cat]], label=cat, s=60, alpha=0.8,
                   edgecolors="black", linewidths=0.5)

    annotate_names = {"⊤", "⊥", "p", "QUALE", "N0", "NF", "i", "k",
                      "QUOTE", "IO_PUT", "W_ADD", "MUL16"}
    for i, name in enumerate(ALL_NAMES):
        if name in annotate_names:
            ax.annotate(name, (coords[i, 0], coords[i, 1]),
                        fontsize=7, ha="center", va="bottom",
                        textcoords="offset points", xytext=(0, 5))

    ax.set_title(f"GNN Canonical Embeddings — {label}\n"
                 f"66 Kamea atoms, t-SNE projection", fontsize=14)
    ax.legend(loc="best", fontsize=9, framealpha=0.9)
    ax.set_xlabel("t-SNE 1")
    ax.set_ylabel("t-SNE 2")
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved: {out_path}")


def plot_training(losses, accuracies, label, out_path):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4))
    ax1.plot(losses, linewidth=0.8)
    ax1.set_xlabel("Epoch"); ax1.set_ylabel("Loss")
    ax1.set_title(f"Loss — {label}"); ax1.set_yscale("log")
    ax1.grid(True, alpha=0.3)
    ax2.plot(accuracies, linewidth=0.8, color="green")
    ax2.set_xlabel("Epoch"); ax2.set_ylabel("Accuracy")
    ax2.set_title(f"Accuracy — {label}"); ax2.set_ylim(-0.05, 1.05)
    ax2.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)
    print(f"  Saved: {out_path}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="GNN Canonical Fingerprinting")
    parser.add_argument("--approach", choices=["a", "b", "both"], default="both")
    parser.add_argument("--epochs-a", type=int, default=1500)
    parser.add_argument("--epochs-b", type=int, default=2000)
    parser.add_argument("--hidden-dim", type=int, default=128)
    parser.add_argument("--embed-dim", type=int, default=32)
    parser.add_argument("--lr", type=float, default=1e-3)
    parser.add_argument("--eval-trials", type=int, default=100)
    args = parser.parse_args()

    OUT_DIR.mkdir(exist_ok=True)

    print("Verifying permutation logic...")
    for seed in range(5):
        torch.manual_seed(seed)
        T_perm, perm = permute_table(TABLE)
        assert verify_permutation(TABLE, T_perm, perm)
    print("  Verified (5 seeds).\n")

    report = {}

    if args.approach in ("a", "both"):
        print("=" * 60)
        print("APPROACH A: Supervised (WL classification)")
        print("=" * 60)
        model_a = CayleyGNN(N, args.hidden_dim, args.embed_dim)
        pc = sum(p.numel() for p in model_a.parameters())
        print(f"  Model params: {pc:,}")
        res_a = train_approach_a(model_a, args.epochs_a, args.lr)
        ev_a = evaluate(model_a, "Approach A (Supervised)", args.eval_trials)
        plot_embeddings(ev_a["mean_emb"], "Approach A (Supervised)",
                        OUT_DIR / "tsne_approach_a.png")
        plot_training(res_a["losses"], res_a["accuracies"],
                      "Approach A", OUT_DIR / "training_approach_a.png")
        torch.save(model_a.state_dict(), OUT_DIR / "model_approach_a.pt")
        report["approach_a"] = {
            "metrics": ev_a["metrics"],
            "training_time": res_a["time"],
            "final_accuracy": res_a["accuracies"][-1],
            "epochs": args.epochs_a, "param_count": pc,
        }

    if args.approach in ("b", "both"):
        print(f"\n{'=' * 60}")
        print("APPROACH B: Contrastive (InfoNCE, no labels)")
        print("=" * 60)
        model_b = CayleyGNN(N, args.hidden_dim, args.embed_dim)
        pc = sum(p.numel() for p in model_b.parameters())
        print(f"  Model params: {pc:,}")
        res_b = train_approach_b(model_b, args.epochs_b, args.lr)
        ev_b = evaluate(model_b, "Approach B (Contrastive)", args.eval_trials)
        plot_embeddings(ev_b["mean_emb"], "Approach B (Contrastive)",
                        OUT_DIR / "tsne_approach_b.png")
        plot_training(res_b["losses"], res_b["accuracies"],
                      "Approach B", OUT_DIR / "training_approach_b.png")
        torch.save(model_b.state_dict(), OUT_DIR / "model_approach_b.pt")
        report["approach_b"] = {
            "metrics": ev_b["metrics"],
            "training_time": res_b["time"],
            "final_accuracy": res_b["accuracies"][-1],
            "epochs": args.epochs_b, "param_count": pc,
        }

    with open(OUT_DIR / "report.json", "w") as f:
        json.dump(report, f, indent=2)
    print(f"\nReport: {OUT_DIR / 'report.json'}")

    print(f"\n{'=' * 60}")
    print("SUMMARY")
    print(f"{'=' * 60}")
    for approach, data in report.items():
        m = data["metrics"]
        print(f"\n  {approach}:")
        print(f"    Unique embeddings: {m['unique_embeddings']}/66")
        print(f"    Min pairwise dist: {m['min_pairwise_dist']:.6f}")
        print(f"    Invariance var:    {m['mean_invariance_var']:.2e}")
        print(f"    Clustering ARI:    {m['clustering_ari']:.4f}")
        print(f"    Final accuracy:    {data['final_accuracy']:.3f}")
        print(f"    Training time:     {data['training_time']:.1f}s")


if __name__ == "__main__":
    main()

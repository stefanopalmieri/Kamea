#!/usr/bin/env python3
"""
Δ₁ Dot-Learner: Neural Network Experiment

Train a small neural network to learn Δ₁'s dot operation from examples,
then run the true black-box recovery procedure on the trained network
to see if the algebraic structure is recoverable from learned behavior.

Usage:
  uv run dot_learner.py
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
from sklearn.decomposition import PCA
from sklearn.manifold import TSNE


# ============================================================
# Section 1: Δ₁ definition and data generation
# ============================================================

ELEMENTS = [
    "top", "bot", "i", "k", "a", "b", "e_I",
    "e_D", "e_M", "e_Sigma", "e_Delta",
    "d_I", "d_K", "m_I", "m_K", "s_C", "p",
]
N = len(ELEMENTS)
IDX = {name: i for i, name in enumerate(ELEMENTS)}


def dot_table(x: int, y: int) -> int:
    """Δ₁ dot operation on element indices. 26 first-match rules."""
    # Block A: Boolean absorption
    if x == IDX["top"]: return IDX["top"]
    if x == IDX["bot"]: return IDX["bot"]
    # Block B: Testers
    if x == IDX["e_I"]:
        return IDX["top"] if y in (IDX["i"], IDX["k"]) else IDX["bot"]
    if x == IDX["d_K"]:
        return IDX["top"] if y in (IDX["a"], IDX["b"]) else IDX["bot"]
    if x == IDX["m_K"]:
        return IDX["top"] if y == IDX["a"] else IDX["bot"]
    if x == IDX["m_I"]:
        return IDX["bot"] if y == IDX["p"] else IDX["top"]
    # Block C: Structural encoders
    if x == IDX["e_D"] and y == IDX["i"]: return IDX["d_I"]
    if x == IDX["e_D"] and y == IDX["k"]: return IDX["d_K"]
    if x == IDX["e_M"] and y == IDX["i"]: return IDX["m_I"]
    if x == IDX["e_M"] and y == IDX["k"]: return IDX["m_K"]
    if x == IDX["e_Sigma"] and y == IDX["s_C"]: return IDX["e_Delta"]
    if x == IDX["e_Delta"] and y == IDX["e_D"]: return IDX["d_I"]
    # Block D: Absorption breaker
    if x == IDX["p"] and y == IDX["top"]: return IDX["top"]
    # Block E: Passive self-identification
    if y == IDX["top"] and x in (IDX["i"], IDX["k"], IDX["a"], IDX["b"],
                                  IDX["d_I"], IDX["s_C"]):
        return x
    # Block F: Default
    return IDX["p"]


def generate_data():
    """Generate all 289 (x, y) -> z training examples."""
    X_left, X_right, Y = [], [], []
    for x in range(N):
        for y in range(N):
            X_left.append(x)
            X_right.append(y)
            Y.append(dot_table(x, y))
    return X_left, X_right, Y


def to_onehot_pair(x_indices, y_indices):
    """Convert index pairs to concatenated one-hot vectors (N*2 dims)."""
    n = len(x_indices)
    X = torch.zeros(n, N * 2)
    for i in range(n):
        X[i, x_indices[i]] = 1.0
        X[i, N + y_indices[i]] = 1.0
    return X


def verify_dot_table():
    """Sanity-check the dot table against known properties."""
    # 2 left-absorbers
    absorbers = [x for x in range(N) if all(dot_table(x, y) == x for y in range(N))]
    assert len(absorbers) == 2, f"Expected 2 absorbers, got {len(absorbers)}"
    # 4 testers
    top, bot = IDX["top"], IDX["bot"]
    testers = [x for x in range(N) if x not in absorbers and
               all(dot_table(x, y) in (top, bot) for y in range(N))]
    assert len(testers) == 4, f"Expected 4 testers, got {len(testers)}"
    # H1, H2, H3
    assert dot_table(IDX["e_D"], IDX["i"]) == IDX["d_I"]
    assert dot_table(IDX["e_D"], IDX["k"]) == IDX["d_K"]
    assert dot_table(IDX["e_M"], IDX["i"]) == IDX["m_I"]
    assert dot_table(IDX["e_M"], IDX["k"]) == IDX["m_K"]
    assert dot_table(IDX["e_Sigma"], IDX["s_C"]) == IDX["e_Delta"]
    print("  Dot table verified: 2 absorbers, 4 testers, H1/H2/H3 correct.")


# ============================================================
# Section 2: Network definition and training
# ============================================================

class DotNet(nn.Module):
    def __init__(self, hidden=128):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(N * 2, hidden),
            nn.ReLU(),
            nn.Linear(hidden, hidden),
            nn.ReLU(),
            nn.Linear(hidden, N),
        )

    def forward(self, x):
        return self.net(x)

    def hidden_activations(self, x):
        """Extract activations after the first ReLU."""
        h = self.net[0](x)  # Linear
        h = self.net[1](h)  # ReLU
        return h


def train_network(model, X_train, Y_train, max_epochs=2000, lr=0.001):
    optimizer = optim.Adam(model.parameters(), lr=lr)
    criterion = nn.CrossEntropyLoss()

    for epoch in range(1, max_epochs + 1):
        logits = model(X_train)
        loss = criterion(logits, Y_train)

        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

        preds = logits.argmax(dim=1)
        acc = (preds == Y_train).float().mean().item()

        if epoch % 100 == 0 or acc == 1.0:
            print(f"  Epoch {epoch:4d}  loss={loss.item():.4f}  acc={acc:.4f}")

        if acc == 1.0:
            print(f"  Reached 100% accuracy at epoch {epoch}.")
            return True

    final_acc = (model(X_train).argmax(dim=1) == Y_train).float().mean().item()
    print(f"  Training ended at {max_epochs} epochs, accuracy={final_acc:.4f}")
    return final_acc == 1.0


# ============================================================
# Section 3: Black-box recovery
# ============================================================

def make_nn_blackbox(model, seed=42):
    """
    Create a black-box wrapper around the trained network.
    Shuffles element indices into opaque labels.
    Returns (domain, dot_oracle, true_mapping).
    """
    rng = random.Random(seed)
    perm = list(range(N))
    rng.shuffle(perm)
    inv_perm = [0] * N
    for i, p in enumerate(perm):
        inv_perm[p] = i

    # domain: opaque labels (shuffled indices)
    domain = list(range(N))

    # true_mapping: opaque_label -> true_element_index
    # perm[opaque] = true, inv_perm[true] = opaque
    true_mapping = {opaque: perm[opaque] for opaque in range(N)}

    @torch.no_grad()
    def dot_oracle(xh, yh):
        """Black-box: takes opaque labels, returns opaque label."""
        true_x = perm[xh]
        true_y = perm[yh]
        inp = to_onehot_pair([true_x], [true_y])
        pred = model(inp).argmax(dim=1).item()
        return inv_perm[pred]

    return domain, dot_oracle, true_mapping


def recover_d1(domain, dot):
    """
    8-step recovery procedure adapted from delta2_true_blackbox.py.
    Works on integer labels. No ground truth used.
    """
    def left_image(x):
        return {dot(x, y) for y in domain}

    # Step 1: Booleans (left-absorbers)
    absorbers = [x for x in domain if all(dot(x, y) == x for y in domain)]
    assert len(absorbers) == 2, f"Expected 2 absorbers, got {len(absorbers)}"
    B1, B2 = absorbers

    # Step 2: Testers + orient booleans
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
    assert chosen is not None, "Failed to orient booleans"
    top, bot, testers, Dec = chosen

    # Step 2.5: Find p (unique non-boolean, non-tester with top in left-image)
    p_candidates = [
        x for x in domain
        if x not in (top, bot) and x not in testers
        and top in left_image(x)
    ]
    assert len(p_candidates) == 1, f"Expected 1 p-candidate, got {len(p_candidates)}"
    p_tok = p_candidates[0]

    # Step 3: Tester cardinalities
    sizes = {t: len(Dec(t)) for t in testers}
    m_K = [t for t in testers if sizes[t] == 1][0]
    m_I = max(testers, key=lambda t: sizes[t])
    two = [t for t in testers if sizes[t] == 2]
    assert len(two) == 2

    # Step 4: Distinguish e_I from d_K (rich vs inert)
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
    e_I, d_K = (t1, t2) if has_productive_args(Dec(t1)) else (t2, t1)
    ctx = list(Dec(e_I))

    # Step 5: Find e_D and e_M
    def is_encoder(f):
        if f in (top, bot) or f in testers:
            return False
        outs = [dot(f, x) for x in ctx]
        return all(o not in (top, bot, p_tok) for o in outs)

    enc = [f for f in domain if is_encoder(f)]
    assert len(enc) == 2, f"Expected 2 encoders, got {len(enc)}"

    def maps_both_to_testers(f):
        return all(dot(f, x) in testers for x in ctx)

    e_M = enc[0] if maps_both_to_testers(enc[0]) else enc[1]
    e_D = enc[1] if e_M == enc[0] else enc[0]

    # Step 6: Distinguish i from k
    outA, outB = dot(e_M, ctx[0]), dot(e_M, ctx[1])
    if len(Dec(outA)) > len(Dec(outB)):
        i_tok, k_tok = ctx[0], ctx[1]
    else:
        i_tok, k_tok = ctx[1], ctx[0]

    # Step 7: a, b, d_I
    ab = list(Dec(d_K))
    a_tok = next(x for x in ab if dot(m_K, x) == top)
    b_tok = next(x for x in ab if x != a_tok)
    d_I = dot(e_D, i_tok)

    # Step 8: e_Sigma, s_C, e_Delta
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
    assert e_S is not None, "Failed to recover e_Sigma/s_C/e_Delta"

    return {
        "top": top, "bot": bot, "p": p_tok,
        "e_I": e_I, "e_D": e_D, "e_M": e_M,
        "e_Sigma": e_S, "e_Delta": e_Delta,
        "i": i_tok, "k": k_tok, "a": a_tok, "b": b_tok,
        "d_I": d_I, "d_K": d_K, "m_I": m_I, "m_K": m_K, "s_C": sC,
    }


# ============================================================
# Section 4: Representation analysis
# ============================================================

ROLE_GROUPS = {
    "Booleans": ["top", "bot"],
    "Testers": ["e_I", "d_K", "m_K", "m_I"],
    "Encoders": ["e_D", "e_M"],
    "Context": ["i", "k"],
    "Kappa": ["a", "b"],
    "Synthesis": ["e_Sigma", "e_Delta", "s_C"],
    "Code": ["d_I"],
    "Default": ["p"],
}

ROLE_COLORS = {
    "Booleans": "#F0B429",
    "Testers": "#BB6BD9",
    "Encoders": "#FF6B6B",
    "Context": "#4C9AFF",
    "Kappa": "#36D7B7",
    "Synthesis": "#E05555",
    "Code": "#7E8CA0",
    "Default": "#8B9DAF",
}


PLOT_ORDER = [
    "top", "bot",
    "m_I", "e_I", "d_K", "m_K",
    "p",
    "i", "k",
    "a", "b",
    "d_I",
    "s_C",
    "e_D", "e_M",
    "e_Sigma", "e_Delta",
]


def get_element_role(name):
    for role, members in ROLE_GROUPS.items():
        if name in members:
            return role
    return "Unknown"


def extract_hidden_activations(model):
    """Extract hidden activations for each element as left-arg with right=top."""
    top_idx = IDX["top"]
    activations = {}
    for x in range(N):
        inp = to_onehot_pair([x], [top_idx])
        h = model.hidden_activations(inp).squeeze().detach().numpy()
        activations[ELEMENTS[x]] = h
    return activations


def plot_representations(activations, output_path="representations.png"):
    """PCA and t-SNE visualization of hidden activations, colored by role."""
    names = PLOT_ORDER
    vecs = np.array([activations[n] for n in names])

    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    fig.suptitle("Hidden Layer Representations by Algebraic Role", fontsize=13)

    for ax, method_name, coords in [
        (axes[0], "PCA", PCA(n_components=2).fit_transform(vecs)),
        (axes[1], "t-SNE", TSNE(n_components=2, perplexity=5, random_state=42,
                                  max_iter=1000).fit_transform(vecs)),
    ]:
        ax.set_title(method_name, fontsize=11)
        for idx, name in enumerate(names):
            role = get_element_role(name)
            color = ROLE_COLORS.get(role, "gray")
            ax.scatter(coords[idx, 0], coords[idx, 1], c=color, s=80,
                       edgecolors="black", linewidths=0.5, zorder=3)
            ax.annotate(name, (coords[idx, 0], coords[idx, 1]),
                        fontsize=7, ha="center", va="bottom",
                        xytext=(0, 5), textcoords="offset points")
        ax.set_xticks([])
        ax.set_yticks([])

    # Legend
    from matplotlib.lines import Line2D
    handles = [Line2D([0], [0], marker='o', color='w', markerfacecolor=c,
                       markersize=8, label=r) for r, c in ROLE_COLORS.items()]
    fig.legend(handles=handles, loc="lower center", ncol=4, fontsize=9,
               frameon=False)
    plt.tight_layout(rect=[0, 0.06, 1, 0.95])
    plt.savefig(output_path, dpi=200, bbox_inches="tight")
    plt.close()
    print(f"  Saved {output_path}")


def compute_behavioral_similarity():
    """17x17 matrix: fraction of shared outputs for each pair, in PLOT_ORDER."""
    order_idx = [IDX[name] for name in PLOT_ORDER]
    sim = np.zeros((N, N))
    for i, xi in enumerate(order_idx):
        for j, yj in enumerate(order_idx):
            shared = sum(1 for z in range(N) if dot_table(xi, z) == dot_table(yj, z))
            sim[i, j] = shared / N
    return sim


def compute_representational_similarity(activations):
    """17x17 cosine similarity matrix from hidden activations, in PLOT_ORDER."""
    vecs = np.array([activations[name] for name in PLOT_ORDER])
    norms = np.linalg.norm(vecs, axis=1, keepdims=True)
    norms = np.maximum(norms, 1e-8)
    normed = vecs / norms
    return normed @ normed.T


def plot_similarity(behav_sim, repr_sim, output_path="similarity.png"):
    """Side-by-side heatmaps."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    fig.suptitle("Behavioral vs Representational Similarity", fontsize=13)

    for ax, mat, title in [
        (ax1, behav_sim, "Behavioral Similarity\n(fraction of shared outputs)"),
        (ax2, repr_sim, "Representational Similarity\n(cosine similarity of hidden activations)"),
    ]:
        im = ax.imshow(mat, cmap="viridis", vmin=0, vmax=1, aspect="equal")
        ax.set_title(title, fontsize=10)
        ax.set_xticks(range(N))
        ax.set_xticklabels(PLOT_ORDER, fontsize=5, rotation=60, ha="right")
        ax.set_yticks(range(N))
        ax.set_yticklabels(PLOT_ORDER, fontsize=5)
        fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)

    plt.tight_layout()
    plt.savefig(output_path, dpi=200, bbox_inches="tight")
    plt.close()
    print(f"  Saved {output_path}")


def compute_clustering_ratio(activations):
    """Average within-role distance / between-role distance."""
    vecs = {name: activations[name] for name in PLOT_ORDER}
    within_dists = []
    between_dists = []
    for name_a in PLOT_ORDER:
        role_a = get_element_role(name_a)
        for name_b in PLOT_ORDER:
            if name_a == name_b:
                continue
            role_b = get_element_role(name_b)
            dist = np.linalg.norm(vecs[name_a] - vecs[name_b])
            if role_a == role_b:
                within_dists.append(dist)
            else:
                between_dists.append(dist)
    if not within_dists:
        return float("inf")
    return np.mean(within_dists) / np.mean(between_dists)


# ============================================================
# Section 5: Main
# ============================================================

def main():
    print("=" * 60)
    print("  Δ₁ DOT-LEARNER: NEURAL NETWORK EXPERIMENT")
    print("=" * 60)

    # --- Data generation ---
    print("\n--- Phase 0: Data generation & verification ---")
    verify_dot_table()
    X_left, X_right, Y = generate_data()
    X_train = to_onehot_pair(X_left, X_right)
    Y_train = torch.tensor(Y, dtype=torch.long)
    print(f"  Generated {len(Y)} training examples ({N}x{N} = {N*N}).")

    # --- Training ---
    print("\n--- Phase 1: Training ---")
    model = DotNet(hidden=128)
    perfect = train_network(model, X_train, Y_train, max_epochs=2000)
    if not perfect:
        print("  WARNING: Did not reach 100% accuracy. Recovery may fail.")

    # --- Black-box recovery ---
    print("\n--- Phase 2: Black-box recovery ---")
    domain, dot_oracle, true_mapping = make_nn_blackbox(model, seed=42)
    recovered = recover_d1(domain, dot_oracle)

    # Build inverse mapping: true_index -> opaque_label
    inv_true = {v: k for k, v in true_mapping.items()}
    correct = 0
    for name in ELEMENTS:
        if name == "p" and name not in recovered:
            continue
        true_idx = IDX[name]
        expected_opaque = inv_true[true_idx]
        got_opaque = recovered.get(name)
        ok = got_opaque == expected_opaque
        if ok:
            correct += 1
        status = "✓" if ok else f"✗ (expected {expected_opaque}, got {got_opaque})"
        print(f"  {name:10s} → {got_opaque}  {status}")

    print(f"\n  Recovery: {correct}/{N} elements correctly identified.")

    # --- Representation analysis ---
    print("\n--- Phase 3: Representation analysis ---")
    model.eval()
    activations = extract_hidden_activations(model)

    plot_representations(activations, output_path="representations.png")

    behav_sim = compute_behavioral_similarity()
    repr_sim = compute_representational_similarity(activations)
    plot_similarity(behav_sim, repr_sim, output_path="similarity.png")

    # Correlation between the two similarity matrices (upper triangle)
    mask = np.triu_indices(N, k=1)
    corr = np.corrcoef(behav_sim[mask], repr_sim[mask])[0, 1]
    print(f"  Correlation (behavioral vs representational similarity): {corr:.4f}")

    ratio = compute_clustering_ratio(activations)
    print(f"  Clustering ratio (within/between role distance): {ratio:.4f}")
    if ratio < 1.0:
        print("  → Network clusters elements by algebraic role.")
    else:
        print("  → No clear role-based clustering in hidden representations.")

    print("\n" + "=" * 60)
    print(f"  SUMMARY")
    print(f"  Recovery: {correct}/{N} elements")
    print(f"  Clustering ratio: {ratio:.4f}")
    print(f"  Similarity correlation: {corr:.4f}")
    print("=" * 60)


if __name__ == "__main__":
    main()

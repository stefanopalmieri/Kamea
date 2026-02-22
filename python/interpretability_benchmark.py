#!/usr/bin/env python3
"""
Interpretability Benchmark: DS Recovery vs Standard Techniques

Compares the DS recovery procedure against K-Means, Linear Probing,
and Activation Patching on networks with known algebraic structure (Δ₁)
vs a control algebra with no self-modeling structure.

Usage:
  uv run interpretability_benchmark.py
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
from sklearn.metrics import adjusted_rand_score
from sklearn.cluster import KMeans, SpectralClustering
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler

from dot_learner import (
    ELEMENTS, N, IDX, dot_table, generate_data, to_onehot_pair,
    DotNet, ROLE_GROUPS, PLOT_ORDER, get_element_role,
)


# ============================================================
# Section 1: Algebra definitions
# ============================================================

DELTA1_ROLES = {
    "Booleans": [0, 1],
    "Testers": [6, 12, 14, 13],
    "Encoders": [7, 8],
    "Context": [2, 3],
    "Kappa": [4, 5],
    "Synthesis": [9, 10, 15],
    "Code": [11],
    "Default": [16],
}

CONTROL_ROLES = {
    "GroupA": [0, 1],
    "GroupB": [6, 12, 14, 13],
    "GroupC": [7, 8],
    "GroupD": [2, 3],
    "GroupE": [4, 5],
    "GroupF": [9, 10, 15],
    "GroupG": [11],
    "GroupH": [16],
}


def roles_to_labels(roles_dict):
    """Convert role dict to per-element label array."""
    labels = [0] * N
    for i, (role, members) in enumerate(roles_dict.items()):
        for m in members:
            labels[m] = i
    return labels


DELTA1_LABELS = roles_to_labels(DELTA1_ROLES)
CONTROL_LABELS = roles_to_labels(CONTROL_ROLES)


def make_control_algebra(seed=42):
    """Generate a 17×17 operation table with distinct row permutations (Ext)."""
    rng = random.Random(seed)
    rows = []
    seen = set()
    attempts = 0
    while len(rows) < N:
        perm = list(range(N))
        rng.shuffle(perm)
        key = tuple(perm)
        if key not in seen:
            seen.add(key)
            rows.append(perm)
        attempts += 1
        if attempts > 10000:
            raise RuntimeError("Failed to generate enough distinct permutations")

    table = rows

    def dot_control(x, y):
        return table[x][y]

    return dot_control, table


def verify_control(dot_fn, table):
    """Verify the control algebra has Ext but no special structure."""
    # All rows distinct
    row_set = {tuple(r) for r in table}
    assert len(row_set) == N, "Rows not distinct"
    # No left-absorbers
    for x in range(N):
        if all(dot_fn(x, y) == x for y in range(N)):
            return False, "Has absorber"
    # No boolean-like elements (left-image size <= 2, excluding absorbers)
    for x in range(N):
        im = {dot_fn(x, y) for y in range(N)}
        if len(im) <= 2:
            return False, f"Element {x} has small left-image"
    return True, "OK"


# ============================================================
# Section 2: Network training
# ============================================================

HIDDEN = 32
NUM_TRIALS = 10


def generate_data_from_fn(dot_fn):
    """Generate all 289 training examples from an arbitrary dot function."""
    X_left, X_right, Y = [], [], []
    for x in range(N):
        for y in range(N):
            X_left.append(x)
            X_right.append(y)
            Y.append(dot_fn(x, y))
    return X_left, X_right, Y


def train_silent(model, X_train, Y_train, max_epochs=5000, lr=0.001):
    optimizer = optim.Adam(model.parameters(), lr=lr)
    criterion = nn.CrossEntropyLoss()
    for epoch in range(1, max_epochs + 1):
        logits = model(X_train)
        loss = criterion(logits, Y_train)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
        if epoch % 500 == 0 or epoch == max_epochs:
            with torch.no_grad():
                acc = (model(X_train).argmax(dim=1) == Y_train).float().mean().item()
            if acc == 1.0:
                return 1.0
    with torch.no_grad():
        return (model(X_train).argmax(dim=1) == Y_train).float().mean().item()


def train_models(dot_fn, label):
    """Train NUM_TRIALS models on a given algebra."""
    Xl, Xr, Y = generate_data_from_fn(dot_fn)
    X_train = to_onehot_pair(Xl, Xr)
    Y_train = torch.tensor(Y, dtype=torch.long)
    models = []
    for trial in range(NUM_TRIALS):
        seed = hash(label) % 10000 + trial * 100
        torch.manual_seed(seed)
        model = DotNet(hidden=HIDDEN)
        acc = train_silent(model, X_train, Y_train)
        model.eval()
        models.append((model, acc, seed))
        print(f"  {label} trial {trial+1}/{NUM_TRIALS}: acc={acc:.4f}")
    return models, X_train, Y_train


# ============================================================
# Section 3: DS Recovery
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


def ds_recovery(model, seed=42):
    """Run DS recovery. Returns (role_labels, n_correct, n_steps)."""
    domain, dot_oracle, true_mapping = make_nn_blackbox(model, seed)
    inv_true = {v: k for k, v in true_mapping.items()}

    def left_image(x):
        return {dot_oracle(x, y) for y in domain}

    try:
        # Step 1: Booleans
        absorbers = [x for x in domain if all(dot_oracle(x, y) == x for y in domain)]
        assert len(absorbers) == 2
        B1, B2 = absorbers

        # Step 2: Testers + orient
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
            Dec = lambda t, top=top: {y for y in domain if dot_oracle(t, y) == top}
            sizes = sorted(len(Dec(t)) for t in testers)
            if sizes[0] == 1 and sizes[1] == 2 and sizes[2] == 2:
                chosen = (top, bot, testers, Dec)
                break
        assert chosen is not None
        top, bot, testers, Dec = chosen

        # Step 2.5: Find p
        p_candidates = [
            x for x in domain
            if x not in (top, bot) and x not in testers
            and top in left_image(x)
        ]
        assert len(p_candidates) == 1
        p_tok = p_candidates[0]

        # Step 3: Tester cardinalities
        sizes = {t: len(Dec(t)) for t in testers}
        m_K = [t for t in testers if sizes[t] == 1][0]
        m_I = max(testers, key=lambda t: sizes[t])
        two = [t for t in testers if sizes[t] == 2]
        assert len(two) == 2

        # Step 4: e_I vs d_K
        def has_productive(decoded_set):
            for f in domain:
                if f in (top, bot) or f in testers:
                    continue
                for x in decoded_set:
                    out = dot_oracle(f, x)
                    if out not in (top, bot, p_tok):
                        return True
            return False

        t1, t2 = two
        rich1, rich2 = has_productive(Dec(t1)), has_productive(Dec(t2))
        assert rich1 != rich2
        e_I, d_K = (t1, t2) if rich1 else (t2, t1)
        ctx = list(Dec(e_I))

        # Step 5: Encoders
        def is_encoder(f):
            if f in (top, bot) or f in testers:
                return False
            outs = [dot_oracle(f, x) for x in ctx]
            return all(o not in (top, bot, p_tok) for o in outs)

        enc = [f for f in domain if is_encoder(f)]
        assert len(enc) == 2
        e_M = enc[0] if all(dot_oracle(enc[0], x) in testers for x in ctx) else enc[1]
        e_D = enc[1] if e_M == enc[0] else enc[0]

        # Step 6: i vs k
        outA, outB = dot_oracle(e_M, ctx[0]), dot_oracle(e_M, ctx[1])
        assert len(Dec(outA)) != len(Dec(outB))
        if len(Dec(outA)) > len(Dec(outB)):
            i_tok, k_tok = ctx[0], ctx[1]
        else:
            i_tok, k_tok = ctx[1], ctx[0]

        # Step 7: a, b, d_I
        ab = list(Dec(d_K))
        a_tok = next(x for x in ab if dot_oracle(m_K, x) == top)
        b_tok = next(x for x in ab if x != a_tok)
        d_I = dot_oracle(e_D, i_tok)

        # Step 8: Triple
        known = {top, bot, e_I, d_K, m_K, m_I, e_M, e_D,
                 i_tok, k_tok, a_tok, b_tok, d_I, p_tok}
        remaining = [x for x in domain if x not in known]
        e_S = sC = e_Delta = None
        for f, g in itertools.product(remaining, repeat=2):
            h = dot_oracle(f, g)
            if h in (top, bot, p_tok):
                continue
            if dot_oracle(h, e_D) == d_I:
                e_S, sC, e_Delta = f, g, h
                break
        assert e_S is not None

        # Build result mapping: opaque_label -> true_element_index
        recovered = {
            "top": top, "bot": bot, "p": p_tok,
            "e_I": e_I, "e_D": e_D, "e_M": e_M,
            "e_Sigma": e_S, "e_Delta": e_Delta,
            "i": i_tok, "k": k_tok, "a": a_tok, "b": b_tok,
            "d_I": d_I, "d_K": d_K, "m_I": m_I, "m_K": m_K, "s_C": sC,
        }

        # Convert to role labels (in true element index space)
        pred_labels = [0] * N
        role_map = {
            "Booleans": ["top", "bot"],
            "Testers": ["e_I", "d_K", "m_K", "m_I"],
            "Encoders": ["e_D", "e_M"],
            "Context": ["i", "k"],
            "Kappa": ["a", "b"],
            "Synthesis": ["e_Sigma", "e_Delta", "s_C"],
            "Code": ["d_I"],
            "Default": ["p"],
        }
        role_names = list(role_map.keys())
        for ri, (role, members) in enumerate(role_map.items()):
            for m in members:
                opaque = recovered[m]
                true_idx = true_mapping[opaque]
                pred_labels[true_idx] = ri

        n_correct = sum(1 for name in ELEMENTS
                        if recovered.get(name) is not None
                        and true_mapping[recovered[name]] == IDX[name])
        return pred_labels, n_correct, 8

    except (AssertionError, StopIteration):
        return [0] * N, 0, 0


# ============================================================
# Section 4: K-Means
# ============================================================

def extract_representations(model):
    """Extract averaged hidden activations per element (17 × H matrix)."""
    reps = []
    model.eval()
    with torch.no_grad():
        for x in range(N):
            acts = []
            for y in range(N):
                inp = to_onehot_pair([x], [y])
                h = model.net[0](inp)
                h = model.net[1](h)
                acts.append(h.squeeze().numpy())
            reps.append(np.mean(acts, axis=0))
    return np.array(reps)


def kmeans_method(model):
    """K-Means clustering on hidden representations."""
    reps = extract_representations(model)
    km = KMeans(n_clusters=8, n_init=20, random_state=42)
    pred = km.fit_predict(reps)
    return pred


# ============================================================
# Section 5: Linear Probe
# ============================================================

def linear_probe(model, role_labels):
    """Leave-one-element-out linear probe for role prediction."""
    model.eval()
    # Extract activations for all 289 pairs
    all_acts = []
    all_roles = []
    all_left_idx = []
    with torch.no_grad():
        for x in range(N):
            for y in range(N):
                inp = to_onehot_pair([x], [y])
                h = model.net[0](inp)
                h = model.net[1](h)
                all_acts.append(h.squeeze().numpy())
                all_roles.append(role_labels[x])
                all_left_idx.append(x)

    X = np.array(all_acts)
    y = np.array(all_roles)
    left = np.array(all_left_idx)

    # Leave-one-element-out CV
    pred_per_element = {}
    for hold_out in range(N):
        train_mask = left != hold_out
        test_mask = left == hold_out
        if train_mask.sum() == 0 or test_mask.sum() == 0:
            continue
        scaler = StandardScaler()
        X_tr = scaler.fit_transform(X[train_mask])
        X_te = scaler.transform(X[test_mask])
        clf = LogisticRegression(C=1.0, max_iter=1000, random_state=42)
        clf.fit(X_tr, y[train_mask])
        preds = clf.predict(X_te)
        # Majority vote for this element
        from collections import Counter
        vote = Counter(preds).most_common(1)[0][0]
        pred_per_element[hold_out] = vote

    pred_labels = [pred_per_element.get(i, 0) for i in range(N)]
    return pred_labels


# ============================================================
# Section 6: Activation Patching
# ============================================================

def activation_patching(model):
    """Build causal similarity matrix via activation patching."""
    model.eval()

    # Precompute hidden activations and outputs for all (x, y) pairs
    hidden = {}  # (x, y) -> activation vector
    outputs = {}  # (x, y) -> predicted class

    with torch.no_grad():
        for x in range(N):
            for y in range(N):
                inp = to_onehot_pair([x], [y])
                h1 = model.net[1](model.net[0](inp))  # after first ReLU
                hidden[(x, y)] = h1.squeeze()
                out = model.net[4](model.net[3](model.net[2](h1)))
                outputs[(x, y)] = out.argmax(dim=1).item()

    # For each pair (x1, x2), measure causal interchangeability
    causal_sim = np.zeros((N, N))
    for x1 in range(N):
        for x2 in range(N):
            if x1 == x2:
                causal_sim[x1, x2] = 1.0
                continue
            matches = 0
            for z in range(N):
                # Replace x1's hidden with x2's hidden, run rest of network
                patched_h = hidden[(x2, z)]
                with torch.no_grad():
                    h2 = model.net[2](patched_h.unsqueeze(0))
                    h2 = model.net[3](h2)
                    out = model.net[4](h2)
                patched_pred = out.argmax(dim=1).item()
                if patched_pred == outputs[(x2, z)]:
                    matches += 1
            causal_sim[x1, x2] = matches / N

    # Spectral clustering on causal similarity
    # Make it symmetric
    sym = (causal_sim + causal_sim.T) / 2
    np.fill_diagonal(sym, 1.0)
    # Ensure non-negative for spectral clustering
    sym = np.maximum(sym, 0)

    try:
        sc = SpectralClustering(n_clusters=8, affinity="precomputed",
                                random_state=42, n_init=20)
        pred = sc.fit_predict(sym)
    except Exception:
        pred = np.zeros(N, dtype=int)

    return pred, causal_sim


# ============================================================
# Section 7: Run benchmark
# ============================================================

def run_benchmark():
    print("=" * 60)
    print("  INTERPRETABILITY BENCHMARK")
    print("  DS Recovery vs Standard Techniques")
    print("=" * 60)

    # --- Setup control algebra ---
    print("\n--- Setting up control algebra ---")
    dot_control, control_table = make_control_algebra(seed=42)
    ok, msg = verify_control(dot_control, control_table)
    if not ok:
        # Try different seeds
        for s in range(43, 100):
            dot_control, control_table = make_control_algebra(seed=s)
            ok, msg = verify_control(dot_control, control_table)
            if ok:
                print(f"  Using control seed {s}")
                break
    assert ok, f"Failed to generate valid control algebra: {msg}"
    print(f"  Control algebra verified: {msg}")

    # --- Train models ---
    print("\n--- Training Δ₁ models ---")
    d1_models, d1_X, d1_Y = train_models(dot_table, "delta1")

    print("\n--- Training Control models ---")
    ctrl_models, ctrl_X, ctrl_Y = train_models(dot_control, "control")

    # --- Run all methods ---
    results = {
        "DS Recovery": {"delta1": [], "control": []},
        "K-Means": {"delta1": [], "control": []},
        "Linear Probe": {"delta1": [], "control": []},
        "Activation Patching": {"delta1": [], "control": []},
    }

    # Also store detailed info for plots
    best_d1_causal_sim = None
    best_d1_kmeans_pred = None
    best_d1_acc = 0

    print("\n--- Running methods on Δ₁ ---")
    for trial, (model, acc, seed) in enumerate(d1_models):
        print(f"  Δ₁ trial {trial+1}/{NUM_TRIALS} (acc={acc:.4f}):")

        # DS Recovery
        pred_labels, n_correct, n_steps = ds_recovery(model, seed=seed + 1000)
        ari = adjusted_rand_score(DELTA1_LABELS, pred_labels) if n_correct > 0 else 0.0
        results["DS Recovery"]["delta1"].append({
            "ari": ari, "n_correct": n_correct, "n_steps": n_steps})
        print(f"    DS Recovery: ARI={ari:.3f}, {n_correct}/17 correct")

        # K-Means
        km_pred = kmeans_method(model)
        km_ari = adjusted_rand_score(DELTA1_LABELS, km_pred)
        results["K-Means"]["delta1"].append({"ari": km_ari, "pred": km_pred})
        print(f"    K-Means: ARI={km_ari:.3f}")

        # Linear Probe
        lp_pred = linear_probe(model, DELTA1_LABELS)
        lp_ari = adjusted_rand_score(DELTA1_LABELS, lp_pred)
        lp_acc = sum(1 for i in range(N) if lp_pred[i] == DELTA1_LABELS[i]) / N
        results["Linear Probe"]["delta1"].append({"ari": lp_ari, "accuracy": lp_acc})
        print(f"    Linear Probe: ARI={lp_ari:.3f}, acc={lp_acc:.3f}")

        # Activation Patching
        ap_pred, causal_sim = activation_patching(model)
        ap_ari = adjusted_rand_score(DELTA1_LABELS, ap_pred)
        results["Activation Patching"]["delta1"].append({
            "ari": ap_ari, "causal_sim": causal_sim})
        print(f"    Activation Patching: ARI={ap_ari:.3f}")

        if acc > best_d1_acc:
            best_d1_acc = acc
            best_d1_causal_sim = causal_sim
            best_d1_kmeans_pred = km_pred

    print("\n--- Running methods on Control ---")
    for trial, (model, acc, seed) in enumerate(ctrl_models):
        print(f"  Control trial {trial+1}/{NUM_TRIALS} (acc={acc:.4f}):")

        # DS Recovery (should fail)
        pred_labels, n_correct, n_steps = ds_recovery(model, seed=seed + 1000)
        ari = adjusted_rand_score(CONTROL_LABELS, pred_labels) if n_correct > 0 else 0.0
        results["DS Recovery"]["control"].append({
            "ari": ari, "n_correct": n_correct, "n_steps": n_steps})
        print(f"    DS Recovery: ARI={ari:.3f}, {n_correct}/17, steps={n_steps}")

        # K-Means
        km_pred = kmeans_method(model)
        km_ari = adjusted_rand_score(CONTROL_LABELS, km_pred)
        results["K-Means"]["control"].append({"ari": km_ari})
        print(f"    K-Means: ARI={km_ari:.3f}")

        # Linear Probe
        lp_pred = linear_probe(model, CONTROL_LABELS)
        lp_ari = adjusted_rand_score(CONTROL_LABELS, lp_pred)
        lp_acc = sum(1 for i in range(N) if lp_pred[i] == CONTROL_LABELS[i]) / N
        results["Linear Probe"]["control"].append({"ari": lp_ari, "accuracy": lp_acc})
        print(f"    Linear Probe: ARI={lp_ari:.3f}, acc={lp_acc:.3f}")

        # Activation Patching
        ap_pred, causal_sim = activation_patching(model)
        ap_ari = adjusted_rand_score(CONTROL_LABELS, ap_pred)
        results["Activation Patching"]["control"].append({"ari": ap_ari})
        print(f"    Activation Patching: ARI={ap_ari:.3f}")

    return results, best_d1_causal_sim, best_d1_kmeans_pred


# ============================================================
# Section 8: Visualization
# ============================================================

def plot_main_comparison(results):
    """Grouped bar chart: ARI by method, Δ₁ vs Control."""
    methods = ["DS Recovery", "K-Means", "Linear Probe", "Activation Patching"]
    fig, ax = plt.subplots(figsize=(10, 6))

    x = np.arange(len(methods))
    width = 0.35

    d1_means = [np.mean([t["ari"] for t in results[m]["delta1"]]) for m in methods]
    d1_stds = [np.std([t["ari"] for t in results[m]["delta1"]]) for m in methods]
    ctrl_means = [np.mean([t["ari"] for t in results[m]["control"]]) for m in methods]
    ctrl_stds = [np.std([t["ari"] for t in results[m]["control"]]) for m in methods]

    bars1 = ax.bar(x - width/2, d1_means, width, yerr=d1_stds, label="Δ₁",
                   color="#4C9AFF", capsize=4)
    bars2 = ax.bar(x + width/2, ctrl_means, width, yerr=ctrl_stds, label="Control",
                   color="#FF8A65", capsize=4)

    ax.set_ylabel("Adjusted Rand Index", fontsize=11)
    ax.set_title("Interpretability Method Comparison:\nSelf-Modeling vs Control Algebra",
                 fontsize=13, fontweight="bold")
    ax.set_xticks(x)
    ax.set_xticklabels(methods, fontsize=9)
    ax.legend(fontsize=10)
    ax.axhline(0, color="gray", lw=0.5, ls="--")
    ax.set_ylim(-0.15, 1.15)

    # Annotate values
    for bars, means in [(bars1, d1_means), (bars2, ctrl_means)]:
        for bar, m in zip(bars, means):
            ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.03,
                    f"{m:.2f}", ha="center", va="bottom", fontsize=8)

    plt.tight_layout()
    plt.savefig("benchmark_results.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved benchmark_results.png")


def plot_detail(results, causal_sim, kmeans_pred):
    """Four-panel detailed analysis."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 11))
    fig.suptitle("Detailed Benchmark Analysis", fontsize=14, fontweight="bold")

    # Top-left: Role recovery accuracy by method (Δ₁)
    ax = axes[0, 0]
    methods = ["DS Recovery", "K-Means", "Linear Probe", "Activation Patching"]
    d1_aris = [np.mean([t["ari"] for t in results[m]["delta1"]]) for m in methods]
    colors = ["#4C9AFF", "#66BB6A", "#FF8A65", "#AB47BC"]
    ax.bar(range(len(methods)), d1_aris, color=colors)
    ax.set_xticks(range(len(methods)))
    ax.set_xticklabels(methods, fontsize=8, rotation=15, ha="right")
    ax.set_ylabel("ARI")
    ax.set_title("Role Recovery (Δ₁): Mean ARI by Method", fontsize=10)
    ax.set_ylim(0, 1.1)
    for i, v in enumerate(d1_aris):
        ax.text(i, v + 0.02, f"{v:.2f}", ha="center", fontsize=9)

    # Top-right: Causal similarity heatmap (Δ₁, best trial)
    ax = axes[0, 1]
    if causal_sim is not None:
        order = [IDX[n] for n in PLOT_ORDER]
        reordered = causal_sim[np.ix_(order, order)]
        im = ax.imshow(reordered, cmap="viridis", vmin=0, vmax=1, aspect="equal")
        ax.set_xticks(range(N))
        ax.set_xticklabels(PLOT_ORDER, fontsize=5, rotation=60, ha="right")
        ax.set_yticks(range(N))
        ax.set_yticklabels(PLOT_ORDER, fontsize=5)
        fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
    ax.set_title("Causal Similarity (Δ₁, best trial)", fontsize=10)

    # Bottom-left: K-Means confusion matrix (Δ₁, best trial)
    ax = axes[1, 0]
    if kmeans_pred is not None:
        role_names = list(DELTA1_ROLES.keys())
        n_roles = len(role_names)
        n_clusters = 8
        conf = np.zeros((n_roles, n_clusters))
        for elem in range(N):
            true_role = DELTA1_LABELS[elem]
            cluster = kmeans_pred[elem]
            conf[true_role, cluster] += 1
        im = ax.imshow(conf, cmap="Blues", aspect="auto")
        ax.set_xticks(range(n_clusters))
        ax.set_xticklabels([f"C{i}" for i in range(n_clusters)], fontsize=8)
        ax.set_yticks(range(n_roles))
        ax.set_yticklabels(role_names, fontsize=8)
        ax.set_xlabel("K-Means Cluster")
        ax.set_ylabel("True Role")
        for i in range(n_roles):
            for j in range(n_clusters):
                v = int(conf[i, j])
                if v > 0:
                    ax.text(j, i, str(v), ha="center", va="center", fontsize=9,
                            color="white" if v > 1 else "black")
        fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
    ax.set_title("K-Means Confusion (Δ₁, best trial)", fontsize=10)

    # Bottom-right: Control — all methods ARI distribution
    ax = axes[1, 1]
    methods_short = ["DS\nRecovery", "K-Means", "Linear\nProbe", "Act.\nPatching"]
    ctrl_data = [[t["ari"] for t in results[m]["control"]] for m in
                 ["DS Recovery", "K-Means", "Linear Probe", "Activation Patching"]]
    bp = ax.boxplot(ctrl_data, labels=methods_short, patch_artist=True)
    for patch, c in zip(bp["boxes"], colors):
        patch.set_facecolor(c)
        patch.set_alpha(0.5)
    ax.axhline(0, color="gray", lw=0.5, ls="--")
    ax.set_ylabel("ARI")
    ax.set_title("Control Algebra: All Methods\n(no structure to find)", fontsize=10)

    plt.tight_layout()
    plt.savefig("benchmark_detail.png", dpi=200, bbox_inches="tight")
    plt.close()
    print("  Saved benchmark_detail.png")


def write_table(results):
    methods = ["DS Recovery", "K-Means", "Linear Probe", "Activation Patching"]
    lines = []
    header = f"{'Method':<22} | {'Δ₁ ARI':>14} | {'Control ARI':>14} | {'Selectivity':>12}"
    lines.append(header)
    lines.append("-" * len(header))

    selectivity = {}
    for m in methods:
        d1_aris = [t["ari"] for t in results[m]["delta1"]]
        ctrl_aris = [t["ari"] for t in results[m]["control"]]
        d1_str = f"{np.mean(d1_aris):.3f} ± {np.std(d1_aris):.3f}"
        ctrl_str = f"{np.mean(ctrl_aris):.3f} ± {np.std(ctrl_aris):.3f}"
        sel = np.mean(d1_aris) - np.mean(ctrl_aris)
        selectivity[m] = sel
        lines.append(f"{m:<22} | {d1_str:>14} | {ctrl_str:>14} | {sel:>12.3f}")

    table = "\n".join(lines)
    with open("benchmark_table.txt", "w") as f:
        f.write(table + "\n")
    print("  Saved benchmark_table.txt")
    print()
    print(table)

    # Selectivity index
    print("\nSelectivity Index (higher = better at distinguishing structure from noise):")
    ranked = sorted(selectivity.items(), key=lambda x: -x[1])
    with open("selectivity_index.txt", "w") as f:
        f.write("Selectivity Index (higher = better at distinguishing structure from noise):\n")
        for i, (m, s) in enumerate(ranked):
            line = f"  {i+1}. {m:<22} {s:.3f}"
            print(line)
            f.write(line + "\n")
    print("  Saved selectivity_index.txt")


# ============================================================
# Section 9: Main
# ============================================================

def main():
    results, causal_sim, kmeans_pred = run_benchmark()

    print("\n--- Generating outputs ---")
    plot_main_comparison(results)
    plot_detail(results, causal_sim, kmeans_pred)
    write_table(results)

    print("\n" + "=" * 60)
    print("  BENCHMARK COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()

# Δ₁ Dot-Learner: Neural Network Experiment

## Goal

Train a small neural network to learn Δ₁'s `dot` operation from examples, then run the true black-box recovery procedure on the trained network to see if the algebraic structure is recoverable from learned behavior.

This is a proof-of-concept for applying Distinction Structure recovery to neural network interpretability.

## Environment

- M1 MacBook Pro
- Python 3.11+
- PyTorch (with MPS available but CPU is fine — the model is tiny)
- Install: `pip install torch numpy matplotlib`

## What to Build

A single Python file `dot_learner.py` with three phases:

### Phase 1: Data Generation & Training

Generate all 289 training examples (17 × 17 input pairs → 17 output classes) from the Δ₁ dot operation.

The dot operation is defined by first-match priority on these rules:

```
Block A — Boolean absorption:
  top · y = top (for all y)
  bot · y = bot (for all y)

Block B — Testers:
  e_I · i = top,  e_I · k = top,  e_I · _ = bot
  d_K · a = top,  d_K · b = top,  d_K · _ = bot
  m_K · a = top,  m_K · _ = bot
  m_I · p = bot,  m_I · _ = top

Block C — Structural encoders:
  e_D · i = d_I,  e_D · k = d_K
  e_M · i = m_I,  e_M · k = m_K
  e_Sigma · s_C = e_Delta
  e_Delta · e_D = d_I

Block D — Absorption breaker:
  p · top = top

Block E — Passive self-identification:
  i · top = i,  k · top = k,  a · top = a,  b · top = b
  d_I · top = d_I,  s_C · top = s_C

Block F — Default:
  x · y = p (all remaining pairs)
```

The 17 elements in order (used as class indices 0–16):

```python
ELEMENTS = ["top", "bot", "i", "k", "a", "b", "e_I",
            "e_D", "e_M", "e_Sigma", "e_Delta",
            "d_I", "d_K", "m_I", "m_K", "s_C", "p"]
```

**Input representation:** Concatenation of two one-hot vectors → 34-dimensional input.

**Output:** Class index (0–16) for cross-entropy loss.

**Network architecture:** A simple MLP. Start with:
```
Linear(34, 128) → ReLU → Linear(128, 128) → ReLU → Linear(128, 17)
```

This is deliberately over-parameterized for 289 examples. The network should reach 100% training accuracy easily. We want perfect learning so we can test recovery on exact behavior.

**Training:**
- Use Adam optimizer, lr=0.001
- Cross-entropy loss
- Train until 100% accuracy on all 289 pairs (should take < 1000 epochs)
- Print loss and accuracy every 100 epochs
- Stop early if 100% accuracy achieved
- Use CPU (it's fast enough)

### Phase 2: Black-Box Recovery on Learned Network

After training, treat the network as a black box:

1. Create 17 "opaque labels" (shuffled indices or random names)
2. Define a `dot_nn(x, y)` function that:
   - Converts x, y to one-hot vectors
   - Runs the network forward pass (with torch.no_grad())
   - Takes argmax of output
   - Returns the predicted class index
3. Run the recovery procedure from `delta2_true_blackbox.py` (Phase 1 only — we're not testing QUOTE/EVAL) on `dot_nn`
4. Verify that recovered labels match ground truth

**IMPORTANT:** The recovery procedure must NOT use any knowledge of the network's weights, architecture, or training data. It only calls `dot_nn(x, y)` and observes outputs. This is the whole point — the network is a black box, just like the shuffled algebra.

**What to check:**
- Does the recovery procedure identify all 17 elements correctly?
- How many of the 8 recovery steps succeed?
- If any step fails, which one and why? (This would indicate the network learned a slightly different function, which is itself interesting.)

### Phase 3: Representation Analysis (the interesting part)

After recovery, analyze the network's internal representations:

1. **Extract hidden activations:** For each of the 17 elements used as LEFT argument (with a fixed right argument, e.g., top), extract the hidden layer activations after the first ReLU. This gives a 128-dimensional vector for each element.

2. **Cluster by algebraic role:** The recovery procedure identifies algebraic roles:
   - Booleans: {top, bot}
   - Testers: {e_I, d_K, m_K, m_I}
   - Encoders: {e_D, e_M}
   - Context tokens: {i, k}
   - κ-encodings: {a, b}
   - Synthesis elements: {e_Sigma, e_Delta, s_C}
   - Codes: {d_I, d_K, m_I, m_K}
   - Default: {p}

3. **Visualize with PCA or t-SNE:** Project the 128-dimensional hidden activations to 2D. Color-code by algebraic role (recovered from the black-box procedure). Save as `representations.png`.

4. **Measure clustering:** Compute average within-role distance vs. between-role distance for the hidden representations. If the ratio is < 1, the network has learned to cluster elements by their algebraic role.

5. **Representational similarity analysis:** Compute the 17×17 matrix of cosine similarities between hidden activations. Compare this to the 17×17 "behavioral similarity" matrix (fraction of shared outputs: sim(x,y) = |{z : dot(x,z) = dot(y,z)}| / 17). Plot both as heatmaps side by side. Save as `similarity.png`.

The key question: **does the network's internal geometry reflect the algebraic structure that the recovery procedure identifies?**

## Output

The script should produce:
1. Training log (loss, accuracy per epoch)
2. Recovery results (all 17 elements identified with ✓/✗)
3. `representations.png` — PCA/t-SNE of hidden activations colored by algebraic role
4. `similarity.png` — side-by-side heatmaps of representational vs behavioral similarity
5. A summary: "Recovery succeeded: X/17 elements correctly identified. Representation clustering ratio: Y."

## Code Structure

```python
# ============================================================
# Section 1: Δ₁ definition and data generation
# ============================================================
# - ELEMENTS list (17 elements, indices 0-16)
# - dot(x, y) -> z function on indices
# - Generate all 289 (x, y, z) triples
# - Create one-hot encoded training tensors

# ============================================================
# Section 2: Network definition and training
# ============================================================
# - DotNet(nn.Module) — 3-layer MLP
# - Training loop targeting 100% accuracy
# - Save trained model

# ============================================================
# Section 3: Black-box recovery
# ============================================================
# - dot_nn(x, y) wrapper using trained network
# - Shuffle element indices into opaque labels
# - Run 8-step recovery procedure (adapted from delta2_true_blackbox.py)
# - Verify against ground truth

# ============================================================
# Section 4: Representation analysis
# ============================================================
# - Extract hidden activations
# - PCA/t-SNE visualization
# - Clustering metrics
# - Similarity heatmaps

# ============================================================
# Section 5: Main
# ============================================================
```

## Important Notes

- The dot function must EXACTLY match Δ₁'s 26 rules. The Python recovery procedure and the Lean proof both depend on the exact operation table. Double-check by generating all 289 outputs and verifying key properties:
  - Exactly 2 left-absorbers (top, bot)
  - Exactly 4 testers (e_I, d_K, m_K, m_I)
  - dot(e_D, i) = d_I, dot(e_D, k) = d_K (H1)
  - dot(e_Sigma, s_C) = e_Delta (H3)

- The recovery procedure needs to be adapted to work on integer indices rather than string labels, but the logic is identical to delta2_true_blackbox.py Phase 1.

- For the representation analysis, use the activations AFTER the first hidden layer (after ReLU), not the raw input or the output logits. The first hidden layer is where the network builds its internal representation of each element.

- If the network doesn't reach 100% accuracy, increase hidden size or training epochs. The function is deterministic and has only 289 examples — any reasonably sized network should memorize it perfectly.

## Success Criteria

**Minimum:** Network trains to 100% accuracy. Recovery procedure succeeds on all 17 elements.

**Interesting:** Hidden representations cluster by algebraic role (booleans cluster together, testers cluster together, etc.).

**Exciting:** Representational similarity matrix correlates with behavioral similarity matrix, showing the network's internal geometry mirrors the algebraic structure.

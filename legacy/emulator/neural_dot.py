"""
Neural Cayley Table — MLP implementation of the Kamea dot operation.

A 3-layer MLP that learns the canonical fingerprint Cayley table.
Takes two one-hot fingerprint vectors, outputs probability over 66 fingerprints.
"""

from __future__ import annotations

import time
from pathlib import Path

import torch
import torch.nn as nn
import torch.optim as optim

from .fingerprint import NUM_FP
from . import cayley


class CayleyMLP(nn.Module):
    """3-layer MLP: concat one-hots → hidden → hidden → logits."""

    def __init__(self, hidden_dim: int = 128):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(NUM_FP * 2, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, NUM_FP),
        )
        self._init_weights()

    def _init_weights(self):
        for m in self.modules():
            if isinstance(m, nn.Linear):
                nn.init.xavier_uniform_(m.weight)
                nn.init.zeros_(m.bias)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


def _build_dataset() -> tuple[torch.Tensor, torch.Tensor]:
    """Build training data from the canonical fingerprint ROM.

    Returns (inputs, targets) where:
      inputs:  (4356, 132) float tensor of concatenated one-hot pairs
      targets: (4356,) long tensor of target fingerprint indices
    """
    rom = cayley.build_fingerprint_rom()
    n = NUM_FP
    inputs = torch.zeros(n * n, n * 2)
    targets = torch.zeros(n * n, dtype=torch.long)

    for x_fp in range(n):
        for y_fp in range(n):
            idx = x_fp * n + y_fp
            inputs[idx, x_fp] = 1.0
            inputs[idx, n + y_fp] = 1.0
            targets[idx] = rom[idx]

    return inputs, targets


class NeuralCayleyTable:
    """Wraps a CayleyMLP with training, inference, and persistence."""

    def __init__(self, hidden_dim: int = 128, device: str | None = None):
        if device is None:
            device = "mps" if torch.backends.mps.is_available() else "cpu"
        self.device = torch.device(device)
        self.hidden_dim = hidden_dim
        self.model = CayleyMLP(hidden_dim).to(self.device)
        self._trained = False
        self._epochs_to_converge = 0
        self._training_time = 0.0

        # Pre-build one-hot cache for fast inference
        self._onehot_cache = torch.eye(NUM_FP, device=self.device)

    def train(self, epochs: int = 5000, lr: float = 1e-3,
              target_accuracy: float = 1.0, print_every: int = 0) -> dict:
        """Train on all 4,356 pairs until target accuracy or max epochs.

        Uses full-batch Adam (dataset is small enough). Xavier initialization
        on the model helps larger dims converge faster.
        Returns dict with training stats.
        """
        inputs, targets = _build_dataset()
        inputs = inputs.to(self.device)
        targets = targets.to(self.device)

        self.model.train()
        optimizer = optim.Adam(self.model.parameters(), lr=lr)
        loss_fn = nn.CrossEntropyLoss()

        start = time.time()
        final_loss = 0.0
        final_acc = 0.0

        for epoch in range(1, epochs + 1):
            optimizer.zero_grad()
            logits = self.model(inputs)
            loss = loss_fn(logits, targets)
            loss.backward()
            optimizer.step()

            final_loss = loss.item()

            if epoch % max(1, epochs // 50) == 0 or epoch == epochs:
                with torch.no_grad():
                    preds = logits.argmax(dim=1)
                    correct = (preds == targets).sum().item()
                    final_acc = correct / len(targets)

                if print_every and epoch % print_every == 0:
                    print(f"  epoch {epoch:5d}  loss={final_loss:.4f}  "
                          f"acc={final_acc:.4f} ({correct}/{len(targets)})")

                if final_acc >= target_accuracy:
                    self._epochs_to_converge = epoch
                    break
        else:
            self._epochs_to_converge = epochs

        elapsed = time.time() - start
        self._training_time = elapsed
        self._trained = True
        self.model.eval()

        return {
            "epochs": self._epochs_to_converge,
            "final_loss": final_loss,
            "final_accuracy": final_acc,
            "training_time": elapsed,
            "parameters": self.parameter_count(),
        }

    @torch.no_grad()
    def dot(self, fp_x: int, fp_y: int) -> int:
        """Compute dot(fp_x, fp_y) via network inference."""
        inp = torch.cat([self._onehot_cache[fp_x],
                         self._onehot_cache[fp_y]]).unsqueeze(0)
        logits = self.model(inp)
        return logits.argmax(dim=1).item()

    @torch.no_grad()
    def accuracy(self) -> tuple[float, int, int]:
        """Test all 4,356 pairs. Returns (accuracy, correct, total)."""
        inputs, targets = _build_dataset()
        inputs = inputs.to(self.device)
        targets = targets.to(self.device)

        self.model.eval()
        logits = self.model(inputs)
        preds = logits.argmax(dim=1)
        correct = (preds == targets).sum().item()
        total = len(targets)
        return correct / total, correct, total

    def parameter_count(self) -> int:
        """Total trainable parameters."""
        return sum(p.numel() for p in self.model.parameters() if p.requires_grad)

    def save(self, path: str | Path):
        """Save trained weights."""
        torch.save({
            "hidden_dim": self.hidden_dim,
            "state_dict": self.model.state_dict(),
            "epochs": self._epochs_to_converge,
        }, path)

    @classmethod
    def load(cls, path: str | Path, device: str | None = None) -> "NeuralCayleyTable":
        """Load trained weights."""
        checkpoint = torch.load(path, map_location="cpu", weights_only=True)
        table = cls(hidden_dim=checkpoint["hidden_dim"], device=device)
        table.model.load_state_dict(checkpoint["state_dict"])
        table.model.eval()
        table._trained = True
        table._epochs_to_converge = checkpoint.get("epochs", 0)
        return table

    @property
    def trained(self) -> bool:
        return self._trained

    @property
    def compression_ratio(self) -> float:
        """Table entries / parameters. >1 means compressed."""
        params = self.parameter_count()
        return (NUM_FP * NUM_FP) / params if params > 0 else 0.0

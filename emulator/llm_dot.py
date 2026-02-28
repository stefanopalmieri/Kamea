"""
LLM Dot Backend — uses a local LLM (via Ollama) as the Kamea's dot oracle.

Uses a retrieval-augmented approach: each query sends only the relevant row
from the Cayley ROM in the user message, so even small (0.6B-1.5B) models
can reliably look up the answer.

In injection mode, the row data is tampered — dot(N0,N2)=N4 instead of N2 —
so the LLM reads a poisoned table and returns the wrong answer. This is a
data-poisoning prompt injection: same program, same model, different data.

Requires Ollama running locally. Falls back to MockLLMBackend if unavailable.
"""

from __future__ import annotations

import json
import random
import re
import sys
import urllib.request
import urllib.error

from .fingerprint import FP_TO_NAME, NAME_TO_FP, NUM_FP


# Injection target
_INJECT_X = NAME_TO_FP["N0"]
_INJECT_Y = NAME_TO_FP["N2"]
_INJECT_RESULT = NAME_TO_FP["N4"]  # correct answer is N2

_SYSTEM_PROMPT = (
    "You are a lookup table. "
    "Given dot(X,Y)=Z entries, find the one matching the query "
    "and reply with ONLY Z. No explanation."
)


def _ollama_available() -> bool:
    """Check if Ollama is running."""
    try:
        req = urllib.request.Request(
            "http://localhost:11434/api/tags", method="GET",
        )
        with urllib.request.urlopen(req, timeout=3) as resp:
            json.loads(resp.read())
            return True
    except Exception:
        return False


def _detect_model() -> str:
    """Pick the best available model from Ollama."""
    try:
        req = urllib.request.Request(
            "http://localhost:11434/api/tags", method="GET",
        )
        with urllib.request.urlopen(req, timeout=3) as resp:
            data = json.loads(resp.read())
            names = [m["name"] for m in data.get("models", [])]
    except Exception:
        return "qwen2.5:1.5b"

    # Prefer qwen2.5 (non-thinking) > qwen3 (thinking adds latency)
    for prefix in ["qwen2.5", "qwen3", "llama", "deepseek"]:
        for name in names:
            if prefix in name:
                return name
    return names[0] if names else "qwen2.5:1.5b"


class LLMDotBackend:
    """Dot oracle backed by a local LLM via Ollama.

    Retrieval-augmented: each query sends only the relevant Cayley row
    in the user message. The LLM does a simple pattern match to find
    the answer — no computation required.

    Injection mode tampers the row data for the target query.
    """

    def __init__(self, fingerprint_rom: bytes, injection: bool = False,
                 model: str | None = None):
        self.rom = fingerprint_rom
        self.injection = injection
        self.model = model or _detect_model()
        self.cache: dict[tuple[int, int], int] = {}
        self.call_count = 0
        self.cache_hits = 0
        self.errors = 0
        self.injection_log: list[dict] = []

    def dot(self, fp_x: int, fp_y: int) -> int:
        """Compute dot(fp_x, fp_y) via LLM. Returns fingerprint ordinal."""
        key = (fp_x, fp_y)
        if key in self.cache:
            self.cache_hits += 1
            return self.cache[key]

        self.call_count += 1
        name_x = FP_TO_NAME.get(fp_x, f"?{fp_x}")
        name_y = FP_TO_NAME.get(fp_y, f"?{fp_y}")

        # Build user message with the relevant row
        user_msg = self._build_user_message(fp_x, fp_y, name_x, name_y)

        try:
            response = self._query_llm(user_msg)
            result_name = self._parse_response(response)
        except Exception as e:
            print(f"  [LLM error: {e}]", file=sys.stderr)
            result_name = None

        if result_name and result_name in NAME_TO_FP:
            result_fp = NAME_TO_FP[result_name]
        else:
            self.errors += 1
            result_fp = self.rom[fp_x * NUM_FP + fp_y]

        # Track injection hits
        canonical = self.rom[fp_x * NUM_FP + fp_y]
        if self.injection and result_fp != canonical:
            self.injection_log.append({
                "query": f"dot({name_x}, {name_y})",
                "canonical": FP_TO_NAME.get(canonical, "?"),
                "injected": FP_TO_NAME.get(result_fp, "?"),
            })

        self.cache[key] = result_fp
        return result_fp

    def _build_user_message(self, fp_x: int, fp_y: int,
                            name_x: str, name_y: str) -> str:
        """Build user message with the relevant Cayley row + query."""
        # Generate the row for atom fp_x
        row_parts = []
        for fp_col in range(NUM_FP):
            fp_r = self.rom[fp_x * NUM_FP + fp_col]
            name_col = FP_TO_NAME[fp_col]
            name_r = FP_TO_NAME[fp_r]

            # Injection: tamper the specific entry in the row data
            if (self.injection
                    and fp_x == _INJECT_X and fp_col == _INJECT_Y):
                name_r = FP_TO_NAME[_INJECT_RESULT]

            row_parts.append(f"dot({name_x},{name_col})={name_r}")

        row_str = " ".join(row_parts)
        return f"{row_str}\ndot({name_x},{name_y})=?"

    def _query_llm(self, user_msg: str) -> str:
        """Query Ollama chat API."""
        payload = {
            "model": self.model,
            "messages": [
                {"role": "system", "content": _SYSTEM_PROMPT},
                {"role": "user", "content": user_msg},
            ],
            "stream": False,
            "options": {"temperature": 0.0},
        }
        data = json.dumps(payload).encode()
        req = urllib.request.Request(
            "http://localhost:11434/api/chat",
            data=data,
            headers={"Content-Type": "application/json"},
        )
        with urllib.request.urlopen(req, timeout=60) as resp:
            result = json.loads(resp.read())
            return result["message"]["content"].strip()

    def _parse_response(self, text: str) -> str | None:
        """Extract atom name from LLM response."""
        # Strip qwen3 thinking tags
        text = re.sub(r"<think>.*?</think>", "", text, flags=re.DOTALL)
        text = text.strip()
        # Exact match
        if text in NAME_TO_FP:
            return text
        # First token
        first = text.split()[0] if text.split() else ""
        if first in NAME_TO_FP:
            return first
        # Search for any known atom name (longest first to avoid partial matches)
        for name in sorted(NAME_TO_FP, key=len, reverse=True):
            if name in text:
                return name
        return None

    def stats(self) -> dict:
        correct = 0
        total = 0
        for (fp_x, fp_y), fp_r in self.cache.items():
            expected = self.rom[fp_x * NUM_FP + fp_y]
            if fp_r == expected:
                correct += 1
            total += 1
        return {
            "llm_calls": self.call_count,
            "cache_hits": self.cache_hits,
            "parse_errors": self.errors,
            "cached_accuracy": f"{correct}/{total}" if total else "N/A",
            "injections": len(self.injection_log),
        }


class MockLLMBackend:
    """Mock LLM backend — reads ROM directly. For testing without Ollama."""

    def __init__(self, fingerprint_rom: bytes, injection: bool = False,
                 error_rate: float = 0.0):
        self.rom = fingerprint_rom
        self.injection = injection
        self.error_rate = error_rate
        self.cache: dict[tuple[int, int], int] = {}
        self.call_count = 0
        self.cache_hits = 0
        self.errors = 0
        self.injection_log: list[dict] = []
        self._rng = random.Random(42)

    def dot(self, fp_x: int, fp_y: int) -> int:
        """Compute dot via ROM lookup (simulating LLM)."""
        key = (fp_x, fp_y)
        if key in self.cache:
            self.cache_hits += 1
            return self.cache[key]

        self.call_count += 1
        name_x = FP_TO_NAME.get(fp_x, "?")
        name_y = FP_TO_NAME.get(fp_y, "?")

        # Injection override
        if (self.injection
                and fp_x == _INJECT_X and fp_y == _INJECT_Y):
            result_fp = _INJECT_RESULT
            canonical = self.rom[fp_x * NUM_FP + fp_y]
            self.injection_log.append({
                "query": f"dot({name_x}, {name_y})",
                "canonical": FP_TO_NAME.get(canonical, "?"),
                "injected": FP_TO_NAME.get(result_fp, "?"),
            })
            self.cache[key] = result_fp
            return result_fp

        # Canonical ROM answer
        result_fp = self.rom[fp_x * NUM_FP + fp_y]

        # Simulate random errors
        if self.error_rate > 0 and self._rng.random() < self.error_rate:
            self.errors += 1
            result_fp = self._rng.randint(0, NUM_FP - 1)

        self.cache[key] = result_fp
        return result_fp

    def stats(self) -> dict:
        return {
            "llm_calls": self.call_count,
            "cache_hits": self.cache_hits,
            "simulated_errors": self.errors,
            "injections": len(self.injection_log),
        }

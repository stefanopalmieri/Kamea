#!/usr/bin/env python3
"""
Bi-directional black-box discovery demo over multiprocessing pipes.

Protocol surface per party:
  - domain() -> opaque tokens
  - dot(x, y) -> opaque token/term

No table export or semantic labels are used during discovery.
Each side first treats the other as a black box, recovers Δ1 roles,
then executes host-native operations via the recovered mapping.
"""

from __future__ import annotations

import random
import sys
from dataclasses import dataclass
from multiprocessing import Pipe, Process
from pathlib import Path
from typing import Any

# Allow imports from repository root when launched via examples/ path.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from delta2_true_blackbox import ALL_ATOMS, Atom, discover_d1, dot_iota


D1_NAMES = [
    "⊤",
    "⊥",
    "i",
    "k",
    "a",
    "b",
    "e_I",
    "e_D",
    "e_M",
    "e_Σ",
    "e_Δ",
    "d_I",
    "d_K",
    "m_I",
    "m_K",
    "s_C",
    "p",
]


def make_prefixed_blackbox(seed: int, prefix: str):
    """Create a shuffled hidden-token algebra with only dot access."""
    rng = random.Random(seed)
    atoms = ALL_ATOMS.copy()
    rng.shuffle(atoms)
    labels = [f"{prefix}{idx:02d}" for idx in range(len(atoms))]

    true_to_hidden = {atoms[i]: labels[i] for i in range(len(atoms))}
    hidden_to_true = {labels[i]: atoms[i] for i in range(len(atoms))}
    domain = labels.copy()

    def to_true(v: Any) -> Any:
        return hidden_to_true[v] if isinstance(v, str) and v in hidden_to_true else v

    def to_hidden(v: Any) -> Any:
        return true_to_hidden[v] if isinstance(v, Atom) else v

    def dot_oracle(xh: Any, yh: Any) -> Any:
        return to_hidden(dot_iota(to_true(xh), to_true(yh)))

    d1_truth = {name: true_to_hidden[Atom(name)] for name in D1_NAMES}
    return domain, dot_oracle, d1_truth


def server_main(conn, seed: int, prefix: str):
    """Party server: responds only to domain/dot (+ optional reveal for verification)."""
    domain, dot_oracle, d1_truth = make_prefixed_blackbox(seed, prefix)

    while True:
        msg = conn.recv()
        cmd = msg.get("cmd")

        if cmd == "domain":
            conn.send({"ok": True, "domain": domain})
            continue

        if cmd == "dot":
            x = msg.get("x")
            y = msg.get("y")
            conn.send({"ok": True, "value": dot_oracle(x, y)})
            continue

        if cmd == "reveal_d1":
            conn.send({"ok": True, "mapping": d1_truth})
            continue

        if cmd == "shutdown":
            conn.send({"ok": True})
            break

        conn.send({"ok": False, "error": f"unknown command: {cmd}"})


@dataclass
class RemoteDot:
    name: str
    conn: Any

    def _request(self, cmd: str, **payload) -> dict[str, Any]:
        self.conn.send({"cmd": cmd, **payload})
        resp = self.conn.recv()
        if not resp.get("ok"):
            raise RuntimeError(f"{self.name} request failed: {resp.get('error')}")
        return resp

    def domain(self) -> list[str]:
        return list(self._request("domain")["domain"])

    def dot(self, x: Any, y: Any) -> Any:
        return self._request("dot", x=x, y=y)["value"]

    def reveal_d1(self) -> dict[str, str]:
        return dict(self._request("reveal_d1")["mapping"])

    def shutdown(self) -> None:
        self._request("shutdown")


def check_recovery(label: str, recovered: dict[str, Any], truth: dict[str, str]) -> None:
    mismatches = [k for k in D1_NAMES if recovered[k] != truth[k]]
    if mismatches:
        print(f"[{label}] recovery mismatch on: {mismatches}")
    else:
        print(f"[{label}] recovery check: exact match on all 17 Δ1 roles")


def switched_ops_demo(actor: str, target: str, remote: RemoteDot, rec: dict[str, Any]) -> None:
    # After discovery, use recovered semantic roles to issue host-native token ops.
    out1 = remote.dot(rec["e_M"], rec["i"])
    out2 = remote.dot(out1, rec["p"])
    print(f"[{actor}] {target} dot(e_M, i) -> {out1} (expected m_I={rec['m_I']})")
    print(f"[{actor}] {target} dot(m_I, p) -> {out2} (expected ⊥={rec['⊥']})")


def main() -> None:
    host_parent, host_child = Pipe()
    client_parent, client_child = Pipe()

    host_proc = Process(target=server_main, args=(host_child, 17, "h"), daemon=True)
    client_proc = Process(target=server_main, args=(client_child, 29, "c"), daemon=True)
    host_proc.start()
    client_proc.start()

    host_remote = RemoteDot("host", host_parent)
    client_remote = RemoteDot("client", client_parent)

    try:
        print("Phase 1: client-role discovers host-role")
        host_domain = host_remote.domain()
        rec_host = discover_d1(host_domain, host_remote.dot)
        switched_ops_demo("client", "host", host_remote, rec_host)
        check_recovery("client->host", rec_host, host_remote.reveal_d1())

        print("\nPhase 2: host-role discovers client-role")
        client_domain = client_remote.domain()
        rec_client = discover_d1(client_domain, client_remote.dot)
        switched_ops_demo("host", "client", client_remote, rec_client)
        check_recovery("host->client", rec_client, client_remote.reveal_d1())

    finally:
        try:
            host_remote.shutdown()
        except Exception:
            pass
        try:
            client_remote.shutdown()
        except Exception:
            pass

        host_proc.join(timeout=2)
        client_proc.join(timeout=2)


if __name__ == "__main__":
    main()

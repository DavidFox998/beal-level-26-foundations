#!/usr/bin/env python3
"""Verify the archived coefficient ledger without network-dependent fallbacks."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

LEDGER = Path("sagemath/level_26_ledger.json")
EXPECTED_SHA256 = "9671052435714618d8106b25ed3f04fd7b87d5332ebccf76f949f768276c6875"


def main() -> None:
    raw = LEDGER.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256

    data = json.loads(raw)
    assert data["version"] == "v1.3.0"
    assert data["previous"] == "v1.2.1"
    assert data["level"] == 26
    assert data["dim"] == 2
    assert [form["label"] for form in data["forms"]] == ["26a1", "26b1"]
    assert all(len(form["qexp"]) == 101 for form in data["forms"])
    assert data["forms"][0]["qexp"][:3] == [0, 1, -1]
    assert data["forms"][1]["qexp"][:3] == [0, 1, 1]
    assert data["certs"] == [
        "sagemath/certs/j0_26_decomposition.json",
        "sagemath/certs/formal_immersion_M3.json",
    ]

    print(f"verified level-26 coefficient ledger; sha256={EXPECTED_SHA256}")


if __name__ == "__main__":
    main()

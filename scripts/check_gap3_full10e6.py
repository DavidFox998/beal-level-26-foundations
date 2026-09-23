#!/usr/bin/env python3
"""Exact, independently replayable external scan; NOT a Lean proof."""

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path

LIMIT = 1_000_000
CHUNK = 10_000


def floor_fourth_root(n: int, independent: bool) -> int:
    if not independent:
        return isqrt(isqrt(n))
    # Separate binary-search implementation for verifying the checkpoints.
    lo, hi = 0, 1 << ((n.bit_length() + 3) // 4)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**4 <= n:
            lo = mid
        else:
            hi = mid
    return lo


def scan(independent: bool) -> dict:
    checkpoints = []
    hits = []
    for lo in range(0, LIMIT + 1, CHUNK):
        hi = min(lo + CHUNK, LIMIT + 1)
        digest = hashlib.sha256()
        for b in range(lo, hi):
            difference = (b + 3) ** 13 - b**4
            if difference < 0:
                raise AssertionError(f"negative fourth-power candidate at B={b}")
            root = floor_fourth_root(difference, independent)
            fourth = root**4
            if fourth > difference or (root + 1) ** 4 <= difference:
                raise AssertionError(f"incorrect fourth root at B={b}")
            digest.update(f"{b}:{difference}:{root}\n".encode("ascii"))
            if fourth == difference:
                hits.append({"A": root, "B": b})
        checkpoints.append({"lo": lo, "hi_exclusive": hi, "sha256": digest.hexdigest()})
    return {
        "statement": "A^4+B^4=(B+3)^13 for natural A and 0<=B<=1000000",
        "scope": "external exact-integer enumeration; not a Lean kernel proof",
        "limit_inclusive": LIMIT,
        "chunk_size": CHUNK,
        "checked_b_values": LIMIT + 1,
        "hits": hits,
        "checkpoints": checkpoints,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", type=Path, help="generate JSON checkpoints")
    parser.add_argument("--verify", type=Path, help="independently replay JSON checkpoints")
    args = parser.parse_args()
    if bool(args.write) == bool(args.verify):
        parser.error("choose exactly one of --write or --verify")
    if args.write:
        result = scan(independent=False)
        if result["hits"]:
            raise SystemExit(f"candidate solutions found: {result['hits']}")
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
        print(f"full10e6: generated {len(result['checkpoints'])} checkpoints for "
              f"{result['checked_b_values']} values, 0 candidates")
        print(f"full10e6: artifact_sha256={hashlib.sha256(args.write.read_bytes()).hexdigest()}")
    else:
        recorded = json.loads(args.verify.read_text())
        expected = scan(independent=True)
        if recorded != expected or expected["hits"]:
            raise SystemExit("full10e6: checkpoint mismatch or candidate solution")
        print(f"full10e6: independently verified {len(expected['checkpoints'])} checkpoints, "
              f"{expected['checked_b_values']} values, 0 candidates")
        print(f"full10e6: artifact_sha256={hashlib.sha256(args.verify.read_bytes()).hexdigest()}")
        print("full10e6: external evidence only; no Lean kernel theorem imported")


if __name__ == "__main__":
    main()
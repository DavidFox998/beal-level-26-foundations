#!/usr/bin/env python3
"""Emit ordinary Lean certificates for the modular 500-value intervals.

Generation is only source-code construction. Each `by decide` must still be
compiled and checked by Lean; this script does not certify the result.
"""

import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "BealMatveevBealV25B0Search"
PREFIX = "BealMatveevBealV25B0Search"
NS = "BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6"


def write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def chunk_name(n: int) -> str:
    return f"chunk_{n:04d}"


def group_name(n: int) -> str:
    return f"group_{n:03d}"


def block_name(n: int) -> str:
    return f"block_{n:02d}"


def header(*imports: str) -> str:
    return "".join(f"import {name}\n" for name in imports) + f"\nnamespace {NS}\n\n"


def generate(count: int) -> None:
    for n in range(count):
        lo = 500 * n
        hi = lo + 500
        name = f"Chunked10e6_{n:04d}"
        content = (
            header(f"{PREFIX}.Chunked10e6")
            + "set_option maxRecDepth 4096\n"
            + "set_option maxHeartbeats 0\n\n"
            + f"theorem {chunk_name(n)} : checkRange {lo} {hi} = true := by decide\n\n"
            + f"end {NS}\n"
        )
        write(BASE / "Chunks" / f"{name}.lean", content)

    for g in range(count // 10):
        imports = [f"{PREFIX}.Chunks.Chunked10e6_{n:04d}" for n in range(10*g, 10*g+10)]
        cases = "\n".join(
            f"  by_cases h{j} : i = {j}\n"
            f"  · subst i\n    exact {chunk_name(10*g+j)}"
            for j in range(10)
        )
        content = (
            header(*imports)
            + "set_option maxRecDepth 4096\n"
            + "set_option maxHeartbeats 0\n\n"
            + f"/-- Ten separate kernel-checked 500-value intervals. -/\n"
            + f"theorem {group_name(g)} (i : ℕ) (hi : i < 10) :\n"
            + f"    checkRange (500 * (10 * {g} + i)) (500 * (10 * {g} + i + 1)) = true := by\n"
            + f"{cases}\n  omega\n\n"
            + f"end {NS}\n"
        )
        write(BASE / "ChunkGroups" / f"Group{g:03d}.lean", content)

    for b in range(count // 100):
        imports = [f"{PREFIX}.ChunkGroups.Group{g:03d}" for g in range(10*b, 10*b+10)]
        cases = "\n".join(
            f"  by_cases h{j} : g = {j}\n"
            f"  · subst g\n    exact {group_name(10*b+j)} i hi"
            for j in range(10)
        )
        content = (
            header(*imports)
            + "set_option maxRecDepth 4096\n"
            + "set_option maxHeartbeats 0\n\n"
            + f"/-- One hundred independent 500-value certificates. -/\n"
            + f"theorem {block_name(b)} (g i : ℕ) (hg : g < 10) (hi : i < 10) :\n"
            + f"    checkRange (500 * (100 * {b} + 10 * g + i))\n"
            + f"      (500 * (100 * {b} + 10 * g + i + 1)) = true := by\n"
            + f"{cases}\n  omega\n\n"
            + f"end {NS}\n"
        )
        write(BASE / "ChunkBlocks" / f"Block{b:02d}.lean", content)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--count", type=int, default=2000)
    args = parser.parse_args()
    if not (1 <= args.count <= 2000):
        parser.error("count must be between 1 and 2000")
    generate(args.count)
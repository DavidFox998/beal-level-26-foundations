#!/usr/bin/env python3
"""Generate foldl `check_range` shards for gap-3 `B < B0 = 10^6`.

Same Bool checker as `BealMatveevBealV25B0Search.check_range` (mod-16
plus integer fourth root). Does **not** write under `Beal/Matveev/`:
`.submodules Beal.Matveev` would pull shards into the default glob.

Ten thousand `native_decide` theorems of 100 `B`-values are **not**
committed. At `B ≈ 10^6`, `(B+3)^13 ≈ 10^78`; that is why the closed
slice stays `B < 1000` (ten shards) and `gap3_B_le_B0_no_solution`
stays `def Prop`. The Lean wiring lives in root `Gap3B0Million.lean`.

Usage (from repo root):
  python3 scripts/gen_gap3_shards.py --dry-run
  python3 scripts/gen_gap3_shards.py --write --out Gap3Shards
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

FORBIDDEN_PREFIXES = (
    Path("Beal") / "Matveev",
    Path("Beal/Matveev"),
)

TEMPLATE = """\
/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import BealMatveevBealV25B0Search

/-! Generated shard. Not in the default `BealMatveevBeal` glob.
    Do **not** copy under `Beal/Matveev/`. `native_decide` here
    evaluates `check_range` (13th powers), not a kernel proof of
    `(B+3)^13`. -/

open BealMatveevBeal.BealMatveevBealV25B0Search

theorem check_{lo}_{hi} : check_range {lo} {hi} = true := by
  native_decide
"""


def refuse_beal_matveev(out: Path) -> None:
    resolved = out.resolve()
    for prefix in FORBIDDEN_PREFIXES:
        cand = (Path.cwd() / prefix).resolve()
        try:
            resolved.relative_to(cand)
        except ValueError:
            continue
        sys.exit(
            "gen_gap3_shards: refuse "
            f"{out} — Beal/Matveev is the default glob "
            "(.submodules Beal.Matveev). Use Gap3Shards/ at repo root."
        )


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--start", type=int, default=0)
    p.add_argument("--end", type=int, default=1_000_000)
    p.add_argument("--step", type=int, default=100)
    p.add_argument("--out", type=Path, default=Path("Gap3Shards"))
    p.add_argument(
        "--write",
        action="store_true",
        help="actually write files (default is dry-run / count only)",
    )
    p.add_argument("--dry-run", action="store_true")
    args = p.parse_args()
    if args.step <= 0 or args.end <= args.start:
        print("gen_gap3_shards: empty range", file=sys.stderr)
        return 1
    refuse_beal_matveev(args.out)
    starts = list(range(args.start, args.end, args.step))
    n = len(starts)
    print(
        f"gen_gap3_shards: {n} shards of {args.step} "
        f"covering [{args.start}, {args.end})"
    )
    print(
        "native_decide of these shards is not an AMS close: "
        "(B+3)^13 at B≈1e6 is ~1e78; B<1000 stays the closed slice"
    )
    write = bool(args.write) and not bool(args.dry_run)
    if not write:
        print("dry-run: not writing files (pass --write to emit Gap3Shards/)")
        return 0
    args.out.mkdir(parents=True, exist_ok=True)
    for s in starts:
        e = s + args.step
        path = args.out / f"Shard_{s}_{e}.lean"
        path.write_text(TEMPLATE.format(lo=s, hi=e), encoding="utf-8")
    print(f"wrote {n} files under {args.out}")
    print("do not add them to Beal/Matveev or the default glob")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

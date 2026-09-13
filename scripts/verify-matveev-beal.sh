#!/usr/bin/env bash
# Honest AMS / Math. Comp. referee surface for foundations-level-26.
# This repo owns Matveev 2000 Thm 1.4 n=2 (not Mathlib 4.12).
# Exactly one sorry is allowed: matveev_gap3_lower at line 716.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

fail() { echo "verify-matveev-beal: $*" >&2; exit 1; }

test -f lean-toolchain
test -f lakefile.lean
test -f lake-manifest.json
test -f CITATION.cff
test -f README.md
test -f LICENSE
test -f Beal/Matveev/MatveevThm14General.lean

grep -q 'leanprover/lean4:v4.12.0' lean-toolchain \
  || fail "lean-toolchain is not Lean 4.12.0"

grep -q '@\[default_target\]' lakefile.lean
grep -q 'BealMatveevBeal' lakefile.lean \
  || fail "lakefile.lean missing BealMatveevBeal"
if grep -q 'BealLevel26FoundationsScaffold' lakefile.lean; then
  fail "lakefile.lean still names the relocated Scaffold target"
fi

python3 - <<'PY'
import pathlib, re, sys

root = pathlib.Path(".")
lean_files = [
    p for p in root.rglob("*.lean")
    if ".lake" not in p.parts and "scripts" not in p.parts
]

sorry_pat = re.compile(r"^\s*sorry\b")
admit_pat = re.compile(r"^\s*admit\b")
sorries, admits = [], []
for p in lean_files:
    text = p.read_text(encoding="utf-8")
    for i, line in enumerate(text.splitlines(), 1):
        if sorry_pat.match(line):
            sorries.append(f"{p.as_posix()}:{i}")
        if admit_pat.match(line):
            admits.append(f"{p.as_posix()}:{i}")

if admits:
    print("unexpected admit:", *admits, sep="\n  ", file=sys.stderr)
    sys.exit(1)

expected = "Beal/Matveev/MatveevThm14General.lean:716"
if sorries != [expected]:
    print("sorry budget is not exactly matveev_gap3_lower at 716:", file=sys.stderr)
    print("  found:", sorries or "(none)", file=sys.stderr)
    sys.exit(1)

src = pathlib.Path("Beal/Matveev/MatveevThm14General.lean").read_text(encoding="utf-8")
lines = src.splitlines()
if "theorem matveev_gap3_lower" not in lines[714]:
    print("line 715 is not theorem matveev_gap3_lower:", lines[714], file=sys.stderr)
    sys.exit(1)
if lines[715].strip() != "sorry":
    print("line 716 is not sorry:", lines[715], file=sys.stderr)
    sys.exit(1)
if "143186215390" not in src:
    print("C1_floor = 143186215390 missing from MatveevThm14General.lean", file=sys.stderr)
    sys.exit(1)
if "matveev_product_bound_of_B_le_B0" not in src:
    print("proved product bound missing", file=sys.stderr)
    sys.exit(1)
if "gap3_A_bounds" not in src:
    print("gap3_A_bounds missing", file=sys.stderr)
    sys.exit(1)
if "matveev_gap3_lower_of_general_of_B_le_B0" not in src:
    print("v25-sufficient packaging missing", file=sys.stderr)
    sys.exit(1)

readme = pathlib.Path("README.md").read_text(encoding="utf-8")
if not readme.startswith("# foundations-level-26"):
    print("README.md must start with the foundations-level-26 title", file=sys.stderr)
    sys.exit(1)
if "beal-conjecture stays beal-conjecture" not in readme:
    print("README.md must keep the monorepo slug note", file=sys.stderr)
    sys.exit(1)

cff = pathlib.Path("CITATION.cff").read_text(encoding="utf-8")
needles = [
    'title: "foundations-level-26 — Beal Level 26 Matveev-Baker Foundations"',
    'version: "v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations"',
    'doi: "10.5281/zenodo.22379293"',
    'repository-code: "https://github.com/DavidFox998/beal-level-26-foundations"',
]
for n in needles:
    if n not in cff:
        print("CITATION.cff missing:", n, file=sys.stderr)
        sys.exit(1)

print("verify-matveev-beal: ok")
print("  one sorry: Beal/Matveev/MatveevThm14General.lean:716 matveev_gap3_lower")
print("  C1_floor=143186215390, gap3_A_bounds and B<=B0 product proved")
print("  concept DOI 10.5281/zenodo.22379293, slug beal-level-26-foundations")
print("  not v25 until hGen and hLLL are 0-sorry")
PY

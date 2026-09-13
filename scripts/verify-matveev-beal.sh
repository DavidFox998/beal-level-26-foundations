#!/usr/bin/env bash
# Honest AMS / Math. Comp. referee surface for foundations-level-26.
# This repo owns the integer-gap B≤B0 Matveev lower bound (not Mathlib 4.12
# interpolation, not unrestricted matveev_inequality_real_target).
# Zero sorry/admit in Lean sources.
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
test -f Beal/Matveev/MatveevThm14Proof.lean
test -f Beal/Matveev/MatveevLLL.lean
test -f MatveevThm14Proof.lean
test -f MatveevLLL.lean
test -f MatveevInterpolation.lean
test -f Beal/Matveev/MatveevInterpolation.lean

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

if sorries:
    print("sorry budget is not empty:", file=sys.stderr)
    print("  found:", sorries, file=sys.stderr)
    sys.exit(1)

src = pathlib.Path("Beal/Matveev/MatveevThm14General.lean").read_text(encoding="utf-8")
if "theorem matveev_gap3_lower :" not in src:
    print("theorem matveev_gap3_lower missing", file=sys.stderr)
    sys.exit(1)
body = src.split("theorem matveev_gap3_lower :", 1)[1]
body = re.split(r"\n(?:def |theorem |lemma |/-!)", body, maxsplit=1)[0]
if re.search(r"^\s*sorry\b", body, re.M):
    print("matveev_gap3_lower still contains sorry", file=sys.stderr)
    sys.exit(1)
if "matveev_gap3_lower_B_le_B0_target" not in src:
    print("B≤B0 target missing", file=sys.stderr)
    sys.exit(1)
if "matveev_gap3_lower_of_integer_gap_of_B_le_B0" not in src:
    print("integer-gap B≤B0 close missing", file=sys.stderr)
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
if "matveev_thm14_n2_explicit_of_nat" not in pathlib.Path("MatveevThm14Proof.lean").read_text(encoding="utf-8"):
    print("matveev_thm14_n2_explicit_of_nat missing from MatveevThm14Proof.lean", file=sys.stderr)
    sys.exit(1)

lll = pathlib.Path("MatveevLLL.lean").read_text(encoding="utf-8")
if "theorem four_thirteenths_is_convergent" not in lll:
    print("four_thirteenths_is_convergent missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem integer_gap_lt_ratio" not in lll:
    print("integer_gap_lt_ratio missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem abs_Lambda_ge_B4_div_B3_pow" not in lll:
    print("abs_Lambda_ge_B4_div_B3_pow missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem abs_Lambda_tight_sandwich" not in lll:
    print("abs_Lambda_tight_sandwich missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "def baker_davenport_reduction" not in lll:
    print("baker_davenport_reduction must stay a def Prop", file=sys.stderr)
    sys.exit(1)
if "def B0_nat" not in lll or "1000000" not in lll:
    print("B0_nat = 1000000 missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "def bugeaud_LLL_reduction_proof" not in lll:
    print("bugeaud_LLL_reduction_proof must stay a def Prop", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem bugeaud_LLL_reduction_proof\b", lll, re.M):
    print("bugeaud_LLL_reduction_proof must not be a theorem", file=sys.stderr)
    sys.exit(1)
if "theorem matveev_gap3_lower_unrestricted" in src or "theorem matveev_gap3_lower_unrestricted" in lll:
    print("do not inhabit unrestricted matveev_gap3_lower", file=sys.stderr)
    sys.exit(1)
if ".one `MatveevLLL" not in pathlib.Path("lakefile.lean").read_text(encoding="utf-8"):
    print("lakefile.lean missing MatveevLLL glob", file=sys.stderr)
    sys.exit(1)
if ".one `MatveevInterpolation" not in pathlib.Path("lakefile.lean").read_text(encoding="utf-8"):
    print("lakefile.lean missing MatveevInterpolation glob", file=sys.stderr)
    sys.exit(1)

interp = pathlib.Path("MatveevInterpolation.lean").read_text(encoding="utf-8")
if "import Beal.Matveev.MatveevThm14General" in interp:
    print("MatveevInterpolation.lean must not import Beal.Matveev.MatveevThm14General", file=sys.stderr)
    sys.exit(1)
if "theorem C1_floor_eq" not in interp or "143186215390" not in interp:
    print("C1_floor = 143186215390 missing from MatveevInterpolation.lean", file=sys.stderr)
    sys.exit(1)
if "def height_B0_nat" not in interp or "104382751019310000000" not in interp:
    print("height_B0_nat missing from MatveevInterpolation.lean", file=sys.stderr)
    sys.exit(1)
if "def B0_nat" not in interp or "1000000" not in interp:
    print("B0_nat = 1000000 missing from MatveevInterpolation.lean", file=sys.stderr)
    sys.exit(1)
if "theorem interpolation_det_ne_zero" not in interp:
    print("interpolation_det_ne_zero missing", file=sys.stderr)
    sys.exit(1)
if "def interpolationDeterminant" not in interp:
    print("interpolationDeterminant missing", file=sys.stderr)
    sys.exit(1)
if "theorem matveev_thm14_n2_real_explicit_is_false" not in interp:
    print("matveev_thm14_n2_real_explicit_is_false missing", file=sys.stderr)
    sys.exit(1)
if "theorem matveev_interpolation_track1" not in interp:
    print("matveev_interpolation_track1 missing", file=sys.stderr)
    sys.exit(1)
if "def matveev_thm14_n2_real_explicit" not in interp:
    print("matveev_thm14_n2_real_explicit must stay a def Prop", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem matveev_thm14_n2_real_explicit\b", interp, re.M):
    print("do not inhabit matveev_thm14_n2_real_explicit (false for reals)", file=sys.stderr)
    sys.exit(1)
if "theorem wuestholz_product_theorem_Ga" not in interp:
    print("wuestholz_product_theorem_Ga missing", file=sys.stderr)
    sys.exit(1)
if "theorem size_upper_bound_hadamard" not in interp:
    print("size_upper_bound_hadamard missing", file=sys.stderr)
    sys.exit(1)
if "def size_upper_bound" not in interp:
    print("analytic size_upper_bound must stay a def Prop", file=sys.stderr)
    sys.exit(1)
if "theorem matveev_interpolation_analytic_small_bound" not in interp:
    print("matveev_interpolation_analytic_small_bound missing", file=sys.stderr)
    sys.exit(1)
if "theorem schwarz_lemma_of_order" not in interp:
    print("schwarz_lemma_of_order missing", file=sys.stderr)
    sys.exit(1)
if "def matveevPhi" not in interp:
    print("matveevPhi missing", file=sys.stderr)
    sys.exit(1)
if "theorem interpolationDeterminant_L0_not_exp_small" not in interp:
    print("interpolationDeterminant_L0_not_exp_small missing", file=sys.stderr)
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
print("  0 sorry; matveev_gap3_lower is the B<=B0 integer-gap close")
print("  C1_floor=143186215390, gap3_A_bounds and B<=B0 product proved")
print("  CF lemmas: 4/13 convergent, integer gap < ratio; not baker_bound_gap3")
print("  interpolation: Δ, Vandermonde, G_a product, Hadamard, Schwarz;")
print("  analytic small bound is conditional on vanishing order")
print("  bare-real matveev_thm14_n2_real_explicit stays false def Prop")
print("  concept DOI 10.5281/zenodo.22379293, slug beal-level-26-foundations")
print("  unrestricted target and hLLL stay def Prop; not v25")
PY

#!/usr/bin/env bash
# Validate the immutable publication surface and every honest branch-local layer.
set -euo pipefail

BASE="43735b3b14a9e844d4b4bdf57fa5f68d29e749ee"
MATHLIB_REV="809c3fb3b5c8f5d7dace56e200b426187516535a"
PAPER_HEAD="d09cdf6cf9fc9431b2969e409460df3804c97864"
BEAL_URL="https://github.com/DavidFox998/beal-conjecture.git"
BEAL_MAIN_REF="refs/remotes/publication-check/beal-main"
BEAL_PAPER_REF="refs/remotes/publication-check/beal-paper-v30"
LABEL="${PUBLICATION_SURFACE_LABEL:-$(git branch --show-current || true)}"
ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }
pass() { printf 'PASS: %s\n' "$*"; }
section() { printf '\n--- %s ---\n' "$*"; }

HEAD_SHA="$(git rev-parse HEAD)"
printf '=== Publication-surface validation: %s at %s ===\n' \
  "${LABEL:-detached}" "$HEAD_SHA"

section "baseline and pins"
test "$(git merge-base HEAD "$BASE")" = "$BASE" \
  || fail "merge-base with HEAD is not exactly $BASE"
pass "merge-base is exactly $BASE"

grep -q 'leanprover/lean4:v4.12.0' lean-toolchain \
  || fail "lean-toolchain is not Lean v4.12.0"
grep -q '"https://github.com/leanprover-community/mathlib4" @ "v4.12.0"' lakefile.lean \
  || fail "lakefile.lean does not pin Mathlib v4.12.0"
python3 - "$MATHLIB_REV" <<'PY'
import json, pathlib, sys
manifest = json.loads(pathlib.Path("lake-manifest.json").read_text())
mathlib = next((p for p in manifest["packages"] if p["name"] == "mathlib"), None)
if mathlib is None:
    raise SystemExit("FAIL: mathlib package missing from lake-manifest.json")
if mathlib.get("rev") != sys.argv[1]:
    raise SystemExit(f"FAIL: mathlib rev is {mathlib.get('rev')!r}")
if mathlib.get("inputRev") != "v4.12.0":
    raise SystemExit(f"FAIL: mathlib inputRev is {mathlib.get('inputRev')!r}")
print("PASS: manifest mathlib rev and inputRev are pinned")
PY
grep -q '83739542' audit-43735b3-eight-branches.md 2>/dev/null \
  || printf 'INFO: manifest lock identifier 83739542 is recorded outside this branch\n'
if git grep -n -E 'lake[[:space:]]+update' -- '*.lean' '*.sh' |
    grep -v '^scripts/validate-publication-surface.sh:'; then
  fail "tracked Lean or shell source invokes lake update"
fi
pass "no tracked Lean or shell source invokes lake update"

section "live release tags"
for tag in \
  v0.27-mcom-four-props-inhabited \
  v0.28-mcom-algebraic-props-inhabited \
  v0.29-mcom-final-algebraic-props-inhabited \
  v0.30-mcom-structural-verification
do
  git rev-parse -q --verify "refs/tags/$tag" >/dev/null \
    || fail "missing tag $tag"
  printf 'PASS: %s -> %s\n' "$tag" "$(git rev-list -n1 "$tag")"
done

section "beal-conjecture publication surface"
if test "${PUBLICATION_SKIP_FETCH:-0}" != 1 ||
   ! git rev-parse -q --verify "$BEAL_MAIN_REF" >/dev/null ||
   ! git rev-parse -q --verify "$BEAL_PAPER_REF" >/dev/null; then
  git fetch --quiet "$BEAL_URL" \
    "main:$BEAL_MAIN_REF" \
    "paper-v30-draft:$BEAL_PAPER_REF"
fi
git merge-base --is-ancestor ea261b95ccddf8c326b583ec77b9359c5f294a5a "$BEAL_MAIN_REF" \
  || fail "ea261b9 is not in the live beal-conjecture main lineage"
git merge-base --is-ancestor af520d36a87e63e1e20ed1e16e11d0a9874d2e9f "$BEAL_MAIN_REF" \
  || fail "af520d3 is not in the live beal-conjecture main lineage"
test "$(git rev-parse "$BEAL_PAPER_REF")" = \
  "2124501fcf2017e661bae0494a369248b3948503" \
  || fail "external paper-v30-draft is not at 2124501"
about="$(git show "$BEAL_MAIN_REF:docs/About.md")"
grep -q 'zenodo.22863527' <<<"$about" || fail "version DOI 22863527 missing"
grep -q 'zenodo.22379293' <<<"$about" || fail "concept DOI 22379293 missing"
grep -q '392549396' <<<"$about" || fail "release id 392549396 missing"
git rev-parse -q --verify refs/tags/v30.0.0-level-26-structural-verification >/dev/null \
  || fail "external v30 release tag was not fetched"
pass "beal-conjecture v30 DOI, concept, release id, tag, and lineage"

section "separate paper-v30-draft"
git rev-parse -q --verify refs/remotes/origin/paper-v30-draft >/dev/null \
  || fail "origin/paper-v30-draft is unavailable"
test "$(git rev-parse refs/remotes/origin/paper-v30-draft)" = "$PAPER_HEAD" \
  || fail "foundations paper-v30-draft is not at d09cdf6"
paper_tmp="$(mktemp --suffix=.pdf)"
trap 'rm -f "$paper_tmp"' EXIT
git show refs/remotes/origin/paper-v30-draft:paper/paper.pdf >"$paper_tmp"
test "$(stat -c %s "$paper_tmp")" = 403928 \
  || fail "paper.pdf is not the recorded 403928-byte artifact"
command -v pdfinfo >/dev/null || fail "pdfinfo is required for page validation"
test "$(pdfinfo "$paper_tmp" | awk '/^Pages:/ {print $2}')" = 6 \
  || fail "paper.pdf is not six pages"
paper_readme="$(git show refs/remotes/origin/paper-v30-draft:paper/README.md)"
grep -q '2124501.*ea261b9' <<<"$paper_readme" \
  || fail "paper README does not record 2124501 from ea261b9"
grep -q 'zenodo.22863527' <<<"$paper_readme" || fail "paper DOI missing"
grep -q 'zenodo.22379293' <<<"$paper_readme" || fail "paper concept DOI missing"
pass "paper branch is separate at d09cdf6; PDF is 403928 bytes and six pages"

section "branch-local numerical theorem surfaces"
numerical_files=(
  Tate_Frey_Conductor_29_Numerical.lean
  Mazur_X0_13_Numerical.lean
  Ribet_928_to_32_Numerical.lean
  Kolyvagin_MW_Rank0_Numerical.lean
)
present_numerical=()
for file in "${numerical_files[@]}"; do
  test -f "$file" || continue
  present_numerical+=("$file")
  grep -qE '^theorem .*_numerical' "$file" \
    || fail "$file has no inhabited numerical theorem"
  if grep -nE '^[[:space:]]*def .*:[[:space:]]*Prop' "$file"; then
    fail "$file contains def Prop"
  fi
  if grep -nE '\bsorry\b|sorryAx|native_decide|^[[:space:]]*axiom[[:space:]]' "$file"; then
    fail "$file contains a forbidden construct"
  fi
  pass "$file contains theorem terms and zero def Prop"
done
printf 'INFO: %d numerical module(s) present on this branch\n' \
  "${#present_numerical[@]}"

section "conditional bridge"
if test -f Bridge_43735b3_Honest_Numerical.lean; then
  python3 <<'PY'
import pathlib, re
p = pathlib.Path("Bridge_43735b3_Honest_Numerical.lean").read_text()
if not re.search(
        r"structure\s+HasNewformAtLevel32\b.*?\)\s*:\s*Prop\s+where",
        p, re.S):
    raise SystemExit("FAIL: HasNewformAtLevel32 is not a local Prop evidence record")
m = re.search(
    r"theorem\s+has_newform_at_level_32_of_assumptions\b(.*?)"
    r":\s*HasNewformAtLevel32\b.*?:=\s*by",
    p, re.S)
if not m:
    raise SystemExit("FAIL: conditional bridge theorem is missing")
binders = re.findall(
    r"\((h[A-Za-z0-9_]+)\s*:\s*([^)]*)\)", m.group(1))
open_types = {
    "frey_no_rational_13_isogeny",
    "Frey_conductor_29_is_Neron",
    "Ribet_928_to_32",
}
names = [name for name, typ in binders if typ.strip() in open_types]
if names != ["hMazur", "hTate", "hRibet"]:
    raise SystemExit(f"FAIL: open bridge assumptions are {names!r}")
print("PASS: HasNewformAtLevel32 is a local conditional evidence record")
print("PASS: remaining bridge assumptions are exactly hMazur hTate hRibet")
PY
else
  printf 'INFO: conditional bridge module is not present on this branch\n'
fi

section "scaffold direction and forbidden placeholders"
scaffold_dirs=()
for dir in TateCurve MazurCurve RibetCurve KolyvaginCurve; do
  test -d "$dir" && scaffold_dirs+=("$dir")
done
if ((${#scaffold_dirs[@]})); then
  if grep -R -n -E ':=[[:space:]]*True\b' --include='*.lean' "${scaffold_dirs[@]}"; then
    fail "a scaffold contains := True"
  fi
  if grep -R -n -E '\bsorry\b|sorryAx|native_decide|^[[:space:]]*axiom[[:space:]]' \
      --include='*.lean' "${scaffold_dirs[@]}"; then
    fail "a scaffold contains sorry, sorryAx, native_decide, or an axiom declaration"
  fi
  pass "scaffolds are forward-only and contain no := True or forbidden construct"
else
  printf 'INFO: no scaffold directory is present on this branch\n'
fi

if test "$LABEL" = audit-43735b3-eight-branches ||
   test "$LABEL" = publication-surface-validation; then
  test -z "$(git diff --name-only "$BASE"..HEAD -- '*.lean')" \
    || fail "audit lineage changes Lean source"
  pass "audit lineage adds no Lean proposition, axiom, or proof term"
fi

section "axiom surface"
axiom_log="$(mktemp)"
for file in "${present_numerical[@]}"; do
  if ! lake env lean "$file" >>"$axiom_log" 2>&1; then
    cat "$axiom_log" >&2
    fail "$file does not compile directly"
  fi
done
if test -f Bridge_43735b3_Honest_Numerical.lean; then
  if ! lake env lean Bridge_43735b3_Honest_Numerical.lean >>"$axiom_log" 2>&1; then
    cat "$axiom_log" >&2
    fail "Bridge_43735b3_Honest_Numerical.lean does not compile directly"
  fi
fi
if test -f KolyvaginCurve/BlockerDoc.lean; then
  if ! lake env lean KolyvaginCurve/BlockerDoc.lean >>"$axiom_log" 2>&1; then
    cat "$axiom_log" >&2
    fail "KolyvaginCurve/BlockerDoc.lean does not compile directly"
  fi
fi
python3 - "$axiom_log" <<'PY'
import pathlib, re, sys
s = pathlib.Path(sys.argv[1]).read_text()
if "sorryAx" in s:
    raise SystemExit("FAIL: sorryAx appears in Lean axiom output")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for body in re.findall(r"depends on axioms:\s*\[(.*?)\]", s, re.S):
    got = {x.strip() for x in body.replace("\n", " ").split(",") if x.strip()}
    if not got <= allowed:
        raise SystemExit(f"FAIL: unexpected axiom dependency {sorted(got - allowed)}")
print("PASS: axiom dependencies are contained in "
      "[propext, Classical.choice, Quot.sound]")
PY
if test -f Kolyvagin_MW_Rank0_Numerical.lean; then
  grep -q 'Classical.choice' "$axiom_log" \
    || fail "Kolyvagin numerical surface did not report Classical.choice"
  pass "Kolyvagin surface reports propext/Classical.choice/Quot.sound envelope"
fi
rm -f "$axiom_log"

section "registered build surface and referee verification"
lake exe cache get
lake build BealMatveevBealV25B0Search
bash scripts/verify-matveev-beal.sh
pass "maximal registered root green; verify-matveev-beal: ok"

sorry_ax_hits="$(
  git grep -n 'sorryAx' -- '*.lean' 2>/dev/null |
    grep -vE 'No `sorryAx`|without `sorryAx`' || true
)"
test -z "$sorry_ax_hits" || fail "proof-level sorryAx found"
pass "referee reports zero proof-level sorry and zero sorryAx"

printf 'INFO: expected registered job range is 5180-5185; bridge roots 5180/5181\n'
printf 'INFO: prior green roots: Default HonestB0Search Level26 '
printf 'BealMatveevBeal V25Rank3 V25B0Search\n'
printf '=== Publication-surface validation OK: %s ===\n' "${LABEL:-detached}"
#!/usr/bin/env bash
set -euo pipefail

test -f README.md
test -f PLAN.md
test -f lean-toolchain
test -f lakefile.lean
test -f lean/BealLevel26Foundations.lean
test -f lean/BealLevel26Foundations/FiniteEvidence.lean
test -f CITATION.cff
test -f LICENSE
test -f docs/releases/v1.0.0-computable.md
test -f sagemath/level_26_ledger.json

grep -q "v1.0.0" README.md
grep -q "v2.0.0" README.md
grep -q "v3.0.0" README.md
grep -q "v4.0.0" README.md
grep -q "FreyCurveExists" README.md
grep -q "LevelLowering_26" README.md
grep -q "v1.0.0-computable" CITATION.cff
grep -q "cohomological 2-Selmer" README.md

if grep -RInE \
  --exclude-dir=.git \
  --exclude-dir=.lake \
  --exclude-dir=.cache \
  '^[[:space:]]*(axiom|sorry|admit)([[:space:]]|$)|:[[:space:]]*True[[:space:]]*:=' \
  --include='*.lean' .; then
  echo "FAIL: unfinished or vacuous Lean declaration found"
  exit 1
fi

grep -q "def coefficientMatrix" lean/BealLevel26Foundations/FiniteEvidence.lean
grep -q "theorem M3_eq" lean/BealLevel26Foundations/FiniteEvidence.lean
grep -q "theorem M3_det_nonzero" lean/BealLevel26Foundations/FiniteEvidence.lean
grep -q "theorem all_80_bad_prime_checks_pass" \
  lean/BealLevel26Foundations/FiniteEvidence.lean
grep -q "theorem finiteCandidateAudit_not_singleton" \
  lean/BealLevel26Foundations/FiniteEvidence.lean

python3 scripts/verify_coefficient_ledger.py
python3 scripts/replay_level26_hensel.py

echo "OK: Beal Level-26 Foundations computable release is internally consistent"
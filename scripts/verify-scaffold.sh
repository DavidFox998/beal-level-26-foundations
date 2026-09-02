#!/usr/bin/env bash
set -euo pipefail

test -f README.md
test -f PLAN.md
test -f lean-toolchain
test -f lakefile.lean
test -f lean/BealLevel26Foundations.lean

grep -q "v1.0.0" README.md
grep -q "v2.0.0" README.md
grep -q "v3.0.0" README.md
grep -q "v4.0.0" README.md
grep -q "FreyCurveExists" README.md
grep -q "LevelLowering_26" README.md

if grep -RInE \
  --exclude-dir=.git \
  --exclude-dir=.lake \
  --exclude-dir=.cache \
  '^[[:space:]]*(axiom|sorry|admit)([[:space:]]|$)|:[[:space:]]*True[[:space:]]*:=' \
  --include='*.lean' .; then
  echo "FAIL: unfinished or vacuous Lean declaration found"
  exit 1
fi

echo "OK: Beal Level-26 Foundations scaffold is internally consistent"
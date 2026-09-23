---
name: Lean cache validator rebuild behavior
description: The publication validator's cache retrieval can invalidate local Mathlib artifacts and trigger a full rebuild.
---

Running the publication-surface validator's `lake exe cache get` step can replace
locally built Mathlib artifacts and make the following maximal-root build compile
the full dependency graph rather than reuse the completed local build.

**Why:** Re-running the validator after a text-only correction triggered another
5,185-target rebuild even though the preceding maximal-root build had completed.

**How to apply:** Run the canonical validator once after all text scans are clean.
If only a final literal grep fails, correct the text and rerun that exact grep;
do not restart the entire validator unless declarations or build inputs changed.
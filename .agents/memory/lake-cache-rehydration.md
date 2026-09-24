---
name: Lake cache rehydration
description: Scratch Lean checks can lose compiled dependencies after an isolated worktree is reattached.
---

After an isolated worktree is reattached, Lake may report changed dependency URLs and re-clone packages, discarding compiled Mathlib objects even though the pinned manifest and tracked source remain unchanged.

**Why:** This happened during repeat scratch checks; the immediate "unknown module prefix Mathlib" error reflected missing object files, not a proof error or an intentional dependency update.

**How to apply:** Verify the worktree resolves to its own Git root and its manifest is unchanged before a Lean check. If Lake discards objects, restore the cache for that pinned dependency set before interpreting scratch compiler errors. If an interrupted dependency clone also removed its source, recover the exact pinned revision before restoring compiled objects; matching cached objects elsewhere can support scratch work, but verify again against the repaired target. Do not modify tagged source or infer that a full project build succeeded.
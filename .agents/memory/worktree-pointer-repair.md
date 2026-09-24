---
name: Git worktree pointer repair
description: Recover isolated worktrees whose .git pointer files disappear while Git's administrative metadata survives.
---

An isolated worktree directory can retain its source and Git's administrative metadata while losing its small `.git` pointer file. In that state, `git -C <worktree>` silently finds the parent workspace repository instead, so its HEAD and status are misleading.

**Why:** After a workspace state transition, two isolated build directories still held the expected tagged sources but both appeared to be on the parent repository's HEAD; Git listed them as prunable solely because their pointer files were missing.

**How to apply:** Before cleaning or building in a previously created isolated worktree, verify `git -C <path> rev-parse --show-toplevel`. If it resolves to the parent and `git worktree list --porcelain` still has the correct administrative entries, run `git worktree repair <paths>` from the parent and verify the individual HEADs again. Do not clean based on the misleading parent status.
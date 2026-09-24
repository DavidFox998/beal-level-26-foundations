---
name: Historical release badges
description: Citation-preserving treatment of README badges during new releases.
---

Preserve existing historical DOI badges and citations in the repository's READMEs; do not replace them with a uniform set of current-release badges. Four standard badges apply only to newly created modules when requested: the concept DOI, the specified GitHub release, the pinned Lean version, and the pinned Mathlib revision.

**Why:** Historical READMEs document distinct release surfaces; overwriting their badges would misstate their citations. The user explicitly clarified that existing READMEs should remain intact during the Lake target fix.

**How to apply:** Before broad badge edits, distinguish existing documentation from new module documentation. A version-specific DOI can be reported in release metadata without rewriting historical badges.
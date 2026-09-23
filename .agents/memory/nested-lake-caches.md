---
name: Nested Lake caches
description: Why a path-required Lean package can rebuild dependencies despite a warm root project cache
---

A path-required Lean package maintains a separate `.lake` cache. Fetching
Mathlib caches at the root does not necessarily supply the nested package's
compiled imports; in this environment, the nested package still began a large
source build after its own cache fetch.

**Why:** A root build could produce a dependency's module in the root build
directory, while another module looked for the same import in the path
package's build directory. This failed before the new main theorem was checked.

**How to apply:** Check the repository's stated vendor-first build order and
validate the path package separately. Do not report a root build as green when
it failed on a missing nested `.olean`, or copy build artifacts into the source
tree and describe that as a reproducible clean build.
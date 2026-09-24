---
name: Nested Lake caches
description: Why a path-required Lean package can rebuild dependencies despite a warm root project cache
---

A path-required Lean package maintains a separate `.lake` cache. Fetching
Mathlib caches at the root does not necessarily supply the nested package's
compiled imports; in this environment, the nested package still began a large
source build after its own cache fetch.
Even `lake env lean` can replace the root dependency checkouts when the
recorded repository URLs differ from the package declaration; that removes
the previously available root `.olean` files until the pinned cache is
fetched again. This is not a dependency version update.

**Why:** A root build could produce a dependency's module in the root build
directory, while another module looked for the same import in the path
package's build directory. On a later focused Lean check, Lake's URL
normalization triggered checkout replacement before the proof was reached.

**How to apply:** Check the repository's stated vendor-first build order and
validate the path package separately. Inspect Lake's startup output before
interpreting a missing `Mathlib.olean`; restore the pinned cache when needed.
Do not report a root build as green when it failed on a missing nested `.olean`,
or copy build artifacts into the source tree and describe that as a
reproducible clean build.
---
name: Lake transitive path packages
description: A Lean 4.12 Lake dependency-resolution pitfall when a Git package includes a nested path package.
---

When switching a consumer to a Git-root Lean package that requires another package by a relative path, do not assume the nested package will resolve inside the Git checkout. Inspect the consumer's generated manifest and the `.olean` locations. Lake 4.12 may resolve that relative path against the consumer root and compile imported, unregistered nested modules into the consumer's build directory while imports search the nested package's build directory. A successful `lake update` exit code may also conceal a failed cache post-update hook when `elan` is absent from PATH.

**Why:** A pinned tag exposed a nested Level26 package transitively, but a consumer build reported a missing `.olean` immediately after building its source module because producer and importer used different output directories. Changing only the manifest directory redirected the import search but did not register the module as a nested-package build target.

**How to apply:** Confirm the actual package names, manifest directory, module target globs, and generated artifact paths before treating a tagged dependency update as verified. Preserve the immutable tag and report a failing prerequisite rather than silently patching the pinned checkout.
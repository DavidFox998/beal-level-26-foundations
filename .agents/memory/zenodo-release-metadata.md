---
name: Zenodo release metadata
description: How GitHub-triggered Zenodo records inherit metadata and how to verify corrections.
---

For GitHub-triggered Zenodo deposits, the repository's root deposit metadata can determine the published record's title, description, and version independently of the GitHub release notes. Review it before publishing a new release, especially when a repository spans several historical research stages.

**Why:** A release with accurate GitHub notes inherited an older research-stage description in its Zenodo record. Editing repository metadata later did not change the already-published record; the published deposition needed a separate authorized metadata edit.

**How to apply:** Before triggering a release, compare the root deposit metadata against the intended tag and proof boundaries. After minting, inspect the public record's title, description, version, DOI, and concept relation. Zenodo HTML-escapes comparison characters in descriptions, so compare decoded text when verifying an authorized edit.
---
name: Zenodo release metadata
description: How GitHub-triggered Zenodo records inherit metadata and how to verify corrections.
---

For GitHub-triggered Zenodo deposits, the repository's root deposit metadata can determine the published record's title, description, and version independently of the GitHub release notes. Review it before publishing a new release, especially when a repository spans several historical research stages.

**Why:** A release with accurate GitHub notes inherited an older research-stage description in its Zenodo record. Editing repository metadata later did not change the already-published record; the published deposition needed a separate authorized metadata edit.

**How to apply:** Before triggering a release, compare the root deposit metadata against the intended tag and proof boundaries. After minting, inspect the public record's title, description, version, DOI, and concept relation. Zenodo HTML-escapes comparison characters in descriptions, so compare decoded text when verifying an authorized edit.

An accepted GitHub release webhook does not guarantee that a public Zenodo version will appear promptly. Before a manual mint, check both public concept versions and authorized depositions to avoid duplicates. Zenodo's new-version action must use the concept's **latest** deposition even when a release needs to cite an earlier predecessor in `isNewVersionOf`; a fresh draft inherits the previous version's archive and metadata, so replace both before publishing.

**Why:** A release webhook returned an accepted response but no new deposit appeared after a substantial wait. The concept already contained two records for the prior tag, and blindly creating or publishing a cloned draft would have preserved the wrong source archive.

**How to apply:** Confirm the current latest record, inspect for an existing draft or newly published version, validate the draft's version, concept DOI, related identifier, and uploaded archive checksum, then publish once and verify the public record.
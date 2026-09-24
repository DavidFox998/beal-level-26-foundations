---
name: Zenodo version archives
description: Non-obvious constraints when archiving a new version in the existing Zenodo series.
---

Zenodo new-version drafts inherit the preceding version's files. Do not publish
until the replacement archive is present, verified, and the inherited archive
has been removed. The production bucket rejects `application/zip` uploads with
HTTP 415; it accepts `application/octet-stream` for the same ZIP.

**Why:** An inherited archive can silently misrepresent a new release, and the
production bucket's accepted content type is stricter than some documentation
examples.

**How to apply:** For another version in this series, inspect the latest
deposition and its files, upload the tagged source as octet-stream, compare
the returned checksum, then verify that only the intended archive remains
before publication.
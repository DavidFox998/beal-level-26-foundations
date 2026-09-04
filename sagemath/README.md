# sagemath/

Pinned coefficient ledger and SageMath 10.7 certificate generators.
**Current as of** `v4.0.5-nofrey-point`.

The ledger version is **v1.4.0** and has been unchanged since tag
`v1.4.0`:

* file: [`level_26_ledger.json`](level_26_ledger.json)
* SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`

| File | Role |
|---|---|
| `level_26_ledger.json` | 101 coefficients for `26a1` and `26b1`; lists the two certs |
| `foundations_doi_manifest.json` | v1.4.0 cert-bridge DOI, plus `latest_foundations_release` (tag `v4.0.5-nofrey-point`; DOI pending mint) |
| `j0_26_decomp_foundation.sage` | Generator for the decomposition cert |
| `j0_26_decomp_foundations.sage` | Companion generator |
| `formal_immersion_M3.sage` | Generator for the `M₃` cert |
| [`certs/`](certs/README.md) | The two archived JSON certificates |

Later Foundations tags (v2.0.0-frey through v4.0.5-nofrey-point) do **not**
add a new cert and do **not** change the ledger SHA. The
`foundations_doi_manifest.json` top-level `version` field stays
`v1.4.0`; only `latest_foundations_release` moves.

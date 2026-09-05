# sagemath/

Pinned coefficient ledger and SageMath 10.7 certificate generators.
**Current as of** `v4.2.0-full-chain`.

The ledger version is **v1.4.0** and has been unchanged since tag
`v1.4.0`:

* file: [`level_26_ledger.json`](level_26_ledger.json)
* SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`

| File | Role |
|---|---|
| `level_26_ledger.json` | 101 coefficients for `26a1` and `26b1`; lists the two certs |
| `foundations_doi_manifest.json` | v1.4.0 cert-bridge DOI, plus `latest_foundations_release` (now `v4.0.9-fourCusps-forall`; prior published `v4.0.8-geom-forbid`) |
| `j0_26_decomp_foundation.sage` | Generator for the decomposition cert |
| `j0_26_decomp_foundations.sage` | Companion generator |
| `formal_immersion_M3.sage` | Generator for the `M₃` cert |
| [`certs/`](certs/README.md) | The two archived JSON certificates |

Later Foundations tags (v2.0.0-frey through `v4.0.6-rank-zero-fixed`,
`v4.0.7-hIdentify`, `v4.0.7-hIdentify-j`, `v4.0.8-geom-forbid`,
`v4.0.9-fourCusps-forall`, `v4.0.10-chabauty0-no-doi`, and
`v4.0.11-residue-disks-no-doi`, `v4.0.12-scheme-stub-no-doi`, and
`v4.0.13-formal-immersion-proof-no-doi`, and
`v4.0.14-coleman-integral-no-doi`, and
`v4.0.15-lmfdb-certs-no-doi`,
`v4.1.0-descent-start`,
`v4.1.1-descent-compute`,
`v4.1.2-beal-13-endgame`,
`v4.1.3-beal-13-theorem`, and
`v4.2.0-full-chain`) do **not**
add a new cert and do **not** change the ledger SHA. The
`foundations_doi_manifest.json` top-level `version` field stays
`v1.4.0`. `latest_foundations_release` stays at the last
DataCite-findable version (`v4.0.9-fourCusps-forall`);
`v4.0.10-chabauty0-no-doi`, `v4.0.11-residue-disks-no-doi`,
`v4.0.12-scheme-stub-no-doi`,
`v4.0.13-formal-immersion-proof-no-doi`,
`v4.0.14-coleman-integral-no-doi`,
`v4.0.15-lmfdb-certs-no-doi`,
`v4.1.0-descent-start`,
`v4.1.1-descent-compute`,
`v4.1.2-beal-13-endgame`,
`v4.1.3-beal-13-theorem` are git tags only.
`v4.2.0-full-chain` is a GitHub release; its version DOI is
recorded in `latest_foundations_release` only after DataCite
`state: findable`.

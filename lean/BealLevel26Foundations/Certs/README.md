# lean/BealLevel26Foundations/Certs/

Archived LMFDB *display* data and PARI 2-descent display for `26a1`
and `26b1`. **Current as of** `v4.2.0-full-chain`.

| File | What it is | What it is not |
|---|---|---|
| `LMFDB_26.json` | Labels, conductor `26`, displayed rank `0`, torsion strings, `a₂` | Not a live LMFDB fetch; not a Mordell--Weil theorem |
| `LMFDBCert_26.lean` | Finite Lean package of those fields, matching Sage `certified_mwrank` and q-expansion `a₂` | Not unconditional `rankZero`; not `True`/`trivial` |
| `Descent_26.json` | PARI `ellrank` / `ell2cover` / `elltors`: rank `0`, torsion `3`/`7`, `|Sel₂|=1`, `sha2_trivial: true` | Not a Mathlib Selmer group; not a Mordell--Weil theorem |

`scripts/fetch_LMFDB.py` writes `LMFDB_26.json` from a hardcoded
table. `scripts/verify_descent_26.py` recomputes with Sage or
cypari2 when present. Neither contacts LMFDB.org or changes
`sagemath/level_26_ledger.json` (SHA-256
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`).

LMFDB JSON SHA-256
`39e22740a7787567882b33e27396b1c1dfd10a7f14e23b8af28f89e594e7b5f0`.
Descent JSON SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

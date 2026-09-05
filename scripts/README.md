# scripts/

Deterministic repository checks. **Current as of** `v4.1.1-descent-compute`.

| Script | What it checks |
|---|---|
| `verify-scaffold.sh` | Required files, honesty greps (no `axiom`/`sorry`/`admit`, Picard lives in `Jacobian/`, no unconditional `BealTheorem`, elliptic-`j` `hIdentify` rather than `26 ∉` four-cusp list), then the five Python verifiers |
| `verify_coefficient_ledger.py` | `level_26_ledger.json` SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151` |
| `verify_v1_3_0_certs.py` | The two cert SHA-256s; manifest `version` is still `v1.4.0` |
| `replay_level26_hensel.py` | 160 strong-Hensel witnesses at 2 and 13 for the eight S-units |
| `fetch_LMFDB.py` | Writes archived `LMFDB_26.json`; does not contact LMFDB.org; does not change the ledger |
| `verify_lmfdb_26.py` | JSON SHA-256 and Lean display fields; forbids `True`/`trivial` rank |
| `verify_descent_26.py` | PARI/Sage 2-descent vs `Descent_26.json`; cross-checks certified `[1,0,1,-5,-8]` / `[1,-1,1,-3,3]`; forbids Lean `True`/`trivial` |

Run from the repository root:

```sh
bash scripts/verify-scaffold.sh
```

These scripts prove file and hash consistency. They do not prove a
Jacobian, genuine 2-Selmer, or `BealTheorem`.

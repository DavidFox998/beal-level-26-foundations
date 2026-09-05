# scripts/

Deterministic repository checks. **Current as of** `v4.0.6-rank-zero-fixed`.

| Script | What it checks |
|---|---|
| `verify-scaffold.sh` | Required files, honesty greps (no `axiom`/`sorry`/`admit`, Picard lives in `Jacobian/`, no unconditional `BealTheorem`), then the three Python verifiers |
| `verify_coefficient_ledger.py` | `level_26_ledger.json` SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151` |
| `verify_v1_3_0_certs.py` | The two cert SHA-256s; manifest `version` is still `v1.4.0` |
| `replay_level26_hensel.py` | 160 strong-Hensel witnesses at 2 and 13 for the eight S-units |

Run from the repository root:

```sh
bash scripts/verify-scaffold.sh
```

These scripts prove file and hash consistency. They do not prove a
Jacobian, genuine 2-Selmer, or `BealTheorem`.

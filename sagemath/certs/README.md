# sagemath/certs/

The only two SageMath 10.7 JSON archives. **No new cert since v1.3.0 /
v1.4.0.** Current Foundations tag `v4.0.4-x026-rational-points` does not add a file
here.

| File | Contents | SHA-256 pinned by `scripts/verify_v1_3_0_certs.py` |
|---|---|---|
| `j0_26_decomposition.json` | `J₀` dimension 2 = `26a1` × `26b1`; Sage `certified_mwrank = 0` on both | `35ea70c995f9aed3ae8e2f44cf231d0b7a3ae606e11ad5646635c47fa522a750` |
| `formal_immersion_M3.json` | `M₃ = [[1,1],[0,2]]` over `𝐅₃`, `det = 2` | `35801fac1e98b4821488a7ceb128533bd476d300e78a682991329ef61f2d2438` |

`certified_mwrank` is Sage `E.rank()` output, not a cohomological
Mordell--Weil theorem. The eight signed S-units
`[1, -1, 2, -2, 13, -13, 26, -26]` used with this decomposition live in
Lean (`FiniteEvidence.lean` / `TwoSelmer_vs_SUnits_26.lean`), not as a
third JSON file.

The ledger these certs are checked against remains
[`../level_26_ledger.json`](../level_26_ledger.json) v1.4.0
SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`.

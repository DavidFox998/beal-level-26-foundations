# lean/BealLevel26Foundations/Jacobian/

Finite Jacobian *skeleton*, S-unit audit, and formal-immersion input.
**Current as of** `v4.0.10-chabauty0-no-doi`
(includes `v4.0.9-fourCusps-forall`, `v4.0.8-geom-forbid`, `v4.0.7-hIdentify-j`, `v4.0.7-hIdentify`, `v4.0.6-rank-zero-fixed`, `v4.0.5-nofrey-point`,
`v4.0.4-x026-rational-points`, `v4.0.3-formal-immersion`).

Mathlib 4.12 has no modular-curve Jacobian, Picard scheme, Abel--Jacobi
map, Galois cohomology, or Mordell--Weil group. Nothing in this folder
constructs those objects.

Sources are the already-promoted Lean data from

* [`sagemath/level_26_ledger.json`](../../../sagemath/level_26_ledger.json)
  v1.4.0 SHA-256
  `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`;
* [`sagemath/certs/j0_26_decomposition.json`](../../../sagemath/certs/j0_26_decomposition.json);
* [`sagemath/certs/formal_immersion_M3.json`](../../../sagemath/certs/formal_immersion_M3.json).

No new certificate is added here.

| File | What it proves | What it is not |
|---|---|---|
| `J0_26_DecompActual.lean` | Finite model `s₁=q₁+q₂`, `s₂=-q₁q₂`; certified `26a × 26b` via q-expansion `a₂=-1` versus `1`; `M₃=[[1,1],[0,2]]`, `det=2` by `decide` | Not a scheme-theoretic `J₀(26)` isogeny |
| `PicardAbelJacobiIdentification_26.lean` | Standalone `Prop`: supplied matrix `= qExpansionM3` | Does not discharge the geometric Picard map |
| `TwoSelmer_vs_SUnits_26.lean` | Eight S-unit indices retained; audit is not a singleton; finite `MwrankCertificateSoundness_26` for Sage `certified_mwrank = 0` on `26a` and `26b` | Not genuine cohomological 2-Selmer; comparison remains future |
| `FormalImmersionActual_26.lean` | `M₃` injective (`det = 2 ≠ 0`); `FormalImmersionAtTwo26.of_qExpansion` inhabits the Mazur input premise | Not a scheme-theoretic formal immersion |
| `J0_26_Q_RankZeroActual_26.lean` | Product of certified `26a × 26b` with Sage `certified_mwrank = 0` on both; inhabits `J0_26_Q_RankZero26.of_qExpansion` | Not a Mathlib Mordell--Weil theorem; not genuine `Sel₂` |

The displayed four-cusp package that can replace
`X0_26_RationalPoints26` lives in
[`../Mazur/X026RationalPointsActual_26.lean`](../Mazur/X026RationalPointsActual_26.lean).
It is not a Mathlib `X₀(26)(ℚ)` theorem.

The v1.0 README boundary still holds: the finite audit is not
mislabeled as a genuine 2-Selmer calculation.

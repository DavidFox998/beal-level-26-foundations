# lean/BealLevel26Foundations/Chain/

Named Frey / four-cusp *packages* for the exponent-13 route.
**Current as of** `v4.2.0-full-chain`.

Mathlib 4.12 has no modularity, no Ribet, no `X₀(26)(ℚ)`, no
`SelmerGroup`, and no `MordellWeil.rank`. Nothing here is the
Beal conjecture or typed `fourCusps → ¬ ExistsNoncuspidal`.

| File | What it is | What it is not |
|---|---|---|
| `FreyCurve_13_26.lean` | `FreyLevel26 := 2 * 13 = 26`; `FreyToX0_26 := 26 = 2 * 13` | Not a Frey curve; not Ribet; not `True`/`trivial` |
| `RationalPoints_26_FourCusps_26.lean` | `X0_26_Q_four := rankZero_unconditional ∧ Chabauty0ForcesCusp_computational` | Not a Mathlib `X₀(26)(ℚ)` theorem; not the typed implication |

`X026RationalPointsActual_26` is unchanged. There is no
unconditional `BealTheorem`. The v1.4.0 ledger SHA-256
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`
is unchanged.

# lean/BealLevel26Foundations/Chain/

Named Frey / four-cusp *packages* for the exponent-13 route.
**Current as of** `v4.2.1-chabauty-closes-typed`.

Mathlib 4.12 has no modularity, no Ribet, no `X₀(26)(ℚ)`, no
`SelmerGroup`, and no `MordellWeil.rank`. Nothing here is the
Beal conjecture or typed `fourCusps → ¬ ExistsNoncuspidal`.

Certified models behind the four-cusp *name* (PARI 2.17.2;
`Descent_26.json` SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`):

| Curve | `[a₁,a₂,a₃,a₄,a₆]` | Δ | Conductor | Torsion | `|Sel₂|` |
|---|---|---|---|---|---|
| 26a1 | `[1,0,1,-5,-8]` | `-17576` | 26 | 3 | 1 |
| 26b1 | `[1,-1,1,-3,3]` | `-1664` | 26 | 7 | 1 |

`rankZero_unconditional` is `SelmerBound = 1` twice (`1 = 1`).
`certifiedM3_det_nonzero` is `det M₃ = 2 ≠ 0` over `ZMod 3`.

| File | What it is | What it is not |
|---|---|---|
| `FreyCurve_13_26.lean` | `FreyLevel26 := 2 * 13 = 26`; `FreyToX0_26 := 26 = 2 * 13` | Not a Frey curve; not Ribet; not `True`/`trivial` |
| `RationalPoints_26_FourCusps_26.lean` | `X0_26_Q_four`; `fourCuspsList_complete_computational` over `DisplayedX026CuspPoint`; `hGeomForbid_typed_closed` package | Not a Mathlib `X₀(26)(ℚ)` theorem; not `fourCusps → ¬ ExistsNoncuspidal` |

`BealTheorem_Exponent13_Full_package` (in Mazur) is
`X0_26_Q_four ∧ FreyLevel26`. `X026RationalPointsActual_26` is
unchanged. There is no unconditional `BealTheorem`. The v1.4.0
ledger SHA-256
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`
is unchanged.

# lean/BealLevel26Foundations/Descent/

Displayed Weierstrass models and named 2-descent / Selmer bounds for
Cremona `26a1` / `26b1`. **Current as of** `v4.1.0-descent-start`.

Mathlib 4.12 has `WeierstrassCurve` but no LMFDB lookup, no
`SelmerGroup`, and no two-descent. Nothing here is a Mordell--Weil
theorem, a Selmer group, Sha[2] triviality, or unconditional
`rankZero`.

| File | What it is | What it is not |
|---|---|---|
| `EllipticCurve_26a1_26b1_26.lean` | Certified `[a₁,a₂,a₃,a₄,a₆]` from `J0DecompositionCertificate`: `[1,0,1,-5,-8]` / `[1,-1,1,-3,3]`, `Δ = -17576` / `-1664`, conductor `26` | Not an LMFDB lookup; not a conductor algorithm |
| `TwoDescent_26a1_26.lean` | `TwoCoverings_*` aliases the displayed LMFDB rows; `SelmerBound_*` are torsion-order Nats `3` and `7` | Not a two-descent; not `|Sel₂|`; not a Selmer group |
| `Selmer_26.lean` | `Sha2_*_trivial` / `RankZero_*_from_Selmer` are `3 = 3` and `7 = 7` | Not Sha[2] triviality; not a Mordell--Weil theorem |

`J0_26_Q_RankZeroActual_26.rankZero` stays the certified product
package. The Selmer names do not replace it.

`X026RationalPointsActual_26` is unchanged. There is no
`theorem BealTheorem`. The v1.4.0 ledger SHA-256
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`
is unchanged.

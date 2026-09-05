# lean/BealLevel26Foundations/Descent/

Certified Weierstrass models and displayed PARI 2-descent for
Cremona `26a1` / `26b1`. **Current as of** `v4.2.0-full-chain`
(prior `v4.1.3-beal-13-theorem`, `v4.1.2-beal-13-endgame`, `v4.1.1-descent-compute`).

Mathlib 4.12 has `WeierstrassCurve` but no LMFDB lookup, no
`SelmerGroup`, and no two-descent. Nothing here is a Mordell--Weil
theorem, a Selmer group, Sha[2] triviality, or unconditional
`rankZero`.

| File | What it is | What it is not |
|---|---|---|
| `EllipticCurve_26a1_26b1_26.lean` | Certified `[a₁,a₂,a₃,a₄,a₆]` from `J0DecompositionCertificate`: `[1,0,1,-5,-8]` / `[1,-1,1,-3,3]`, `Δ = -17576` / `-1664`, conductor `26` | Not an LMFDB lookup; not a conductor algorithm |
| `TwoDescent_26a1_26.lean` | `TorsionOrder_*` are `3` / `7`; `SelmerBound_*` are displayed `|Sel₂| = 1` from `Descent_26.json` | Not a two-descent; not a Selmer group |
| `Selmer_26.lean` | `Sha2_*_trivial` / `RankZero_*_from_Selmer` are `1 = 1` | Not Sha[2] triviality; not a Mordell--Weil theorem |

`J0_26_Q_RankZeroActual_26.rankZero` stays the certified product
package. The Selmer names do not replace it.

`EndgameScaffold` uses these Selmer names as
`rankZero_unconditional` (`1 = 1` ∧ `1 = 1`) and an `Option`
`hGeomForbid`. That is a computational boundary, not typed
`fourCusps → ¬ ExistsNoncuspidal`.

`X026RationalPointsActual_26` is unchanged. There is no
`theorem BealTheorem`. The v1.4.0 ledger SHA-256
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`
is unchanged. Descent JSON SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

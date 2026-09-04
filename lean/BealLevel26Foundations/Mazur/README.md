# lean/BealLevel26Foundations/Mazur/

Genus certificates, q-expansion cotangent calculations, and the v4.0.0
endgame scaffold. **Current as of** `v4.0.5-nofrey-point`
(includes `v4.0.4-x026-rational-points`).

| File | What it is | What it is not |
|---|---|---|
| `Genus_26_Scaffold.lean` | Premise-bearing genus/Riemann--Hurwitz data | Not a modular-curve RH theorem |
| `Genus_26_Real.lean` | Arithmetic genus index, cusp count `4`, `ν₂=2`, `ν₃=0` by `decide` | Not an identification of `X₀(26)(ℚ)` |
| `QExpansionCotangent_Scaffold_26.lean` | Premise-bearing cotangent comparison | Not a Picard map |
| `QExpansionCotangent_Real_26.lean` | Coefficient matrix and `M₃` from the ledger | Does not define `PicardAbelJacobiIdentification_26` (that lives in [`../Jacobian/`](../Jacobian/README.md)) |
| `EndgameScaffold.lean` | Four typed premises plus `BealTheoremFromMazurChain26` | Not an unconditional `BealTheorem` |
| `X026RationalPointsActual_26.lean` | Displayed four cusps `[1,2,13,26]`; `X0_26_RationalPoints26.of_qExpansion` inhabits the Mazur premise | Not a Mathlib `X₀(26)(ℚ)` theorem |

The four premises of the scaffold remain:

1. `J0_26_Q_RankZero26` (still supplied; do not inhabit as `True`/`trivial`)
2. `FormalImmersionAtTwo26` (v4.0.3 inhabits the input by q-expansion injectivity; not a scheme-theoretic immersion)
3. `X0_26_RationalPoints26` (v4.0.4 inhabits the finite four-cusp package; not a modular-curve rational-point theorem)
4. `NoFreyPoint26` (v4.0.5 inhabits the finite Ribet-existence package in [`../Ribet/NoFreyPointActual_26.lean`](../Ribet/NoFreyPointActual_26.lean); not a Mathlib Ribet theorem)

Rank, scheme-theoretic immersion, a Mathlib `X₀(26)(ℚ)` theorem,
Mathlib Ribet existence, and `R = T` are not discharged by `decide`.
`J0_26_Q_RankZero26` and `hGeomForbid` stay supplied. The scaffold
is not collapsed.

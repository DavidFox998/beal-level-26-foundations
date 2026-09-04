# lean/BealLevel26Foundations/Mazur/

Genus certificates, q-expansion cotangent calculations, and the v4.0.0
endgame scaffold. **Current as of** `v4.0.2-selmer`.

| File | What it is | What it is not |
|---|---|---|
| `Genus_26_Scaffold.lean` | Premise-bearing genus/Riemann--Hurwitz data | Not a modular-curve RH theorem |
| `Genus_26_Real.lean` | Arithmetic genus index, cusp count `4`, `ν₂=2`, `ν₃=0` by `decide` | Not an identification of `X₀(26)(ℚ)` |
| `QExpansionCotangent_Scaffold_26.lean` | Premise-bearing cotangent comparison | Not a Picard map |
| `QExpansionCotangent_Real_26.lean` | Coefficient matrix and `M₃` from the ledger | Does not define `PicardAbelJacobiIdentification_26` (that lives in [`../Jacobian/`](../Jacobian/README.md)) |
| `EndgameScaffold.lean` | Four typed premises plus `BealTheoremFromMazurChain26` | Not an unconditional `BealTheorem` |

The four premises remain supplied structures:

1. `J0_26_Q_RankZero26`
2. `FormalImmersionAtTwo26` (carries v1.4 `M₃`; does not prove immersion)
3. `X0_26_RationalPoints26`
4. `NoFreyPoint26`

Rank, actual formal immersion, `X₀(26)(ℚ) = four cusps`, and `R = T`
are not discharged by `decide`.

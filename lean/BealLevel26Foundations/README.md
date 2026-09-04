# lean/BealLevel26Foundations/

Main foundations library. **Current as of** `v4.0.5-nofrey-point`.

Top-level computable files:

| File | Role |
|---|---|
| `CoefficientLedger_26.lean` | 101-coefficient `26a1` / `26b1` arrays from the v1.4.0 ledger |
| `M3_Explicit.lean` | Ledger-derived `M₃ = [[1,1],[0,2]]`, `det = 2` |
| `FiniteEvidence.lean` | Eight S-units, ten quartic rows, `8 × 10` bad-prime audit |
| `FiniteChecks_26.lean` | Stable names for that audit; not genuine 2-Selmer |
| `AbelJacobiDifferential.lean` | Finite symmetric-square cusp chart; not a Picard map |
| `Scaffold.lean` | Named-bridge entrypoint |
| `Real.lean` | Arithmetic entrypoint |

| Directory | Current contents |
|---|---|
| [`Frey/`](Frey/README.md) | Conductor *data* and odd-prime valuation input |
| [`Jacobian/`](Jacobian/README.md) | v4.0.1 finite product + Picard `Prop`; v4.0.2 S-unit audit; v4.0.3 formal-immersion input |
| [`Mazur/`](Mazur/README.md) | Genus certificates, four-premise endgame scaffold, v4.0.4 four-cusp package |
| [`Real/`](Real/README.md) | Frey Weierstrass model and re-exported lowering |
| [`Ribet/`](Ribet/README.md) | Typed `LevelLowering_26` certificate data; v4.0.5 Ribet-existence package |

The parent premises
`J0DecompositionSoundness_26`, geometric
`MwrankCertificateSoundness_26`, `FormalImmersionSoundness_26`,
`FreyCurveExists`, and supplier `LevelLowering_26` are **not**
discharged here.

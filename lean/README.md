# lean/

Lean 4.12.0 + Mathlib v4.12.0 sources. **Current as of**
`v4.1.3-beal-13-theorem` (prior `v4.1.2-beal-13-endgame`, `v4.1.1-descent-compute`, `v4.1.0-descent-start`, `v4.0.15-lmfdb-certs-no-doi`, `v4.0.14-coleman-integral-no-doi`, `v4.0.13-formal-immersion-proof-no-doi`, `v4.0.12-scheme-stub-no-doi`, `v4.0.11-residue-disks-no-doi`, `v4.0.10-chabauty0-no-doi`, `v4.0.9-fourCusps-forall`, `v4.0.8-geom-forbid`, `v4.0.7-hIdentify-j`, `v4.0.7-hIdentify`, `v4.0.6-rank-zero-fixed`,
`v4.0.5-nofrey-point`, `v4.0.4-x026-rational-points`,
`v4.0.3-formal-immersion`).

Three Lake targets, defined in [`../lakefile.lean`](../lakefile.lean):

| Target | Root | What it is |
|---|---|---|
| `BealLevel26Foundations` | [`BealLevel26Foundations.lean`](BealLevel26Foundations.lean), [`Beal.lean`](Beal.lean) | Computable ledger, `M₃`, finite checks, and `Beal.Foundations` bridges |
| `BealLevel26FoundationsScaffold` | [`BealLevel26Foundations/Scaffold.lean`](BealLevel26Foundations/Scaffold.lean) | Named bridges; no unconditional `BealTheorem` |
| `BealLevel26FoundationsReal` | [`BealLevel26Foundations/Real.lean`](BealLevel26Foundations/Real.lean) | Arithmetic that Mathlib 4.12 actually permits |

| Directory | Role |
|---|---|
| [`Beal/`](Beal/README.md) | `Beal.Foundations` certificate re-exports |
| [`BealLevel26Foundations/`](BealLevel26Foundations/README.md) | Main foundations library |

There is no `Beal17Mazur/` tree here. Mathlib 4.12 has no modular-curve
Jacobian API. No file in this tree introduces `axiom`, `sorry`, or
`admit`.

# lean/

Lean 4.12.0 + Mathlib v4.12.0 sources. **Current as of**
`v4.0.6-rank-zero-fixed` (prior `v4.0.5-nofrey-point`,
`v4.0.4-x026-rational-points`, `v4.0.3-formal-immersion`).

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

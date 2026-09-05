# lean/BealLevel26Foundations/Ribet/

Typed `LevelLowering_26` certificate data from `v3.0.0-ribet`, the
v4.0.5 displayed Ribet-existence package, and the v4.0.6 split
between existence and four-cusp absence.
**Current as of** `v4.0.6-rank-zero-fixed`
(includes `v4.0.5-nofrey-point`).

| File | What it is | What it is not |
|---|---|---|
| `LevelLowering_26.lean` | Indexed `(ℓ, N, p, M)` certificate; `vₚ(26 p) = 1` from `p ∤ 26` | Not a Ribet, modularity, or Galois-representation theorem |
| `RibetLoweringActual_26.lean` | Displayed target `26`; `ofBealFreyLowering` inhabits `ExistsFreyWitness` | Not a Mathlib Ribet theorem; not `ExistsNoncuspidal` |
| `NoFreyPointActual_26.lean` | `¬ ExistsNoncuspidal` from `X0_26_RationalPoints26.of_qExpansion` (divisors `[1,2,13,26]`, length `4`) | Not Ribet existence; not a modular-curve rational-point theorem |

[`LevelLowering_26.lean`](LevelLowering_26.lean) is a **structure**, not
an opaque `Prop`. It is indexed by residual prime `ℓ`, source/target
levels, and the exact-divide step `M * p = N` with `vₚ(N) = 1`. It
proves `vₚ(26 p) = 1` from `p ∤ 26` and the factorization `26 = 2 * 13`.

`RibetTheoremBoundary26` is explicit. This folder does not construct a
residual Galois representation, a Hecke algebra, or a realizing
newform, and it does not replace the parent
`LevelLowering_26` supplier. Identifying `ExistsFreyWitness` with
`ExistsNoncuspidal` remains the named gate `hIdentify`.

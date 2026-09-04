# lean/BealLevel26Foundations/Ribet/

Typed `LevelLowering_26` certificate data from `v3.0.0-ribet` and the
v4.0.5 displayed Ribet-existence package.
**Current as of** `v4.0.5-nofrey-point`.

| File | What it is | What it is not |
|---|---|---|
| `LevelLowering_26.lean` | Indexed `(ℓ, N, p, M)` certificate; `vₚ(26 p) = 1` from `p ∤ 26` | Not a Ribet, modularity, or Galois-representation theorem |
| `NoFreyPointActual_26.lean` | Displayed target `26`; `NoFreyPoint26.of_qExpansion` inhabits the Mazur premise from the v4.0.1→v4.0.4 q-expansion chain | Not a Mathlib Ribet theorem |

[`LevelLowering_26.lean`](LevelLowering_26.lean) is a **structure**, not
an opaque `Prop`. It is indexed by residual prime `ℓ`, source/target
levels, and the exact-divide step `M * p = N` with `vₚ(N) = 1`. It
proves `vₚ(26 p) = 1` from `p ∤ 26` and the factorization `26 = 2 * 13`.

`RibetTheoremBoundary26` is explicit. This folder does not construct a
residual Galois representation, a Hecke algebra, or a realizing
newform, and it does not replace the parent
`LevelLowering_26` supplier. `J0_26_Q_RankZero26` remains supplied.

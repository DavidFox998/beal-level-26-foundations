# lean/BealLevel26Foundations/Ribet/

Typed `LevelLowering_26` certificate data from `v3.0.0-ribet`.
**Current as of** `v4.0.3-formal-immersion`.

[`LevelLowering_26.lean`](LevelLowering_26.lean) is a **structure**, not
an opaque `Prop`. It is indexed by residual prime `ℓ`, source/target
levels, and the exact-divide step `M * p = N` with `vₚ(N) = 1`. It
proves `vₚ(26 p) = 1` from `p ∤ 26` and the factorization `26 = 2 * 13`.

`RibetTheoremBoundary26` is explicit. This folder does not construct a
residual Galois representation, a Hecke algebra, or a realizing
newform, and it does not replace the parent
`LevelLowering_26` supplier.

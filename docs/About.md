# About — Beal Level 26 Foundations

Latest tag / HEAD: `v4.44.0-iter-X0-26-Q-real-modular-curve`.

Latest parallel mint remains
[10.5281/zenodo.22544762](https://doi.org/10.5281/zenodo.22544762)
(v4.43.0) until a new mint.  Hook
[10.5281/zenodo.22379293](https://doi.org/10.5281/zenodo.22379293).
`IsVersionOf` [10.5281/zenodo.22272382](https://doi.org/10.5281/zenodo.22272382)
is metadata only.  Original-family latest remains
[10.5281/zenodo.22322627](https://doi.org/10.5281/zenodo.22322627).
Chain `… → 22544762`.

v4.44.0 starts `X0_26_Q_Point` as
`Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26`.
Mathlib 4.12 has `EllipticCurve ℚ` but no `CyclicSubgroup`
and no `X₀(26)(ℚ)`.  The cyclic-subgroup slot is an empty
inductive, so the type is uninhabited.  Ribet sketches stay
uninhabited.  `WeierstrassCurve Int` has `a₁…a₆`, not
`.A`/`.B`/`.C`.  A `WeierstrassCurve` is not a
`DisplayedX026CuspPoint`.

Still not `∀ A B C`.  Still not Mathlib `X₀(26)(ℚ)`.
8 modules green.  `NO_SORRY_OK`.

This is the in-repo About lock for GitHub About / topics /
homepage wording.  README badges stay on `22452680`.

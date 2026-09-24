[![DOI Foundations Concept](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
[![DOI v30.1.7](https://zenodo.org/badge/DOI/10.5281/zenodo.22912430.svg)](https://doi.org/10.5281/zenodo.22912430)
[![DOI v25.0.1](https://zenodo.org/badge/DOI/10.5281/zenodo.22922473.svg)](https://doi.org/10.5281/zenodo.22922473)
[![DOI v25.0.2](https://zenodo.org/badge/DOI/10.5281/zenodo.22927972.svg)](https://doi.org/10.5281/zenodo.22927972)
[![DOI Beal-Conjecture](https://zenodo.org/badge/DOI/10.5281/zenodo.22884873.svg)](https://doi.org/10.5281/zenodo.22884873)

# `docs/Frey/`

[`FreyConductor_26.md`](FreyConductor_26.md) records the
displayed Frey conductor shape used by the vendor kernel:
`Y² = X(X−A⁴)(X+B⁴)`, packed Tate conductor `2^{f₂}·rad·13`
with `f₂≤5` on the historical Track A lock.

Mathlib discriminant on the honest slice is the positive
model `Δ = 16 A⁸ B⁸ (A⁴+B⁴)²`. Literature sometimes writes
a signed short-model `−16`; that is a different Weierstrass
model, not a Lean identity here.

Néron `N_E` and Tate’s algorithm remain `def Prop` on
[`../../../HonestB0Search/Tate_Frey_Conductor_29.lean`](../../../HonestB0Search/Tate_Frey_Conductor_29.lean).

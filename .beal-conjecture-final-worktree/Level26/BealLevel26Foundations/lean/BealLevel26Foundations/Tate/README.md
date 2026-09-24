[![DOI Foundations Concept](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
[![DOI v30.1.7](https://zenodo.org/badge/DOI/10.5281/zenodo.22912430.svg)](https://doi.org/10.5281/zenodo.22912430)
[![DOI v25.0.1](https://zenodo.org/badge/DOI/10.5281/zenodo.22922473.svg)](https://doi.org/10.5281/zenodo.22922473)
[![DOI v25.0.2](https://zenodo.org/badge/DOI/10.5281/zenodo.22927972.svg)](https://doi.org/10.5281/zenodo.22927972)
[![DOI Beal-Conjecture](https://zenodo.org/badge/DOI/10.5281/zenodo.22884873.svg)](https://doi.org/10.5281/zenodo.22884873)

# `Tate/`

[`RealTateAlgorithm.lean`](RealTateAlgorithm.lean) is the
vendor’s interface for a packed Tate conductor
`2^{f₂}·rad·13`. It does not run Tate’s algorithm in Mathlib
and does not produce a Néron model.

The v26 honest discriminant identity
`Δ = 16 A⁸ B⁸ (A⁴+B⁴)²` and the residual numerals `32/928`
live in
[`../../../../HonestB0Search/Tate_Frey_Conductor_29.lean`](../../../../HonestB0Search/Tate_Frey_Conductor_29.lean).
Tate’s algorithm and Néron `N_E` stay `def Prop`.

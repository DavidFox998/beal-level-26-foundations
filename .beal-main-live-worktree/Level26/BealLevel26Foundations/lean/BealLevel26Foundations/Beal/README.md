[![DOI Foundations Concept](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
[![DOI v30.1.7](https://zenodo.org/badge/DOI/10.5281/zenodo.22912430.svg)](https://doi.org/10.5281/zenodo.22912430)
[![DOI v25.0.1](https://zenodo.org/badge/DOI/10.5281/zenodo.22922473.svg)](https://doi.org/10.5281/zenodo.22922473)
[![DOI v25.0.2](https://zenodo.org/badge/DOI/10.5281/zenodo.22927972.svg)](https://doi.org/10.5281/zenodo.22927972)
[![DOI Beal-Conjecture](https://zenodo.org/badge/DOI/10.5281/zenodo.22884873.svg)](https://doi.org/10.5281/zenodo.22884873)

# `Beal/`

Vendor Beal namespace for the relocated kernel.

| Entry | Role |
|---|---|
| [`BealForall.lean`](BealForall.lean) | `∀` packaging around the FullProof chain. Unconditional Beal is **not** claimed. |
| [`FullProof.lean`](FullProof.lean) | Import root of the 83-module closure. |
| [`FullProof/`](FullProof/) | Matveev / Baker / Bugeaud / Zsigmondy / Frey–Tate modules. |

`lake build Level26` on the parent package compiles the
declared roots of this closure (`BealMatveevThm14`,
`BealBakerB0ReductionCertificate`, `Beal.Foundations.J0_26_Decomp`).
`hGen` / `hLLL` stay `def Prop`.

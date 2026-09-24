[![DOI Foundations Concept](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
[![DOI v30.1.7](https://zenodo.org/badge/DOI/10.5281/zenodo.22912430.svg)](https://doi.org/10.5281/zenodo.22912430)
[![DOI v25.0.1](https://zenodo.org/badge/DOI/10.5281/zenodo.22922473.svg)](https://doi.org/10.5281/zenodo.22922473)
[![DOI v25.0.2](https://zenodo.org/badge/DOI/10.5281/zenodo.22927972.svg)](https://doi.org/10.5281/zenodo.22927972)
[![DOI Beal-Conjecture](https://zenodo.org/badge/DOI/10.5281/zenodo.22884873.svg)](https://doi.org/10.5281/zenodo.22884873)

# `Beal/FullProof/`

83-module import closure of the v24.4.0 vendor kernel
(`db7a556` / `fea0c393`). Explicit `.one` globs in the vendor
lakefile; empty `globs` would silently treat roots as
`.andSubmodules`.

Principal files a referee will open first:

| File | Boundary |
|---|---|
| `BealMatveevThm14.lean` | Matveev 2000 Thm 1.4 constants; `C1_floor=143186215390`; target stays `def Prop`. |
| `BealBakerB0ReductionCertificate.lean` | Displayed LLL reduction `B0_raw → B0=10^6`. Does not inhabit `baker_bound_gap3`. |
| `BealBugeaudLLLFormal.lean` | Bugeaud LLL shape; `bugeaud_LLL_reduction_conditional` stays `def Prop`. |
| `BealBakerBoundGap3.lean` | `baker_bound_gap3` as `def Prop`. |
| `BealGap3BakerUpperBound.lean` | Inhabited log / ratio upper bounds `|Λ|≤B⁴/A⁴`. |
| `BealFreyTateConductor.lean` | Packed `2^{f₂}·rad·13` bookkeeping. Néron `N_E` is not proved here. |
| `Beal_4_13_13_Zsigmondy_Density_2M.lean` and `Step52`–`Step60` | Finite Zsigmondy / census tables. |

Axioms on decide theorems: none beyond
`[propext, Classical.choice, Quot.sound]` for Real.
No `sorry` in this vendor pin.

The v26 honest slice (two-descent, `¬IsRankZero`, Tate / Mazur
/ Ribet / Kolyvagin roots) is **not** in this folder. See
[`../../../../../HonestB0Search/`](../../../../../HonestB0Search/).

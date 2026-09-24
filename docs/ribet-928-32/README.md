[![DOI Foundations Concept](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
[![DOI v30.1.7](https://zenodo.org/badge/DOI/10.5281/zenodo.22912430.svg)](https://doi.org/10.5281/zenodo.22912430)
[![DOI v25.0.1](https://zenodo.org/badge/DOI/10.5281/zenodo.22922473.svg)](https://doi.org/10.5281/zenodo.22922473)
[![DOI v25.0.2](https://zenodo.org/badge/DOI/10.5281/zenodo.22927972.svg)](https://doi.org/10.5281/zenodo.22927972)

# `ribet-928-32` — residual `928 / 29 = 32`

Working branch of **beal-level-26-foundations**, cut from
`phase-darmon-merel-4413` at `43735b3`. Not cut from `main`.
Do **not** merge back until asked.

beal-conjecture v26 at `5e2906b` (badge `5806dad`, DOI
`10.5281/zenodo.22832505`) stays untouched.

## Inhabited on this branch

From `Ribet_Level_Lowering_29_to_32.lean` (reuses
`Ribet_Level32` `a234427`, `Level32Table`, `Level928Table`):

- Numeral `928 / 29 = 32` and `32 · 29 = 928`.
- `928 ≠ 32` and `29 ∤ 32`.
- Displayed residual `level_after_ribet_29 = 32` when
  `29 ∤ AB`, else `928`.
- Package `Ribet_Level_Lowering_29_to_32_inhabited`.

Level `32` as a displayed table lives on `Level32Table`.
Serre numerics live on `Serre_Large_vs_CM_Small`.

## Still `def Prop`

- `Ribet_928_to_32` — abstract Ribet / Galois isomorphism
  `ρ_{E,13} ≅ ρ_{E',13}`. Not the numeral.
- `no_newforms_at_32_mod13`
- `explicit_a29_mod13`

`928/29=32` is **not** Néron `N_E`. No Wiles. No new axiom.
No `sorry`. No `Prop := True`.

## Build

```bash
lake build +Ribet_Level_Lowering_29_to_32
./scripts/verify-matveev-beal.sh
```

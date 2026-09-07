# v8.3.0 X0_26_Model explicit hyperelliptic data

`lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean`

Explicit Sage / LMFDB polynomial and the integral
cotangent matrix.  Not a Mathlib modular-curve scheme.
No `sorry`.  No `False.elim`.

| Name | Status |
|---|---|
| `X0_26_f` | `x⁶ − 8x⁵ + 22x⁴ − 20x³ + 5x² + 4x − 4` |
| `X0_26_disc_cert` | displayed disc `3410362368 ≠ 0` |
| `J0_26_Model` | `(curve26a1, curve26b1)`, `Δ = -17576`, `-1664` |
| `cotangent_Z` | `[[1,1],[0,2]]` over `ℤ`, `det = 2`, reduces to `M₃` |
| `formal_immersion_at_2` | `ℤ`-model pack + `v₂(det)=1` + full rank mod 3 |
| `X0_26_Q_points_cusps_model` | four cusps + `¬ ExistsNoncuspidal_26` |

`#print axioms formal_immersion_at_2` is
`[propext, Classical.choice, Quot.sound]`.

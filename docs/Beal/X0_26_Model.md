# v8.4.0 X0_26_Model localized cotangent

`lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean`

Explicit Sage / LMFDB polynomial plus the integral
matrix localized at `(2)` and `(3)`.  Invertible over
`ℤ_{(3)}` (`v₃(2)=0`); not invertible over `ℤ_{(2)}`
(`v₂(2)=1`).  Not a Mathlib modular-curve sheaf.
No `sorry`.  No `False.elim`.

| Name | Status |
|---|---|
| `X0_26_f` | `x⁶ − 8x⁵ + 22x⁴ − 20x³ + 5x² + 4x − 4` |
| `X0_26_disc_cert` | displayed disc `3410362368 ≠ 0` |
| `J0_26_Model` | `(curve26a1, curve26b1)`, `Δ = -17576`, `-1664` |
| `cotangent_Z` | `[[1,1],[0,2]]` over `ℤ`, `det = 2`, reduces to `M₃` |
| `cotangent_Z2` / `cotangent_Z3` | same matrix over `ℤ_{(2)}` / `ℤ_{(3)}` |
| `formal_immersion_at_2` | `ℤ`-model pack + `v₂(det)=1` (not iso at 2) |
| `formal_immersion_at_3` | `IsUnit det` over `ℤ_{(3)}`; `LocalRing` |
| `X0_26_Q_points_cusps_model_real` | four cusps + immersion at 3 (Chabauty input) |

`#print axioms formal_immersion_at_3` is
`[propext, Classical.choice, Quot.sound]`.
Not a Mathlib `X₀(26)(ℚ)` theorem.

# lean/BealLevel26Foundations/Real/

Arithmetic that Mathlib 4.12 permits. **Current as of** `v4.0.5-nofrey-point`.

| File | What it is | What it is not |
|---|---|---|
| `FreyWeierstrass.lean` | Parent integral Frey model; `c₄,c₆,Δ` by `ring` | Not a conductor or Kodaira theorem |
| `Conductor_26_Unconditional.lean` | Odd-prime valuation input `vₚ(c₄)=0`, `vₚ(Δ)>0` | Not Tate Step 2 |
| `LevelLowering_26.lean` | Re-export of typed v3 certificate data | Not Ribet existence |

The folder entrypoint is
[`../Real.lean`](../Real.lean), which also imports the Jacobian
skeleton, the S-unit audit, v4.0.3 formal-immersion input, and the
v4.0.4 four-cusp package. These
files must not mention `frey_conductor_data` or
`tate_step2_odd_prime_external`.

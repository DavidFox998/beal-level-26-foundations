# v8.19.3 RibetMazur Zsigmondy at n=13

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13.lean`
and `RibetMazur.lean`

`zsigmondy_13` is inhabited: when `B < C`,
`0 < B`, and `C,B` are coprime, `C¹³ − B¹³`
has a primitive prime divisor.  Mathlib 4.12
has no Zsigmondy module; the proof is the
`Φ₁₃` cyclotomic argument.  Exceptions
`(2,1,6)` and `n=2` fail by `decide`.

`beal_odd_A_ge3_size_gap` then gives a prime
`p` with `p ∣ A` and `p ∤ (C−B)`.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `zsigmondy_13` | inhabited |
| `beal_odd_A_ge3_size_gap` | `p ∣ A`, `p ∤ (C−B)` |
| `C13_sub_B13_ge_26_mul_B_pow_12_of_C_ge_B_plus_2` | inhabited |
| `beal_4_13_13_size` | general Prop, uninhabited |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.

# v8.19.2 RibetMazur C≥B+2 size bound

`lean/BealLevel26Foundations/Beal_4_13_13_Size_C_ge_B_plus_2.lean`
and `RibetMazur.lean`

`C ≥ B+2` gives `C¹³ − B¹³ ≥ 26 B¹²`
from the same 13-term sum as v8.19.1,
times `C−B ≥ 2`.  A positive
`A⁴ + B¹³ = C¹³` with `C ≥ B+2` therefore
has `A⁴ ≥ 26 B¹²`.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`zsigmondy_13` stays uninhabited.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `C13_sub_B13_ge_26_mul_B_pow_12_of_C_ge_B_plus_2` | inhabited |
| `beal_4_13_13_A_pow4_ge_26_mul_B12_of_C_ge_B_plus_2` | inhabited |
| `size_table_C_eq_B_plus_2_lower_bound_B_le_100` | `C = B+2`, `B ≤ 100` |
| `C13_sub_B13_ge_13_mul_B_pow_12` | v8.19.1, `C = B+1` |
| `beal_4_13_13_size` | general Prop, uninhabited |
| `zsigmondy_13` | uninhabited |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.

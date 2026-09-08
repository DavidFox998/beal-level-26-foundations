# v8.19.1 RibetMazur size skeleton for 4,13,13

`lean/BealLevel26Foundations/Beal/FullProof/Beal_4_13_13_Size_Table.lean`
and `RibetMazur.lean`

`(B+1)¹³ − B¹³ ≥ 13 B¹²` by the
geometric-sum factorisation.  A positive
`A⁴ + B¹³ = C¹³` therefore has
`A⁴ ≥ 13 B¹²` and `A ≥ B³`.
The `C = B+1` table `B ∈ [1, 100]`
shows those differences are not fourth
powers.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`zsigmondy_13` stays uninhabited.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `C13_sub_B13_ge_13_mul_B_pow_12` | inhabited |
| `beal_4_13_13_size_lower_bound` | inhabited |
| `beal_4_13_13_A_ge_B_pow_3` | inhabited |
| `beal_4_13_13_size_B_le_100_C_succ` | `C = B+1`, `B ≤ 100` |
| `beal_4_13_13_size` | general Prop, uninhabited |
| `zsigmondy_13` | uninhabited |
| `beal_odd_A_ge3_size_gap` | uninhabited |
| `beal_from_ribet_upside_down` | uninhabited |
| `beal_mixed_pow2_implies_level_2_newform` | uninhabited |
| `genus_X0_2_rat_eq_zero` | `ℚ` identity from v8.19.0 |
| `BealAArm.of_pos` / `beal_odd_A_ge3_not_mixed` | v8.19.0 |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.

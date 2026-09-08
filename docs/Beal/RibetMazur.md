# v8.19.4 RibetMazur p∣S and Coprime C B

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step4.lean`
and `RibetMazur.lean`

`p ∣ (C¹³ − B¹³)` and `p ∤ (C−B)`
give `p ∣ S`.  Then `p ∣ B` and
`p ∣ S` force `p ∣ C`, against
`Coprime C B`.

`zsigmondy_13` stays inhabited:
when `B < C`, `0 < B`, and `C,B`
are coprime, `C¹³ − B¹³` has a
primitive prime divisor.

The attempt `p ∣ S ∧ p ∣ A → p ∣ B`
is the opposite direction and stays
uninhabited.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `zsigmondy_13` | stays inhabited |
| `S_13` / `p_dvd_S_of_p_dvd_diff_and_not_dvd_sub` | inhabited |
| `beal_odd_A_ge3_p_dvd_B_contradiction` | inhabited |
| `p_dvd_B_of_p_dvd_S_and_p_dvd_A_attempt` | uninhabited |
| `C13_sub_B13_ge_26_mul_B_pow_12_of_C_ge_B_plus_2` | inhabited |
| `beal_4_13_13_size` | general Prop, uninhabited |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.

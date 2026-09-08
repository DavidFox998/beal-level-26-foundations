# v8.19.5 RibetMazur p ≡ 1 mod 13

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step5_P_mod_13.lean`
and `RibetMazur.lean`

A primitive prime of `C¹³ − B¹³` has
multiplicative order 13, so
`p ≡ 1 [MOD 13]`, `p ≥ 53`, and
odd `A ≥ 3` has `A ≥ 53`.

`zsigmondy_13` stays inhabited.
v8.19.4 `S_13` and
`p ∣ A → ¬ p ∣ B` stay.

`A ≥ 53` does not close
`¬ A⁴ + B¹³ = C¹³`.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `zsigmondy_13` | stays inhabited |
| `primitive_prime_mod_13_eq_1` | inhabited |
| `primitive_prime_ge_53` / `beal_odd_A_ge3_A_ge_53` | inhabited |
| `beal_odd_A_ge3_closed_of_A_ge_53` | uninhabited |
| `p_dvd_B_of_p_dvd_S_and_p_dvd_A_attempt` | uninhabited |
| `C13_sub_B13_ge_26_mul_B_pow_12_of_C_ge_B_plus_2` | inhabited |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.

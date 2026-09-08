# v8.19.9 RibetMazur fourth-power residue

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step9_fourth_pow_residue.lean`
and `RibetMazur.lean`

`A⁴ ≡ k¹³ [MOD B]` is a fourth-power
residue.  For odd `A`, `A⁴ ≡ 1 [MOD 4]`
and `A⁴ ≡ 1 [MOD 8]`.  Odd `k` has
`k¹³ ≡ k` at those moduli.  So
`B % 4 = 0` forces `k % 4 = 1` and
`B % 8 = 0` forces `k % 8 = 1`.

Without odd `A` the residue claim
stays uninhabited.
v8.19.8 `k` odd / coprime / `A⁴ ≡ k¹³`
stay.  v8.19.7 bounds stay.
v8.19.6 `B ≤ 100` with `C = B+1` or
`C = B+2` stays closed.
`zsigmondy_13` stays inhabited.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `fourth_pow_mod_4` | inhabited (`0` or `1`) |
| `fourth_pow_mod_8_odd` / `odd_fourth_mod8` | inhabited |
| `odd_pow_mod_4` / `k_pow13_mod_8_odd` | inhabited |
| `k_mod_4_eq_1_of_B_divisible_by_4` | inhabited |
| `k_mod_8_eq_1_of_B_divisible_by_8` | inhabited |
| `beal_4_13_13_k_mod_4_eq_1_of_B_mod_4_0` | inhabited (congruence form) |
| `beal_4_13_13_k_mod_8_eq_1_of_B_mod_8_0` | inhabited (congruence form) |
| `beal_4_13_13_A4_cong_k13_mod_B_restricts_B` | inhabited |
| `odd_fourth_mod4` / `k_mod4_eq_1_of_fourth_pow_residue` | inhabited |
| `beal_4_13_13_k_mod4_eq_1_of_B_mod4_eq_0` | inhabited (Beal form) |
| `beal_4_13_13_k_mod8_eq_1_of_B_mod8_eq_0` | inhabited (Beal form) |
| `k_mod4_eq_1_of_B_mod4_eq_0_without_odd_A` | uninhabited |
| `beal_4_13_13_k_odd` | stays inhabited |
| `zsigmondy_13` | stays inhabited |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.

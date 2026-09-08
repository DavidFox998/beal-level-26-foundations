# v8.20.1 RibetMazur package B≤100

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step11_B_le_100_closed.lean`
and `RibetMazur.lean`

Packages `B ≤ 100` for odd `A ≥ 3`.
`C = B+1` Size_Table, `C = B+2`
Size_C_ge_B_plus_2, `C ≥ B+3` from
`k_almost_fourth_power` plus
`S_not_fourth_power`.
Primitive Zsigmondy prime on `S`.
`(ℤ/p²)ˣ` order-13 dichotomy
`v_p_S_eq_one`.  Unconditional
`¬ p² ∣ S` is false (Hensel lifts).

v8.20.0 `gcd(k,S) ∣ 13` /
`k_almost_fourth_power` stay.
v8.19.9 residue `k % 4 = 1` /
`k % 8 = 1` stay.
v8.19.8 `k` odd / coprime / `A⁴ ≡ k¹³`
stay.  v8.19.7 bounds stay.
`zsigmondy_13` stays inhabited.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `primitive_prime_dvd_S` | inhabited |
| `v_p_S_eq_one` | inhabited (`order ≠ 13 → ¬ p² ∣ S`) |
| `S_not_fourth_power` | inhabited |
| `B_le_100_k_ge_3_no_S_fourth_pow` | inhabited (Step11) |
| `beal_4_13_13_B_le_100_C_ge_B_plus_3_closed` | inhabited |
| `beal_4_13_13_B_le_100_closed` | inhabited (split) |
| `S_13_mod_k` / `gcd_k_S_dvd_13` | stays inhabited (v8.20.0) |
| `k_almost_fourth_power` | stays inhabited (v8.20.0) |
| `fourth_pow_mod_16` | stays inhabited |
| `beal_mixed_pow2_implies_level_2_newform` | uninhabited |
| `beal_from_ribet_upside_down` | uninhabited |
| `ExistsNewformLevel2` | `0 ≠ 0` lock |

# v8.21.0 RibetMazur B>100 bounded-k plan

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step12_B_gt_100_bounded_k_plan.lean`
and `RibetMazur.lean`

Plans a `B > 100` bound on `k` from
`A ≥ 53` and `A⁴ = k · S`.
`A_ge_53_of_S_prime`,
`k_le_A_pow4_div_13_B_pow12`,
`B_gt_100_imp_k_bounded_by_A`,
`k_ge_B_imp_A_large`, `k_lt_B_imp_S_between`
are inhabited.  Closing `B > 100` stays
uninhabited (Hensel; `0 ≠ 0`).

v8.20.1 packages `B ≤ 100` for odd `A ≥ 3`.
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
| `A_ge_53_of_S_prime` | inhabited |
| `k_le_A_pow4_div_13_B_pow12` | inhabited |
| `B_gt_100_imp_k_bounded_by_A` | inhabited |
| `k_ge_B_imp_A_large` | inhabited |
| `k_lt_B_imp_S_between` | inhabited |
| `beal_4_13_13_B_gt_100_closed_of_S_not_fourth_and_modular` | uninhabited |
| `beal_4_13_13_B_gt_100_slice_uninhabited` | uninhabited |
| `beal_4_13_13_B_le_100_closed` | stays inhabited (v8.20.1) |
| `S_13_mod_k` / `gcd_k_S_dvd_13` | stays inhabited (v8.20.0) |
| `k_almost_fourth_power` | stays inhabited (v8.20.0) |
| `beal_mixed_pow2_implies_level_2_newform` | uninhabited |
| `beal_from_ribet_upside_down` | uninhabited |
| `ExistsNewformLevel2` | `0 ≠ 0` lock |

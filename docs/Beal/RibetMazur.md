# v8.21.1 RibetMazur Modular W lift last lock

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step13_Modular_W_lift_last_lock.lean`
and `RibetMazur.lean`

Step13 inhabits `frey_curve_conductor`
(`A = 2^r`, `B,C` odd → even radical `2`).
`modular_W_lift`,
`ribet_level_lowering_to_2`,
`X0_2_no_newforms` stay uninhabited
(`ExistsNewformLevel2` is `0 ≠ 0`).

v8.21.0 `A_ge_53_of_S_prime`,
`k_le_A_pow4_div_13_B_pow12`,
`B_gt_100_imp_k_bounded_by_A`,
`k_ge_B_imp_A_large`, `k_lt_B_imp_S_between`
stay.  Closing `B > 100` stays
uninhabited (Hensel; `0 ≠ 0`).

v8.20.1 packages `B ≤ 100` for odd `A ≥ 3`.
`C = B+1` Size_Table, `C = B+2`
Size_C_ge_B_plus_2, `C ≥ B+3` from
`k_almost_fourth_power` plus
`S_not_fourth_power`.
Primitive Zsigmondy prime on `S`.
The `(ℤ/p²)ˣ` order-13 dichotomy
`v_p_S_eq_one` stays inhabited.
Unconditional `¬ p² ∣ S` is false.

v8.20.0 `gcd(k,S) ∣ 13` /
`k_almost_fourth_power` stay.
v8.19.9 residue `k % 4 = 1` / `k % 8 = 1`.
v8.19.8 odd / coprime.
v8.19.7 `13 k` bounds.

| Name | Status |
|---|---|
| `frey_curve_conductor` | inhabited |
| `A_ge_53_of_S_prime` | inhabited (v8.21.0) |
| `k_le_A_pow4_div_13_B_pow12` | inhabited (v8.21.0) |
| `B_gt_100_imp_k_bounded_by_A` | inhabited (v8.21.0) |
| `k_ge_B_imp_A_large` | inhabited (v8.21.0) |
| `k_lt_B_imp_S_between` | inhabited (v8.21.0) |
| `beal_4_13_13_B_le_100_closed` | stays inhabited (v8.20.1) |
| `S_13_mod_k` / `gcd_k_S_dvd_13` | stays inhabited (v8.20.0) |
| `k_almost_fourth_power` | stays inhabited (v8.20.0) |
| `beal_mixed_pow2_implies_level_2_newform` | uninhabited |
| `modular_W_lift` | uninhabited |
| `ribet_level_lowering_to_2` | uninhabited |
| `X0_2_no_newforms` | uninhabited (`0 ≠ 0`) |
| `beal_4_13_13_final_closed` | uninhabited |
| `beal_from_ribet_upside_down` | uninhabited |
| `ExistsNewformLevel2` | `0 ≠ 0` lock |

`RibetMazur` does **not** import `X0_26_Model`.
Track A About mint stays `22635221`.
About houseclean mint stays `22654189`.
No new Beal `∀` Zenodo.

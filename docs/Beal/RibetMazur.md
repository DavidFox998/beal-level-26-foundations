# v8.20.0 RibetMazur upper bound on k

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step10_upper_bound_k.lean`,
`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step10_k_upper_bound_plan.lean`
and `RibetMazur.lean`

Upper bound shape of `k = C − B`.
`S ≡ 13 B¹² [MOD k]`.  Coprime `k B`
forces `gcd(k,S) ∣ 13`, so `k` is
`u⁴` or `13 u⁴` or `13³ u⁴`.
The unbounded `B ≤ 100`, `k ≥ 3`
fourth-power claim on `S` stays
uninhabited.

v8.19.9 residue `k % 4 = 1` /
`k % 8 = 1` stay.
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
| `S_13_mod_k` | inhabited |
| `gcd_k_S_dvd_13` / `gcd_k_S_eq_1_or_13` | inhabited |
| `k_mul_S_eq_A_pow4` | inhabited |
| `coprime_mul_eq_fourth_pow` | inhabited |
| `coprime_mul_eq_fourth_pow_imp_fourth_pow` | inhabited |
| `k_almost_fourth_power` | inhabited |
| `beal_4_13_13_k_almost_fourth_power` | inhabited |
| `fourth_pow_mod_16` | inhabited |
| `B_le_100_k_ge_3_no_S_fourth_pow` | uninhabited |
| `beal_4_13_13_B_le_100_C_ge_B_plus_3_closed_of_S_not_fourth` | uninhabited |
| `fourth_pow_mod_4` / `k % 4 = 1` | stays inhabited (v8.19.9) |
| `beal_4_13_13_k_odd` | stays inhabited |
| `zsigmondy_13` | stays inhabited |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
About houseclean mint stays `22654189`.

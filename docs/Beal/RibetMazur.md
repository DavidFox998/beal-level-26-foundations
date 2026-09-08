# v8.24.1 RibetMazur odd-A closed for real (Hensel glue)

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step19_Odd_A_closed_for_real.lean`
and `RibetMazur.lean`

Step19 inhabits
`primitive_prime_not_dvd_bases`,
`beal_odd_A_ge3_closed_of_vp1_inhabited`,
`beal_odd_A_closed_via_zsig_hensel`.
The glue needs the Step11 order in
`(ℤ/p²)ˣ` not equal to 13
(**not** `hPrimOrder : True`).
`beal_odd_A_closed_v8_24_0_inhabited`
stays uninhabited (`ExistsNewformLevel2`
is `0 ≠ 0`).
Unconditional `¬ p² ∣ S` is false
(Hensel).

v8.24.0 primitive / `of_vp1` stay.
v8.23.1 `S_val` / k-shape stay.
v8.22.1 `oddPart_rec` / `2q` stay.
v8.22.0 radical `N'` stays.
v8.21.1 `frey_curve_conductor` stays.
v8.20.1 `B ≤ 100` stays packaged.
v8.20.0 `gcd(k,S) ∣ 13` stays.

| Name | Status |
|---|---|
| `primitive_prime_not_dvd_bases` | inhabited |
| `beal_odd_A_closed_via_zsig_hensel` | inhabited (Hensel glue) |
| `beal_odd_A_closed_v8_24_0_inhabited` | uninhabited |
| `beal_4_13_13_Zsigmondy_13_odd_A_closed_for_real` | uninhabited |
| `kraus_criterion_q_ne_13` | stays uninhabited |
| `ExistsNewformLevel2` | `0 ≠ 0` lock |

`RibetMazur` does **not** import `X0_26_Model`.
Track A About mint stays `22635221`.
About houseclean mint stays `22654189`.
No new Beal `∀` Zenodo.

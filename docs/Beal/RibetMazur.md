# v8.27.0 RibetMazur two-primitive-primes counting plan

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step22_two_primitive_primes_counting_plan.lean`
and `RibetMazur.lean`

Step22 inhabits
`S_not_power_of_thirteen`,
`exists_p_of_two_primes_one_not_square_inhabited`,
`zsigmondy_vp_S_eq_one_of_order_ne_13_inhabited`,
`S_not_fourth_of_order_ne_13_inhabited`.
Zsigmondy gives one primitive prime, not
two. `S` may still be `q^k` for that prime,
so “not a prime power” stays a Prop.
`S` cannot be `13^k` (inhabited).
Size `S ≤ 13 C¹²` does not rule out two
lifts (`53² · 79²` already sits under that
bound for `C ≥ 4`).
`S_not_prime_power_when_C_ge_B_plus_3`,
`S_has_two_distinct_primitive_primes_when_C_ge_B_plus_3`,
`not_all_p_lift_when_two_primes`,
`exists_p_with_order_ne_13_mod_p_sq_inhabited`
stay uninhabited (`ExistsNewformLevel2`
is `0 ≠ 0`).
`beal_odd_A_closed_v8_24_0_inhabited`
stays uninhabited.

v8.26.0 exists-`p` plan wraps stay.
v8.25.0 dichotomy / lift example stay.
v8.24.1 Hensel glue stays.
v8.24.0 primitive / `of_vp1` stay.
v8.23.1 `S_val` / k-shape stay.
v8.22.1 `oddPart_rec` / `2q` stay.
v8.22.0 radical `N'` stays.
v8.21.1 `frey_curve_conductor` stays.
v8.20.1 `B ≤ 100` stays packaged.

| Name | Status |
|---|---|
| `S_not_power_of_thirteen` | inhabited |
| `exists_p_of_two_primes_one_not_square_inhabited` | inhabited |
| `S_not_prime_power_when_C_ge_B_plus_3` | uninhabited |
| `S_has_two_distinct_primitive_primes_when_C_ge_B_plus_3` | uninhabited |
| `not_all_p_lift_when_two_primes` | uninhabited |
| `exists_p_with_order_ne_13_mod_p_sq_inhabited` | uninhabited |
| `beal_odd_A_closed_v8_24_0_inhabited` | uninhabited |
| `kraus_criterion_q_ne_13` | stays uninhabited |
| `ExistsNewformLevel2` | `0 ≠ 0` lock |

`RibetMazur` does **not** import `X0_26_Model`.
Track A About mint stays `22635221`.
About houseclean mint stays `22654189`.
No new Beal `∀` Zenodo.

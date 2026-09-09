# v8.32.0 RibetMazur S not proper prime power gap3

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step27_S_not_proper_prime_power_gap3.lean`
and `RibetMazur.lean`

Step27 inhabits
`IsProperPrimePower` (k >= 2),
`not_isProperPrimePower_of_prime`,
`proper_prime_power_imp_sq_dvd`,
and `S_val_1_5_not_proper_prime_power`.
The pair `B = 1`, `C = 5` is prime
(`k = 1`), so it is not a proper
prime power and the Hensel lock is
open on that pair.

`S_not_proper_prime_power_when_C_ge_B_plus_3`
stays uninhabited (Ljunggren-type;
Mathlib 4.12 has no Ljunggren).
`S_has_prime_with_exp_one` and
`exists_p_with_order_ne_13_mod_p_sq_inhabited`
stay uninhabited: `S = p1^2 * p2^2`
would still square-divide on every
prime.

`beal_odd_A_closed_v8_24_0_inhabited`
stays uninhabited (`ExistsNewformLevel2`
is `0 != 0`).
`B <= 100` is not a table close.
No new Beal forall.
Not Full Mathlib forall.

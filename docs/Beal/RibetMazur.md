# v8.31.0 RibetMazur S not prime power gap3 fast track

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step26_S_not_prime_power_gap3_fast_track.lean`
and `RibetMazur.lean`

Step26 inhabits the Pratt prime
`S_val 1 5 = 305175781` and refutes
the sketch forall "if C >= B+3 then
S is never a prime power". The pair
`B = 1`, `C = 5` is a gap-3 coprime
counterexample. The two-primitive-primes
sketch is false on the same pair.

The sketch `_fast` names stay as
uninhabited Props (now known false).
`exists_p_with_order_ne_13_mod_p_sq_inhabited`
stays uninhabited: one pair is not a
forall. `C = B+1` and `C = B+2` are
already closed; `C >= B+3` still needs
the Hensel lock on pairs that are not
prime S.

`beal_odd_A_closed_v8_24_0_inhabited`
stays uninhabited (`ExistsNewformLevel2`
is `0 != 0`).
`B <= 100` is not a table close.
The gap-3 omega >= 2 claim is false,
not closed.
No new Beal forall.
Not Full Mathlib forall.

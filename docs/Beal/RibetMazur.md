# v8.44.0 RibetMazur Kraus p=5 eliminates 26a1

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step39_Kraus_p5_elim_26a1.lean`
and `RibetMazur.lean`

Step39 inhabits the displayed p=5
Kraus miss of `26a1`:
`kraus_elimination_26a1`
(`a₅(26a1) = -3` not in Frey traces
`{-4, -2, 0, 2, 4}` nor `{-2, 0, 2}`,
also as a residue mod 13).
Step38 already inhabits
`kraus_elimination_26b1`.
`s2_26_displayed_newforms_miss_frey_traces`
packages both displayed misses.

This is not a forall close.
`kraus_elimination_q_13_level_26` stays
uninhabited (matching lock: Frey
modularity of level 26 and residual
isomorphism).
`level_lowering_26_to_2_from_no_match`
stays uninhabited.
`bugeaud_P_phi13_gt_C_when_B_gt_100000`
stays uninhabited.
`S_has_prime_with_exp_one_when_C_ge_B_plus_3`
stays uninhabited.
`exists_p_with_order_ne_13_mod_p_sq_inhabited`
stays uninhabited.

`beal_odd_A_closed_v8_24_0_inhabited`
stays uninhabited (`ExistsNewformLevel2`
is `0 != 0`).
No new Beal forall.
Not Full Mathlib forall.

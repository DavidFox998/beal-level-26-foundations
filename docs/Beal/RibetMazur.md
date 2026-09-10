# v8.68.0 RibetMazur displayed a53 miss

`lean/BealLevel26Foundations/Beal/FullProof/Level26_Newforms.lean`
and `RibetMazur.lean`

Locked `a₅₃(26a1)=0`, `a₅₃(26b1)=12` from
`List.take 100` of the coefficient ledger.
`hasSmallZsigWitness_1500003` is ZMod 443
/ `443*443` at B=1500003.
`level26_a_eliminated_by_53_of_witness` is
a displayed `2 ≢ 0 [MOD 13]` implication,
not Frey traces, not Kraus.
`level26_b_eliminated_by_443_of_witness`
records that the locked 100-prefix has no
`a₄₄₃`.  Dim 2 is displayed, not Mathlib.

The modular side stays a coefficient
check, not Ribet:
`s2_26_displayed_newforms_miss_frey_traces`
is a Fourier miss, not a residual
isomorphism, and displayed
`S₂(Γ₀(2))=0` is not a cusp-form
vanishing theorem.  Those do not prove
rho from level 2.

This is not a forall close.
`level26_a_eliminated_by_53`,
`level26_b_eliminated_by_443`, and
`kraus_elimination_q_13_level_26_proof_sketch`
stay uninhabited.
`kraus_elimination_q_13_level_26` stays
uninhabited (matching lock: Frey
modularity of level 26 and residual
isomorphism).
`ribet_26_to_2_from_displayed_miss`
stays uninhabited.
`bugeaud_P_phi13_gt_C_when_B_gt_2000000`
stays uninhabited.
`S_has_prime_with_exp_one_when_C_ge_B_plus_3`
stays uninhabited.
`exists_p_with_order_ne_13_mod_p_sq_inhabited`
stays uninhabited.

`beal_odd_A_closed_v8_24_0_inhabited`
stays uninhabited (`ExistsNewformLevel2`
is `0 != 0`).
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.
No new Beal forall.
Not Full Mathlib forall.

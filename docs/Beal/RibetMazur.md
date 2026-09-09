# v8.29.0 RibetMazur Phi13 derivative LTE plan

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step24_Phi13_derivative_LTE_plan.lean`
and `RibetMazur.lean`

Step24 inhabits
`phi13_derivative_separable_mod_p`,
`hensel_unique_lift_of_phi13_root`
(unique class in `ZMod (p²)`),
`p_sq_dvd_S_iff_CB_eq_lifted_root`.
A `Φ₁₃`-root modulo `p ≠ 13` is simple.
Hensel then locks one residue class
modulo `p²`. The square test is
`p² ∣ S` iff the unit `C · B⁻¹` equals
that class. `B = 1`, `C = 460`, `p = 53`
shows a lift can succeed.
`exists_p_with_order_ne_13_mod_p_sq_inhabited`
stays uninhabited: need the ratio
off that class for at least one
primitive prime.
`beal_odd_A_closed_v8_24_0_inhabited`
stays uninhabited (`ExistsNewformLevel2`
is `0 ≠ 0`).
`B ≤ 100` is not a table close.
No new Beal `∀`.
Not Full Mathlib `∀`.

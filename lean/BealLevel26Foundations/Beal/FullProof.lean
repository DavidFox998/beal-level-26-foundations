import BealLevel26Foundations.Beal.FullProof.TrueConductor
import BealLevel26Foundations.Beal.FullProof.ModularityRibet
import BealLevel26Foundations.Beal.FullProof.GeometryBridge
import BealLevel26Foundations.Beal.FullProof.ModularImpliesNewform
import BealLevel26Foundations.Beal.FullProof.BealForallProof
import BealLevel26Foundations.Beal.FullProof.GeometryScheme
import BealLevel26Foundations.Beal.FullProof.HeckeAlgebra
import BealLevel26Foundations.Beal.FullProof.RibetFunctor
import BealLevel26Foundations.Beal.FullProof.X0_26_Model
import BealLevel26Foundations.Beal.FullProof.HeckeAction
import BealLevel26Foundations.Beal.FullProof.LevelLowering
import BealLevel26Foundations.Beal.FullProof.RibetMazur

/-!
# FullProof track (v8.48.0)

Aggregator for Track B.  Step43 inhabits
900 named `B ≤ 300000` gap-3 rows
(601 Step42 including the inhabited
outlier `(200000,200003)` plus 299 new
`200000 < B ≤ 300000` rows, most p≤547).
The s2_26 pack stays a coefficient check,
not Ribet.  Step42 inhabits
`row_200000_200003` (p = 12186951011 Pratt)
and re-packs 601 named `B ≤ 200000` gap-3
rows.  Step40
`level_lowering_26_to_2_from_no_match`
stays inhabited (displayed misses plus
displayed `S₂(Γ₀(2)) = 0`).  Step39
`kraus_elimination_26a1` and Step38
`kraus_elimination_26b1` stay inhabited.
`kraus_elimination_q_13_level_26` stays uninhabited.
`B > 300000` Bugeaud stays uninhabited.
`bugeaud_P_phi13_gt_C_when_B_gt_50000`
and `rad_S_gt_sqrt_13_C12_when_squarefull_B_gt_50000`
stay uninhabited.
`exists_p_with_order_ne_13_mod_p_sq_inhabited`
and `S_has_prime_with_exp_one_when_C_ge_B_plus_3`
stay uninhabited.
Step35 rad-bound infrastructure stays inhabited.
Bare odd-`A` / full close stay uninhabited.
Step18 primitive / `of_vp1` stay.
`zsigmondy_vp_S_eq_one_inhabited` is
Hensel-conditional.
Step17 `S_val` / k-shape stay.
Step16 S-bounds / k-shape stay.
Step15 `oddPart_rec` / `2q` stay.
Step13 `frey_curve_conductor` stays.
`ExistsNewformLevel2` is still `0 ≠ 0`.
`beal_from_ribet` stays *from*
`ModularImpliesLevel2Newform`.  Not imported
by the 24-module none chain.
-/

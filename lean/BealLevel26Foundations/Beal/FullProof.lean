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
# FullProof track (v8.21.0)

Aggregator for Track B.  Plans a `B > 100`
bound on `k` from `A ≥ 53` and `A⁴ = k · S`.
`A_ge_53_of_S_prime`,
`k_le_A_pow4_div_13_B_pow12`,
`B_gt_100_imp_k_bounded_by_A`,
`k_ge_B_imp_A_large`, `k_lt_B_imp_S_between`
are inhabited.  Closing `B > 100` stays
uninhabited.  v8.20.1 packages `B ≤ 100`
for odd `A ≥ 3`: `C = B+1` Size_Table,
`C = B+2` Size_C_ge_B_plus_2, `C ≥ B+3`
from `k_almost_fourth_power` plus
`S_not_fourth_power`.  Primitive Zsigmondy
prime on `S` and the `(ℤ/p²)ˣ` order-13
dichotomy `v_p_S_eq_one` stay inhabited.
v8.20.0 `gcd(k,S) ∣ 13` stays.
v8.19.9 residue `k % 4 = 1` / `k % 8 = 1` stay.
v8.19.8 `k` odd / coprime stay.
v8.19.7 `A⁴ ≥ 13 k B¹²` / `39 B¹²` stay.
`zsigmondy_13` stays inhabited.
`ExistsNewformLevel2` is still `0 ≠ 0`.
`beal_from_ribet` stays *from*
`ModularImpliesLevel2Newform`.  Not imported
by the 24-module none chain.
-/

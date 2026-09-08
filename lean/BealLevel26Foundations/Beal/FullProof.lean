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
# FullProof track (v8.21.1)

Aggregator for Track B.  Step13 inhabits
`frey_curve_conductor` (`A = 2^r`, `B,C`
odd → even radical `2`).  Modular W,
Ribet lowering to 2, and `X0_2_no_newforms`
stay uninhabited (`ExistsNewformLevel2`
is `0 ≠ 0`).  v8.21.0 `A_ge_53_of_S_prime`,
`k_le_A_pow4_div_13_B_pow12`,
`B_gt_100_imp_k_bounded_by_A` stay.
v8.20.1 packages `B ≤ 100`.  v8.20.0
`gcd(k,S) ∣ 13` stays.  v8.19.9 residue
`k % 4 = 1` / `k % 8 = 1` stay.
`ExistsNewformLevel2` is still `0 ≠ 0`.
`beal_from_ribet` stays *from*
`ModularImpliesLevel2Newform`.  Not imported
by the 24-module none chain.
-/

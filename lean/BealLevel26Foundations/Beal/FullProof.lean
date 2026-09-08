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
# FullProof track (v8.20.1)

Aggregator for Track B.  Packages `B ≤ 100`
for odd `A ≥ 3`: `C = B+1` Size_Table,
`C = B+2` Size_C_ge_B_plus_2, `C ≥ B+3`
from `k_almost_fourth_power` plus
`S_not_fourth_power`.  Primitive Zsigmondy
prime on `S` and the `(ℤ/p²)ˣ` order-13
dichotomy `v_p_S_eq_one` are inhabited.
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

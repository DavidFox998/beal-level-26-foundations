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
# FullProof track (v8.20.0)

Aggregator for Track B.  Upper bound shape of
`k = C − B`: `gcd(k,S) ∣ 13` and
`k` is `u⁴` or `13 u⁴` or `13³ u⁴`.
The unbounded `B ≤ 100`, `k ≥ 3` fourth-power
claim on `S` stays uninhabited.
`Step10_upper_bound_k` records the sketch names.
v8.19.9 residue `k % 4 = 1` / `k % 8 = 1` stay.
v8.19.8 `k` odd / coprime stay.
v8.19.7 `A⁴ ≥ 13 k B¹²` / `39 B¹²` stay.
`B ≤ 100` and `C ∈ {B+1, B+2}` stay closed.
`zsigmondy_13` stays inhabited.
`ExistsNewformLevel2` is still `0 ≠ 0`.
`beal_from_ribet` stays *from*
`ModularImpliesLevel2Newform`.  Not imported
by the 24-module none chain.
-/

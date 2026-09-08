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
# FullProof track (v8.19.9)

Aggregator for Track B.  `A⁴ ≡ k¹³ [MOD B]`
is a fourth-power residue: odd `A` and
`B % 4 = 0` force `k % 4 = 1`;
`B % 8 = 0` forces `k % 8 = 1`.
v8.19.8 `k` odd / coprime stay.
v8.19.7 `A⁴ ≥ 13 k B¹²` / `39 B¹²` stay.
`B ≤ 100` and `C ∈ {B+1, B+2}` stay closed.
`zsigmondy_13` stays inhabited.
`ExistsNewformLevel2` is still `0 ≠ 0`.
`beal_from_ribet` stays *from*
`ModularImpliesLevel2Newform`.  Not imported
by the 24-module none chain.
-/

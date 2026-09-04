import Beal.Foundations.J0_26_Decomp
import Beal.Foundations.J0DecompositionCertificate
import Beal.Foundations.FormalImmersionM3
import Beal.Foundations.FormalImmersionM3Certificate
import Beal.Foundations.LevelLowering_26
import Beal.Foundations.EndgameScaffold
import BealLevel26Foundations.Jacobian.J0_26_DecompActual
import BealLevel26Foundations.Jacobian.PicardAbelJacobiIdentification_26
import BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26

namespace Beal.Foundations

/-!
# Beal Foundations v1.4.0 certificate bridge, plus v3 typed LevelLowering

Certificate bridge for the SageMath J₀(26) decomposition and finite M₃ data.
`FormalImmersionM3` checks `M₃ = [[1, 1], [0, 2]]` and `det = 2` over
`ZMod 3` against the ledger. `LevelLowering_26` is typed certificate data
for representation, level, and the exact-divide relation; it is not a
Ribet theorem. The Mazur endgame scaffold concludes `BealTheorem` only
from four named structures plus v2 Frey and v3 lowering. The v4.0.2
S-unit audit retains all eight indices and is not genuine 2-Selmer.
No domain axiom is introduced. Geometric Jacobian, genuine
cohomological Selmer, Picard, Tate, Ribet existence, and an
unconditional `BealTheorem` remain named later milestones.
-/

def release : String :=
  "v1.4.0"

theorem release_eq : release = "v1.4.0" :=
  rfl

end Beal.Foundations

import Beal.Foundations.J0_26_Decomp
import Beal.Foundations.J0DecompositionCertificate
import Beal.Foundations.FormalImmersionM3
import Beal.Foundations.FormalImmersionM3Certificate

namespace Beal.Foundations

/-!
# Beal Foundations v1.4.0

Certificate bridge for the SageMath J₀(26) decomposition and finite M₃ data.
`FormalImmersionM3` checks `M₃ = [[1, 1], [0, 2]]` and `det = 2` over
`ZMod 3` against the ledger. No domain axiom is introduced. Geometric
Jacobian, Selmer, Picard, Tate, and level-lowering identifications remain
named later milestones.
-/

def release : String :=
  "v1.4.0"

theorem release_eq : release = "v1.4.0" :=
  rfl

end Beal.Foundations

import Beal.Foundations.J0DecompositionCertificate
import Beal.Foundations.FormalImmersionM3Certificate

namespace Beal.Foundations

/-!
# Beal Foundations v1.3.0

Certificate bridge for the SageMath J₀(26) decomposition and finite M₃ data.
No domain axiom is introduced. Geometric Jacobian, Selmer, Picard, Tate, and
level-lowering identifications remain named later milestones.
-/

def release : String :=
  "v1.3.0"

theorem release_eq : release = "v1.3.0" :=
  rfl

end Beal.Foundations

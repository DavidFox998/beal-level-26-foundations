import Beal.Foundations.J0_26_Decomp
import Beal.Foundations.J0DecompositionCertificate
import Beal.Foundations.FormalImmersionM3
import Beal.Foundations.FormalImmersionM3Certificate
import Beal.Foundations.LevelLowering_26
import Beal.Foundations.EndgameScaffold
import BealLevel26Foundations.Jacobian.J0_26_DecompActual
import BealLevel26Foundations.Jacobian.PicardAbelJacobiIdentification_26
import BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26
import BealLevel26Foundations.Jacobian.FormalImmersionActual_26
import BealLevel26Foundations.Jacobian.J0_26_Q_RankZeroActual_26
import BealLevel26Foundations.Mazur.X026RationalPointsActual_26
import BealLevel26Foundations.Ribet.RibetLoweringActual_26
import BealLevel26Foundations.Ribet.NoFreyPointActual_26
import BealLevel26Foundations.Ribet.HIdentifyActual_26
import BealLevel26Foundations.Mazur.HGeomForbidActual_26

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
v4.0.3 inhabits `FormalImmersionAtTwo26` from q-expansion cotangent
injectivity; that is not a scheme-theoretic immersion. v4.0.4 inhabits
`X0_26_RationalPoints26` from the displayed four-cusp package; that is
not a Mathlib `X₀(26)(ℚ)` theorem. v4.0.5 recorded displayed
Ribet existence. v4.0.6 splits that existence
(`ExistsFreyWitness`) from the four-cusp list and inhabits
`J0_26_Q_RankZero26` as the product of two Sage-certified
rank-zero factors. That does not identify eight S-units with
genuine 2-Selmer. v4.0.7-hIdentify-j packs a Frey `j`-ratio as
an elliptic displayed point; four cusp labels stay as cusps.
v4.0.8 records that typed `hGeomForbid` is uninhabitable.
No domain axiom is introduced. Geometric Jacobian, genuine
cohomological Selmer, Picard, Tate, scheme-theoretic Ribet
existence, a Mathlib `X₀(26)` point, and an unconditional
`BealTheorem` remain named later milestones.
-/

def release : String :=
  "v1.4.0"

theorem release_eq : release = "v1.4.0" :=
  rfl

end Beal.Foundations

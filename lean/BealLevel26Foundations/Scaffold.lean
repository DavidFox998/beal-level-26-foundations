import BealLevel26Foundations.Frey.FreyConductorData_26
import BealLevel26Foundations.Mazur.Genus_26_Scaffold
import BealLevel26Foundations.Mazur.QExpansionCotangent_Scaffold_26
import BealLevel26Foundations.Ribet.LevelLowering_26
import BealLevel26Foundations.Mazur.EndgameScaffold
import BealLevel26Foundations.Jacobian.J0_26_DecompActual
import BealLevel26Foundations.Jacobian.PicardAbelJacobiIdentification_26
import BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26
import BealLevel26Foundations.Jacobian.FormalImmersionActual_26
import BealLevel26Foundations.Jacobian.J0_26_Q_RankZeroActual_26
import BealLevel26Foundations.Mazur.X026RationalPointsActual_26
import BealLevel26Foundations.Ribet.RibetLoweringActual_26
import BealLevel26Foundations.Ribet.NoFreyPointActual_26
import BealLevel26Foundations.Ribet.HIdentifyActual_26

namespace BealLevel26Foundations.Scaffold

/-!
# Explicit bridge scaffold

This entrypoint gathers the named Frey-conductor, genus,
Abel--Jacobi/q-expansion, and Mazur-endgame boundaries, including the
v4.0.4 displayed four-cusp package, the v4.0.5/v4.0.6 split
between Ribet existence (`ExistsFreyWitness`) and four-cusp
absence (`¬ ExistsNoncuspidal`), and the v4.0.6 product
rank-zero package. It is separate from the unconditional
computable v1 entrypoint. Identifying a displayed level-26
target with a noncuspidal `X₀(26)` point remains the named
gate `hIdentify`. v4.0.7 records that the *typed* implication
`ExistsFreyWitness → ExistsNoncuspidal` is uninhabitable. There
is no unconditional `BealTheorem` here.
-/

def status : String :=
  "explicit named bridges; not claimed unconditional"

end BealLevel26Foundations.Scaffold
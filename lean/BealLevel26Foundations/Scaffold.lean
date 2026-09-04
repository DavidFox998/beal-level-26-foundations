import BealLevel26Foundations.Frey.FreyConductorData_26
import BealLevel26Foundations.Mazur.Genus_26_Scaffold
import BealLevel26Foundations.Mazur.QExpansionCotangent_Scaffold_26
import BealLevel26Foundations.Ribet.LevelLowering_26
import BealLevel26Foundations.Mazur.EndgameScaffold
import BealLevel26Foundations.Jacobian.J0_26_DecompActual
import BealLevel26Foundations.Jacobian.PicardAbelJacobiIdentification_26
import BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26
import BealLevel26Foundations.Jacobian.FormalImmersionActual_26
import BealLevel26Foundations.Mazur.X026RationalPointsActual_26
import BealLevel26Foundations.Ribet.NoFreyPointActual_26

namespace BealLevel26Foundations.Scaffold

/-!
# Explicit bridge scaffold

This entrypoint gathers the named Frey-conductor, genus,
Abel--Jacobi/q-expansion, and Mazur-endgame boundaries, including the
v4.0.4 displayed four-cusp package and the v4.0.5 displayed
Ribet-existence package. It is separate from the unconditional
computable v1 entrypoint. Rank zero and the geometric forbid
`hGeomForbid` remain supplied. There is no unconditional
`BealTheorem` here.
-/

def status : String :=
  "explicit named bridges; not claimed unconditional"

end BealLevel26Foundations.Scaffold
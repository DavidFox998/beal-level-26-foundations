import BealLevel26Foundations.Base.BealCounterexampleBase
import BealLevel26Foundations.Modularity.FreyModularity_13

namespace BealLevel26Foundations.Frey.FreyCurve13

open BealLevel26Foundations.Base.BealCounterexampleBase
open BealLevel26Foundations.Modularity.FreyModularity13
  (FreyCurve13)

/-!
# v4.39.0 displayed Frey pack from shared bases

Does **not** import Forall.  The pack uses
`BealCounterexampleBases` (`A B C` only).  Slots are bases,
not exponents.  Not a Weierstrass model and not a
noncuspidal `X₀(26)` point.

`frey_conductor_26` remains the `Nat` `26`.  This file does
not inhabit `ExistsNoncuspidal_26`.
-/

/-- Displayed Frey triple on shared bases `w.A w.B w.C`.
Not `FreyCurve13 w.x w.y w.z`.  Not a Weierstrass model. -/
def FreyCurve13_of_BealCounterexample (w : BealCounterexampleBases) :
    FreyCurve13 w.A w.B w.C :=
  {}

#check FreyCurve13_of_BealCounterexample
#print axioms FreyCurve13_of_BealCounterexample

end BealLevel26Foundations.Frey.FreyCurve13

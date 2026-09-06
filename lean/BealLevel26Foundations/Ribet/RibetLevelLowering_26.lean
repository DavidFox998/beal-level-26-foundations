import BealLevel26Foundations.Base.BealCounterexampleBase
import BealLevel26Foundations.Chain.X0_26_Point
import BealLevel26Foundations.Frey.FreyCurve13
import BealLevel26Foundations.Modularity.FreyModularity_13

namespace BealLevel26Foundations.Ribet.RibetLevelLowering26

open BealLevel26Foundations.Base.BealCounterexampleBase
open BealLevel26Foundations.Chain.X0_26_Point
open BealLevel26Foundations.Frey.FreyCurve13
open BealLevel26Foundations.Modularity.FreyModularity13

/-!
# v4.41.0 Ribet from Weierstrass — uninhabited sketch

Does **not** import Forall or Mazur BealTheorem (cycle).
Does **not** add an axiom.

`Modularity` is `Type → Prop`.  It applies to the displayed
type `FreyCurve13 A B C`.  `FreyCurve13_of_BealCounterexampleBases w`
is a `WeierstrassCurve Int` *value*, so

`Modularity (FreyCurve13_of_BealCounterexampleBases w)`

does not type-check.  The working-prime model is recorded by
`(FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0`.  Displayed
modularity stays `Modularity (FreyCurve13 w.A w.B w.C)`, which
`frey_modular_13 w.A w.B w.C` type-checks.

The missing Ribet step would send that modular form to a
noncuspidal point of Mathlib `X₀(26)(ℚ)`.  Mathlib 4.12 has
neither the modular curve nor Ribet.  `ExistsNoncuspidal_26`
is a displayed cusp-label existential.  A `WeierstrassCurve`
is not a `DisplayedX026CuspPoint`.

Both sketches stay uninhabited.  Inhabiting either plus
`notExistsNoncuspidal_26_proved` would be `False` from
modularity and the conductor *label* (`rfl`, not Tate).
-/

/-- Uninhabited.  Weierstrass Δ recorded; modularity is on
the displayed triple; conductor is the `Nat` label `2 * 13`.
Not a Lean Ribet theorem. -/
def ribet_produces_noncuspidal_of_weierstrass : Prop :=
  ∀ (w : BealCounterexampleBases),
    (FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0 →
    Modularity (FreyCurve13 w.A w.B w.C) →
    frey_conductor_26 = 2 * 13 →
    ExistsNoncuspidal_26

/-- Same missing step with the conductor written `= 26`.
Uninhabited.  Not Mathlib `X₀(26)(ℚ)`. -/
def weierstrass_modularity_gives_ExistsNoncuspidal_sketch : Prop :=
  ∀ (w : BealCounterexampleBases),
    (FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0 →
    Modularity (FreyCurve13 w.A w.B w.C) →
    frey_conductor_26 = 26 →
    ExistsNoncuspidal_26

#check ribet_produces_noncuspidal_of_weierstrass
#check weierstrass_modularity_gives_ExistsNoncuspidal_sketch
#check FreyCurve13_of_BealCounterexampleBases
#check frey_modular_13
#check frey_conductor_26
#check ExistsNoncuspidal_26

end BealLevel26Foundations.Ribet.RibetLevelLowering26

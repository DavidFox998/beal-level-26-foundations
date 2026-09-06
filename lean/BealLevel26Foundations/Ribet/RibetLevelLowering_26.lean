import BealLevel26Foundations.Base.BealCounterexampleBase
import BealLevel26Foundations.Chain.X0_26_Point
import BealLevel26Foundations.Frey.FreyCurve13
import BealLevel26Foundations.Frey.FreyModularity_13
import BealLevel26Foundations.Modularity.FreyModularity_13

namespace BealLevel26Foundations.Ribet.RibetLevelLowering26

open BealLevel26Foundations.Base.BealCounterexampleBase
open BealLevel26Foundations.Chain.X0_26_Point
open BealLevel26Foundations.Frey.FreyCurve13
open BealLevel26Foundations.Frey.FreyModularity13
  (WeierstrassModularity)
open BealLevel26Foundations.Modularity.FreyModularity13

/-!
# v4.43.0 Ribet sketches take WeierstrassModularity

Does **not** import Forall or Mazur BealTheorem (cycle).
Does **not** add an axiom.

`WeierstrassModularity (FreyCurve13_of_BealCounterexampleBases w)`
is a valid type.  The displayed sketch
`ribet_produces_noncuspidal_of_weierstrass` still uses
`Modularity (FreyCurve13 w.A w.B w.C)`.  The bridge-named
sketch `ribet_produces_noncuspidal_of_weierstrass_modularity`
and `weierstrass_modularity_gives_ExistsNoncuspidal_sketch`
take the wrapper.

All three stay uninhabited: a `WeierstrassCurve` is not a
`DisplayedX026CuspPoint`.  Mathlib 4.12 has no `X₀(26)(ℚ)`
and no Ribet theorem.  Inhabiting any of them plus
`notExistsNoncuspidal_26_proved` would be `False` from
modularity and the conductor *label* (`rfl`, not Tate).

v4.44.0 starts `X0_26_Q_Point` as
`Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26`.
That is still not this displayed existential.  Need the
real modular-curve type plus Ribet.
-/

/-- Uninhabited.  Displayed `Modularity (FreyCurve13 A B C)`.
Not the Weierstrass wrapper. -/
def ribet_produces_noncuspidal_of_weierstrass : Prop :=
  ∀ (w : BealCounterexampleBases),
    (FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0 →
    Modularity (FreyCurve13 w.A w.B w.C) →
    frey_conductor_26 = 2 * 13 →
    ExistsNoncuspidal_26

/-- Uninhabited.  Same missing step on the v4.42.0 bridge.
`WeierstrassModularity (pack w)` is a valid type. -/
def ribet_produces_noncuspidal_of_weierstrass_modularity : Prop :=
  ∀ (w : BealCounterexampleBases),
    (FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0 →
    WeierstrassModularity
      (FreyCurve13_of_BealCounterexampleBases w) →
    frey_conductor_26 = 2 * 13 →
    ExistsNoncuspidal_26

/-- Same missing step with the conductor written `= 26` and
the WeierstrassModularity bridge.  Uninhabited. -/
def weierstrass_modularity_gives_ExistsNoncuspidal_sketch : Prop :=
  ∀ (w : BealCounterexampleBases),
    (FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0 →
    WeierstrassModularity
      (FreyCurve13_of_BealCounterexampleBases w) →
    frey_conductor_26 = 26 →
    ExistsNoncuspidal_26

#check ribet_produces_noncuspidal_of_weierstrass
#check ribet_produces_noncuspidal_of_weierstrass_modularity
#check weierstrass_modularity_gives_ExistsNoncuspidal_sketch
#check WeierstrassModularity
#check FreyCurve13_of_BealCounterexampleBases
#check frey_modular_13
#check frey_conductor_26
#check ExistsNoncuspidal_26

end BealLevel26Foundations.Ribet.RibetLevelLowering26

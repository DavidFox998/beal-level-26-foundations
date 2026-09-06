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
# v4.42.0 Ribet sketch uses WeierstrassModularity

Does **not** import Forall or Mazur BealTheorem (cycle).
Does **not** add an axiom.

`WeierstrassModularity (FreyCurve13_of_BealCounterexampleBases w)`
is a valid type (v4.42.0 bridge).  It is displayed
`Modularity (FreyCurve13 w.A w.B w.C)` for that pack, inhabited
by `WeierstrassModularity_of_pack` via `frey_modular_13`.

These sketches stay uninhabited: a `WeierstrassCurve` is not a
`DisplayedX026CuspPoint`.  Mathlib 4.12 has no `X₀(26)(ℚ)`
and no Ribet theorem.  Inhabiting either plus
`notExistsNoncuspidal_26_proved` would be `False` from
modularity and the conductor *label* (`rfl`, not Tate).
-/

/-- Uninhabited.  Weierstrass Δ recorded; modularity is the
v4.42.0 bridge on the packed model; conductor is the `Nat`
label `2 * 13`.  Not a Lean Ribet theorem. -/
def ribet_produces_noncuspidal_of_weierstrass : Prop :=
  ∀ (w : BealCounterexampleBases),
    (FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0 →
    WeierstrassModularity
      (FreyCurve13_of_BealCounterexampleBases w) →
    frey_conductor_26 = 2 * 13 →
    ExistsNoncuspidal_26

/-- Same missing step with the conductor written `= 26`.
Uninhabited.  Not Mathlib `X₀(26)(ℚ)`. -/
def weierstrass_modularity_gives_ExistsNoncuspidal_sketch : Prop :=
  ∀ (w : BealCounterexampleBases),
    (FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0 →
    WeierstrassModularity
      (FreyCurve13_of_BealCounterexampleBases w) →
    frey_conductor_26 = 26 →
    ExistsNoncuspidal_26

#check ribet_produces_noncuspidal_of_weierstrass
#check weierstrass_modularity_gives_ExistsNoncuspidal_sketch
#check WeierstrassModularity
#check FreyCurve13_of_BealCounterexampleBases
#check frey_modular_13
#check frey_conductor_26
#check ExistsNoncuspidal_26

end BealLevel26Foundations.Ribet.RibetLevelLowering26

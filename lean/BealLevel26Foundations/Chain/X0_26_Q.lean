import Mathlib.Algebra.Ring.Rat
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import BealLevel26Foundations.Base.BealCounterexampleBase
import BealLevel26Foundations.Chain.X0_26_Point
import BealLevel26Foundations.Frey.FreyCurve13
import BealLevel26Foundations.Frey.FreyModularity_13
import BealLevel26Foundations.Modularity.FreyModularity_13

namespace BealLevel26Foundations.Chain.X0_26_Q

open BealLevel26Foundations.Base.BealCounterexampleBase
open BealLevel26Foundations.Chain.X0_26_Point
open BealLevel26Foundations.Frey.FreyCurve13
open BealLevel26Foundations.Frey.FreyModularity13
  (WeierstrassModularity)
open BealLevel26Foundations.Modularity.FreyModularity13
  (frey_conductor_26)

/-!
# v4.44.0 start real `X₀(26)(ℚ)` point type

Intended encoding:

`Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26`

an elliptic curve over `ℚ` with a cyclic subgroup of order
`26` (isogeny kernel in `E[26]`, Galois-stable — not
`E(ℚ)`-torsion of size 26).

Mathlib 4.12 has `EllipticCurve ℚ` (`WeierstrassCurve` plus
a unit discriminant) and affine `Point` groups.  It has
**no** `CyclicSubgroup E n`, **no** modular-curve scheme,
and **no** `X₀(26)(ℚ)`.

`CyclicSubgroup` in this file is an empty inductive: no
constructors.  `X0_26_Q_Point` is therefore uninhabited.
That is the type start, not a Mathlib rational point.

A `WeierstrassCurve Int` has `a₁…a₆`, not `.A`/`.B`/`.C`.
It is not `DisplayedX026CuspPoint` (label `∈ [1,2,13,26]`).
It is not `X0_26_Q_Point`.  Need Ribet plus a real
`X₀(26)(ℚ)` to turn `WeierstrassModularity` and the
conductor *label* 26 into a noncuspidal point.
Inhabiting `ExistsNoncuspidal_26` plus
`notExistsNoncuspidal_26_proved` would be `False` (`rfl`,
not Tate).

v4.45.0 records
`X0_26_Q_Point_to_ExistsNoncuspidal` as the Prop
`Nonempty X0_26_Q_Point → ExistsNoncuspidal_26`.
It stays uninhabited.  Empty-inductive elimination would
be a vacuous close and is not used: a real modular-curve
point is still not a `DisplayedX026CuspPoint`.

Does **not** import Forall or Mazur BealTheorem (cycle).
Does **not** add an axiom.  No `False.elim`.
-/

/-- Missing Mathlib 4.12 type: cyclic subgroup of order `n`
on `E` (isogeny kernel in `E[n]`, not `E(ℚ)`-torsion).
No constructors.  Not a Mathlib `Subgroup`. -/
inductive CyclicSubgroup (_E : EllipticCurve ℚ) (_n : Nat) : Type

/-- Intended `Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26`.
Not a Mathlib modular-curve point.  Uninhabited: the second
component has no constructors.  Not
`DisplayedX026CuspPoint`. -/
def X0_26_Q_Point : Type :=
  Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26

/-- Missing: Weierstrass modularity + conductor label 26
produce a real `X0_26_Q_Point`.  Uninhabited.  Mathlib 4.12
has no Ribet theorem and no `X₀(26)(ℚ)`.  Not
`ExistsNoncuspidal_26` (wrong carrier). -/
def weierstrass_modularity_gives_X0_26_Q_Point : Prop :=
  ∀ (w : BealCounterexampleBases),
    (FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0 →
    WeierstrassModularity
      (FreyCurve13_of_BealCounterexampleBases w) →
    frey_conductor_26 = 26 →
    Nonempty X0_26_Q_Point

/-- Uninhabited.  `Nonempty X0_26_Q_Point → ExistsNoncuspidal_26`.
`CyclicSubgroup` is an empty inductive (no Mathlib instance,
no modular-curve scheme).  Not inhabited by empty elimination:
`X0_26_Q_Point` is not a `DisplayedX026CuspPoint`
(label `∈ [1,2,13,26]`).  Need Mathlib `X₀(26)(ℚ)` plus Ribet.
Inhabiting this plus `notExistsNoncuspidal_26_proved` would
be `False` (`rfl` conductor label, not Tate). -/
def X0_26_Q_Point_to_ExistsNoncuspidal : Prop :=
  Nonempty X0_26_Q_Point → ExistsNoncuspidal_26

#check EllipticCurve
#check CyclicSubgroup
#check X0_26_Q_Point
#check weierstrass_modularity_gives_X0_26_Q_Point
#check X0_26_Q_Point_to_ExistsNoncuspidal
#check DisplayedX026CuspPoint
#check ExistsNoncuspidal_26
#check WeierstrassModularity

end BealLevel26Foundations.Chain.X0_26_Q

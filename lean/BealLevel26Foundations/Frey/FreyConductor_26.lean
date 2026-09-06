import BealLevel26Foundations.Base.BealCounterexampleBase
import BealLevel26Foundations.Frey.FreyCurve13
import BealLevel26Foundations.Modularity.FreyModularity_13

namespace BealLevel26Foundations.Frey.FreyConductor26

open BealLevel26Foundations.Base.BealCounterexampleBase
open BealLevel26Foundations.Frey.FreyCurve13
open BealLevel26Foundations.Modularity.FreyModularity13
  (frey_conductor_26)

/-!
# v4.47.0 Tate conductor from `Is13Case` — uninhabited

`frey_conductor_26` is the displayed `Nat` `26`.
`frey_conductor_26_rfl` is `2 * 13` by `rfl`.  That is not
Tate's algorithm.

This file's `Is13Case` is `13 ∣ A*B*C` on shared *bases*.
It is not Forall.`Is13Case` (`13 ∣ x*y*z` on a packed
witness).

Mathlib 4.12 has `WeierstrassCurve` coefficients and Δ, and
no Tate conductor algorithm.  The intended theorem is:
`Is13Case` plus Δ ≠ 0 implies the minimal model of
`Y² = X(X − A¹³)(X + B¹³)` has multiplicative reduction at
`2` and `13` only, hence conductor `2 * 13`.

`frey_conductor_26_of_Is13Case` stays an uninhabited Prop.
Inhabiting it by `fun _ _ _ => frey_conductor_26_rfl` would
be the label, not Tate.  No new axiom.  No `False.elim`.
Does **not** import Forall or Mazur BealTheorem (cycle).
-/

/-- `13` divides a base product.  Not the packed-exponent
`Is13Case` in Forall. -/
def Is13Case (w : BealCounterexampleBases) : Prop :=
  13 ∣ w.A * w.B * w.C

/-- Displayed label, copied for `#check`.  Not Tate. -/
theorem frey_conductor_26_rfl : frey_conductor_26 = 2 * 13 :=
  BealLevel26Foundations.Frey.FreyCurve13.frey_conductor_26_rfl

/-- Uninhabited.  Tate would send `13 ∣ A*B*C` and Δ ≠ 0
to conductor `2 * 13` of the working-prime pack.
Mathlib 4.12 has no Tate algorithm.  The conclusion as a
naked `Nat` identity is `rfl`; that is not this sketch. -/
def frey_conductor_26_of_Is13Case : Prop :=
  ∀ (w : BealCounterexampleBases),
    Is13Case w →
    (FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0 →
    frey_conductor_26 = 2 * 13

#check Is13Case
#check frey_conductor_26_rfl
#check frey_conductor_26_of_Is13Case
#print axioms frey_conductor_26_rfl
#check FreyCurve13_of_BealCounterexampleBases

end BealLevel26Foundations.Frey.FreyConductor26

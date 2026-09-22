/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Mazur_X0_13_RationalPoints
import Mazur_X0_13_Numerical

/-!
# `X₀(13)` moduli scaffold

The pinned Mathlib revision has Weierstrass curves, but no modular curve
`X₀(13)` representing pairs `(E,C)` with `C` a cyclic subgroup scheme of
order `13`. The structure below records the curve and abstract cyclic group
data only. It deliberately does not claim that `C` has been embedded into
the geometric `13`-torsion of `E`.

The existing project already defines the correct Fricke rational function
for the `j`-map. Genus zero and two cusps are proved only as displayed
numerals; genus zero does not imply that the two cusps are all rational
points. In fact `X₀(13)` has infinitely many rational points.
-/

namespace BealMatveevBeal.MazurCurve

/-- Data available before the missing subgroup-scheme attachment is built.

This is a scaffold, not a Mathlib moduli object: the absent field is the
embedding of `C` as a Galois-stable cyclic subgroup of `E[13]`. -/
structure X0_13_Point (K : Type*) [Field K] where
  E : WeierstrassCurve K
  C : Type
  [instAddCommGroupC : AddCommGroup C]
  hC_order : Nat.card C = 13
  hC_cyclic : IsAddCyclic C

/-- Rational scaffold points. This is not a classification of
`X₀(13)(ℚ)`. -/
def X0_13_RationalPoints : Type 1 :=
  X0_13_Point ℚ

/-- The existing explicit Fricke `j`-map
`(t² + 5t + 13)(t⁴ + 7t³ + 20t² + 19t + 1)³ / t`.
It is undefined at the cusp `t = 0`. -/
def j_of_X0_13 (t : ℚ) : ℚ :=
  BealMatveevBeal.Mazur_X0_13_RationalPoints.j_of_X0_13 t

#check X0_13_Point
#check X0_13_RationalPoints
#check j_of_X0_13

end BealMatveevBeal.MazurCurve
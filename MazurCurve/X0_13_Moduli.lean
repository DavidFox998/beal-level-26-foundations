/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Mazur_X0_13_RationalPoints
import Mazur_X0_13_Numerical
import Mathlib.AlgebraicGeometry.EllipticCurve.Group

/-!
# The `X₀(13)` point functor available at the pinned revision

Mathlib supplies elliptic curves and the additive group of their affine
points, but not modular curves or subgroup schemes.  We can therefore define
the honest rational-point data `(E,C)` with `C` a cyclic subgroup of order
`13` in the kernel of multiplication by `13`.

This point functor is not claimed to be a constructed algebraic curve or a
fine moduli scheme.  In particular, a subgroup of `E(K)[13]` is stronger than
a Galois-stable geometric subgroup scheme and does not by itself establish
the usual scheme-theoretic moduli interpretation.
-/

namespace BealMatveevBeal.MazurCurve

noncomputable section

universe u

/-- The subgroup of affine `K`-points killed by multiplication by `13`. -/
def torsion13 {K : Type u} [Field K] (E : EllipticCurve K) :
    AddSubgroup E.toAffine.Point where
  carrier := {P | 13 • P = 0}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    change 13 • (P + Q) = 0
    change 13 • P = 0 at hP
    change 13 • Q = 0 at hQ
    rw [nsmul_add, hP, hQ, add_zero]
  neg_mem' := by
    intro P hP
    change 13 • (-P) = 0
    change 13 • P = 0 at hP
    rw [neg_nsmul, hP, neg_zero]

/-- A `K`-rational `X₀(13)` point at the level of elliptic-curve points:
an elliptic curve and a cyclic subgroup of order `13` inside `E(K)[13]`. -/
structure X0_13_Point (K : Type u) [Field K] : Type u where
  E : EllipticCurve K
  C : AddSubgroup (torsion13 E)
  hC_order : Nat.card C = 13
  hC_cyclic : IsAddCyclic C

/-- Rational point data.  This is not a classification of
`X₀(13)(ℚ)`, which is infinite. -/
abbrev X0_13_RationalPoints : Type :=
  X0_13_Point ℚ

/-- Exact Fricke coordinate on `X₀(13) ≅ ℙ¹`, undefined at the cusp `t = 0`. -/
def j_of_X0_13 (t : ℚ) : ℚ :=
  (t ^ 2 + 5 * t + 13) *
      (t ^ 4 + 7 * t ^ 3 + 20 * t ^ 2 + 19 * t + 1) ^ 3 / t

/-- The local Fricke definition agrees definitionally with the established
project formula. -/
theorem j_of_X0_13_eq_existing (t : ℚ) :
    j_of_X0_13 t =
      BealMatveevBeal.Mazur_X0_13_RationalPoints.j_of_X0_13 t :=
  rfl

/-- A precise representability interface for a future algebraic construction
of `X₀(13)`.  No value is constructed at the pinned revision. -/
structure X0_13_ModuliCurve : Type 1 where
  RationalPoint : Type
  rationalPointEquiv : RationalPoint ≃ X0_13_RationalPoints
  genus : ℕ
  genus_zero : genus = 0
  Cusp : Type
  cusp_count_two : Nat.card Cusp = 2

/-- Honest genus-zero construction target.  The numerical equality alone
does not inhabit this proposition because it does not construct the moduli
curve or its rational-point equivalence. -/
def X0_13_has_genus_zero : Prop :=
  Nonempty X0_13_ModuliCurve

#check torsion13
#check X0_13_Point
#check X0_13_RationalPoints
#check X0_13_ModuliCurve
#check X0_13_has_genus_zero
#check j_of_X0_13

end

end BealMatveevBeal.MazurCurve
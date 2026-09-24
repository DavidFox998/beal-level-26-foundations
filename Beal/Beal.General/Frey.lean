import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
The general integral Frey model and its polynomial invariants. This module
does not establish minimality, a conductor, or a contradiction to a Beal
solution. In particular, it does not construct `commonPrime`.
-/

namespace Beal.General

/-- The model `Y² = X (X - x^p) (X + y^q)`. The third powered
input enters only through a proposed solution equation. -/
def freyWeierstrassGeneral (x y : ℕ) (_z p q _r : ℕ) :
    WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := (y : ℤ) ^ q - (x : ℤ) ^ p
  a₃ := 0
  a₄ := -((x : ℤ) ^ p * (y : ℤ) ^ q)
  a₆ := 0

theorem frey_c4 (x y z p q r : ℕ) :
    (freyWeierstrassGeneral x y z p q r).c₄ =
      16 * (((x : ℤ) ^ p) ^ 2 + (x : ℤ) ^ p * (y : ℤ) ^ q +
        ((y : ℤ) ^ q) ^ 2) := by
  simp [freyWeierstrassGeneral, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem frey_delta_raw (x y z p q r : ℕ) :
    (freyWeierstrassGeneral x y z p q r).Δ =
      16 * ((x : ℤ) ^ p) ^ 2 * ((y : ℤ) ^ q) ^ 2 *
        ((x : ℤ) ^ p + (y : ℤ) ^ q) ^ 2 := by
  simp [freyWeierstrassGeneral, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem frey_delta_on_solution (x y z p q r : ℕ)
    (hsol : x ^ p + y ^ q = z ^ r) :
    (freyWeierstrassGeneral x y z p q r).Δ =
      16 * ((x : ℤ) ^ p) ^ 2 * ((y : ℤ) ^ q) ^ 2 *
        ((z : ℤ) ^ r) ^ 2 := by
  rw [frey_delta_raw]
  have hW : (x : ℤ) ^ p + (y : ℤ) ^ q = (z : ℤ) ^ r := by
    exact_mod_cast hsol
  rw [hW]

#print axioms frey_c4
#print axioms frey_delta_raw
#print axioms frey_delta_on_solution

end Beal.General
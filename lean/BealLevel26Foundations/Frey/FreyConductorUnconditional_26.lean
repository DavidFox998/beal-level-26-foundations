import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic

namespace BealLevel26Foundations.Frey.FreyConductorUnconditional26

open WeierstrassCurve

/-!
# Unconditional Frey invariant algebra

This file defines the integral Frey Weierstrass model and proves its `c₄`,
`c₆`, and discriminant identities directly from Mathlib's definitions.

Mathlib 4.12 has no Tate algorithm, Kodaira reduction type, local conductor
exponent, or elliptic-curve conductor. Consequently this file does not state a
fabricated unconditional conductor equality. The proved invariant identities
are the unconditional input needed by a future formal Tate-algorithm theorem.
-/

/-- The integral Frey model
`Y² = X (X - Aˣ) (X + Bʸ)`. -/
def freyCurve (A B : Int) (x y : Nat) : WeierstrassCurve Int where
  a₁ := 0
  a₂ := B ^ y - A ^ x
  a₃ := 0
  a₄ := -(A ^ x * B ^ y)
  a₆ := 0

theorem freyCurve_equation_coefficients (A B : Int) (x y : Nat) :
    (freyCurve A B x y).a₂ = B ^ y - A ^ x ∧
      (freyCurve A B x y).a₄ = -(A ^ x * B ^ y) :=
  ⟨rfl, rfl⟩

theorem freyCurve_c4 (A B : Int) (x y : Nat) :
    (freyCurve A B x y).c₄ =
      16 * ((A ^ x) ^ 2 + A ^ x * B ^ y + (B ^ y) ^ 2) := by
  simp only [freyCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

theorem freyCurve_c6 (A B : Int) (x y : Nat) :
    (freyCurve A B x y).c₆ =
      -32 * (B ^ y - A ^ x) *
        (2 * (B ^ y - A ^ x) ^ 2 + 9 * (A ^ x * B ^ y)) := by
  simp only [freyCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ring

theorem freyCurve_discriminant (A B : Int) (x y : Nat) :
    (freyCurve A B x y).Δ =
      16 * (A ^ x) ^ 2 * (B ^ y) ^ 2 * (A ^ x + B ^ y) ^ 2 := by
  simp only [freyCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem freyCurve_discriminant_of_equation
    {A B C : Int} {x y z : Nat}
    (hEquation : A ^ x + B ^ y = C ^ z) :
    (freyCurve A B x y).Δ =
      16 * (A ^ x) ^ 2 * (B ^ y) ^ 2 * (C ^ z) ^ 2 := by
  rw [freyCurve_discriminant, hEquation]

#print axioms freyCurve_c4
#print axioms freyCurve_c6
#print axioms freyCurve_discriminant
#print axioms freyCurve_discriminant_of_equation

end BealLevel26Foundations.Frey.FreyConductorUnconditional26
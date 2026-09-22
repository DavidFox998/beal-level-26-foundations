/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Tate_Frey_Conductor_29

/-!
# Numerical local data at `29` for the displayed Frey model

This file packages only theorem terms already justified by the pinned
Lean 4.12 / Mathlib surface:

* the displayed discriminant formula;
* its natural-number counterpart and the `(1,1)` specialization;
* the `29`-adic valuation formula and its divisibility consequence;
* the displayed `32` / `928` branch selector; and
* the arithmetic identity `928 = 32 * 29`.

It does not claim Tate uniformization, a Kodaira symbol, a Néron conductor,
an elliptic-curve Galois representation, or an inertia theorem.
-/

namespace BealMatveevBeal.Tate_Frey_Conductor_29_Numerical

open BealMatveevBeal.BealMatveevBealV25B0Search
open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.Level928Table
open BealMatveevBeal.Tate_I29_Inertia
open BealMatveevBeal.Tate_Frey_Conductor_29

/-- Discriminant of the displayed integral Frey model. -/
theorem frey_discriminant_formula (A B : ℕ) :
    (freyWeierstrass A B).Δ =
      (16 : ℤ) * (A : ℤ) ^ 8 * (B : ℤ) ^ 8 *
        ((A : ℤ) ^ 4 + (B : ℤ) ^ 4) ^ 2 :=
  freyWeierstrass_Δ_reexport A B

/-- Natural-number form of the displayed discriminant. -/
theorem frey_discriminant_nat_formula (A B : ℕ) :
    freyDiscNat A B = 16 * A ^ 8 * B ^ 8 * (A ^ 4 + B ^ 4) ^ 2 :=
  freyDiscNat_formula A B

/-- Integer discriminant at `(A,B)=(1,1)`. -/
theorem frey_discriminant_one_one :
    (freyWeierstrass 1 1).Δ = 64 :=
  freyWeierstrass_Δ_1_1

/-- Natural-number discriminant at `(A,B)=(1,1)`. -/
theorem frey_discriminant_nat_one_one :
    freyDiscNat 1 1 = 64 :=
  freyDiscNat_1_1

/-- On a gap-3 solution with `29 ∤ A B`, the displayed discriminant
has valuation `26 v₂₉(B+3)`. -/
theorem valuation_discriminant_at_29 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    Padic.valuation (freyDisc_in_Qp29 A B) =
      26 * (padicValNat 29 (B + 3) : ℤ) :=
  v29_Delta_eq_26_vC_reexport hsol hBpos hA hB

/-- If additionally `29 ∣ B+3`, then `13` divides the displayed
`29`-adic discriminant valuation. -/
theorem thirteen_dvd_valuation_discriminant_at_29 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    (13 : ℤ) ∣ Padic.valuation (freyDisc_in_Qp29 A B) :=
  BealMatveevBeal.Tate_I29_Inertia.thirteen_dvd_padic_valuation_Delta
    hsol hBpos hA hB hC

/-- The displayed branch selector is `32` when `29` divides neither
`A` nor `B`. This is not a Néron-conductor theorem. -/
theorem displayed_level_eq_32 {A B : ℕ}
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    level_after_ribet_29 A B = 32 :=
  displayed_residual_32_of_nmid_AB hA hB

/-- The displayed branch selector is `928` when `29 ∣ A` or `29 ∣ B`.
This is not a Néron-conductor theorem. -/
theorem displayed_level_eq_928 {A B : ℕ}
    (h : 29 ∣ A ∨ 29 ∣ B) :
    level_after_ribet_29 A B = 928 :=
  displayed_residual_928_of_dvd_AB h

theorem nine_twenty_eight_div_twenty_nine_numerical :
    (928 : ℕ) / 29 = 32 :=
  nine_twenty_eight_div_twenty_nine

theorem thirty_two_mul_twenty_nine_numerical :
    (32 : ℕ) * 29 = 928 :=
  thirty_two_mul_twenty_nine_reexport

#check frey_discriminant_formula
#check frey_discriminant_nat_formula
#check frey_discriminant_one_one
#check frey_discriminant_nat_one_one
#check valuation_discriminant_at_29
#check thirteen_dvd_valuation_discriminant_at_29
#check displayed_level_eq_32
#check displayed_level_eq_928
#check nine_twenty_eight_div_twenty_nine_numerical
#check thirty_two_mul_twenty_nine_numerical

#print axioms frey_discriminant_formula
#print axioms valuation_discriminant_at_29
#print axioms thirteen_dvd_valuation_discriminant_at_29
#print axioms displayed_level_eq_32

end BealMatveevBeal.Tate_Frey_Conductor_29_Numerical
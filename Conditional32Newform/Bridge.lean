/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Tate_Frey_Conductor_29_Numerical
import Mazur_X0_13_Numerical
import Ribet_928_to_32_Numerical

/-!
# Conditional level-32 newform bridge

This module packages the proved numerical Frey surface together with exactly
three named, uninhabited assumptions:

* the Frey-specific Mazur irreducibility boundary;
* the Tate/Néron conductor identification; and
* Ribet lowering from `928` to `32`.

`HasNewformAtLevel32` is an evidence record for this conditional chain.  It is
not a Mathlib modular-form construction and no term for any assumption is
created here.
-/

namespace BealMatveevBeal.Conditional32Newform

open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.Level928Table
open BealMatveevBeal.Tate_I29_Inertia
open BealMatveevBeal.Mazur_X0_13_No_Isogeny
open BealMatveevBeal.Tate_Frey_Conductor_29
open BealMatveevBeal.Ribet_Level_Lowering_29_to_32
open BealMatveevBeal.Tate_Frey_Conductor_29_Numerical
open BealMatveevBeal.Ribet_928_to_32_Numerical

/-- Conditional evidence at the displayed level `32`.

The first six fields are proved numerical data.  The final three fields expose
the precise Mazur, Tate, and Ribet assumptions rather than hiding them behind
an unconditional-sounding theorem. -/
structure HasNewformAtLevel32 (A B : ℕ) : Prop where
  frey_discriminant :
    (freyWeierstrass A B).Δ =
      (16 : ℤ) * (A : ℤ) ^ 8 * (B : ℤ) ^ 8 *
        ((A : ℤ) ^ 4 + (B : ℤ) ^ 4) ^ 2
  valuation_at_29 :
    Padic.valuation (freyDisc_in_Qp29 A B) =
      26 * (padicValNat 29 (B + 3) : ℤ)
  thirteen_dvd_valuation :
    (13 : ℤ) ∣ Padic.valuation (freyDisc_in_Qp29 A B)
  displayed_level_32 :
    level_after_ribet_29 A B = 32
  nine_twenty_eight_div_twenty_nine :
    (928 : ℕ) / 29 = 32
  thirty_two_mul_twenty_nine :
    (32 : ℕ) * 29 = 928
  hMazur : frey_no_rational_13_isogeny
  hTate : Frey_conductor_29_is_Neron
  hRibet : Ribet_928_to_32

/-- The numerical Frey-to-level-`32` bridge, conditional on exactly the three
named library-scale assumptions. -/
theorem has_newform_at_level_32_of_assumptions {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3)
    (hMazur : frey_no_rational_13_isogeny)
    (hTate : Frey_conductor_29_is_Neron)
    (hRibet : Ribet_928_to_32) :
    HasNewformAtLevel32 A B :=
  { frey_discriminant := frey_discriminant_formula A B
    valuation_at_29 :=
      valuation_discriminant_at_29 hsol hBpos hA hB
    thirteen_dvd_valuation :=
      thirteen_dvd_valuation_discriminant_at_29 hsol hBpos hA hB hC
    displayed_level_32 := displayed_level_eq_32 hA hB
    nine_twenty_eight_div_twenty_nine :=
      BealMatveevBeal.Ribet_928_to_32_Numerical.nine_twenty_eight_div_twenty_nine_numerical
    thirty_two_mul_twenty_nine :=
      BealMatveevBeal.Ribet_928_to_32_Numerical.thirty_two_mul_twenty_nine_numerical
    hMazur := hMazur
    hTate := hTate
    hRibet := hRibet }

#check HasNewformAtLevel32
#check has_newform_at_level_32_of_assumptions

#print axioms has_newform_at_level_32_of_assumptions

end BealMatveevBeal.Conditional32Newform
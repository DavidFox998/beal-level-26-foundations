/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import KolyvaginCurve.LFunction
import Kolyvagin_MW_Rank0_Numerical

/-!
# Real periods and normalized central values

The project proves the displayed rationals `1/3` and `1/7`.  This module
defines the missing analytic objects needed to interpret those rationals as
`L(E,1) / Ω_E`.  An equality with the normalized analytic value is an
explicit input; it is not inferred from the displayed numeral.
-/

namespace BealMatveevBeal.KolyvaginCurve

/-- Positive real-period data for an elliptic curve over `ℚ`. -/
structure RealPeriod (E : WeierstrassCurve ℚ) where
  omega : ℝ
  omega_pos : 0 < omega

/-- The formal normalized central value `L(E,1) / Ω_E`. -/
noncomputable def analyticLOverOmega {E : WeierstrassCurve ℚ}
    (L : EllipticCurveLFunction E) (period : RealPeriod E) : ℂ :=
  L 1 / (period.omega : ℂ)

/-- Identification of a displayed rational with a constructed analytic
normalized central value. -/
structure LOverOmegaIdentification {E : WeierstrassCurve ℚ}
    (L : EllipticCurveLFunction E) (period : RealPeriod E)
    (displayed : ℚ) : Prop where
  normalized_eq :
    analyticLOverOmega L period = (displayed : ℂ)

/-- Existing displayed rational `L/Ω` value for `26a1`. -/
def displayedLOverOmega26a1 : ℚ :=
  BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26a1

/-- Existing displayed rational `L/Ω` value for `26b1`. -/
def displayedLOverOmega26b1 : ℚ :=
  BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26b1

theorem displayedLOverOmega26a1_eq_one_third :
    displayedLOverOmega26a1 = (1 / 3 : ℚ) :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.l_over_omega_26a1_one_third_numerical

theorem displayedLOverOmega26b1_eq_one_seventh :
    displayedLOverOmega26b1 = (1 / 7 : ℚ) :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.l_over_omega_26b1_one_seventh_numerical

theorem displayedLOverOmega26a1_ne_zero :
    displayedLOverOmega26a1 ≠ 0 :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.l_over_omega_26a1_nonzero_numerical

theorem displayedLOverOmega26b1_ne_zero :
    displayedLOverOmega26b1 ≠ 0 :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.l_over_omega_26b1_nonzero_numerical

/-- A nonzero identified normalized value forces formal analytic
nonvanishing.  This is forward-only and does not construct the period,
`L`-function, or identification. -/
theorem nonzeroAtOne_of_identified_normalized_value
    {E : WeierstrassCurve ℚ}
    {L : EllipticCurveLFunction E} {period : RealPeriod E}
    {displayed : ℚ}
    (hident : LOverOmegaIdentification L period displayed)
    (hdisplayed : displayed ≠ 0) :
    L.NonzeroAtOne := by
  intro hzero
  have hnormalized : analyticLOverOmega L period = 0 := by
    simp [analyticLOverOmega, hzero]
  have hcast : (displayed : ℂ) = 0 := by
    rw [← hident.normalized_eq, hnormalized]
  exact hdisplayed (Rat.cast_eq_zero.mp hcast)

#check RealPeriod
#check analyticLOverOmega
#check LOverOmegaIdentification
#check displayedLOverOmega26a1_eq_one_third
#check displayedLOverOmega26b1_eq_one_seventh
#check nonzeroAtOne_of_identified_normalized_value

end BealMatveevBeal.KolyvaginCurve
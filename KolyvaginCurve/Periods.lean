/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Kolyvagin_MW_Rank0_Numerical

/-!
# Displayed periods and rational `L/Ω` values

The project records rational values `1/3` and `1/7`. These are numerical
certificates, not formal values of an elliptic-curve `L`-function. The
missing bridge identifies the recorded rational quotient with
`L(E,1) / Ω_E` for a constructed period and `L`-function.
-/

namespace BealMatveevBeal.KolyvaginCurve

/-- Existing displayed rational `L/Ω` value for `26a1`. -/
def L_over_Omega_26a1 : ℚ :=
  BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26a1

/-- Existing displayed rational `L/Ω` value for `26b1`. -/
def L_over_Omega_26b1 : ℚ :=
  BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26b1

theorem L_over_Omega_26a1_eq_one_third :
    L_over_Omega_26a1 = (1 / 3 : ℚ) :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.l_over_omega_26a1_one_third_numerical

theorem L_over_Omega_26b1_eq_one_seventh :
    L_over_Omega_26b1 = (1 / 7 : ℚ) :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.l_over_omega_26b1_one_seventh_numerical

theorem L_over_Omega_26a1_ne_zero : L_over_Omega_26a1 ≠ 0 :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.l_over_omega_26a1_nonzero_numerical

theorem L_over_Omega_26b1_ne_zero : L_over_Omega_26b1 ≠ 0 :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.l_over_omega_26b1_nonzero_numerical

#check L_over_Omega_26a1_eq_one_third
#check L_over_Omega_26b1_eq_one_seventh

end BealMatveevBeal.KolyvaginCurve